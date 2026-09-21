"""
지방소멸대응기금 뉴스 자동 스크랩 & 텔레그램 전송

- 네이버 뉴스 검색 API + 구글 뉴스 RSS
- 제목 유사도 / 링크 기준 중복 제거 (같은 실행 내)
- 저장소에 커밋되는 sent_history.json으로 발송 이력을 기억해서
  오전 회차에 보낸 기사가 오후 회차에 다시 발송되지 않도록 방지
- GitHub Actions에서 한국시간 매일 08:50, 16:50 자동 실행
- 오전 회차: 실제 실행 시각 기준 최근 16시간
- 오후 회차: 실제 실행 시각 기준 최근 8시간
- 지연·실패 시 마지막 정상 조회 시각부터 재조회 (최대 48시간)
- 성공한 메시지에 포함된 기사만 즉시 발송 이력에 기록
- 예약 실행이 지연돼도 GitHub 예약 정보(NEWS_SCHEDULE)로 회차 구분
- 메시지에 예약 회차와 실제 시작 시각을 구분해 표시
- 텔레그램 HTML 포맷 및 분할 전송

[수정 사항 - 2026-09]
- 네이버 API 실패 시 원인(HTTP 상태 코드/응답 본문/예외 메시지)을 로그에 상세히 기록
- 5xx/일시적 오류로 판단되면 네이버 API 요청을 1회 자동 재시도
- 뉴스 소스 중 일부만 실패했는데 텔레그램 발송 자체는 성공한 경우,
  더 이상 워크플로를 실패로 표시하지 않고 경고 로그만 남김
  (실제 발송이 실패했을 때만 워크플로를 실패 처리)
- 네이버·구글 뉴스 수집이 모두 실패해 이번 회차에 기사를 하나도
  보내지 못한 경우, GitHub Actions 로그와 별도로 텔레그램에도
  오류 알림을 전송
"""

import os
import re
import sys
import json
import html
import time
import logging
from datetime import datetime, timezone, timedelta
from email.utils import parsedate_to_datetime
from difflib import SequenceMatcher
from urllib.parse import quote

import requests
import feedparser


# ------------------------------------------------------------------
# 기본 설정
# ------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
logger = logging.getLogger(__name__)

SEARCH_KEYWORD = "지방소멸대응기금"

NAVER_CLIENT_ID = (os.environ.get("NAVER_CLIENT_ID") or "").strip()
NAVER_CLIENT_SECRET = (os.environ.get("NAVER_CLIENT_SECRET") or "").strip()
TELEGRAM_TOKEN = (os.environ.get("TELEGRAM_TOKEN") or "").strip()
TELEGRAM_CHAT_ID = (os.environ.get("TELEGRAM_CHAT_ID") or "").strip()

# 2026년부터 네이버 검색 오픈API는 NAVER API HUB(네이버클라우드플랫폼)로 이관되어,
# 요청 주소와 인증 헤더 이름이 기존 개발자센터 방식과 다릅니다.
# (기존: openapi.naver.com + X-Naver-Client-Id/Secret
#  신규: naverapihub.apigw.ntruss.com + X-NCP-APIGW-API-KEY-ID/KEY)
# 응답 JSON 구조(items/title/originallink/link/description/pubDate)는 동일합니다.
NAVER_NEWS_URL = "https://naverapihub.apigw.ntruss.com/search/v1/news"
GOOGLE_NEWS_RSS_URL = (
    "https://news.google.com/rss/search?q={query}&hl=ko&gl=KR&ceid=KR:ko"
)
TELEGRAM_SEND_URL = "https://api.telegram.org/bot{token}/sendMessage"

TITLE_SIMILARITY_THRESHOLD = 0.72
NAVER_DISPLAY_COUNT = 30
TELEGRAM_MAX_LEN = 4000

# 네이버 API가 일시적 오류(5xx, 타임아웃, 연결 오류)로 보일 때
# 이 시간(초)만큼 대기한 뒤 1회만 재시도합니다. 인증 오류(4xx)는
# 재시도해도 소용없으므로 재시도하지 않고 바로 실패 처리합니다.
NAVER_RETRY_DELAY_SECONDS = 3

KST = timezone(timedelta(hours=9))

# GitHub 예약식(UTC)을 기준으로 회차를 구분합니다.
# 실제 실행이 지연돼도 오전·오후 구분은 유지됩니다.
RUN_SCHEDULE = {
    "50 23 * * *": {
        "label": "08:50 자동실행",
        "lookback_hours": 16,
    },
    "50 7 * * *": {
        "label": "16:50 자동실행",
        "lookback_hours": 8,
    },
}

DEFAULT_LOOKBACK_HOURS = 16

# 발송 이력 파일 (저장소 루트에 커밋되어 실행 간에 이어집니다)
HISTORY_FILE = "sent_history.json"
# 최대 lookback(16시간)보다 여유 있게 잡아, 지연 실행 상황에서도
# 과거 발송 기록과 안전하게 대조할 수 있도록 합니다.
HISTORY_RETENTION_HOURS = 48
MAX_LOOKBACK_HOURS = 48
WINDOW_OVERLAP_MINUTES = 5


# ------------------------------------------------------------------
# 공용 유틸
# ------------------------------------------------------------------
def strip_tags(text: str) -> str:
    """HTML 태그 제거 및 엔티티 변환."""
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", "", text)
    return html.unescape(text).strip()


def truncate_summary(text: str, max_chars: int = 160) -> str:
    """요약 길이 제한."""
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= max_chars:
        return text
    return text[:max_chars].rstrip() + "..."


def normalize_title(title: str) -> str:
    """유사도 비교용 제목 정규화."""
    title = strip_tags(title)
    title = re.sub(r"[^0-9a-zA-Z가-힣]", "", title)
    return title.lower()


def normalize_link(link: str) -> str:
    if not link:
        return ""
    link = link.strip().rstrip("/")
    return re.sub(r"^https?://(www\.)?", "", link)


def is_similar_title(a: str, b: str) -> bool:
    a_norm = normalize_title(a)
    b_norm = normalize_title(b)

    if not a_norm or not b_norm:
        return False

    ratio = SequenceMatcher(None, a_norm, b_norm).ratio()
    return ratio >= TITLE_SIMILARITY_THRESHOLD


def get_run_context() -> dict:
    """실제 시작 시각이 아닌 GitHub 예약 정보로 오전·오후를 구분."""
    now_utc = datetime.now(timezone.utc)
    now_kst = now_utc.astimezone(KST)

    event_name = os.environ.get("GITHUB_EVENT_NAME", "").strip()
    cron = os.environ.get("NEWS_SCHEDULE", "").strip()

    if event_name == "schedule":
        schedule = RUN_SCHEDULE.get(cron)

        if schedule is None:
            raise ValueError(
                f"알 수 없는 예약 설정: {cron!r}. "
                "news_cron.yml을 확인하세요."
            )

        label = schedule["label"]
        lookback_hours = schedule["lookback_hours"]

    else:
        label = (
            "수동실행"
            if event_name == "workflow_dispatch"
            else "별도실행"
        )
        lookback_hours = DEFAULT_LOOKBACK_HOURS

    logger.info(
        "실행 유형=%s / 예약=%s",
        event_name,
        cron,
    )

    return {
        "now_utc": now_utc,
        "label": label,
        "actual_start_kst": now_kst.strftime("%Y-%m-%d %H:%M:%S"),
        "lookback_hours": lookback_hours,
        "cutoff_utc": now_utc - timedelta(hours=lookback_hours),
    }


def parse_naver_date(pub_date: str):
    """네이버 기사 발행일을 UTC로 변환."""
    if not pub_date:
        return None

    try:
        dt = parsedate_to_datetime(pub_date)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def parse_google_date(entry):
    """구글 RSS 기사 발행일을 UTC로 변환."""
    struct = entry.get("published_parsed")
    if not struct:
        return None

    try:
        return datetime(*struct[:6], tzinfo=timezone.utc)
    except (TypeError, ValueError):
        return None


# ------------------------------------------------------------------
# 1. 네이버 뉴스 수집
# ------------------------------------------------------------------
def _request_naver(keyword: str) -> dict:
    """네이버 뉴스 검색 API를 1회 호출. 실패 시 requests 예외를 그대로 전파."""
    headers = {
        "X-NCP-APIGW-API-KEY-ID": NAVER_CLIENT_ID,
        "X-NCP-APIGW-API-KEY": NAVER_CLIENT_SECRET,
    }
    params = {
        "query": keyword,
        "display": NAVER_DISPLAY_COUNT,
        "start": 1,
        "sort": "date",
    }
    resp = requests.get(
        NAVER_NEWS_URL,
        headers=headers,
        params=params,
        timeout=10,
    )
    resp.raise_for_status()
    return resp.json()


def fetch_naver_news(keyword: str) -> list:
    if not NAVER_CLIENT_ID or not NAVER_CLIENT_SECRET:
        raise RuntimeError("네이버 API 키가 설정되지 않았습니다.")

    data = None
    last_error = None

    # 최대 2회 시도(최초 1회 + 일시적 오류로 보일 때 1회 재시도).
    for attempt in range(2):
        try:
            data = _request_naver(keyword)
            break

        except requests.RequestException as e:
            status = getattr(e.response, "status_code", None)
            body = ""
            if e.response is not None:
                body = e.response.text[:300]

            last_error = RuntimeError(
                f"네이버 뉴스 API 요청 실패 "
                f"(status={status}, body={body!r}, error={e})"
            )

            # 상태 코드를 알 수 없거나(타임아웃/연결 오류) 5xx면 일시적 문제로
            # 보고 한 번만 재시도합니다. 401/403/429 같은 4xx는 재시도해도
            # 같은 결과이므로 바로 실패 처리합니다.
            transient = status is None or status >= 500
            if attempt == 0 and transient:
                logger.warning(
                    "네이버 뉴스 API 일시 오류로 판단, %s초 후 재시도합니다 "
                    "(status=%s)",
                    NAVER_RETRY_DELAY_SECONDS,
                    status,
                )
                time.sleep(NAVER_RETRY_DELAY_SECONDS)
                continue

            raise last_error from e

        except ValueError as e:
            raise RuntimeError(f"네이버 뉴스 API 응답 파싱 실패: {e}") from e

    if data is None:
        raise last_error or RuntimeError("네이버 뉴스 API 요청 실패 (원인 불명)")

    results = []

    for item in data.get("items", []):
        title = strip_tags(item.get("title", ""))
        description = strip_tags(item.get("description", ""))
        link = item.get("originallink") or item.get("link", "")
        pub_date = parse_naver_date(item.get("pubDate", ""))

        if not title or not link:
            continue

        results.append(
            {
                "title": title,
                "summary": truncate_summary(description),
                "link": link,
                "pub_date": pub_date,
                "source": "네이버뉴스",
            }
        )

    logger.info("네이버 뉴스 %s건 수집", len(results))
    return results


# ------------------------------------------------------------------
# 2. 구글 뉴스 RSS 수집
# ------------------------------------------------------------------
def fetch_google_news(keyword: str) -> list:
    url = GOOGLE_NEWS_RSS_URL.format(query=quote(keyword))

    try:
        # 통신 제한시간을 지정한 뒤 RSS 내용을 파싱합니다.
        resp = requests.get(url, timeout=20)
        resp.raise_for_status()
        feed = feedparser.parse(resp.content)

    except Exception as e:
        raise RuntimeError(f"구글 뉴스 RSS 수집 실패: {e}") from e

    if getattr(feed, "bozo", 0) and not feed.entries:
        raise RuntimeError("구글 뉴스 RSS 응답 형식 오류")

    results = []

    for entry in feed.entries:
        title = strip_tags(entry.get("title", ""))
        title = re.sub(r"\s*-\s*[^-]{1,30}$", "", title).strip() or title

        description = strip_tags(
            entry.get("summary", "") or entry.get("description", "")
        )
        link = entry.get("link", "")
        pub_date = parse_google_date(entry)

        source = ""
        if "source" in entry and hasattr(entry.source, "title"):
            source = entry.source.title

        if not title or not link:
            continue

        results.append(
            {
                "title": title,
                "summary": truncate_summary(description),
                "link": link,
                "pub_date": pub_date,
                "source": source or "구글뉴스",
            }
        )

    logger.info("구글 뉴스 %s건 수집", len(results))
    return results


# ------------------------------------------------------------------
# 3. 시간 필터링
# ------------------------------------------------------------------
def filter_recent_articles(
    articles: list,
    cutoff_utc: datetime,
    now_utc: datetime,
) -> list:
    """조회 범위 안의 기사만 유지. 발행일 불명 기사는 기존 방식대로 포함."""
    filtered = []

    for article in articles:
        pub_date = article.get("pub_date")

        if pub_date is None:
            logger.warning(
                "발행일 파싱 실패로 필터 없이 포함: %s",
                article["title"],
            )
            filtered.append(article)
            continue

        if cutoff_utc <= pub_date <= now_utc + timedelta(minutes=5):
            filtered.append(article)

    logger.info(
        "시간 필터링(%s ~ %s) 후 %s건 / 필터 전 %s건",
        cutoff_utc.isoformat(),
        now_utc.isoformat(),
        len(filtered),
        len(articles),
    )
    return filtered


# ------------------------------------------------------------------
# 4. 중복 제거 (같은 실행 내)
# ------------------------------------------------------------------
def deduplicate(articles: list) -> list:
    """이번 실행에서 수집한 기사끼리 중복 제거."""
    unique = []
    seen_links = set()

    for article in articles:
        norm_link = normalize_link(article["link"])

        if norm_link and norm_link in seen_links:
            continue

        is_dup = False

        for kept in unique:
            if norm_link and normalize_link(kept["link"]) == norm_link:
                is_dup = True
                break

            if is_similar_title(article["title"], kept["title"]):
                is_dup = True
                break

        if is_dup:
            continue

        unique.append(article)

        if norm_link:
            seen_links.add(norm_link)

    logger.info(
        "중복 제거 후 %s건 / 원본 %s건",
        len(unique),
        len(articles),
    )
    return unique


# ------------------------------------------------------------------
# 5. 발송 이력 (오전/오후 회차 간 중복 방지)
# ------------------------------------------------------------------
def load_state() -> dict:
    """기존 목록 형식의 이력도 읽고, 새 형식으로 자동 전환합니다."""
    if not os.path.exists(HISTORY_FILE):
        return {"version": 2, "articles": [], "last_checked_utc": None}
    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError) as e:
        raise RuntimeError("발송 이력 읽기 실패. 기존 파일을 확인하세요.") from e
    if isinstance(data, list):
        return {"version": 2, "articles": data, "last_checked_utc": None}
    if isinstance(data, dict) and isinstance(data.get("articles"), list):
        return data
    raise RuntimeError("sent_history.json의 형식이 올바르지 않습니다.")


def prune_history(history: list, now_utc: datetime) -> list:
    """최근 48시간의 정상적인 발송 기록을 유지합니다."""
    cutoff = now_utc - timedelta(hours=HISTORY_RETENTION_HOURS)
    result = []
    for entry in history:
        if not isinstance(entry, dict):
            logger.warning("형식이 잘못된 발송 기록 1건 제외")
            continue
        try:
            sent_at = datetime.fromisoformat(entry.get("sent_at", ""))
            if sent_at.tzinfo is None:
                logger.warning("시간대가 없는 기존 발송 기록은 UTC로 해석합니다.")
                sent_at = sent_at.replace(tzinfo=timezone.utc)
            if not isinstance(entry.get("link", ""), str):
                raise ValueError("잘못된 링크")
            if not isinstance(entry.get("title_norm", ""), str):
                raise ValueError("잘못된 제목")
        except (TypeError, ValueError):
            logger.warning("날짜 또는 내용이 잘못된 발송 기록 1건 제외")
            continue
        if sent_at >= cutoff:
            result.append(entry)
    return result


def save_state(state: dict) -> None:
    """임시 파일을 작성한 뒤 교체하여 이력을 보존합니다."""
    temp_path = HISTORY_FILE + ".tmp"
    try:
        with open(temp_path, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
            f.write("\n")
        os.replace(temp_path, HISTORY_FILE)
    except OSError as e:
        raise RuntimeError("발송 이력 저장 실패") from e


def extend_window(run_ctx: dict, state: dict) -> dict:
    """기본 조회 범위와 마지막 정상 조회 시각 중 더 이른 시각부터 조회."""
    cutoff = run_ctx["cutoff_utc"]
    raw = state.get("last_checked_utc")
    if raw:
        try:
            last = datetime.fromisoformat(raw)
            if last.tzinfo is None:
                raise ValueError("시간대 없음")
            if last > run_ctx["now_utc"]:
                raise ValueError("미래 시각")
            cutoff = min(cutoff, last - timedelta(minutes=WINDOW_OVERLAP_MINUTES))
        except (TypeError, ValueError):
            logger.warning("마지막 조회 시각 오류: 최근 48시간을 다시 조회합니다.")
            cutoff = run_ctx["now_utc"] - timedelta(hours=MAX_LOOKBACK_HOURS)
    earliest = run_ctx["now_utc"] - timedelta(hours=MAX_LOOKBACK_HOURS)
    if cutoff < earliest:
        logger.warning("미조회 기간이 48시간을 초과하여 최근 48시간만 복구 조회합니다.")
        cutoff = earliest
    run_ctx["cutoff_utc"] = cutoff
    return run_ctx


def is_in_history(article: dict, history: list) -> bool:
    """링크가 같거나 제목이 유사한 기사가 이미 발송 이력에 있는지 확인."""
    norm_link = normalize_link(article["link"])
    title_norm = normalize_title(article["title"])

    for entry in history:
        if norm_link and entry.get("link") == norm_link:
            return True

        entry_title = entry.get("title_norm", "")
        if entry_title and title_norm:
            ratio = SequenceMatcher(None, title_norm, entry_title).ratio()
            if ratio >= TITLE_SIMILARITY_THRESHOLD:
                return True

    return False


def filter_against_history(articles: list, history: list) -> list:
    """이전 회차(들)에서 이미 보낸 기사를 제외한다."""
    filtered = [a for a in articles if not is_in_history(a, history)]

    logger.info(
        "발송 이력 대조 후 %s건 / 대조 전 %s건",
        len(filtered),
        len(articles),
    )
    return filtered


def append_to_history(history: list, articles: list, now_utc: datetime) -> list:
    sent_at_str = now_utc.isoformat()
    for article in articles:
        history.append(
            {
                "link": normalize_link(article["link"]),
                "title_norm": normalize_title(article["title"]),
                "sent_at": sent_at_str,
            }
        )
    return history


# ------------------------------------------------------------------
# 6. 텔레그램 메시지 작성
# ------------------------------------------------------------------
def escape_html(text: str) -> str:
    return html.escape(text, quote=False)


def build_messages(articles: list, run_ctx: dict) -> list:
    """각 메시지와 그 메시지에 포함된 기사 목록을 함께 반환합니다."""
    start = run_ctx["cutoff_utc"].astimezone(KST).strftime("%m-%d %H:%M")
    end = run_ctx["now_utc"].astimezone(KST).strftime("%m-%d %H:%M")
    header = (
        f"📰 <b>{escape_html(SEARCH_KEYWORD)} 뉴스 브리핑</b>\n"
        f"예약 회차: {escape_html(run_ctx['label'])}\n"
        f"실제 시작: {escape_html(run_ctx['actual_start_kst'])} KST\n"
        f"조회 범위: {start} ~ {end} KST\n"
        "이미 발송한 기사 제외\n"
    )
    if run_ctx.get("source_errors"):
        header += "⚠ 일부 뉴스 수집 실패. 수집된 기사만 전송합니다.\n"
    if not articles:
        return [(header + "\n추가로 발송할 기사가 없습니다.", [])]
    header += f"총 {len(articles)}건\n\n"
    messages, included = [], []
    current = header
    for idx, article in enumerate(articles, start=1):
        title = escape_html(article["title"])
        summary = escape_html(article["summary"])
        link = html.escape(article["link"], quote=True)
        source = escape_html(article["source"])
        block = f"{idx}. <b>{title}</b>\n({source})\n"
        if summary:
            block += summary + "\n"
        block += f'<a href="{link}">기사 원문 보기</a>\n\n'
        if len(block.encode("utf-16-le")) // 2 > TELEGRAM_MAX_LEN:
            raise ValueError("단일 기사 메시지가 너무 깁니다.")
        if len((current + block).encode("utf-16-le")) // 2 > TELEGRAM_MAX_LEN:
            messages.append((current.rstrip(), included))
            current, included = "", []
        current += block
        included.append(article)
    if current.strip():
        messages.append((current.rstrip(), included))
    return messages


# ------------------------------------------------------------------
# 7. 텔레그램 전송
# ------------------------------------------------------------------
def send_telegram_message(text: str) -> bool:
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        logger.error(
            "TELEGRAM_TOKEN 또는 TELEGRAM_CHAT_ID가 설정되지 않았습니다."
        )
        return False

    url = TELEGRAM_SEND_URL.format(token=TELEGRAM_TOKEN)
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }

    try:
        resp = requests.post(url, data=payload, timeout=10)
        resp.raise_for_status()
        result = resp.json()

        if not result.get("ok"):
            logger.error(
                "텔레그램 API가 전송 실패를 반환했습니다: %s",
                result.get("description", "(설명 없음)"),
            )
            return False

        logger.info(
            "텔레그램 전송 성공 / 한국시간 %s",
            datetime.now(KST).strftime("%Y-%m-%d %H:%M:%S"),
        )
        return True

    except (requests.RequestException, ValueError) as e:
        # 예외 메시지의 요청 URL에 포함될 수 있는 토큰을 가립니다.
        safe_error = str(e).replace(TELEGRAM_TOKEN, "[REDACTED]")
        logger.error("텔레그램 전송 실패: %s", safe_error)
        return False


# ------------------------------------------------------------------
# 메인 실행
# ------------------------------------------------------------------
def main():
    run_ctx = get_run_context()
    state = load_state()
    state["version"] = 2
    state["articles"] = prune_history(state["articles"], run_ctx["now_utc"])
    run_ctx = extend_window(run_ctx, state)
    save_state(state)
    logger.info(
        "회차=%s / 실제 시작(KST)=%s / 조회 시작(UTC)=%s",
        run_ctx["label"], run_ctx["actual_start_kst"],
        run_ctx["cutoff_utc"].isoformat(),
    )
    articles, errors = [], []
    for name, fetch in [("네이버", fetch_naver_news), ("구글", fetch_google_news)]:
        try:
            articles.extend(fetch(SEARCH_KEYWORD))
        except Exception as e:
            # 실패 원인을 그대로 로그에 남깁니다 (기존에는 예외 타입 이름만
            # 남아 원인 파악이 불가능했습니다).
            logger.error("%s 수집 실패: %s", name, e)
            errors.append(name)
    run_ctx["source_errors"] = errors

    if len(errors) == 2:
        # 두 소스 모두 실패해 이번 회차엔 보낼 기사가 전혀 없는 상태.
        # GitHub Actions 로그만으로는 바로 알기 어려우니 텔레그램에도 알립니다.
        alert_text = (
            f"⚠ <b>{escape_html(SEARCH_KEYWORD)} 뉴스 봇 오류</b>\n"
            f"예약 회차: {escape_html(run_ctx['label'])}\n"
            f"실제 시작: {escape_html(run_ctx['actual_start_kst'])} KST\n"
            "네이버·구글 뉴스 수집이 모두 실패하여 "
            "이번 회차는 기사를 보내지 못했습니다.\n"
            "GitHub Actions 실행 로그를 확인해주세요."
        )
        send_telegram_message(alert_text)
        raise RuntimeError("모든 뉴스 수집 실패. 조회 완료 시각은 갱신하지 않습니다.")

    recent = filter_recent_articles(articles, run_ctx["cutoff_utc"], run_ctx["now_utc"])
    recent.sort(
        key=lambda a: a["pub_date"] or datetime.min.replace(tzinfo=timezone.utc),
        reverse=True,
    )
    new_articles = filter_against_history(deduplicate(recent), state["articles"])
    messages = build_messages(new_articles, run_ctx)
    success_count = 0
    for message, included in messages:
        if send_telegram_message(message):
            success_count += 1
            # 일부 메시지만 성공해도 그 메시지에 포함된 기사만 즉시 기록.
            state["articles"] = append_to_history(
                state["articles"], included, datetime.now(timezone.utc)
            )
            save_state(state)
        time.sleep(1)

    all_sent = success_count == len(messages)
    # last_checked_utc는 "이번 회차의 모든 소스를 문제없이 확인했다"는
    # 의미이므로, 일부 소스가 실패했다면 갱신하지 않아 다음 회차가
    # 그 구간을 다시 조회하도록 그대로 둡니다.
    if all_sent and not errors:
        state["last_checked_utc"] = run_ctx["now_utc"].isoformat()
    save_state(state)
    logger.info("메시지 %s/%s개 전송 성공", success_count, len(messages))

    if not all_sent:
        # 텔레그램 발송 자체가 실패한 경우만 워크플로를 실패로 표시합니다.
        logger.error(
            "텔레그램 발송 실패: %s/%s개만 성공", success_count, len(messages)
        )
        sys.exit(1)

    if errors:
        # 발송은 정상적으로 끝났지만 일부 소스가 실패한 경우.
        # 메시지 헤더에도 이미 경고가 포함되어 있으므로(build_messages),
        # 여기서는 워크플로를 실패로 표시하지 않고 로그만 남깁니다.
        logger.warning(
            "일부 뉴스 소스 수집 실패로 이번 회차는 해당 소스 기사가 "
            "빠졌을 수 있습니다: %s",
            ", ".join(errors),
        )


if __name__ == "__main__":
    main()
