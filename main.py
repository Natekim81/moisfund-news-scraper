"""
지방소멸대응기금 뉴스 자동 스크랩 & 텔레그램 전송

- 네이버 뉴스 검색 API + 구글 뉴스 RSS
- 제목 유사도 / 링크 기준 중복 제거 (같은 실행 내)
- 저장소에 커밋되는 sent_history.json으로 발송 이력을 기억해서
  오전 회차에 보낸 기사가 오후 회차에 다시 발송되지 않도록 방지
- GitHub Actions에서 한국시간 매일 08:50, 16:50 자동 실행
- 오전 회차: 실제 실행 시각 기준 최근 16시간
- 오후 회차: 실제 실행 시각 기준 최근 8시간
- 예약 실행이 지연돼도 GitHub 예약 정보(NEWS_SCHEDULE)로 회차 구분
- 메시지에 예약 회차와 실제 시작 시각을 구분해 표시
- 텔레그램 HTML 포맷 및 분할 전송
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

NAVER_NEWS_URL = "https://openapi.naver.com/v1/search/news.json"
GOOGLE_NEWS_RSS_URL = (
    "https://news.google.com/rss/search?q={query}&hl=ko&gl=KR&ceid=KR:ko"
)
TELEGRAM_SEND_URL = "https://api.telegram.org/bot{token}/sendMessage"

TITLE_SIMILARITY_THRESHOLD = 0.72
NAVER_DISPLAY_COUNT = 30
TELEGRAM_MAX_LEN = 4000

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
def fetch_naver_news(keyword: str) -> list:
    if not NAVER_CLIENT_ID or not NAVER_CLIENT_SECRET:
        logger.warning(
            "네이버 API 키가 설정되지 않아 네이버 수집을 건너뜁니다."
        )
        return []

    headers = {
        "X-Naver-Client-Id": NAVER_CLIENT_ID,
        "X-Naver-Client-Secret": NAVER_CLIENT_SECRET,
    }
    params = {
        "query": keyword,
        "display": NAVER_DISPLAY_COUNT,
        "start": 1,
        "sort": "date",
    }

    try:
        resp = requests.get(
            NAVER_NEWS_URL,
            headers=headers,
            params=params,
            timeout=10,
        )
        resp.raise_for_status()
        data = resp.json()

    except requests.RequestException as e:
        logger.error("네이버 뉴스 API 요청 실패: %s", e)
        return []

    except ValueError as e:
        logger.error("네이버 뉴스 API 응답 파싱 실패: %s", e)
        return []

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
        logger.error("구글 뉴스 RSS 수집 실패: %s", e)
        return []

    if getattr(feed, "bozo", 0) and not feed.entries:
        logger.warning(
            "구글 뉴스 RSS 응답 이상: %s",
            getattr(feed, "bozo_exception", "원인 미상"),
        )

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
def load_history() -> list:
    """저장소에 커밋된 sent_history.json을 읽어온다. 없으면 빈 이력."""
    if not os.path.exists(HISTORY_FILE):
        return []

    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return data
        logger.warning("발송 이력 파일 형식이 예상과 달라 빈 이력으로 시작합니다.")
        return []
    except (json.JSONDecodeError, OSError) as e:
        logger.warning("발송 이력 파일 읽기 실패, 빈 이력으로 시작: %s", e)
        return []


def prune_history(history: list, now_utc: datetime) -> list:
    """오래된 이력(HISTORY_RETENTION_HOURS 초과)을 제거해 파일이 계속 커지지 않게 한다."""
    cutoff = now_utc - timedelta(hours=HISTORY_RETENTION_HOURS)
    pruned = []

    for entry in history:
        sent_at_raw = entry.get("sent_at")
        try:
            sent_at = datetime.fromisoformat(sent_at_raw)
        except (TypeError, ValueError):
            continue  # 형식이 깨진 항목은 버림

        if sent_at >= cutoff:
            pruned.append(entry)

    logger.info(
        "발송 이력 정리: %s건 -> %s건 (보관 %s시간)",
        len(history),
        len(pruned),
        HISTORY_RETENTION_HOURS,
    )
    return pruned


def save_history(history: list) -> None:
    try:
        with open(HISTORY_FILE, "w", encoding="utf-8") as f:
            json.dump(history, f, ensure_ascii=False, indent=2)
    except OSError as e:
        logger.error("발송 이력 저장 실패: %s", e)


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
    """텔레그램 메시지를 기사 단위로 분할."""
    label = run_ctx["label"]
    lookback = run_ctx["lookback_hours"]
    actual_start = run_ctx["actual_start_kst"]

    header = (
        f"📰 <b>{escape_html(SEARCH_KEYWORD)} 뉴스 브리핑</b>\n"
        f"실행 회차: {escape_html(label)}\n"
        f"실제 시작: {escape_html(actual_start)} KST\n"
        f"실제 시작 시각 기준 최근 {lookback}시간 이내 기사 (이전 회차 발송분 제외)\n"
    )

    if not articles:
        return [header + "\n해당 시간대 신규 기사가 없습니다."]

    header += f"총 {len(articles)}건\n\n"

    messages = []
    current = header

    for idx, article in enumerate(articles, start=1):
        title = escape_html(article["title"])
        summary = escape_html(article["summary"])
        link = html.escape(article["link"], quote=True)
        source = escape_html(article["source"])

        block = (
            f"{idx}. <b>{title}</b>\n"
            f"({source})\n"
        )

        if summary:
            block += f"{summary}\n"

        block += f'<a href="{link}">기사 원문 보기</a>\n\n'

        if len(current) + len(block) > TELEGRAM_MAX_LEN:
            messages.append(current.rstrip())
            current = block
        else:
            current += block

    if current.strip():
        messages.append(current.rstrip())

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
            logger.error("텔레그램 API가 전송 실패를 반환했습니다.")
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

    logger.info(
        "실행 회차=%s / 실제 시작(KST)=%s / 조회=%s시간 / 기준(UTC)=%s",
        run_ctx["label"],
        run_ctx["actual_start_kst"],
        run_ctx["lookback_hours"],
        run_ctx["cutoff_utc"].isoformat(),
    )

    history = load_history()
    history = prune_history(history, run_ctx["now_utc"])

    naver_articles = fetch_naver_news(SEARCH_KEYWORD)
    google_articles = fetch_google_news(SEARCH_KEYWORD)

    all_articles = naver_articles + google_articles

    # 조회 범위를 먼저 적용해 오래된 유사 기사가 최신 기사를
    # 중복으로 제거하는 상황을 줄입니다.
    recent_articles = filter_recent_articles(
        all_articles,
        run_ctx["cutoff_utc"],
        run_ctx["now_utc"],
    )

    recent_articles.sort(
        key=lambda a: (
            a["pub_date"]
            or datetime.min.replace(tzinfo=timezone.utc)
        ),
        reverse=True,
    )

    unique_articles = deduplicate(recent_articles)

    # 이전 회차(오전/오후)에서 이미 보낸 기사는 제외
    new_articles = filter_against_history(unique_articles, history)

    messages = build_messages(new_articles, run_ctx)

    success_count = 0

    for msg in messages:
        if send_telegram_message(msg):
            success_count += 1
        time.sleep(1)

    logger.info(
        "총 %s개 메시지 중 %s개 전송 성공",
        len(messages),
        success_count,
    )

    all_sent = success_count == len(messages)

    # 전부 정상 전송된 경우에만 이번에 보낸 기사를 이력에 추가합니다.
    # (전송이 실패한 기사를 "보냈다"고 잘못 기록해서 다음 회차에서
    #  누락되는 것을 방지)
    if all_sent and new_articles:
        history = append_to_history(history, new_articles, run_ctx["now_utc"])

    save_history(history)

    # 일부 메시지만 전송된 경우도 실패로 표시합니다.
    if not all_sent:
        sys.exit(1)


if __name__ == "__main__":
    main()
