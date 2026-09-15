"""
지방소멸대응기금 뉴스 자동 스크랩 & 텔레그램 전송 스크립트
- 네이버 뉴스 검색 API (JSON)
- 구글 뉴스 RSS (feedparser)
- 제목 유사도 / 링크 기준 중복 제거
- 실행 시각 기준 최근 N시간 이내 기사만 필터링
  · 오전(09:00 KST) 실행: 최근 16시간 이내 (전일 17:00 실행 이후 공백 포함)
  · 오후(17:00 KST) 실행: 최근 8시간 이내 (당일 09:00 실행 이후 공백)
- 텔레그램 HTML 포맷으로 전송 (4096자 제한 대응 분할 전송)
"""

import os
import re
import sys
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

TITLE_SIMILARITY_THRESHOLD = 0.72  # 이 값 이상이면 같은 기사로 판단
NAVER_DISPLAY_COUNT = 30           # 네이버 API 최대 수집 개수
TELEGRAM_MAX_LEN = 4000            # 여유를 둔 텔레그램 메시지 길이 제한

KST = timezone(timedelta(hours=9))

# 실행 시각(UTC hour) -> (한국시간 라벨, lookback 시간)
# 00:00 UTC = 09:00 KST (오전) -> 최근 16시간
# 08:00 UTC = 17:00 KST (오후) -> 최근 8시간
RUN_SCHEDULE = {
    0: {"label": "오전 09:00", "lookback_hours": 16},
    8: {"label": "오후 17:00", "lookback_hours": 8},
}
DEFAULT_LOOKBACK_HOURS = 16  # 수동 실행 등 스케줄 외 시각에 돌릴 때의 기본값


# ------------------------------------------------------------------
# 공용 유틸
# ------------------------------------------------------------------
def strip_tags(text: str) -> str:
    """HTML 태그 제거 + 엔티티 언이스케이프"""
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", "", text)
    return html.unescape(text).strip()


def truncate_summary(text: str, max_chars: int = 160) -> str:
    """요약을 2~3줄 분량으로 자르기"""
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= max_chars:
        return text
    return text[:max_chars].rstrip() + "..."


def normalize_title(title: str) -> str:
    """유사도 비교를 위한 제목 정규화 (공백/기호/대소문자 제거)"""
    title = strip_tags(title)
    title = re.sub(r"[^0-9a-zA-Z가-힣]", "", title)
    return title.lower()


def normalize_link(link: str) -> str:
    if not link:
        return ""
    link = link.strip().rstrip("/")
    link = re.sub(r"^https?://(www\.)?", "", link)
    return link


def is_similar_title(a: str, b: str) -> bool:
    a_norm, b_norm = normalize_title(a), normalize_title(b)
    if not a_norm or not b_norm:
        return False
    ratio = SequenceMatcher(None, a_norm, b_norm).ratio()
    return ratio >= TITLE_SIMILARITY_THRESHOLD


def get_run_context() -> dict:
    """현재 UTC 시각을 기준으로 이번 실행이 오전/오후 중 어떤 회차인지, lookback 시간은 얼마인지 결정"""
    now_utc = datetime.now(timezone.utc)
    schedule = RUN_SCHEDULE.get(now_utc.hour)

    if schedule is None:
        logger.warning(
            f"정해진 스케줄 시각(UTC 0시/8시)이 아닌 {now_utc.hour}시에 실행되어 "
            f"기본 lookback({DEFAULT_LOOKBACK_HOURS}시간)을 적용합니다."
        )
        label = now_utc.astimezone(KST).strftime("%H:%M 수동실행")
        lookback_hours = DEFAULT_LOOKBACK_HOURS
    else:
        label = schedule["label"]
        lookback_hours = schedule["lookback_hours"]

    return {
        "now_utc": now_utc,
        "label": label,
        "lookback_hours": lookback_hours,
        "cutoff_utc": now_utc - timedelta(hours=lookback_hours),
    }


def parse_naver_date(pub_date: str):
    """네이버 API의 RFC 1123 형식 날짜를 UTC datetime으로 변환"""
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
    """구글 뉴스 RSS 항목의 published_parsed(struct_time, UTC)를 datetime으로 변환"""
    struct = entry.get("published_parsed")
    if not struct:
        return None
    try:
        return datetime(*struct[:6], tzinfo=timezone.utc)
    except (TypeError, ValueError):
        return None


# ------------------------------------------------------------------
# 1) 네이버 뉴스 API 수집
# ------------------------------------------------------------------
def fetch_naver_news(keyword: str) -> list:
    if not NAVER_CLIENT_ID or not NAVER_CLIENT_SECRET:
        logger.warning("네이버 API 키가 설정되지 않아 네이버 뉴스 수집을 건너뜁니다.")
        return []

    headers = {
        "X-Naver-Client-Id": NAVER_CLIENT_ID,
        "X-Naver-Client-Secret": NAVER_CLIENT_SECRET,
    }
    params = {
        "query": keyword,
        "display": NAVER_DISPLAY_COUNT,
        "start": 1,
        "sort": "date",  # 최신순
    }

    try:
        resp = requests.get(NAVER_NEWS_URL, headers=headers, params=params, timeout=10)
        resp.raise_for_status()
        data = resp.json()
    except requests.RequestException as e:
        logger.error(f"네이버 뉴스 API 요청 실패: {e}")
        return []
    except ValueError as e:
        logger.error(f"네이버 뉴스 API 응답 파싱 실패: {e}")
        return []

    results = []
    for item in data.get("items", []):
        title = strip_tags(item.get("title", ""))
        description = strip_tags(item.get("description", ""))
        # originallink가 있으면 우선 사용, 없으면 link 사용
        link = item.get("originallink") or item.get("link", "")
        pub_date_raw = item.get("pubDate", "")
        pub_date = parse_naver_date(pub_date_raw)

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

    logger.info(f"네이버 뉴스 {len(results)}건 수집")
    return results


# ------------------------------------------------------------------
# 2) 구글 뉴스 RSS 수집
# ------------------------------------------------------------------
def fetch_google_news(keyword: str) -> list:
    url = GOOGLE_NEWS_RSS_URL.format(query=quote(keyword))

    try:
        feed = feedparser.parse(url)
    except Exception as e:
        logger.error(f"구글 뉴스 RSS 파싱 실패: {e}")
        return []

    if getattr(feed, "bozo", 0) and not feed.entries:
        logger.warning(f"구글 뉴스 RSS 응답에 문제가 있을 수 있습니다: {feed.bozo_exception}")

    results = []
    for entry in feed.entries:
        title = strip_tags(entry.get("title", ""))
        # 구글 뉴스 RSS는 title에 " - 언론사명"이 붙는 경우가 많아 제거
        title = re.sub(r"\s*-\s*[^-]{1,30}$", "", title).strip() or title
        description = strip_tags(entry.get("summary", "") or entry.get("description", ""))
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

    logger.info(f"구글 뉴스 {len(results)}건 수집")
    return results


# ------------------------------------------------------------------
# 3) 시간 필터링
# ------------------------------------------------------------------
def filter_recent_articles(articles: list, cutoff_utc: datetime, now_utc: datetime) -> list:
    """cutoff_utc 이후 ~ now_utc 이전에 작성된 기사만 남긴다.
    발행일을 파싱할 수 없는 기사는 판단 불가로 보고 일단 포함시키되 로그를 남긴다."""
    filtered = []
    for article in articles:
        pub_date = article.get("pub_date")

        if pub_date is None:
            logger.warning(f"발행일 파싱 실패로 필터 없이 포함: {article['title']}")
            filtered.append(article)
            continue

        if cutoff_utc <= pub_date <= now_utc + timedelta(minutes=5):
            filtered.append(article)

    logger.info(
        f"시간 필터링({cutoff_utc.isoformat()} ~ {now_utc.isoformat()}) 후 "
        f"{len(filtered)}건 남음 (필터 전 {len(articles)}건)"
    )
    return filtered


# ------------------------------------------------------------------
# 4) 중복 제거 (제목 유사도 + 링크 동일 여부)
# ------------------------------------------------------------------
def deduplicate(articles: list) -> list:
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

    logger.info(f"중복 제거 후 {len(unique)}건 남음 (원본 {len(articles)}건)")
    return unique


# ------------------------------------------------------------------
# 5) 텔레그램 메시지 포맷 & 전송
# ------------------------------------------------------------------
def escape_html(text: str) -> str:
    return html.escape(text, quote=False)


def build_messages(articles: list, run_ctx: dict) -> list:
    """텔레그램 4096자 제한을 고려해 여러 메시지로 분할"""
    label = run_ctx["label"]
    lookback = run_ctx["lookback_hours"]

    header = (
        f"📰 <b>{escape_html(SEARCH_KEYWORD)} 뉴스 브리핑 ({escape_html(label)})</b>\n"
        f"최근 {lookback}시간 이내 기사 기준\n"
    )

    if not articles:
        return [header + "\n해당 시간대 신규 기사가 없습니다."]

    header += f"총 {len(articles)}건\n\n"

    messages = []
    current = header
    for idx, article in enumerate(articles, start=1):
        title = escape_html(article["title"])
        summary = escape_html(article["summary"])
        link = escape_html(article["link"])
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


def send_telegram_message(text: str) -> bool:
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        logger.error("TELEGRAM_TOKEN 또는 TELEGRAM_CHAT_ID가 설정되지 않았습니다.")
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
        return True
    except requests.RequestException as e:
        body = getattr(e.response, "text", "")
        logger.error(f"텔레그램 전송 실패: {e} / 응답: {body}")
        return False


# ------------------------------------------------------------------
# 메인 실행
# ------------------------------------------------------------------
def main():
    run_ctx = get_run_context()
    logger.info(
        f"실행 회차: {run_ctx['label']} / lookback {run_ctx['lookback_hours']}시간 "
        f"/ cutoff(UTC) {run_ctx['cutoff_utc'].isoformat()}"
    )

    naver_articles = fetch_naver_news(SEARCH_KEYWORD)
    google_articles = fetch_google_news(SEARCH_KEYWORD)

    all_articles = naver_articles + google_articles
    unique_articles = deduplicate(all_articles)
    recent_articles = filter_recent_articles(
        unique_articles, run_ctx["cutoff_utc"], run_ctx["now_utc"]
    )

    # 최신순 정렬 (발행일 없는 기사는 뒤로)
    recent_articles.sort(
        key=lambda a: a["pub_date"] or datetime.min.replace(tzinfo=timezone.utc),
        reverse=True,
    )

    messages = build_messages(recent_articles, run_ctx)

    success_count = 0
    for msg in messages:
        if send_telegram_message(msg):
            success_count += 1
        time.sleep(1)  # 텔레그램 API rate limit 대비

    logger.info(f"총 {len(messages)}개 메시지 중 {success_count}개 전송 성공")

    if success_count == 0 and messages:
        sys.exit(1)


if __name__ == "__main__":
    main()
