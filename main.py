"""
지방소멸대응기금 · 인구감소지역 · 생활인구 뉴스 자동 스크랩 & 텔레그램 전송

[주제별 분리 발송 - 2026-09]
한 번 실행할 때 TOPICS에 정의된 주제(기금, 인구감소지역)를 차례로
수집해, 텔레그램 그룹의 주제(Topics) 탭으로 각각 보냅니다.
- 발송 이력과 마지막 조회 시각은 주제별로 따로 관리
- 여러 주제에 해당하는 기사는 기금 > 인구감소지역 > 생활인구 순으로 한 탭에만 발송
- 탭 번호(TELEGRAM_TOPIC_FUND / _POP / _LIFE)가 비어 있으면
  그룹의 기본(General) 대화로 보냄 → 탭 설정 전에도 발송은 정상 동작

- 네이버 뉴스 검색 API + 구글 뉴스 RSS
- 제목 유사도 / 링크 기준 중복 제거 (같은 실행 내)
- 저장소에 커밋되는 sent_history.json으로 발송 이력을 기억해서
  오전 회차에 보낸 기사가 오후 회차에 다시 발송되지 않도록 방지
- 오전 회차: 실제 실행 시각 기준 최근 16시간
- 오후 회차: 실제 실행 시각 기준 최근 8시간
- 지연·실패 시 마지막 정상 조회 시각부터 재조회 (최대 48시간)
- 성공한 메시지에 포함된 기사만 즉시 발송 이력에 기록
- 메시지에 회차와 실제 시작 시각을 구분해 표시
- 텔레그램 HTML 포맷 및 분할 전송

[실행 방식 변경 - 2026-09 (방안 B)]
GitHub 예약(schedule) 실행이 매번 2~5시간씩 지연되어, 정시 발송은
외부 스케줄러(cron-job.org)가 GitHub API로 workflow_dispatch를
호출하는 방식으로 바꿨습니다. 수동 실행과 같은 경로라 예약 대기열의
지연을 받지 않습니다.
- 정시 실행: 외부 스케줄러가 slot=am(오전 08시), slot=pm(오후 17시)으로 호출
- 백업 실행: GitHub 예약(schedule)은 외부 호출이 실패한 날을 대비한
  예비용으로만 남겨두고, 같은 날 같은 회차가 이미 발송됐으면 아무것도
  보내지 않고 조용히 종료
- 수동 실행: Actions 화면에서 slot=manual(기본값)로 실행하면 회차와
  무관하게 즉시 발송하며, 회차 발송 기록은 남기지 않음
- 회차 발송 기록은 sent_history.json의 slot_runs 항목에 저장
  (텔레그램 발송이 모두 성공했을 때만 기록 → 실패 시 백업이 재시도)

[수정 사항 - 2026-09]
- 네이버 API 실패 시 원인(HTTP 상태 코드/응답 본문/예외 메시지)을 로그에 상세히 기록
- 5xx/일시적 오류로 판단되면 네이버 API 요청을 1회 자동 재시도
- 뉴스 소스 중 일부만 실패했는데 텔레그램 발송 자체는 성공한 경우,
  더 이상 워크플로를 실패로 표시하지 않고 경고 로그만 남김
  (실제 발송이 실패했을 때만 워크플로를 실패 처리)
- 네이버·구글 뉴스 수집이 모두 실패해 이번 회차에 기사를 하나도
  보내지 못한 경우, GitHub Actions 로그와 별도로 텔레그램에도
  오류 알림을 전송
- 서로 다른 언론사가 같은 소식(같은 보도자료)을 다른 제목으로 보도한
  경우를 묶어서, 대표 기사 1건 + "다른 언론사 N곳도 보도"로 표시
  (제목 문자열 유사도만으로는 이런 경우를 잡아내지 못해, 제목+요약의
  핵심 단어 겹침 비율(자카드 유사도)을 함께 확인)
- 네이버 뉴스는 API 응답에 언론사명이 없어 그동안 전부 "네이버뉴스"로
  표시됐던 것을, 원문 링크의 도메인으로 대체해 실제 언론사를 구분
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
from urllib.parse import quote, urlparse

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

# ------------------------------------------------------------------
# 주제(탭)별 검색 설정
# ------------------------------------------------------------------
# 네이버·구글 검색은 검색어를 단어 단위로 쪼개 부분 일치 기사까지
# 돌려주므로, 수집 후 required_phrases로 한 번 더 걸러냅니다.
# 비교할 때는 띄어쓰기·기호를 무시합니다("소멸 기금" = "소멸기금").
#
# naver_queries / google_queries : 검색어 목록(구글은 큰따옴표 = 정확 일치)
# required_phrases     : 기사에 반드시 있어야 하는 표현(하나라도 있으면 통과)
# require_in_title     : True면 제목에 있어야 통과(네이버·구글 모두)
#                        False면 네이버는 제목+요약문, 구글은 정확 일치 검색을 신뢰
# exclude_title_phrases: 제목에 이 단어가 있고 required_phrases가 없으면 제외
# naver_display        : 네이버 검색어 1개당 가져올 기사 수(최대 100)
# thread_env           : 텔레그램 주제 탭 번호를 담은 환경변수 이름
# skip_if_topics       : 이 주제들의 기준에도 맞는 기사는 여기서 제외(중복 발송 방지)
#                        우선순위: 기금 > 인구감소지역 > 생활인구
TOPICS = [
    {
        "key": "fund",
        "name": "지방소멸대응기금",
        "emoji": "📰",
        "naver_queries": ["지방소멸대응기금", "소멸기금"],
        "google_queries": ['"지방소멸대응기금"', '"소멸기금"'],
        "required_phrases": ["지방소멸대응기금", "소멸기금"],
        "require_in_title": False,
        "exclude_title_phrases": ["미래대응기금"],
        "naver_display": 30,
        "thread_env": "TELEGRAM_TOPIC_FUND",
        "skip_if_topics": [],
    },
    {
        "key": "pop",
        "name": "인구감소지역",
        "emoji": "🏘",
        "naver_queries": ["인구감소지역"],
        "google_queries": ['"인구감소지역"'],
        "required_phrases": ["인구감소지역"],
        # 지역 기사가 많아 제목에 등장한 기사만 받습니다.
        "require_in_title": True,
        "exclude_title_phrases": [],
        "naver_display": 100,
        "thread_env": "TELEGRAM_TOPIC_POP",
        "skip_if_topics": ["fund"],
    },
    {
        "key": "life",
        "name": "생활인구",
        "emoji": "👥",
        "naver_queries": ["생활인구"],
        "google_queries": ['"생활인구"'],
        "required_phrases": ["생활인구"],
        "require_in_title": True,
        "exclude_title_phrases": [],
        "naver_display": 100,
        "thread_env": "TELEGRAM_TOPIC_LIFE",
        "skip_if_topics": ["fund", "pop"],
    },
]
TOPIC_BY_KEY = {t["key"]: t for t in TOPICS}

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
TELEGRAM_MAX_LEN = 4000

# --- "같은 소식, 다른 언론사" 묶음(그룹핑) 기준 ---
# 위 TITLE_SIMILARITY_THRESHOLD(0.72)는 완전히 같은 기사가 재게재된
# 경우를 잡기 위한 값이라 엄격하게 유지합니다. 서로 다른 기자가 같은
# 보도자료를 각자 다르게 풀어 쓴 "같은 소식"은 제목만으로는 유사도가
# 훨씬 낮게 나오는 경우가 많아, 아래 두 기준 중 하나라도 만족하면
# 같은 소식으로 판단해 대표 기사 1건으로 묶습니다.
#   1) 제목 유사도가 SAME_STORY_TITLE_THRESHOLD 이상이거나
#   2) 제목+요약에서 뽑은 핵심 단어 집합의 자카드 유사도가
#      SAME_STORY_JACCARD_THRESHOLD 이상인 경우
# 실제 발송된 기사 26건을 놓고 값을 조정해, 명백히 다른 기사끼리
# 잘못 묶이는 경우 없이 같은 사안(예: 특정 기관의 같은 날 발표)을
# 다룬 기사들이 하나로 모이는 것을 확인한 값입니다.
SAME_STORY_TITLE_THRESHOLD = 0.60
SAME_STORY_JACCARD_THRESHOLD = 0.15
# 자카드 유사도 계산에서 제외할, 이 프로젝트 성격상 모든 기사에
# 공통으로 등장해 변별력이 없는 단어들.
SAME_STORY_STOPWORDS = {"관련", "위한", "대한", "있다", "했다", "이번", "이후", "지난", "가운데"}
# 한 소식에 묶인 "다른 언론사" 목록을 메시지에 표시할 때 최대로 나열할 개수.
MAX_OTHER_SOURCES_SHOWN = 4

# 네이버 API가 일시적 오류(5xx, 타임아웃, 연결 오류)로 보일 때
# 이 시간(초)만큼 대기한 뒤 1회만 재시도합니다. 인증 오류(4xx)는
# 재시도해도 소용없으므로 재시도하지 않고 바로 실패 처리합니다.
NAVER_RETRY_DELAY_SECONDS = 3

KST = timezone(timedelta(hours=9))

# 회차 설정.
# slot_date_offset_hours: "이 실행이 며칠자 회차인가"를 정할 때 현재
# 한국시간에서 빼는 시간입니다. 목표 시각보다 2시간 이른 시점부터를
# 그날 회차로 봅니다. 예) 오후 백업 실행이 자정을 넘겨 다음 날 00:30에
# 돌아도 전날 오후 회차로 판정되어, 다음 날 오후 발송을 막지 않습니다.
SLOTS = {
    "am": {
        "label": "오전 회차(08:00)",
        "lookback_hours": 15,
        "slot_date_offset_hours": 6,
    },
    "pm": {
        "label": "오후 회차(17:00)",
        "lookback_hours": 9,
        "slot_date_offset_hours": 15,
    },
}

# 백업용 GitHub 예약식(UTC) → 회차. news_cron.yml의 cron과 반드시 일치해야 합니다.
BACKUP_CRON_TO_SLOT = {
    "20 23 * * *": "am",  # 한국시간 08:20
    "20 8 * * *": "pm",  # 한국시간 17:20
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


def extract_press_name(link: str) -> str:
    """원문 링크의 도메인으로 언론사를 표시합니다.

    네이버 뉴스 검색 API 응답에는 언론사명이 별도 필드로 오지 않아서,
    그동안 네이버발 기사는 전부 "네이버뉴스"라는 똑같은 이름으로만
    표시되어 "다른 언론사 N곳도 보도" 같은 구분이 불가능했습니다.
    originallink(기사 원문 도메인)가 있으면 그 도메인을, naver.com
    도메인이거나 원문 링크가 없으면 "네이버뉴스"를 사용합니다.
    """
    if not link:
        return "네이버뉴스"
    try:
        netloc = (urlparse(link).netloc or "").lower()
    except ValueError:
        return "네이버뉴스"
    if netloc.startswith("www."):
        netloc = netloc[4:]
    if not netloc or "naver.com" in netloc:
        return "네이버뉴스"
    return netloc


def is_similar_title(a: str, b: str) -> bool:
    a_norm = normalize_title(a)
    b_norm = normalize_title(b)

    if not a_norm or not b_norm:
        return False

    ratio = SequenceMatcher(None, a_norm, b_norm).ratio()
    return ratio >= TITLE_SIMILARITY_THRESHOLD


def get_run_context() -> dict:
    """실행 경로(외부 호출·백업 예약·수동)에 따라 회차를 판정."""
    now_utc = datetime.now(timezone.utc)
    now_kst = now_utc.astimezone(KST)

    event_name = os.environ.get("GITHUB_EVENT_NAME", "").strip()
    cron = os.environ.get("NEWS_SCHEDULE", "").strip()
    slot_input = os.environ.get("NEWS_SLOT", "").strip().lower()

    slot = None
    is_backup = False

    if event_name == "schedule":
        slot = BACKUP_CRON_TO_SLOT.get(cron)
        if slot is None:
            raise ValueError(
                f"알 수 없는 예약 설정: {cron!r}. "
                "news_cron.yml과 main.py의 BACKUP_CRON_TO_SLOT을 확인하세요."
            )
        is_backup = True
    elif event_name == "workflow_dispatch" and slot_input in SLOTS:
        slot = slot_input
    elif event_name == "workflow_dispatch" and slot_input in ("", "manual"):
        slot = None
    else:
        raise ValueError(
            f"알 수 없는 실행 방식입니다: event={event_name!r}, slot={slot_input!r}"
        )

    if slot:
        conf = SLOTS[slot]
        label = conf["label"] + (" · 백업 실행" if is_backup else "")
        lookback_hours = conf["lookback_hours"]
        slot_date = (
            now_kst - timedelta(hours=conf["slot_date_offset_hours"])
        ).strftime("%Y-%m-%d")
    else:
        label = "수동실행"
        lookback_hours = DEFAULT_LOOKBACK_HOURS
        slot_date = None

    logger.info(
        "실행 유형=%s / 예약식=%s / 회차=%s / 회차 날짜=%s",
        event_name, cron or "-", slot or "수동", slot_date or "-",
    )

    return {
        "now_utc": now_utc,
        "label": label,
        "slot": slot,
        "slot_date": slot_date,
        "is_backup": is_backup,
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
def _request_naver(keyword: str, display: int = 30) -> dict:
    """네이버 뉴스 검색 API를 1회 호출. 실패 시 requests 예외를 그대로 전파."""
    headers = {
        "X-NCP-APIGW-API-KEY-ID": NAVER_CLIENT_ID,
        "X-NCP-APIGW-API-KEY": NAVER_CLIENT_SECRET,
    }
    params = {
        "query": keyword,
        "display": display,
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


def fetch_naver_news(keyword: str, display: int = 30) -> list:
    if not NAVER_CLIENT_ID or not NAVER_CLIENT_SECRET:
        raise RuntimeError("네이버 API 키가 설정되지 않았습니다.")

    data = None
    last_error = None

    # 최대 2회 시도(최초 1회 + 일시적 오류로 보일 때 1회 재시도).
    for attempt in range(2):
        try:
            data = _request_naver(keyword, display)
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
                "match_text": f"{title} {description}",
                "source_type": "naver",
                "link": link,
                "pub_date": pub_date,
                "source": extract_press_name(item.get("originallink") or ""),
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
                "match_text": f"{title} {description}",
                "source_type": "google",
                "link": link,
                "pub_date": pub_date,
                "source": source or "구글뉴스",
            }
        )

    logger.info("구글 뉴스 %s건 수집", len(results))
    return results


# ------------------------------------------------------------------
# 2-1. 키워드 정확도 필터
# ------------------------------------------------------------------
def _has_phrase(text: str, phrases: list) -> bool:
    text_norm = normalize_title(text)
    return any(normalize_title(p) in text_norm for p in phrases)


def _qualifies_for(article: dict, topic: dict) -> bool:
    """다른 주제의 기준(제목 필수 여부 포함)으로 봐도 해당되는 기사인지."""
    target = article["title"] if topic["require_in_title"] else article.get("match_text", article["title"])
    return _has_phrase(target, topic["required_phrases"])


def filter_by_keyword(articles: list, topic: dict) -> list:
    """검색어가 부분 일치로만 걸린 기사, 다른 주제로 보낼 기사를 걸러낸다."""
    required = topic["required_phrases"]
    others = [TOPIC_BY_KEY[k] for k in topic.get("skip_if_topics", [])]
    kept = []
    for article in articles:
        title = article["title"]
        text = article.get("match_text", title)

        if _has_phrase(title, topic["exclude_title_phrases"]) and not _has_phrase(
            title, required
        ):
            logger.info("[%s] 제외(제외 단어): %s", topic["key"], title)
            continue

        if topic["require_in_title"]:
            if not _has_phrase(title, required):
                logger.info("[%s] 제외(제목에 검색어 없음): %s", topic["key"], title)
                continue
        elif article.get("source_type") == "naver" and not _has_phrase(text, required):
            logger.info("[%s] 제외(검색어 없음): %s", topic["key"], title)
            continue

        owner = next((o for o in others if _qualifies_for(article, o)), None)
        if owner:
            logger.info("[%s] 제외(%s 탭으로 발송): %s", topic["key"], owner["key"], title)
            continue

        kept.append(article)

    logger.info("[%s] 키워드 필터: %s건 중 %s건 유지", topic["key"], len(articles), len(kept))
    return kept


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
# 4-1. "같은 소식, 다른 언론사" 묶기
# ------------------------------------------------------------------
def _content_tokens(article: dict) -> set:
    """제목+요약에서 자카드 유사도 비교용 핵심 단어 집합을 뽑는다."""
    text = f"{article.get('title', '')} {article.get('summary', '')}"
    words = re.findall(r"[0-9A-Za-z가-힣]{2,}", text)
    key_norms = {normalize_title(p) for t in TOPICS for p in t["required_phrases"]}
    tokens = set()
    for w in words:
        if w in SAME_STORY_STOPWORDS:
            continue
        # 검색 키워드 자체(예: "지방소멸대응기금")는 모든 기사에 공통으로
        # 등장해 변별력이 없으므로 제외한다.
        if normalize_title(w) in key_norms:
            continue
        tokens.add(w)
    return tokens


def _is_same_story(a: dict, b: dict) -> bool:
    """제목이 거의 같거나(재게재), 서로 다르게 쓰였어도 같은 사안을
    다룬 것으로 보이면(핵심 단어 겹침) 같은 소식으로 판단한다."""
    if is_similar_title(a["title"], b["title"]):
        return True

    title_ratio = SequenceMatcher(
        None, normalize_title(a["title"]), normalize_title(b["title"])
    ).ratio()
    if title_ratio >= SAME_STORY_TITLE_THRESHOLD:
        return True

    tokens_a, tokens_b = _content_tokens(a), _content_tokens(b)
    if not tokens_a or not tokens_b:
        return False
    jaccard = len(tokens_a & tokens_b) / len(tokens_a | tokens_b)
    return jaccard >= SAME_STORY_JACCARD_THRESHOLD


def group_related_articles(articles: list) -> list:
    """서로 다른 언론사가 같은 소식을 다른 제목으로 보도한 경우를 묶는다.

    각 그룹에서 가장 최근(pub_date 기준) 기사를 대표로 삼고, 나머지는
    지우지 않고 대표 기사의 "other_sources"(다른 언론사 이름 목록)와
    "cluster_members"(발송 이력에 함께 기록할 원본 기사 목록)로 붙여
    반환한다. 이렇게 하면 목록은 짧아지되 정보는 사라지지 않는다.

    주의: 제목 문자열만으로는 "같은 보도자료를 다른 기자가 다르게 쓴
    기사"를 안정적으로 구분할 수 없어(실측 결과 임계값을 아무리 조정해도
    오탐/미탐이 뒤섞임), 제목+요약의 핵심 단어 겹침 비율을 함께 사용한다.
    완벽하지는 않지만(예: 같은 사안을 다른 소식과 함께 다룬 기사는
    묶이지 않을 수 있음), 실제 데이터로 검증했을 때 서로 다른 기사를
    잘못 묶는 경우는 거의 없었다.
    """
    n = len(articles)
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for i in range(n):
        for j in range(i + 1, n):
            if _is_same_story(articles[i], articles[j]):
                union(i, j)

    clusters = {}
    for i in range(n):
        clusters.setdefault(find(i), []).append(i)

    def sort_key(idx: int):
        return articles[idx].get("pub_date") or datetime.min.replace(tzinfo=timezone.utc)

    grouped = []
    for indices in clusters.values():
        indices.sort(key=sort_key, reverse=True)
        primary = dict(articles[indices[0]])
        members = [articles[idx] for idx in indices]
        primary["cluster_members"] = members

        if len(indices) > 1:
            other_sources = []
            seen = set()
            for idx in indices[1:]:
                src = articles[idx].get("source") or ""
                if src and src not in seen:
                    other_sources.append(src)
                    seen.add(src)
            if other_sources:
                primary["other_sources"] = other_sources

        grouped.append(primary)

    grouped.sort(key=lambda a: a.get("pub_date") or datetime.min.replace(tzinfo=timezone.utc), reverse=True)

    logger.info(
        "관련 기사 묶음 처리 후 %s건 / 묶기 전 %s건",
        len(grouped),
        len(articles),
    )
    return grouped


# ------------------------------------------------------------------
# 5. 발송 이력 (오전/오후 회차 간 중복 방지)
# ------------------------------------------------------------------
def _empty_topic_state() -> dict:
    return {"articles": [], "last_checked_utc": None}


def load_state() -> dict:
    """이전 형식(v1 목록, v2 단일 주제)도 읽어 주제별 형식(v3)으로 전환합니다."""
    data = None
    if os.path.exists(HISTORY_FILE):
        try:
            with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError) as e:
            raise RuntimeError("발송 이력 읽기 실패. 기존 파일을 확인하세요.") from e

    if data is None:
        state = {"version": 3, "topics": {}, "slot_runs": {}}
    elif isinstance(data, list):
        # v1: 기사 목록만 있던 형식 → 기금 주제의 이력으로 이전
        state = {"version": 3, "topics": {"fund": {"articles": data, "last_checked_utc": None}}, "slot_runs": {}}
    elif isinstance(data, dict) and isinstance(data.get("topics"), dict):
        state = data
    elif isinstance(data, dict) and isinstance(data.get("articles"), list):
        # v2: 기금 단일 주제 형식 → 기금 주제로 이전
        state = {
            "version": 3,
            "topics": {
                "fund": {
                    "articles": data["articles"],
                    "last_checked_utc": data.get("last_checked_utc"),
                }
            },
            "slot_runs": data.get("slot_runs") or {},
        }
    else:
        raise RuntimeError("sent_history.json의 형식이 올바르지 않습니다.")

    state["version"] = 3
    if not isinstance(state.get("slot_runs"), dict):
        state["slot_runs"] = {}
    for topic in TOPICS:
        ts = state["topics"].get(topic["key"])
        if not isinstance(ts, dict) or not isinstance(ts.get("articles"), list):
            state["topics"][topic["key"]] = _empty_topic_state()
    return state


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


def extend_window(run_ctx: dict, topic_state: dict) -> datetime:
    """기본 조회 범위와 (주제별) 마지막 정상 조회 시각 중 더 이른 시각을 반환."""
    cutoff = run_ctx["cutoff_utc"]
    raw = topic_state.get("last_checked_utc")
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
    return cutoff


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


def build_messages(articles: list, run_ctx: dict, topic: dict) -> list:
    """각 메시지와 그 메시지에 포함된 기사 목록을 함께 반환합니다."""
    start = run_ctx["cutoff_utc"].astimezone(KST).strftime("%m-%d %H:%M")
    end = run_ctx["now_utc"].astimezone(KST).strftime("%m-%d %H:%M")
    header = (
        f"{topic['emoji']} <b>{escape_html(topic['name'])} 뉴스 브리핑</b>\n"
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
        block += f'<a href="{link}">기사 원문 보기</a>\n'
        other_sources = article.get("other_sources")
        if other_sources:
            shown = other_sources[:MAX_OTHER_SOURCES_SHOWN]
            extra = len(other_sources) - len(shown)
            shown_text = ", ".join(escape_html(s) for s in shown)
            if extra > 0:
                shown_text += f" 외 {extra}곳"
            block += f"<i>🔗 같은 소식: {shown_text}에서도 보도</i>\n"
        block += "\n"
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
def get_thread_id(topic: dict):
    """주제 탭 번호. 비어 있으면 None(그룹 기본 대화로 발송)."""
    raw = (os.environ.get(topic["thread_env"]) or "").strip()
    if not raw:
        return None
    if not raw.isdigit():
        logger.error("%s 값이 숫자가 아닙니다(%r). 기본 대화로 보냅니다.", topic["thread_env"], raw)
        return None
    return int(raw)


def send_telegram_message(text: str, thread_id=None) -> bool:
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
    if thread_id:
        payload["message_thread_id"] = thread_id

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
def collect_topic(topic: dict) -> tuple:
    """주제의 모든 검색어로 수집. (기사 목록, 실패 목록, 전부 실패 여부)"""
    articles, errors, calls = [], [], 0
    jobs = [("네이버", q, lambda q: fetch_naver_news(q, topic["naver_display"])) for q in topic["naver_queries"]]
    jobs += [("구글", q, fetch_google_news) for q in topic["google_queries"]]
    for name, query, fetch in jobs:
        calls += 1
        try:
            articles.extend(fetch(query))
        except Exception as e:
            logger.error("[%s] %s 수집 실패(%s): %s", topic["key"], name, query, e)
            errors.append(f"{name}({query})")
    return articles, errors, len(errors) == calls


def process_topic(topic: dict, state: dict, run_ctx: dict) -> tuple:
    """주제 1개를 수집·발송. (텔레그램 전부 성공 여부, 수집 전부 실패 여부)"""
    key = topic["key"]
    ts = state["topics"][key]
    ts["articles"] = prune_history(ts["articles"], run_ctx["now_utc"])
    thread_id = get_thread_id(topic)

    ctx = dict(run_ctx)
    ctx["cutoff_utc"] = extend_window(run_ctx, ts)
    logger.info("[%s] 조회 시작(UTC)=%s / 탭 번호=%s", key, ctx["cutoff_utc"].isoformat(), thread_id or "기본")

    articles, errors, all_failed = collect_topic(topic)
    ctx["source_errors"] = errors

    if all_failed:
        alert_text = (
            f"⚠ <b>{escape_html(topic['name'])} 뉴스 봇 오류</b>\n"
            f"예약 회차: {escape_html(run_ctx['label'])}\n"
            f"실제 시작: {escape_html(run_ctx['actual_start_kst'])} KST\n"
            "네이버·구글 뉴스 수집이 모두 실패하여 "
            "이번 회차는 기사를 보내지 못했습니다.\n"
            "GitHub Actions 실행 로그를 확인해주세요."
        )
        send_telegram_message(alert_text, thread_id)
        return False, True

    articles = filter_by_keyword(articles, topic)
    recent = filter_recent_articles(articles, ctx["cutoff_utc"], ctx["now_utc"])
    recent.sort(
        key=lambda a: a["pub_date"] or datetime.min.replace(tzinfo=timezone.utc),
        reverse=True,
    )
    # 다른 주제(예: 기금)에서 이미 보낸 기사도 이 주제에서 다시 보내지 않음
    history_for_check = list(ts["articles"])
    for other_key in topic.get("skip_if_topics", []):
        history_for_check += state["topics"][other_key]["articles"]
    new_articles = filter_against_history(deduplicate(recent), history_for_check)
    grouped_articles = group_related_articles(new_articles)
    messages = build_messages(grouped_articles, ctx, topic)

    success_count = 0
    for message, included in messages:
        if send_telegram_message(message, thread_id):
            success_count += 1
            # 묶음으로 보낸 기사는 함께 묶인 다른 언론사 기사까지 이력에 기록
            sent_articles = []
            for art in included:
                sent_articles.extend(art.get("cluster_members", [art]))
            ts["articles"] = append_to_history(
                ts["articles"], sent_articles, datetime.now(timezone.utc)
            )
            save_state(state)
        time.sleep(1)

    all_sent = success_count == len(messages)
    # 일부 소스가 실패했다면 조회 완료 시각을 갱신하지 않아 다음 회차가 다시 조회
    if all_sent and not errors:
        ts["last_checked_utc"] = run_ctx["now_utc"].isoformat()
    save_state(state)
    logger.info("[%s] 메시지 %s/%s개 전송 성공", key, success_count, len(messages))
    if errors:
        logger.warning("[%s] 일부 수집 실패: %s", key, ", ".join(errors))
    return all_sent, False


def main():
    run_ctx = get_run_context()
    state = load_state()

    slot = run_ctx["slot"]
    if slot and state["slot_runs"].get(slot) == run_ctx["slot_date"]:
        # 외부 호출로 이미 이 회차를 보냈거나, 백업이 먼저 보낸 경우.
        # 이력 파일을 건드리지 않고 조용히 종료합니다(텔레그램 메시지 없음).
        logger.info(
            "%s 회차(%s)는 이미 발송되어 이번 실행은 건너뜁니다.",
            slot, run_ctx["slot_date"],
        )
        return

    save_state(state)
    logger.info("회차=%s / 실제 시작(KST)=%s", run_ctx["label"], run_ctx["actual_start_kst"])

    send_failed, collect_failed = [], []
    for topic in TOPICS:
        # 한 주제에서 예외가 나도 다른 주제는 계속 발송
        try:
            all_sent, all_failed = process_topic(topic, state, run_ctx)
        except Exception as e:
            logger.exception("[%s] 처리 중 오류: %s", topic["key"], e)
            all_sent, all_failed = False, False
        if not all_sent and not all_failed:
            send_failed.append(topic["key"])
        if all_failed:
            collect_failed.append(topic["key"])

    # 모든 주제가 정상 발송됐을 때만 이 회차를 완료로 기록합니다.
    # (하나라도 실패하면 백업 실행이 다시 시도하며, 이미 보낸 기사는 이력으로 걸러집니다.)
    if slot and not send_failed and not collect_failed:
        state["slot_runs"][slot] = run_ctx["slot_date"]
    save_state(state)

    if send_failed or collect_failed:
        logger.error("발송 실패 주제: %s / 수집 전부 실패 주제: %s",
                     send_failed or "-", collect_failed or "-")
        sys.exit(1)


if __name__ == "__main__":
    main()
