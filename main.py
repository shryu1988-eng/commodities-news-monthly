# main.py
# -------------------------------
# 월간 원자재 기사 수집 → 중복 제거 → 최대 20건 선별 → 한국어 메일 본문 + CSV 첨부 발송
# 안정화 패치: 안전 JSON 파싱, 재시도(간격 포함), GDELT Context 2.0의 72시간 제한 반영
# -------------------------------

import os, re, json, time
import requests
import pandas as pd
from datetime import datetime, timedelta, timezone
import yaml, tldextract
from rapidfuzz import fuzz, process

# 이메일 전송
import smtplib
from email.message import EmailMessage
from email.utils import formataddr

# ---- 환경 변수 (GitHub Secrets로 세팅 권장) ----
NEWSAPI_KEY = os.getenv("NEWSAPI_KEY", "")                   # 선택
EVENT_REGISTRY_API_KEY = os.getenv("EVENT_REGISTRY_API_KEY", "")  # 선택
GMAIL_USER = os.getenv("GMAIL_USER", "")                     # 필수(이메일 버전)
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")     # 필수(이메일 버전)

# ---- 타임존/상수 ----
KST = timezone(timedelta(hours=9))

# ---- 설정 로드 ----
with open("config.yaml", "r", encoding="utf-8") as f:
    CFG = yaml.safe_load(f)

OUTDIR = CFG["run"]["output_dir"]
os.makedirs(OUTDIR, exist_ok=True)

# ---- 기간 계산 ----
def daterange():
    end = datetime.now(tz=KST)
    start = end - timedelta(days=int(CFG["run"]["lookback_days"]))
    return start, end

# ---- 공통 유틸 ----
def norm_domain(url):
    try:
        ext = tldextract.extract(url)
        return ".".join([p for p in [ext.domain, ext.suffix] if p])
    except:
        return ""

def allow_domain(url):
    if not url:
        return False
    if any(b in url for b in CFG["sources"]["blacklist_domains"]):
        return False
    wl = CFG["sources"]["whitelist_domains"]
    return True if not wl else any(w in url for w in wl)

def simple_summary(text, max_len=40):
    text = re.sub(r"\s+", " ", (text or "")).strip()
    return " ".join(text.split()[:max_len])

def safe_json(resp):
    """
    응답이 JSON이 아니거나 비었을 때 None 반환.
    GDELT/외부 API가 간헐적으로 HTML/빈 본문을 반환하는 경우 방어.
    """
    try:
        ct = (resp.headers.get("Content-Type") or "").lower()
        if "json" not in ct:
            return None
        return resp.json()
    except Exception:
        return None

def get_with_retry(url, params=None, headers=None, tries=3, sleep_sec=5, timeout=30):
    """
    일시 오류/비JSON 응답을 흡수하기 위한 재시도.
    참고: GDELT 측도 가이던스에서 레이트 리미팅/간헐적 응답을 언급합니다. (재시도 권장)
    """
    for i in range(tries):
        try:
            r = requests.get(url, params=params, headers=headers, timeout=timeout)
        except Exception:
            r = None
        data = safe_json(r) if (r and r.ok) else None
        if data:
            return data
        if i < tries - 1:
            time.sleep(sleep_sec)
    return {}

def dedupe(df):
    if df.empty: 
        return df
    df["title_norm"] = df["title"].str.lower().str.replace(r"[^a-z0-9가-힣一-龥 ]","", regex=True).str.strip()
    df["domain"] = df["url"].apply(norm_domain)
    df = df.drop_duplicates(subset=["domain","title_norm"])
    # 제목 유사도 중복 제거(90 이상)
    keep, seen = [], []
    for _, row in df.iterrows():
        t = row["title_norm"]
        if not seen:
            keep.append(True); seen.append(t); continue
        score = max(process.extractOne(t, seen, scorer=fuzz.token_set_ratio)[1], default=0)
        if score >= 90:
            keep.append(False)
        else:
            keep.append(True); seen.append(t)
    return df[pd.Series(keep, index=df.index)].drop(columns=["title_norm"])

def select_top_cap(df_all, max_total=20, per_min=2):
    if df_all.empty:
        return df_all
    df_all = df_all.sort_values("published", ascending=False)

    # 1) 품목별 최소 할당
    picks = []
    for code, sub in df_all.groupby("commodity"):
        picks.append(sub.head(per_min))
    base = pd.concat(picks).drop_duplicates(subset=["url"])

    # 2) 최신순으로 보충
    remain = max_total - len(base)
    if remain > 0:
        extra = (df_all[~df_all["url"].isin(base["url"])]).head(remain)
        sel = pd.concat([base, extra])
    else:
        sel = base.head(max_total)

    return sel.sort_values("published", ascending=False).head(max_total)

def query_terms(names, must_have):
    # (copper OR 구리 OR 铜) AND (price OR export ...)
    name_part = "(" + " OR ".join(sorted(set(sum(names.values(), [])))) + ")"
    mh_part = "(" + " OR ".join(must_have) + ")"
    return f"{name_part} AND {mh_part}"

# ---- 수집기 ----
# GDELT Doc 2.0 (ArtList/JSON) — 전 세계 뉴스 문서 메타 검색
# 공식 블로그 문서: JSON/ArtList 등 포맷 안내.  :contentReference[oaicite:0]{index=0}
def fetch_gdelt_doc(q, start, end, lang=None):
    url = "https://api.gdeltproject.org/api/v2/doc/doc"
    params = {
        "format": "JSON",
        "mode": "ArtList",
        "maxrecords": 120,
        "sort": "datedesc",
        "query": q,
        "startdatetime": start.strftime("%Y%m%d%H%M%S"),
        "enddatetime": end.strftime("%Y%m%d%H%M%S"),
    }
    if lang: 
        params["sourcelang"] = lang

    data = get_with_retry(url, params=params, tries=3, sleep_sec=5)
    rows = []
    for a in (data.get("articles") or []):
        if not allow_domain(a.get("url","")): 
            continue
        rows.append({
            "source": "GDELT",
            "title": a.get("title"),
            "url": a.get("url"),
            "published": a.get("seendate"),
            "language": a.get("language"),
            "country": a.get("sourcecountry"),
            "snippet": None
        })
    return rows

# GDELT Context 2.0 — 문장 단위 스니펫 제공 (ArticleList 출력 포맷 지원)
# 주의: Context 2.0은 "최근 72시간" 윈도 내에서 START/END가 유효합니다.  :contentReference[oaicite:1]{index=1}
def fetch_gdelt_context(q, start, end, lang=None):
    ctx_end = datetime.now(tz=KST)
    ctx_start = max(ctx_end - timedelta(hours=72), start)

    url = "https://api.gdeltproject.org/api/v2/doc/context"
    params = {
        "format":"JSON",
        "query": q,
        "maxrecords": 80,
        "mode":"ArtList",
        "startdatetime": ctx_start.strftime("%Y%m%d%H%M%S"),
        "enddatetime": ctx_end.strftime("%Y%m%d%H%M%S"),
    }
    if lang: 
        params["sourcelang"] = lang

    data = get_with_retry(url, params=params, tries=3, sleep_sec=5)
    rows = []
    for a in (data.get("articles") or []):
        if not allow_domain(a.get("url","")): 
            continue
        rows.append({
            "source": "GDELT-CTX",
            "title": a.get("title"),
            "url": a.get("url"),
            "published": a.get("seendate"),
            "language": a.get("language"),
            "country": a.get("sourcecountry"),
            "snippet": simple_summary(a.get("context")),
        })
    return rows

# NewsAPI (선택) — Everything 엔드포인트, pageSize 최대 100  :contentReference[oaicite:2]{index=2}
def fetch_newsapi(q, start, end):
    if not NEWSAPI_KEY: 
        return []
    url = "https://newsapi.org/v2/everything"
    headers = {"X-Api-Key": NEWSAPI_KEY}
    params = {
        "q": q,
        "from": start.date().isoformat(),
        "to": end.date().isoformat(),
        "pageSize": 50,     # 최대 100까지 가능. 여기선 네트워크 비용↓
        "page": 1,
        "sortBy": "publishedAt",
    }
    r = requests.get(url, headers=headers, params=params, timeout=30)
    data = safe_json(r) if r.ok else None
    if not data:
        return []
    rows = []
    for a in data.get("articles", []):
        if not allow_domain(a.get("url","")): 
            continue
        rows.append({
            "source": "NewsAPI",
            "title": a.get("title"),
            "url": a.get("url"),
            "published": a.get("publishedAt"),
            "language": None,
            "country": None,
            "snippet": simple_summary(a.get("description") or a.get("content")),
        })
    return rows

# Event Registry (선택) — 기사/언어 필터 등 제공
def fetch_event_registry(q, start, end):
    if not EVENT_REGISTRY_API_KEY: 
        return []
    url = "https://eventregistry.org/api/v1/article/getArticles"
    params = {
        "apiKey": EVENT_REGISTRY_API_KEY,
        "keyword": q,
        "dateStart": start.date().isoformat(),
        "dateEnd": end.date().isoformat(),
        "lang": "eng,kor,zho",
        "sortBy": "date",
        "maxItems": 120,
        "includeArticleConcepts": False
    }
    data = get_with_retry(url, params=params, tries=2, sleep_sec=5)
    if not data:
        return []
    res = data.get("articles", {}).get("results", [])
    rows = []
    for a in res:
        if not allow_domain(a.get("url","")): 
            continue
        rows.append({
            "source": "EventRegistry",
            "title": a.get("title"),
            "url": a.get("url"),
            "published": a.get("dateTime"),
            "language": a.get("lang"),
            "country": a.get("source",{}).get("location",{}).get("country",{}).get("label"),
            "snippet": simple_summary(a.get("body"))
        })
    return rows

# ---- 이메일 ----
def send_email_ko(subject, body_markdown, attach_csv_path, to_addr):
    if not GMAIL_USER or not GMAIL_APP_PASSWORD:
        raise RuntimeError("Gmail 발신 계정/앱 비밀번호가 없습니다. GMAIL_USER, GMAIL_APP_PASSWORD Secrets를 설정하세요.")

    msg = EmailMessage()
    display_from = formataddr((CFG["email"]["from_name_ko"], GMAIL_USER))
    msg["From"] = display_from
    msg["To"] = to_addr
    msg["Subject"] = subject
    msg.set_content(body_markdown)

    if attach_csv_path and os.path.exists(attach_csv_path):
        with open(attach_csv_path, "rb") as f:
            data = f.read()
        msg.add_attachment(data, maintype="text", subtype="csv", filename=os.path.basename(attach_csv_path))

    # Gmail 2단계 인증 + 앱 비밀번호 필요 (공식 가이드)  :contentReference[oaicite:3]{index=3}
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)
        smtp.send_message(msg)

# ---- 실행 ----
def run_once():
    start, end = daterange()
    frames = []
    for c in CFG["commodities"]:
        q = query_terms(c["names"], c["must_have"])
        rows = []
        rows += fetch_gdelt_doc(q, start, end)
        rows += fetch_gdelt_context(q, start, end)
        rows += fetch_event_registry(q, start, end)  # 선택
        rows += fetch_newsapi(q, start, end)         # 선택
        df = pd.DataFrame(rows)
        if df.empty:
            frames.append(pd.DataFrame())
            continue
        df["commodity"] = c["code"]
        df = df[["commodity","source","published","language","country","title","snippet","url"]]
        frames.append(df)

    all_df = pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()
    if all_df.empty:
        body = f"""안녕하세요.

이번 달({start.date()} ~ {end.date()})에는 조건에 맞는 기사를 찾지 못했습니다.
설정(config.yaml)이나 키워드를 확인해 주세요.

감사합니다.
"""
        subject = f"{CFG['email']['subject_prefix_ko']} (데이터 없음)"
        send_email_ko(subject, body, None, CFG["email"]["to"])
        print("No data. Email sent.")
        return

    all_df["published"] = pd.to_datetime(all_df["published"], errors="coerce")
    all_df = all_df.dropna(subset=["title","url"])
    all_df = dedupe(all_df).sort_values("published", ascending=False)

    # 20건 이하로 축소
    max_total = int(CFG["run"]["max_total"])
    per_min   = int(CFG["run"]["per_commodity_min"])
    sel_df = select_top_cap(all_df, max_total=max_total, per_min=per_min)

    # CSV 저장 (도메인/링크 포함)
    sel_df["domain"] = sel_df["url"].apply(norm_domain)
    sel_df = sel_df[["commodity","published","domain","source","language","country","title","snippet","url"]]
    stamp = datetime.now(tz=KST).strftime("%Y%m%d")
    csv_path = os.path.join(OUTDIR, f"commodities_{stamp}.csv")
    sel_df.to_csv(csv_path, index=False, encoding="utf-8-sig")

    # 이메일 본문(한국어)
    lines = []
    lines.append(f"# {CFG['email']['subject_prefix_ko']} {start.date()} ~ {end.date()}\n")
    lines.append("다음은 자동 수집·중복제거 후 선정된 상위 기사입니다. (최대 20건)\n")
    for code, sub in sel_df.groupby("commodity"):
        lines.append(f"## {code}")
        for _, r in sub.iterrows():
            d = str(r["published"])[:10]
            lines.append(f"- {r['title']} — {d} · {r.get('domain','')} ({r.get('source','')})")
            lines.append(f"  링크: {r['url']}")
            if r.get("snippet"):
                lines.append(f"  요약: {r['snippet']}")
        lines.append("")
    body_md = "\n".join(lines)

    subject = f"{CFG['email']['subject_prefix_ko']} {stamp}"
    send_email_ko(subject, body_md, csv_path, CFG["email"]["to"])
    print("Saved CSV and sent email:", csv_path)

if __name__ == "__main__":
    run_once()
