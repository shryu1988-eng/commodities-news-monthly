# -*- coding: utf-8 -*-
# 강화판 main.py
# - 신뢰도 가중치 + 관련성 스코어링 + 보도자료 차단
# - 안전 JSON 파싱, 재시도, GDELT Context 72시간 제한

import os, re, time
import requests
import pandas as pd
from datetime import datetime, timedelta, timezone
import yaml, tldextract
from rapidfuzz import fuzz, process
import smtplib
from email.message import EmailMessage
from email.utils import formataddr

KST = timezone(timedelta(hours=9))

# ---- 환경 변수 (Secrets 권장) ----
NEWSAPI_KEY = os.getenv("NEWSAPI_KEY", "")                      # 선택
EVENT_REGISTRY_API_KEY = os.getenv("EVENT_REGISTRY_API_KEY", "")# 선택
GMAIL_USER = os.getenv("GMAIL_USER", "")                        # 필수(이메일 버전)
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")        # 필수(이메일 버전)

# ---- 설정 로드 ----
with open("config.yaml", "r", encoding="utf-8") as f:
    CFG = yaml.safe_load(f)

OUTDIR = CFG["run"]["output_dir"]
os.makedirs(OUTDIR, exist_ok=True)

# ====== 유틸 ======
def daterange():
    end = datetime.now(tz=KST)
    start = end - timedelta(days=int(CFG["run"]["lookback_days"]))
    return start, end

def norm_domain(url: str) -> str:
    try:
        ext = tldextract.extract(url)
        return ".".join([p for p in [ext.domain, ext.suffix] if p])
    except:
        return ""

def simple_summary(text, max_len=40):
    text = re.sub(r"\s+", " ", (text or "")).strip()
    return " ".join(text.split()[:max_len])

def safe_json(resp):
    try:
        if not resp: return None
        ct = (resp.headers.get("Content-Type") or "").lower()
        if "json" not in ct:
            return None
        return resp.json()
    except Exception:
        return None

def get_with_retry(url, params=None, headers=None, tries=3, sleep_sec=5, timeout=30):
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

# ====== 신뢰도 & 필터 ======
PRESS_RELEASE_HOSTS = [
    "prnewswire.com","globenewswire.com","businesswire.com","einnews.com",
    "marketscreener.com","newsfilecorp.com","streetinsider.com"
]
AGGREGATORS = ["news.google.com","flipboard.com","bing.com/news"]

# 도메인 신뢰도 스코어 (0~1). 필요시 config.yaml의 trust_domains로 덮어쓰기 가능
DEFAULT_TRUST = {
    # 금속/원자재 전문
    "lme.com": 1.00,                      # LME 공식. :contentReference[oaicite:3]{index=3}
    "spglobal.com": 0.95,                 # S&P Global Commodity Insights(Platts). :contentReference[oaicite:4]{index=4}
    "fastmarkets.com": 0.92,              # Fastmarkets/Metal Bulletin. :contentReference[oaicite:5]{index=5}
    "icis.com": 0.92,                     # 화학(ACN 등). :contentReference[oaicite:6]{index=6}
    "argusmedia.com": 0.90,               # Argus Media. :contentReference[oaicite:7]{index=7}
    "mining.com": 0.88,                   # 광산/금속 전문
    "kitco.com": 0.85,                    # 귀금속/원자재

    # 범용 유력 매체 (경제/시장)
    "reuters.com": 0.95,
    "ft.com": 0.93,
    "wsj.com": 0.92,
    "nikkei.com": 0.90,
    "bloomberg.com": 0.95,
    "cnbc.com": 0.85
}

TRUST_OVERRIDE = {d.lower(): s for d, s in (CFG.get("sources", {}).get("trust_domains") or {}).items()}

def domain_trust_score(url: str) -> float:
    d = norm_domain(url).lower()
    score = TRUST_OVERRIDE.get(d, DEFAULT_TRUST.get(d, 0.50))
    # 보도자료/어그리게이터 강한 페널티
    if any(h in url for h in PRESS_RELEASE_HOSTS+AGGREGATORS):
        score = min(score, 0.20)
    return score

def allow_url(url: str) -> bool:
    if not url: return False
    if any(b in url for b in CFG["sources"]["blacklist_domains"]): return False
    wl = CFG["sources"]["whitelist_domains"]
    return True if not wl else any(w in url for w in wl)

# ====== 관련성 스코어 ======
def keyword_hits(text: str, terms: list[str]) -> int:
    if not text: return 0
    t = text.lower()
    return sum(1 for k in terms if k.lower() in t)

def near_match_in_title(title: str, names_all: list[str], must: list[str]) -> bool:
    if not title: return False
    tl = title.lower()
    return (any(n.lower() in tl for n in names_all) and any(m.lower() in tl for m in must))

def relevance_score(row, names_all, must_list, lang_weight=1.0):
    # 기본: 제목 가중치↑, 스니펫 가중치↓
    title = (row.get("title") or "")
    snip  = (row.get("snippet") or "")
    title_hit = keyword_hits(title, names_all) * 2 + keyword_hits(title, must_list) * 3
    snip_hit  = keyword_hits(snip, names_all) + keyword_hits(snip, must_list) * 2

    # 제목 내 동시 출현/근접 매칭 보너스
    bonus = 3 if near_match_in_title(title, names_all, must_list) else 0

    # 언어 가중치(ko/en/zh 우선)
    lang = (row.get("language") or "").lower()
    lang_map = {"ko":1.2, "en":1.1, "zh":1.05}
    lw = lang_map.get(lang, 1.0) * lang_weight

    return (title_hit + snip_hit + bonus) * lw

# ====== 수집기 ======
def query_terms(names_dict, must_have):
    all_names = sorted(set(sum(names_dict.values(), [])))
    name_part = "(" + " OR ".join(all_names) + ")"
    mh_part = "(" + " OR ".join(must_have) + ")"
    return f"{name_part} AND {mh_part}", all_names

def fetch_gdelt_doc(q, start, end, lang=None):
    # GDELT DOC 2.0 ArtList JSON (공식 블로그) :contentReference[oaicite:8]{index=8}
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
    if lang: params["sourcelang"] = lang
    data = get_with_retry(url, params=params, tries=3, sleep_sec=5)
    rows = []
    for a in (data.get("articles") or []):
        u = a.get("url","")
        if not allow_url(u): 
            continue
        rows.append({
            "source": "GDELT",
            "title": a.get("title"),
            "url": u,
            "published": a.get("seendate"),
            "language": a.get("language"),
            "country": a.get("sourcecountry"),
            "snippet": None
        })
    return rows

def fetch_gdelt_context(q, start, end, lang=None):
    # Context 2.0: 최근 72시간 윈도만 지원 :contentReference[oaicite:9]{index=9}
    ctx_end = datetime.now(tz=KST)
    ctx_start = max(ctx_end - timedelta(hours=72), start)
    url = "https://api.gdeltproject.org/api/v2/doc/context"
    params = {
        "format":"JSON","mode":"ArtList","maxrecords":80,"query":q,
        "startdatetime": ctx_start.strftime("%Y%m%d%H%M%S"),
        "enddatetime": ctx_end.strftime("%Y%m%d%H%M%S"),
    }
    if lang: params["sourcelang"] = lang
    data = get_with_retry(url, params=params, tries=3, sleep_sec=5)
    rows = []
    for a in (data.get("articles") or []):
        u = a.get("url","")
        if not allow_url(u): 
            continue
        rows.append({
            "source": "GDELT-CTX",
            "title": a.get("title"),
            "url": u,
            "published": a.get("seendate"),
            "language": a.get("language"),
            "country": a.get("sourcecountry"),
            "snippet": simple_summary(a.get("context"))
        })
    return rows

def fetch_newsapi(q, start, end):
    # NewsAPI: everything pageSize 최대 100 :contentReference[oaicite:10]{index=10}
    if not NEWSAPI_KEY: return []
    url = "https://newsapi.org/v2/everything"
    headers = {"X-Api-Key": NEWSAPI_KEY}
    params = {
        "q": q,
        "from": start.date().isoformat(),
        "to": end.date().isoformat(),
        "pageSize": 100,
        "page": 1,
        "sortBy": "publishedAt",
    }
    r = requests.get(url, headers=headers, params=params, timeout=30)
    data = safe_json(r) if r.ok else None
    rows = []
    for a in (data.get("articles", []) if data else []):
        u = a.get("url","")
        if not allow_url(u): 
            continue
        rows.append({
            "source": "NewsAPI",
            "title": a.get("title"),
            "url": u,
            "published": a.get("publishedAt"),
            "language": None,
            "country": None,
            "snippet": simple_summary(a.get("description") or a.get("content"))
        })
    return rows

def fetch_event_registry(q, start, end):
    if not EVENT_REGISTRY_API_KEY: return []
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
    rows = []
    for a in (data.get("articles", {}).get("results", []) if data else []):
        u = a.get("url","")
        if not allow_url(u): 
            continue
        rows.append({
            "source": "EventRegistry",
            "title": a.get("title"),
            "url": u,
            "published": a.get("dateTime"),
            "language": a.get("lang"),
            "country": a.get("source",{}).get("location",{}).get("country",{}).get("label"),
            "snippet": simple_summary(a.get("body"))
        })
    return rows

# ====== 중복·스코어·선정 ======
def dedupe_strict(df):
    if df.empty: return df
    df["title_norm"] = (
        df["title"].str.lower()
        .str.replace(r"[^a-z0-9가-힣一-龥 ]","", regex=True)
        .str.strip()
    )
    df["domain"] = df["url"].apply(norm_domain)
    # 1차: (domain,title_norm)
    df = df.drop_duplicates(subset=["domain","title_norm"])
    # 2차: 제목 유사도(90↑) 제거
    keep, seen = [], []
    for _, row in df.iterrows():
        t = row["title_norm"]
        if not seen:
            keep.append(True); seen.append(t); continue
        res = process.extractOne(t, seen, scorer=fuzz.token_set_ratio)
        score = res[1] if res else 0
        if score >= 90: keep.append(False)
        else:
            keep.append(True); seen.append(t)
    return df[pd.Series(keep, index=df.index)].drop(columns=["title_norm"])

def select_ranked(df_all, commodities_cfg, max_total=20, per_min=2):
    if df_all.empty: return df_all
    out_rows = []
    for c in commodities_cfg:
        code = c["code"]
        names_dict = c["names"]; must_list = c["must_have"]
        q, names_all = query_terms(names_dict, must_list)

        sub = df_all[df_all["commodity"]==code].copy()
        if sub.empty: 
            continue

        # 스코어링
        scores = []
        for _, r in sub.iterrows():
            trust = domain_trust_score(r["url"])
            rel   = relevance_score(r, names_all, must_list, lang_weight=1.0)
            total = rel*0.7 + trust*10*0.3   # (0~?)*0.7 + (0~10)*0.3
            scores.append(total)
        sub["score"] = scores

        # 보도자료/어그리게이터 강제 제거
        mask_bad = False
        for h in PRESS_RELEASE_HOSTS + AGGREGATORS:
            mask_bad = mask_bad | sub["url"].str.contains(h, na=False)
        sub = sub[~mask_bad]

        # 품목별 상위 per_min 선반영
        sub = sub.sort_values(["score","published"], ascending=[False, False])
        out_rows.append(sub.head(per_min))

    base = pd.concat(out_rows) if out_rows else pd.DataFrame()
    rest = df_all[~df_all.index.isin(base.index)].copy()

    # 나머지는 전 품목 통합 스코어로 최신/점수 순 보충
    if not rest.empty:
        rest_scores = []
        for _, r in rest.iterrows():
            trust = domain_trust_score(r["url"])
            # 어떤 품목의 names/must가 더 맞는지 모르니 타이틀 기반 대략치
            # (간단히: 전체 키워드 합산)
            names_flat = sorted(set(sum([sum(c["names"].values(), []) for c in commodities_cfg], [])))
            must_flat  = sorted(set(sum([c["must_have"] for c in commodities_cfg], [])))
            rel = relevance_score(r, names_flat, must_flat, lang_weight=1.0)
            rest_scores.append(rel*0.7 + trust*10*0.3)
        rest["score"] = rest_scores
        pool = pd.concat([base, rest]).sort_values(["score","published"], ascending=[False, False])
    else:
        pool = base.sort_values(["score","published"], ascending=[False, False])

    return pool.head(max_total)

# ====== 메일 ======
def send_email_ko(subject, body_markdown, attach_csv_path, to_addr):
    if not GMAIL_USER or not GMAIL_APP_PASSWORD:
        raise RuntimeError("GMAIL_USER/GMAIL_APP_PASSWORD가 없습니다.")
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
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)
        smtp.send_message(msg)

# ====== 실행 ======
def run_once():
    start, end = daterange()
    frames = []
    for c in CFG["commodities"]:
        q, _names_all = query_terms(c["names"], c["must_have"])
        rows = []
        rows += fetch_gdelt_doc(q, start, end)
        rows += fetch_gdelt_context(q, start, end)
        rows += fetch_event_registry(q, start, end)  # 선택
        rows += fetch_newsapi(q, start, end)         # 선택
        df = pd.DataFrame(rows)
        if df.empty:
            frames.append(pd.DataFrame()); continue
        df["commodity"] = c["code"]
        df = df[["commodity","source","published","language","country","title","snippet","url"]]
        frames.append(df)

    all_df = pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()
    if all_df.empty:
        subject = f"{CFG['email']['subject_prefix_ko']} (데이터 없음)"
        body = f"수집 기간 {start.date()} ~ {end.date()}에 유의미한 기사가 없습니다."
        send_email_ko(subject, body, None, CFG["email"]["to"])
        print("No data. Email sent."); return

    all_df["published"] = pd.to_datetime(all_df["published"], errors="coerce")
    all_df = all_df.dropna(subset=["title","url"])
    all_df = dedupe_strict(all_df)

    # 신뢰/관련성 기반 랭킹 → 최대 20건
    sel_df = select_ranked(
        all_df.sort_values("published", ascending=False),
        CFG["commodities"],
        max_total=int(CFG["run"]["max_total"]),
        per_min=int(CFG["run"]["per_commodity_min"])
    )

    # CSV 저장
    sel_df["domain"] = sel_df["url"].apply(norm_domain)
    sel_df = sel_df[["commodity","published","domain","source","language","country","title","snippet","url","score"]]
    stamp = datetime.now(tz=KST).strftime("%Y%m%d")
    csv_path = os.path.join(OUTDIR, f"commodities_{stamp}.csv")
    sel_df.to_csv(csv_path, index=False, encoding="utf-8-sig")

    # 이메일 본문
    lines = [f"# {CFG['email']['subject_prefix_ko']} {start.date()} ~ {end.date()}\n",
             "신뢰·관련성 스코어 반영 상위 기사(최대 20건):\n"]
    for code, sub in sel_df.groupby("commodity"):
        lines.append(f"## {code}")
        for _, r in sub.sort_values(["score","published"], ascending=[False,False]).iterrows():
            d = str(r["published"])[:10]
            lines.append(f"- {r['title']} — {d} · {r.get('domain','')} (score {r['score']:.1f})")
            lines.append(f"  링크: {r['url']}")
            if r.get("snippet"): lines.append(f"  요약: {r['snippet']}")
        lines.append("")
    body_md = "\n".join(lines)

    subject = f"{CFG['email']['subject_prefix_ko']} {stamp}"
    send_email_ko(subject, body_md, csv_path, CFG["email"]["to"])
    print("Saved CSV and sent email:", csv_path)

if __name__ == "__main__":
    run_once()
