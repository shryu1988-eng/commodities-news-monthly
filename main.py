# -*- coding: utf-8 -*-
# main.py — 기사 수집 → 중복/스코어링 → 상위 20건 → 한국어 메일(제목/요약 번역) + CSV 첨부
# 번역 우선순위: DeepL → Azure Translator → Google Cloud Translate(v2)
# 안전 JSON/재시도, GDELT Context 72h 제한, RapidFuzz 중복제거, 신뢰/관련성 스코어링 유지

import os, re, time, json
import requests
import pandas as pd
from datetime import datetime, timedelta, timezone
import yaml, tldextract
from rapidfuzz import fuzz, process
from langdetect import detect, DetectorFactory
DetectorFactory.seed = 0  # langdetect 결과 안정화

import smtplib
from email.message import EmailMessage
from email.utils import formataddr

KST = timezone(timedelta(hours=9))

# ==== Secrets / API Keys ====
NEWSAPI_KEY = os.getenv("NEWSAPI_KEY", "")                      # 선택
EVENT_REGISTRY_API_KEY = os.getenv("EVENT_REGISTRY_API_KEY", "")# 선택
GMAIL_USER = os.getenv("GMAIL_USER", "")                        # 필수(이메일)
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")        # 필수(이메일)

# 번역: 하나만 있어도 됨 (DeepL 권장)
DEEPL_API_KEY = os.getenv("DEEPL_API_KEY", "")
DEEPL_API_URL = os.getenv("DEEPL_API_URL", "https://api-free.deepl.com/v2/translate")  # 유료는 https://api.deepl.com/v2/translate
AZURE_TRANSLATOR_KEY = os.getenv("AZURE_TRANSLATOR_KEY", "")
AZURE_TRANSLATOR_REGION = os.getenv("AZURE_TRANSLATOR_REGION", "")
GOOGLE_TRANSLATE_API_KEY = os.getenv("GOOGLE_TRANSLATE_API_KEY", "")

# ==== 설정 로드 ====
with open("config.yaml", "r", encoding="utf-8") as f:
    CFG = yaml.safe_load(f)

OUTDIR = CFG["run"]["output_dir"]
os.makedirs(OUTDIR, exist_ok=True)

# ==== 유틸/HTTP ====
def daterange():
    end = datetime.now(tz=KST)
    start = end - timedelta(days=int(CFG["run"]["lookback_days"]))
    return start, end

def norm_domain(url):
    try:
        ext = tldextract.extract(url)
        return ".".join([p for p in [ext.domain, ext.suffix] if p])
    except:
        return ""

def safe_json(resp):
    try:
        if not resp: return None
        ct = (resp.headers.get("Content-Type") or "").lower()
        if "json" not in ct:
            return None
        return resp.json()
    except Exception:
        return None

def get_with_retry(url, params=None, headers=None, tries=3, sleep_sec=5, timeout=30, json_body=None, method="GET"):
    for i in range(tries):
        try:
            if method == "GET":
                r = requests.get(url, params=params, headers=headers, timeout=timeout)
            else:
                r = requests.post(url, params=params, headers=headers, timeout=timeout, json=json_body)
        except Exception:
            r = None
        data = safe_json(r) if (r and r.ok) else None
        if data:
            return data
        if i < tries - 1:
            time.sleep(sleep_sec)
    return {}

def simple_summary(text, max_len=40):
    text = re.sub(r"\s+", " ", (text or "")).strip()
    return " ".join(text.split()[:max_len])

# ==== 출처 필터/신뢰 가중 ====
PRESS_RELEASE_HOSTS = [
    "prnewswire.com","globenewswire.com","businesswire.com","einnews.com",
    "marketscreener.com","newsfilecorp.com","streetinsider.com"
]
AGGREGATORS = ["news.google.com","flipboard.com","bing.com/news"]

DEFAULT_TRUST = {
    "lme.com": 1.00, "spglobal.com": 0.95, "fastmarkets.com": 0.92, "icis.com": 0.92,
    "argusmedia.com": 0.90, "mining.com": 0.88, "kitco.com": 0.85,
    "reuters.com": 0.95, "ft.com": 0.93, "wsj.com": 0.92, "nikkei.com": 0.90, "bloomberg.com": 0.95, "cnbc.com": 0.85
}
TRUST_OVERRIDE = {d.lower(): s for d, s in (CFG.get("sources", {}).get("trust_domains") or {}).items()}

def allow_url(url):
    if not url: return False
    if any(b in url for b in CFG["sources"]["blacklist_domains"]): return False
    wl = CFG["sources"]["whitelist_domains"]
    return True if not wl else any(w in url for w in wl)

def domain_trust_score(url):
    d = norm_domain(url).lower()
    score = TRUST_OVERRIDE.get(d, DEFAULT_TRUST.get(d, 0.50))
    if any(h in url for h in PRESS_RELEASE_HOSTS+AGGREGATORS):
        score = min(score, 0.20)
    return score

# ==== 관련성 스코어 ====
def keyword_hits(text, terms):
    if not text: return 0
    t = text.lower()
    return sum(1 for k in terms if k.lower() in t)

def near_match_in_title(title, names_all, must):
    if not title: return False
    tl = title.lower()
    return (any(n.lower() in tl for n in names_all) and any(m.lower() in tl for m in must))

def relevance_score(row, names_all, must_list, lang_weight=1.0):
    title = (row.get("title") or "")
    snip  = (row.get("snippet") or "")
    title_hit = keyword_hits(title, names_all) * 2 + keyword_hits(title, must_list) * 3
    snip_hit  = keyword_hits(snip, names_all) + keyword_hits(snip, must_list) * 2
    bonus = 3 if near_match_in_title(title, names_all, must_list) else 0
    lang = (row.get("language") or "").lower()
    lang_map = {"ko":1.2, "en":1.1, "zh":1.05}
    lw = lang_map.get(lang, 1.0) * lang_weight
    return (title_hit + snip_hit + bonus) * lw

# ==== 번역기 ====
def detect_lang(text):
    try:
        return detect(text) if text and text.strip() else ""
    except Exception:
        return ""

def translate_text_to_ko(text):
    """DeepL → Azure → Google v2 순으로 사용. 실패/키 없음/한국어면 원문 반환."""
    if not text or not text.strip():
        return text

    # 이미 한국어면 그대로
    try:
        if detect(text) == "ko":
            return text
    except Exception:
        pass

    # 1) DeepL
    if DEEPL_API_KEY:
        headers = {"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"}
        params = {"target_lang": "KO"}
        data = get_with_retry(DEEPL_API_URL, params=params, headers=headers,
                              tries=2, sleep_sec=3, method="POST",
                              json_body={"text": [text]})
        try:
            tr = data.get("translations", [{}])[0].get("text")
            if tr: return tr
        except Exception:
            pass

    # 2) Azure Translator
    if AZURE_TRANSLATOR_KEY and AZURE_TRANSLATOR_REGION:
        url = "https://api.cognitive.microsofttranslator.com/translate"
        params = {"api-version":"3.0", "to":"ko"}
        headers = {
            "Ocp-Apim-Subscription-Key": AZURE_TRANSLATOR_KEY,
            "Ocp-Apim-Subscription-Region": AZURE_TRANSLATOR_REGION,
            "Content-Type": "application/json"
        }
        data = get_with_retry(url, params=params, headers=headers,
                              tries=2, sleep_sec=3, method="POST",
                              json_body=[{"text": text}])
        try:
            tr = data[0]["translations"][0]["text"]
            if tr: return tr
        except Exception:
            pass

    # 3) Google Cloud Translate v2 (API Key)
    if GOOGLE_TRANSLATE_API_KEY:
        url = "https://translation.googleapis.com/language/translate/v2"
        params = {"key": GOOGLE_TRANSLATE_API_KEY}
        headers = {"Content-Type":"application/json"}
        body = {"q": text, "target": "ko", "format": "text"}
        data = get_with_retry(url, params=params, headers=headers,
                              tries=2, sleep_sec=3, method="POST",
                              json_body=body)
        try:
            tr = data["data"]["translations"][0]["translatedText"]
            if tr: return tr
        except Exception:
            pass

    # 실패 시 원문 반환
    return text

# ==== 중복 제거 & 선정 ====
def dedupe_strict(df):
    if df.empty: return df
    df["title_norm"] = (
        df["title"].str.lower()
        .str.replace(r"[^a-z0-9가-힣一-龥 ]","", regex=True)
        .str.strip()
    )
    df["domain"] = df["url"].apply(norm_domain)
    df = df.drop_duplicates(subset=["domain","title_norm"])
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

def query_terms(names_dict, must_have):
    all_names = sorted(set(sum(names_dict.values(), [])))
    name_part = "(" + " OR ".join(all_names) + ")"
    mh_part = "(" + " OR ".join(must_have) + ")"
    return f"{name_part} AND {mh_part}", all_names

def select_ranked(df_all, commodities_cfg, max_total=20, per_min=2):
    if df_all.empty: return df_all
    out_rows = []
    for c in commodities_cfg:
        code = c["code"]
        names_dict = c["names"]; must_list = c["must_have"]
        _, names_all = query_terms(names_dict, must_list)
        sub = df_all[df_all["commodity"]==code].copy()
        if sub.empty: 
            continue
        scores = []
        for _, r in sub.iterrows():
            trust = domain_trust_score(r["url"])
            rel   = relevance_score(r, names_all, must_list, lang_weight=1.0)
            total = rel*0.7 + trust*10*0.3
            scores.append(total)
        sub["score"] = scores
        # 보도자료/어그리게이터 제거
        bad = False
        for h in PRESS_RELEASE_HOSTS + AGGREGATORS:
            bad = bad | sub["url"].str.contains(h, na=False)
        sub = sub[~bad]
        out_rows.append(sub.sort_values(["score","published"], ascending=[False,False]).head(per_min))
    base = pd.concat(out_rows) if out_rows else pd.DataFrame()
    rest = df_all[~df_all.index.isin(base.index)].copy()
    if not rest.empty:
        names_flat = sorted(set(sum([sum(c["names"].values(), []) for c in commodities_cfg], [])))
        must_flat  = sorted(set(sum([c["must_have"] for c in commodities_cfg], [])))
        rest_scores = []
        for _, r in rest.iterrows():
            trust = domain_trust_score(r["url"])
            rel = relevance_score(r, names_flat, must_flat, lang_weight=1.0)
            rest_scores.append(rel*0.7 + trust*10*0.3)
        rest["score"] = rest_scores
        pool = pd.concat([base, rest]).sort_values(["score","published"], ascending=[False, False])
    else:
        pool = base.sort_values(["score","published"], ascending=[False, False])
    return pool.head(max_total)

# ==== 수집기 (GDELT/NewsAPI/EventRegistry) ====
def fetch_gdelt_doc(q, start, end, lang=None):
    url = "https://api.gdeltproject.org/api/v2/doc/doc"
    params = {
        "format": "JSON", "mode": "ArtList", "maxrecords": 120, "sort": "datedesc",
        "query": q, "startdatetime": start.strftime("%Y%m%d%H%M%S"), "enddatetime": end.strftime("%Y%m%d%H%M%S"),
    }
    if lang: params["sourcelang"] = lang
    data = get_with_retry(url, params=params, tries=3, sleep_sec=5)
    rows = []
    for a in (data.get("articles") or []):
        u = a.get("url","")
        if not allow_url(u): continue
        rows.append({
            "source":"GDELT","title":a.get("title"),"url":u,"published":a.get("seendate"),
            "language":a.get("language"),"country":a.get("sourcecountry"),"snippet":None
        })
    return rows

def fetch_gdelt_context(q, start, end, lang=None):
    # Context 2.0: 72시간 윈도우 제한
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
        if not allow_url(u): continue
        rows.append({
            "source":"GDELT-CTX","title":a.get("title"),"url":u,"published":a.get("seendate"),
            "language":a.get("language"),"country":a.get("sourcecountry"),
            "snippet": simple_summary(a.get("context"))
        })
    return rows

def fetch_newsapi(q, start, end):
    if not NEWSAPI_KEY: return []
    url = "https://newsapi.org/v2/everything"
    headers = {"X-Api-Key": NEWSAPI_KEY}
    params = {"q": q, "from": start.date().isoformat(), "to": end.date().isoformat(),
              "pageSize": 100, "page": 1, "sortBy": "publishedAt"}
    r = requests.get(url, headers=headers, params=params, timeout=30)
    data = safe_json(r) if r.ok else None
    rows = []
    for a in (data.get("articles", []) if data else []):
        u = a.get("url","")
        if not allow_url(u): continue
        rows.append({
            "source":"NewsAPI","title":a.get("title"),"url":u,"published":a.get("publishedAt"),
            "language":None,"country":None,"snippet": simple_summary(a.get("description") or a.get("content"))
        })
    return rows

def fetch_event_registry(q, start, end):
    if not EVENT_REGISTRY_API_KEY: return []
    url = "https://eventregistry.org/api/v1/article/getArticles"
    params = {
        "apiKey": EVENT_REGISTRY_API_KEY, "keyword": q,
        "dateStart": start.date().isoformat(), "dateEnd": end.date().isoformat(),
        "lang": "eng,kor,zho", "sortBy": "date", "maxItems": 120, "includeArticleConcepts": False
    }
    data = get_with_retry(url, params=params, tries=2, sleep_sec=5)
    rows = []
    for a in (data.get("articles", {}).get("results", []) if data else []):
        u = a.get("url","")
        if not allow_url(u): continue
        rows.append({
            "source":"EventRegistry","title":a.get("title"),"url":u,"published":a.get("dateTime"),
            "language":a.get("lang"),"country":a.get("source",{}).get("location",{}).get("country",{}).get("label"),
            "snippet": simple_summary(a.get("body"))
        })
    return rows

# ==== 이메일 ====
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

# ==== 실행 ====
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
    # 중복 제거
    all_df = dedupe_strict(all_df)

    # 신뢰/관련성 스코어 기반 선정
    sel_df = select_ranked(
        all_df.sort_values("published", ascending=False),
        CFG["commodities"],
        max_total=int(CFG["run"]["max_total"]),
        per_min=int(CFG["run"]["per_commodity_min"])
    )

    # ---- 한국어 번역 (제목/요약) ----
    titles_ko, snips_ko = [], []
    for _, r in sel_df.iterrows():
        t = r.get("title") or ""
        s = r.get("snippet") or ""
        titles_ko.append(translate_text_to_ko(t) if t else "")
        snips_ko.append(translate_text_to_ko(s) if s else "")
    sel_df["title_ko"] = titles_ko
    sel_df["snippet_ko"] = snips_ko

    # CSV 저장
    sel_df["domain"] = sel_df["url"].apply(norm_domain)
    sel_df = sel_df[["commodity","published","domain","source","language","country",
                     "title","title_ko","snippet","snippet_ko","url","score"]]
    stamp = datetime.now(tz=KST).strftime("%Y%m%d")
    csv_path = os.path.join(OUTDIR, f"commodities_{stamp}.csv")
    sel_df.to_csv(csv_path, index=False, encoding="utf-8-sig")

    # 메일 본문(번역본 우선 표기, 필요 시 원문 병기)
    lines = [f"# {CFG['email']['subject_prefix_ko']} {start.date()} ~ {end.date()}\n",
             "아래는 번역(한국어) 포함 상위 기사입니다. (최대 20건)\n"]
    for code, sub in sel_df.groupby("commodity"):
        lines.append(f"## {code}")
        for _, r in sub.sort_values(["score","published"], ascending=[False,False]).iterrows():
            d = str(r["published"])[:10]
            title_show = r["title_ko"] or r["title"]
            lines.append(f"- {title_show} — {d} · {r.get('domain','')} (score {r['score']:.1f})")
            lines.append(f"  링크: {r['url']}")
            if r.get("snippet_ko"): 
                lines.append(f"  요약(한글): {r['snippet_ko']}")
            elif r.get("snippet"):
                lines.append(f"  요약(원문): {r['snippet']}")
        lines.append("")
    body_md = "\n".join(lines)

    subject = f"{CFG['email']['subject_prefix_ko']} {stamp}"
    send_email_ko(subject, body_md, csv_path, CFG["email"]["to"])
    print("Saved CSV and sent email:", csv_path)

if __name__ == "__main__":
    run_once()
