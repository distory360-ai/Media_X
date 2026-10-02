from __future__ import annotations

import asyncio
import datetime as dt
import hashlib
import json
import logging
import os
import random
import re
import sys
import unicodedata
import urllib.parse
from collections import Counter, defaultdict
from typing import Optional

import asyncpg
import httpx
from dateutil import parser as date_parser
from textblob import TextBlob

try:
    import py3langid as langid
except ImportError:                                   # language detection is optional
    langid = None

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(name)s: %(message)s")
log = logging.getLogger("MediaPulseX")


def _env_int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, default))
    except ValueError:
        return default


API_KEY = os.environ.get("X_BEARER_TOKEN") or os.environ.get("TWITTERAPI_IO_KEY") or ""
RAW_DB_URL = os.environ.get("DATABASE_URL") or os.environ.get("DB_URL") or ""
SEARCH_URL = "https://api.twitterapi.io/twitter/tweet/advanced_search"

INITIAL_LOOKBACK_H = _env_int("X_INITIAL_LOOKBACK_HOURS", 24)
MAX_LOOKBACK_H = _env_int("X_MAX_LOOKBACK_HOURS", 72)
OVERLAP_MIN = 10                                       # re-read the last 10 minutes; upserts dedupe
MAX_PAGES = _env_int("X_MAX_PAGES_PER_QUERY", 15)
MAX_TWEETS = _env_int("X_MAX_TWEETS_PER_RUN", 6000)
CONCURRENCY = _env_int("X_CONCURRENCY", 3)
MAX_QUERY_CHARS = _env_int("X_MAX_QUERY_CHARS", 450)
INCLUDE_RETWEETS = os.environ.get("X_INCLUDE_RETWEETS", "0") == "1"
ONLY_CLIENTS = os.environ.get("X_ONLY_CLIENTS", "0") == "1"
STORE_RAW = os.environ.get("STORE_RAW", "0") == "1"
LEGACY_TABLE = os.environ.get("LEGACY_TABLE", "1") == "1"
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK_URL", "")
SENTIMENT_MODEL = os.environ.get("X_SENTIMENT_MODEL", "")
COST_PER_1K = 0.15
MAX_RETRIES = 5

# ─────────────────────────────────────────────────────────────────────────────
# BRAND REGISTRY
#   terms     words/phrases matched in tweet text (word boundaries; acronyms of ≤4 capitals are
#             matched case-sensitively so "KCB" does not match "kcb" inside other words)
#   handles   X usernames WITHOUT @ (max 15 characters — longer ones are not real accounts and
#             are dropped with a warning). Used for @mentions, replies and the brand's own posts.
#   hashtags  without #
#   context   optional: for ambiguous names, at least one of these words must also appear
#   client    True = paying client (gets alerts, negative watch, X_ONLY_CLIENTS mode)
# Handles marked "verify" are my best knowledge, not checked against X — confirm them once.
# Add brands without editing code via BRANDS_FILE (same shape, JSON) or EXTRA_BRANDS.
# ─────────────────────────────────────────────────────────────────────────────
BRANDS: dict[str, dict] = {
    # ── clients ──
    "Mastercard Foundation": {"terms": ["Mastercard Foundation", "MastercardFdn", "Mastercard Foundation Scholars"],
                              "handles": ["MastercardFdn"], "hashtags": ["MastercardFoundation"],  # verify
                              "country": "AF", "client": True},
    "Safaricom": {"terms": ["Safaricom", "M-Pesa", "MPesa", "M-PESA", "Fuliza", "Bonga points"],
                  "handles": ["SafaricomPLC", "Safaricom_Care"], "hashtags": ["Safaricom", "MPesa"],
                  "country": "KE", "client": True},
    "Equity Group": {"terms": ["Equity Bank", "Equity Group", "EquityBank", "Equitel", "Equity Afia"],
                     "handles": ["KeEquityBank"], "hashtags": ["EquityBank"],                      # verify
                     "country": "KE", "client": True},
    "KCB Group": {"terms": ["KCB", "KCB Group", "KCB Bank", "KCB M-Pesa"],
                  "handles": ["KCBGroup"], "hashtags": ["KCB"], "country": "KE", "client": True},
    "African Wildlife Foundation": {"terms": ["African Wildlife Foundation", "AWF"],
                                    "handles": ["AWF_Official"], "hashtags": [],                 # verify
                                    "context": ["wildlife", "conservation", "Africa", "elephant", "rhino",
                                                "foundation", "forest", "ranger"],
                                    "country": "AF", "client": True},
    "Science for Africa Foundation": {"terms": ["Science for Africa Foundation", "SFA Foundation"],
                                      "handles": [], "hashtags": [], "country": "AF", "client": True},
    # ── Kenya ──
    "Airtel Kenya": {"terms": ["Airtel Kenya", "Airtel Money"], "handles": ["AIRTEL_KE"], "hashtags": [],  # verify
                     "country": "KE"},
    "NCBA": {"terms": ["NCBA", "NCBA Bank", "M-Shwari", "Loop by NCBA"], "handles": ["NCBABankKenya"],
             "hashtags": [], "country": "KE"},
    "Co-op Bank": {"terms": ["Co-op Bank", "Co-operative Bank", "Coop Bank", "MCo-op Cash"],
                   "handles": ["Coopbankenya"], "hashtags": [], "country": "KE"},                  # verify
    "Kenya Power": {"terms": ["Kenya Power", "KPLC"], "handles": ["KenyaPower_Care", "KenyaPower"],
                    "hashtags": ["KenyaPower"], "context": ["Kenya Power", "KPLC", "blackout", "power",
                                                            "stima", "outage", "token"],
                    "country": "KE"},
    "EABL": {"terms": ["EABL", "East African Breweries", "Tusker"], "handles": ["EABL_PLC"],       # verify
             "hashtags": [], "country": "KE"},
    "Kenyatta National Hospital": {"terms": ["Kenyatta National Hospital", "KNH"], "handles": [],
                                   "hashtags": [], "context": ["hospital", "patient", "Kenyatta", "doctor",
                                                               "nurse", "ward", "KNH"], "country": "KE"},
    "M-KOPA": {"terms": ["M-KOPA", "MKOPA"], "handles": ["MKOPAKenya"], "hashtags": [], "country": "KE"},  # verify
    # ── Pan-African / Nigeria / South Africa / Ethiopia ──
    "MTN": {"terms": ["MTN", "MoMo", "MTN MoMo"], "handles": ["MTNGroup", "MTNNG"], "hashtags": ["MTN"],
            "country": "AF"},
    "Dangote": {"terms": ["Dangote", "Dangote Group", "Dangote Refinery", "Dangote Cement"],
                "handles": ["DangoteGroup"], "hashtags": ["Dangote"], "country": "NG"},
    "Absa": {"terms": ["Absa", "Absa Bank"], "handles": ["AbsaSouthAfrica", "AbsaKenya"],          # verify
             "hashtags": [], "country": "AF"},
    "Flutterwave": {"terms": ["Flutterwave"], "handles": ["theflutterwave"], "hashtags": [], "country": "NG"},
    "Paystack": {"terms": ["Paystack"], "handles": ["paystack"], "hashtags": [], "country": "NG"},
    "Moniepoint": {"terms": ["Moniepoint"], "handles": ["moniepointng"], "hashtags": [], "country": "NG"},  # verify
    "OPay": {"terms": ["OPay"], "handles": ["OPay_NG"], "hashtags": [], "country": "NG"},          # verify
    "Access Bank": {"terms": ["Access Bank"], "handles": ["myaccessbank"], "hashtags": [], "country": "NG"},
    "GTCO": {"terms": ["GTBank", "GTCO", "Guaranty Trust"], "handles": ["gtbank"], "hashtags": [], "country": "NG"},
    "Zenith Bank": {"terms": ["Zenith Bank"], "handles": ["ZenithBank"], "hashtags": [], "country": "NG"},
    "Ecobank": {"terms": ["Ecobank"], "handles": ["gotoecobank"], "hashtags": [], "country": "AF"},  # verify
    "Jumia": {"terms": ["Jumia"], "handles": ["JumiaGroup"], "hashtags": [], "country": "AF"},
    "Ethio Telecom": {"terms": ["Ethio Telecom", "ethiotelecom", "telebirr", "ኢትዮ ቴሌኮም", "ቴሌብር"],
                      "handles": ["ethiotelecom"], "hashtags": ["telebirr"], "country": "ET"},
}

# Topic listening (not tied to one brand). Global hashtags like #AI are scoped to Africa,
# otherwise they flood the run with tweets from everywhere.
TOPIC_QUERIES: dict[str, str] = {
    "africa_tech": "#TechInAfrica OR #AfricaTech OR #NairobiTech OR #LagosTech OR #CapeTownTech OR #AfricanStartups",
    "africa_ai": "(#AI OR \"artificial intelligence\") (Kenya OR Nigeria OR Africa OR Nairobi OR Lagos OR Rwanda OR Ghana)",
    "amr_africa": "(#AMR OR \"antimicrobial resistance\") (Africa OR Kenya OR Nigeria OR Uganda OR Tanzania)",
}

# ─────────────────────────────────────────────────────────────────────────────
# THEMES AND RISK FLAGS (English + Swahili/Sheng + a little Pidgin; whole-word match)
# ─────────────────────────────────────────────────────────────────────────────
THEMES: dict[str, list[str]] = {
    "customer_complaint": ["customer care", "customer service", "no response", "not answering", "complaint",
                           "worst", "terrible", "poor service", "disappointed", "frustrated", "huduma mbovu",
                           "hamjibu", "mnaboeka", "nimechoka", "hakuna jibu", "una sabi"],
    "service_outage": ["down", "outage", "not working", "failed", "failing", "offline", "network issues",
                       "hakuna network", "haifanyi kazi", "imekataa", "blackout", "no signal", "app crashing",
                       "crashing", "system down"],
    "fraud_scam": ["scam", "fraud", "fraudster", "conned", "stolen", "hacked", "phishing", "wizi", "nimeibiwa",
                   "matapeli", "tapeli", "419", "unauthorized"],
    "pricing_fees": ["charges", "fees", "expensive", "price hike", "tariff", "interest rate", "bei", "ghali",
                     "overcharged", "hidden charges"],
    "loans_credit": ["loan", "mkopo", "credit limit", "overdraft", "fuliza", "crb", "default", "repayment"],
    "product_launch": ["launch", "launched", "unveil", "unveiled", "introducing", "new product", "rollout",
                       "now available", "imezinduliwa"],
    "csr_impact": ["scholarship", "scholars", "foundation", "donation", "donated", "community", "impact",
                   "sustainability", "conservation", "youth", "women", "empower", "jamii"],
    "leadership_governance": ["ceo", "board", "chairman", "resign", "resigned", "appointed", "appointment",
                              "managing director", "agm", "governance"],
    "regulatory_legal": ["court", "lawsuit", "regulator", "fine", "fined", "cbk", "ca kenya", "cbn",
                         "competition authority", "license", "licence", "ban", "banned", "tax", "kra"],
    "financial_results": ["profit", "revenue", "results", "earnings", "dividend", "half year", "full year",
                          "share price", "nse", "faida"],
    "jobs_careers": ["hiring", "vacancy", "vacancies", "internship", "job opening", "kazi", "graduate trainee"],
}
RISK_FLAGS: dict[str, list[str]] = {
    "boycott": ["boycott", "#boycott", "cancel", "susia"],
    "legal_threat": ["sue", "suing", "lawyer", "court", "demand letter"],
    "safety": ["death", "died", "injured", "poison", "contaminated", "fire", "accident"],
    "data_privacy": ["data breach", "leak", "leaked", "privacy", "my data", "data protection"],
    "viral_complaint": ["retweet so", "rt so", "until they respond", "trending", "everyone should know"],
}

# Tiny Swahili/Sheng polarity lexicon so the most common Kenyan complaints are not left unscored.
SW_POS = {"asante", "poa", "safi", "bora", "nzuri", "furaha", "shukran", "fiti", "hongera", "mzuri", "vizuri"}
SW_NEG = {"mbovu", "wizi", "mbaya", "wezi", "tapeli", "matapeli", "nimeibiwa", "hasira", "ovyo", "ghali",
          "nimechoka", "uongo", "hamjibu", "shida", "taabu", "kero", "aibu"}


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────
def now_utc() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def norm(text: str) -> str:
    return unicodedata.normalize("NFKC", text or "")


def is_nonlatin(s: str) -> bool:
    return any(ord(c) > 0x024F and unicodedata.category(c).startswith("L") for c in s)


def compile_term(term: str) -> re.Pattern:
    """Word-boundary pattern. Short all-caps acronyms (KCB, MTN, AWF) are case-sensitive;
    non-Latin scripts (Ge'ez, Arabic) are substring-matched because \\b does not apply."""
    t = norm(term).strip()
    esc = re.escape(t).replace(r"\-", r"[-\s]?").replace(r"\ ", r"\s+")
    if is_nonlatin(t):
        return re.compile(esc)
    flags = 0 if (t.isupper() and len(t) <= 4) else re.IGNORECASE
    return re.compile(rf"(?<![\w@#]){esc}(?!\w)", flags)


def compile_words(words: list[str]) -> re.Pattern:
    parts = sorted({re.escape(w.lower()).replace(r"\ ", r"\s+") for w in words}, key=len, reverse=True)
    return re.compile(rf"(?<![\w]){'|'.join(parts)}(?!\w)", re.IGNORECASE)


THEME_PATTERNS = {k: compile_words(v) for k, v in THEMES.items()}
RISK_PATTERNS = {k: compile_words(v) for k, v in RISK_FLAGS.items()}
HANDLE_RE = re.compile(r"^[A-Za-z0-9_]{1,15}$")


def load_brands() -> dict[str, dict]:
    brands = {k: dict(v) for k, v in BRANDS.items()}
    path = os.environ.get("BRANDS_FILE")
    if path and os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            extra = json.load(fh)
        brands.update(extra)
        log.info(f"Loaded {len(extra)} brand(s) from {path}")
    for chunk in filter(None, (os.environ.get("EXTRA_BRANDS") or "").split(";")):
        name, _, terms = chunk.partition(":")
        if name.strip():
            brands[name.strip()] = {"terms": [t.strip() for t in (terms or name).split("|") if t.strip()],
                                    "handles": [], "hashtags": []}
    clean = {}
    for name, b in brands.items():
        handles = []
        for h in b.get("handles", []):
            h = h.lstrip("@")
            if HANDLE_RE.match(h):
                handles.append(h)
            else:
                log.warning(f"[{name}] dropping invalid X handle @{h} (X handles are max 15 letters/digits/_)")
        b["handles"] = handles
        b["hashtags"] = [t.lstrip("#") for t in b.get("hashtags", [])]
        b.setdefault("terms", [name])
        if ONLY_CLIENTS and not b.get("client"):
            continue
        clean[name] = b
    return clean


class BrandMatcher:
    def __init__(self, brands: dict[str, dict]):
        self.brands = brands
        self.term_pats = {n: [(t, compile_term(t)) for t in b["terms"]] for n, b in brands.items()}
        self.context = {n: compile_words(b["context"]) for n, b in brands.items() if b.get("context")}
        self.handle_to_brand = {h.lower(): n for n, b in brands.items() for h in b["handles"]}
        self.tag_to_brand = {t.lower(): n for n, b in brands.items() for t in b["hashtags"]}

    def match(self, tw: dict) -> dict[str, dict]:
        """Returns {brand: {"terms": [...], "type": text|mention|hashtag|reply|owned, "owned": bool}}."""
        text = norm(tw["text"])
        found: dict[str, dict] = {}

        def add(brand, term, mtype):
            e = found.setdefault(brand, {"terms": [], "type": mtype, "owned": False})
            if term not in e["terms"]:
                e["terms"].append(term)

        author = (tw["author_handle"] or "").lower()
        if author in self.handle_to_brand:
            b = self.handle_to_brand[author]
            add(b, "@" + tw["author_handle"], "owned")
            found[b]["owned"] = True
        for h in tw["mentions"]:
            if h.lower() in self.handle_to_brand:
                add(self.handle_to_brand[h.lower()], "@" + h, "mention")
        for t in tw["hashtags"]:
            if t.lower() in self.tag_to_brand:
                add(self.tag_to_brand[t.lower()], "#" + t, "hashtag")
        for name, pats in self.term_pats.items():
            hits = [t for t, p in pats if p.search(text)]
            if not hits:
                continue
            if name in self.context and name not in found and not self.context[name].search(text):
                continue                                   # ambiguous word without supporting context
            for t in hits:
                add(name, t, found.get(name, {}).get("type", "text"))
        reply_to = (tw.get("in_reply_to_handle") or "").lower()
        if reply_to in self.handle_to_brand and self.handle_to_brand[reply_to] not in found:
            add(self.handle_to_brand[reply_to], "reply→@" + tw["in_reply_to_handle"], "reply")
        return found


# ─────────────────────────────────────────────────────────────────────────────
# Language, sentiment, themes
# ─────────────────────────────────────────────────────────────────────────────
_hf_pipe = None
_hf_tried = False


def detect_language(text: str, api_lang: Optional[str]) -> str:
    if api_lang and api_lang not in ("und", "qme", "qht", "zxx", "art"):
        return api_lang
    clean = re.sub(r"https?://\S+|[@#]\w+", " ", text)
    if langid is None or len(clean.strip()) < 12:
        return api_lang or "und"
    return langid.classify(clean)[0]


def sentiment(text: str, lang: str) -> tuple[Optional[str], Optional[float]]:
    """Scores only where a method fits the language. Unsupported → (None, None), shown as 'Not scored',
    never faked as Neutral."""
    global _hf_pipe, _hf_tried
    clean = re.sub(r"https?://\S+|@\w+", " ", text)
    if SENTIMENT_MODEL and not _hf_tried:
        _hf_tried = True
        try:
            from transformers import pipeline
            _hf_pipe = pipeline("sentiment-analysis", model=SENTIMENT_MODEL, truncation=True)
            log.info(f"Sentiment model loaded: {SENTIMENT_MODEL}")
        except Exception as exc:
            log.warning(f"Could not load {SENTIMENT_MODEL} ({exc}); falling back to TextBlob/lexicon")
    if _hf_pipe is not None:
        try:
            r = _hf_pipe(clean[:512])[0]
            lab = r["label"].lower()
            label = "Positive" if "pos" in lab else "Negative" if "neg" in lab else "Neutral"
            score = r["score"] if label == "Positive" else -r["score"] if label == "Negative" else 0.0
            return label, round(float(score), 4)
        except Exception:
            pass
    if lang == "en":
        s = TextBlob(clean).sentiment.polarity
        return ("Positive" if s > 0.05 else "Negative" if s < -0.05 else "Neutral"), round(s, 4)
    if lang == "sw":
        words = set(re.findall(r"[a-z]+", clean.lower()))
        p, n = len(words & SW_POS), len(words & SW_NEG)
        if p == n == 0:
            return None, None
        s = (p - n) / (p + n)
        return ("Positive" if s > 0 else "Negative" if s < 0 else "Neutral"), round(s, 4)
    return None, None


def labels(text: str, patterns: dict[str, re.Pattern]) -> list[str]:
    return [k for k, p in patterns.items() if p.search(text)]


# ─────────────────────────────────────────────────────────────────────────────
# Query building
# ─────────────────────────────────────────────────────────────────────────────
def q_atom(term: str) -> str:
    return f'"{term}"' if (" " in term or "-" in term) else term


def build_queries(brands: dict[str, dict]) -> list[dict]:
    """Packs brand atoms into OR-queries no longer than MAX_QUERY_CHARS. Each query remembers which
    brands it covers (for logs) and gets a stable key (for since_time state)."""
    atoms: list[tuple[str, str]] = []
    for name, b in brands.items():
        seen = set()
        for a in ([q_atom(t) for t in b["terms"]] + [f"@{h}" for h in b["handles"]] +
                  [f"from:{h}" for h in b["handles"]] + [f"#{t}" for t in b["hashtags"]]):
            if a.lower() not in seen:
                seen.add(a.lower())
                atoms.append((name, a))
    suffix_len = 60                                     # room for -filter:retweets since_time:…
    queries, cur, cur_brands = [], [], set()
    for name, a in atoms:
        if cur and len(" OR ".join(cur + [a])) + suffix_len > MAX_QUERY_CHARS:
            queries.append({"kind": "brand", "body": " OR ".join(cur), "brands": sorted(cur_brands)})
            cur, cur_brands = [], set()
        cur.append(a)
        cur_brands.add(name)
    if cur:
        queries.append({"kind": "brand", "body": " OR ".join(cur), "brands": sorted(cur_brands)})
    for topic, body in TOPIC_QUERIES.items():
        queries.append({"kind": "topic", "body": body, "brands": [], "topic": topic})
    for q in queries:
        q["key"] = hashlib.sha1(q["body"].encode()).hexdigest()[:16]
    return queries


def full_query(q: dict, since: dt.datetime) -> str:
    rt = "" if INCLUDE_RETWEETS else " -filter:retweets"
    return f"({q['body']}){rt} since_time:{int(since.timestamp())}"


# ─────────────────────────────────────────────────────────────────────────────
# Tweet parsing
# ─────────────────────────────────────────────────────────────────────────────
def parse_ts(raw) -> Optional[dt.datetime]:
    if raw in (None, ""):
        return None
    try:
        if isinstance(raw, (int, float)) or str(raw).replace(".", "", 1).isdigit():
            v = float(raw)
            return dt.datetime.fromtimestamp(v / 1000 if v > 1e11 else v, dt.timezone.utc)
        d = date_parser.parse(str(raw))
        return d if d.tzinfo else d.replace(tzinfo=dt.timezone.utc)
    except Exception:
        return None


def _int(v) -> int:
    try:
        return int(v or 0)
    except (TypeError, ValueError):
        return 0


def parse_tweet(t: dict) -> Optional[dict]:
    tid = t.get("id") or t.get("id_str")
    if not tid:
        return None
    a = t.get("author") or t.get("user") or {}
    ent = t.get("entities") or {}
    text = t.get("text") or t.get("full_text") or ""
    hashtags = [h.get("text") or h.get("tag") for h in ent.get("hashtags", []) if isinstance(h, dict)]
    hashtags = [h for h in hashtags if h] or re.findall(r"#(\w+)", text)
    mentions = [m.get("screen_name") or m.get("username") for m in ent.get("user_mentions", []) if isinstance(m, dict)]
    mentions = [m for m in mentions if m] or re.findall(r"@(\w{1,15})", text)
    urls = [u.get("expanded_url") or u.get("url") for u in ent.get("urls", []) if isinstance(u, dict)]
    quoted = t.get("quoted_tweet") or {}
    likes, rts, replies = _int(t.get("likeCount")), _int(t.get("retweetCount")), _int(t.get("replyCount"))
    quotes, views, bookmarks = _int(t.get("quoteCount")), _int(t.get("viewCount")), _int(t.get("bookmarkCount"))
    handle = a.get("userName") or a.get("screen_name") or ""
    return {
        "tweet_id": str(tid),
        "url": t.get("url") or (f"https://x.com/{handle}/status/{tid}" if handle else None),
        "text": text,
        "api_lang": t.get("lang"),
        "created_at": parse_ts(t.get("createdAt") or t.get("created_at")),
        "conversation_id": str(t.get("conversationId") or "") or None,
        "in_reply_to_id": str(t.get("inReplyToId") or "") or None,
        "in_reply_to_handle": t.get("inReplyToUsername") or "",
        "is_reply": bool(t.get("isReply") or t.get("inReplyToId")),
        "is_quote": bool(quoted),
        "quoted_tweet_id": str(quoted.get("id")) if quoted.get("id") else None,
        "is_retweet": bool(t.get("retweeted_tweet")),
        "hashtags": list(dict.fromkeys(hashtags)),
        "mentions": list(dict.fromkeys(mentions)),
        "urls": [u for u in urls if u],
        "likes": likes, "retweets": rts, "replies": replies, "quotes": quotes,
        "views": views, "bookmarks": bookmarks,
        "engagement": likes + rts + replies + quotes,
        "author_id": str(a.get("id") or handle or ""),
        "author_handle": handle,
        "author_name": a.get("name") or "",
        "followers": _int(a.get("followers") or a.get("followersCount") or a.get("followers_count")),
        "following": _int(a.get("following") or a.get("friendsCount") or a.get("friends_count")),
        "verified": bool(a.get("isBlueVerified") or a.get("isVerified") or a.get("verified")),
        "location": a.get("location") or "",
        "description": a.get("description") or "",
        "account_created": parse_ts(a.get("createdAt") or a.get("created_at")),
        "statuses": _int(a.get("statusesCount") or a.get("statuses_count")),
        "raw": t if STORE_RAW else None,
    }


def enrich(tw: dict, matcher: BrandMatcher, topic: Optional[str]) -> dict:
    tw["lang"] = detect_language(tw["text"], tw["api_lang"])
    tw["sentiment"], tw["sentiment_score"] = sentiment(tw["text"], tw["lang"])
    tw["themes"] = labels(tw["text"], THEME_PATTERNS)
    tw["risk_flags"] = labels(tw["text"], RISK_PATTERNS)
    tw["brands"] = matcher.match(tw)
    tw["topics"] = [topic] if topic else []
    return tw


# ─────────────────────────────────────────────────────────────────────────────
# Database
# ─────────────────────────────────────────────────────────────────────────────
SCHEMA_SQL = """
CREATE SCHEMA IF NOT EXISTS x_intel;

CREATE TABLE IF NOT EXISTS x_intel.authors (
    author_id       TEXT PRIMARY KEY,
    handle          TEXT,
    name            TEXT,
    followers       BIGINT,
    following       BIGINT,
    verified        BOOLEAN,
    location        TEXT,
    description     TEXT,
    account_created TIMESTAMPTZ,
    statuses        BIGINT,
    first_seen      TIMESTAMPTZ DEFAULT now(),
    last_seen       TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS x_intel.tweets (
    tweet_id         TEXT PRIMARY KEY,
    url              TEXT,
    text             TEXT,
    lang             TEXT,
    created_at       TIMESTAMPTZ,
    author_id        TEXT REFERENCES x_intel.authors(author_id),
    author_handle    TEXT,
    author_followers BIGINT,
    conversation_id  TEXT,
    in_reply_to_id   TEXT,
    is_reply         BOOLEAN,
    is_quote         BOOLEAN,
    quoted_tweet_id  TEXT,
    hashtags         TEXT[],
    mentions         TEXT[],
    urls             TEXT[],
    likes            BIGINT, retweets BIGINT, replies BIGINT, quotes BIGINT,
    views            BIGINT, bookmarks BIGINT, engagement BIGINT,
    sentiment        TEXT,            -- NULL = no model for this language ("Not scored")
    sentiment_score  REAL,
    themes           TEXT[],
    risk_flags       TEXT[],
    topics           TEXT[],
    raw              JSONB,
    first_seen       TIMESTAMPTZ DEFAULT now(),
    last_seen        TIMESTAMPTZ DEFAULT now()
);
CREATE INDEX IF NOT EXISTS tweets_created_idx ON x_intel.tweets (created_at DESC);
CREATE INDEX IF NOT EXISTS tweets_author_idx ON x_intel.tweets (author_id);
CREATE INDEX IF NOT EXISTS tweets_conv_idx ON x_intel.tweets (conversation_id);

CREATE TABLE IF NOT EXISTS x_intel.tweet_metrics (
    tweet_id    TEXT REFERENCES x_intel.tweets(tweet_id) ON DELETE CASCADE,
    captured_at TIMESTAMPTZ DEFAULT now(),
    likes BIGINT, retweets BIGINT, replies BIGINT, quotes BIGINT, views BIGINT, bookmarks BIGINT,
    PRIMARY KEY (tweet_id, captured_at)
);

CREATE TABLE IF NOT EXISTS x_intel.brand_mentions (
    tweet_id      TEXT REFERENCES x_intel.tweets(tweet_id) ON DELETE CASCADE,
    brand         TEXT,
    matched_terms TEXT[],
    match_type    TEXT,       -- text | mention | hashtag | reply | owned
    is_owned      BOOLEAN,    -- the brand's own account posted it
    is_client     BOOLEAN,
    country       TEXT,
    PRIMARY KEY (tweet_id, brand)
);
CREATE INDEX IF NOT EXISTS bm_brand_idx ON x_intel.brand_mentions (brand);

CREATE TABLE IF NOT EXISTS x_intel.query_state (
    query_key       TEXT PRIMARY KEY,
    query_body      TEXT,
    last_tweet_time TIMESTAMPTZ,
    last_run_at     TIMESTAMPTZ,
    last_count      INT
);

CREATE TABLE IF NOT EXISTS x_intel.runs (
    run_id         SERIAL PRIMARY KEY,
    started_at     TIMESTAMPTZ DEFAULT now(),
    finished_at    TIMESTAMPTZ,
    status         TEXT,
    queries        INT,
    pages          INT,
    tweets_fetched INT,
    tweets_stored  INT,
    dropped_no_brand INT,
    est_cost_usd   NUMERIC(10,4),
    note           TEXT
);

-- Legacy table used by the existing dashboard (created only if missing).
CREATE TABLE IF NOT EXISTS public.social_media_feeds (
    tweet_id        TEXT PRIMARY KEY,
    content         TEXT,
    author          TEXT,
    created_at      TIMESTAMP,
    sentiment       TEXT,
    sentiment_score REAL,
    follower_count  BIGINT,
    user_location   TEXT
);
"""

VIEWS_SQL = """
-- Earned mentions (excludes the brand's own posts) per brand per day
CREATE OR REPLACE VIEW x_intel.daily_volume AS
SELECT m.brand, date_trunc('day', t.created_at)::date AS day,
       COUNT(*)                                            AS mentions,
       COUNT(DISTINCT t.author_id)                         AS unique_authors,
       SUM(COALESCE(t.author_followers, 0))                AS potential_reach,
       SUM(COALESCE(t.engagement, 0))                      AS engagement,
       SUM(COALESCE(t.views, 0))                           AS views,
       COUNT(*) FILTER (WHERE t.sentiment = 'Positive')    AS positive,
       COUNT(*) FILTER (WHERE t.sentiment = 'Negative')    AS negative,
       COUNT(*) FILTER (WHERE t.sentiment = 'Neutral')     AS neutral,
       COUNT(*) FILTER (WHERE t.sentiment IS NULL)         AS not_scored,
       ROUND(100.0 * COUNT(*) FILTER (WHERE t.sentiment = 'Negative')
             / NULLIF(COUNT(*) FILTER (WHERE t.sentiment IS NOT NULL), 0), 1) AS negative_pct
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE NOT m.is_owned
GROUP BY 1, 2;

CREATE OR REPLACE VIEW x_intel.share_of_voice_7d AS
SELECT m.brand, COUNT(*) AS mentions,
       SUM(COALESCE(t.author_followers, 0)) AS potential_reach,
       ROUND(100.0 * COUNT(*) / NULLIF(SUM(COUNT(*)) OVER (), 0), 2) AS share_pct
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE NOT m.is_owned AND t.created_at >= now() - interval '7 days'
GROUP BY 1;

-- Same, but only within a country (KE, NG, ET, ...) — compare a client with local peers
CREATE OR REPLACE VIEW x_intel.share_of_voice_7d_by_country AS
SELECT m.country, m.brand, COUNT(*) AS mentions,
       ROUND(100.0 * COUNT(*) / NULLIF(SUM(COUNT(*)) OVER (PARTITION BY m.country), 0), 2) AS share_pct
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE NOT m.is_owned AND t.created_at >= now() - interval '7 days'
GROUP BY 1, 2;

-- Today's volume vs the previous 14 days (z-score)
CREATE OR REPLACE VIEW x_intel.spikes AS
WITH d AS (SELECT brand, day, mentions FROM x_intel.daily_volume WHERE day >= current_date - 15),
base AS (
  SELECT brand, AVG(mentions) AS avg_m, COALESCE(STDDEV_SAMP(mentions), 0) AS sd_m, COUNT(*) AS days
  FROM d WHERE day < current_date GROUP BY brand)
SELECT d.brand, d.day, d.mentions, ROUND(b.avg_m, 1) AS baseline_avg,
       ROUND((d.mentions - b.avg_m) / NULLIF(GREATEST(b.sd_m, 1), 0), 2) AS z_score
FROM d JOIN base b USING (brand)
WHERE d.day = current_date AND b.days >= 3;

CREATE OR REPLACE VIEW x_intel.top_authors_30d AS
SELECT m.brand, a.handle, a.name, a.followers, a.verified, a.location,
       COUNT(*) AS tweets, SUM(t.engagement) AS engagement,
       COUNT(*) FILTER (WHERE t.sentiment = 'Negative') AS negative_tweets
FROM x_intel.brand_mentions m
JOIN x_intel.tweets t USING (tweet_id)
JOIN x_intel.authors a ON a.author_id = t.author_id
WHERE NOT m.is_owned AND t.created_at >= now() - interval '30 days'
GROUP BY 1, 2, 3, 4, 5, 6;

-- Negative posts about clients in the last 48h, highest reach first
CREATE OR REPLACE VIEW x_intel.negative_watch AS
SELECT m.brand, t.created_at, t.author_handle, t.author_followers, t.engagement, t.views,
       t.themes, t.risk_flags, t.text, t.url
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE m.is_client AND NOT m.is_owned AND t.sentiment = 'Negative'
  AND t.created_at >= now() - interval '48 hours'
ORDER BY COALESCE(t.author_followers, 0) + 10 * COALESCE(t.engagement, 0) DESC;

-- Fastest-growing posts: engagement per hour since posting
CREATE OR REPLACE VIEW x_intel.viral_48h AS
SELECT m.brand, t.tweet_id, t.author_handle, t.author_followers, t.engagement, t.views, t.sentiment,
       ROUND(t.engagement / GREATEST(EXTRACT(EPOCH FROM now() - t.created_at) / 3600, 1)::numeric, 1) AS eng_per_hour,
       t.text, t.url
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE t.created_at >= now() - interval '48 hours'
ORDER BY eng_per_hour DESC;

CREATE OR REPLACE VIEW x_intel.themes_7d AS
SELECT m.brand, th AS theme, COUNT(*) AS tweets,
       COUNT(*) FILTER (WHERE t.sentiment = 'Negative') AS negative
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id), unnest(t.themes) th
WHERE NOT m.is_owned AND t.created_at >= now() - interval '7 days'
GROUP BY 1, 2;

CREATE OR REPLACE VIEW x_intel.hashtags_7d AS
SELECT m.brand, lower(h) AS hashtag, COUNT(*) AS tweets
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id), unnest(t.hashtags) h
WHERE t.created_at >= now() - interval '7 days'
GROUP BY 1, 2;

CREATE OR REPLACE VIEW x_intel.language_mix_30d AS
SELECT m.brand, t.lang, COUNT(*) AS tweets
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE t.created_at >= now() - interval '30 days'
GROUP BY 1, 2;

-- The brand's own posts: how its content performs
CREATE OR REPLACE VIEW x_intel.owned_performance_30d AS
SELECT m.brand, COUNT(*) AS posts, ROUND(AVG(t.engagement), 1) AS avg_engagement,
       ROUND(AVG(t.views), 0) AS avg_views, MAX(t.engagement) AS best_engagement
FROM x_intel.brand_mentions m JOIN x_intel.tweets t USING (tweet_id)
WHERE m.is_owned AND t.created_at >= now() - interval '30 days'
GROUP BY 1;

-- Identical text from many accounts = coordinated / copy-paste campaigns
CREATE OR REPLACE VIEW x_intel.copy_paste_7d AS
SELECT md5(lower(regexp_replace(t.text, '(https?://\\S+|@\\w+|\\s+)', ' ', 'g'))) AS text_hash,
       MIN(t.text) AS sample_text, COUNT(DISTINCT t.author_id) AS accounts, COUNT(*) AS tweets,
       array_agg(DISTINCT m.brand) AS brands
FROM x_intel.tweets t JOIN x_intel.brand_mentions m USING (tweet_id)
WHERE t.created_at >= now() - interval '7 days' AND length(t.text) > 40
GROUP BY 1
HAVING COUNT(DISTINCT t.author_id) >= 5;
"""


def clean_db_url(raw: str) -> str:
    """URL-encodes the password once (without double-encoding one that already is) and drops
    channel_binding, which asyncpg does not understand."""
    p = urllib.parse.urlparse(raw)
    netloc = p.netloc
    if p.password:
        pw = urllib.parse.quote(urllib.parse.unquote(p.password), safe="")
        netloc = f"{p.username}:{pw}@{p.hostname}" + (f":{p.port}" if p.port else "")
    q = [(k, v) for k, v in urllib.parse.parse_qsl(p.query) if k != "channel_binding"]
    return p._replace(netloc=netloc, query=urllib.parse.urlencode(q)).geturl()


async def ensure_schema(conn: asyncpg.Connection):
    await conn.execute(SCHEMA_SQL)
    await conn.execute(VIEWS_SQL)


async def load_state(conn) -> dict[str, dt.datetime]:
    rows = await conn.fetch("SELECT query_key, last_tweet_time FROM x_intel.query_state")
    return {r["query_key"]: r["last_tweet_time"] for r in rows if r["last_tweet_time"]}


async def save_tweets(pool: asyncpg.Pool, tweets: list[dict], brands: dict[str, dict]):
    if not tweets:
        return
    authors = {}
    for t in tweets:
        if t["author_id"]:
            authors[t["author_id"]] = t
    async with pool.acquire() as conn, conn.transaction():
        await conn.executemany("""
            INSERT INTO x_intel.authors (author_id, handle, name, followers, following, verified, location,
                                         description, account_created, statuses)
            VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10)
            ON CONFLICT (author_id) DO UPDATE SET
                handle = EXCLUDED.handle, name = EXCLUDED.name, followers = EXCLUDED.followers,
                following = EXCLUDED.following, verified = EXCLUDED.verified, location = EXCLUDED.location,
                description = EXCLUDED.description, statuses = EXCLUDED.statuses, last_seen = now()
        """, [(a["author_id"], a["author_handle"], a["author_name"], a["followers"], a["following"],
               a["verified"], a["location"], a["description"], a["account_created"], a["statuses"])
              for a in authors.values()])
        await conn.executemany("""
            INSERT INTO x_intel.tweets (tweet_id, url, text, lang, created_at, author_id, author_handle,
                author_followers, conversation_id, in_reply_to_id, is_reply, is_quote, quoted_tweet_id,
                hashtags, mentions, urls, likes, retweets, replies, quotes, views, bookmarks, engagement,
                sentiment, sentiment_score, themes, risk_flags, topics, raw)
            VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12,$13,$14,$15,$16,$17,$18,$19,$20,$21,$22,$23,
                    $24,$25,$26,$27,$28,$29::jsonb)
            ON CONFLICT (tweet_id) DO UPDATE SET
                likes = EXCLUDED.likes, retweets = EXCLUDED.retweets, replies = EXCLUDED.replies,
                quotes = EXCLUDED.quotes, views = EXCLUDED.views, bookmarks = EXCLUDED.bookmarks,
                engagement = EXCLUDED.engagement, author_followers = EXCLUDED.author_followers,
                topics = (SELECT array_agg(DISTINCT x) FROM unnest(x_intel.tweets.topics || EXCLUDED.topics) x),
                last_seen = now()
        """, [(t["tweet_id"], t["url"], t["text"], t["lang"], t["created_at"], t["author_id"] or None,
               t["author_handle"], t["followers"], t["conversation_id"], t["in_reply_to_id"], t["is_reply"],
               t["is_quote"], t["quoted_tweet_id"], t["hashtags"], t["mentions"], t["urls"], t["likes"],
               t["retweets"], t["replies"], t["quotes"], t["views"], t["bookmarks"], t["engagement"],
               t["sentiment"], t["sentiment_score"], t["themes"], t["risk_flags"], t["topics"],
               json.dumps(t["raw"]) if t["raw"] is not None else None) for t in tweets])
        await conn.executemany("""
            INSERT INTO x_intel.tweet_metrics (tweet_id, likes, retweets, replies, quotes, views, bookmarks)
            VALUES ($1,$2,$3,$4,$5,$6,$7) ON CONFLICT DO NOTHING
        """, [(t["tweet_id"], t["likes"], t["retweets"], t["replies"], t["quotes"], t["views"], t["bookmarks"])
              for t in tweets])
        bm = [(t["tweet_id"], b, m["terms"], m["type"], m["owned"], bool(brands.get(b, {}).get("client")),
               brands.get(b, {}).get("country"))
              for t in tweets for b, m in t["brands"].items()]
        await conn.executemany("""
            INSERT INTO x_intel.brand_mentions (tweet_id, brand, matched_terms, match_type, is_owned, is_client, country)
            VALUES ($1,$2,$3,$4,$5,$6,$7)
            ON CONFLICT (tweet_id, brand) DO UPDATE SET matched_terms = EXCLUDED.matched_terms,
                match_type = EXCLUDED.match_type, is_owned = EXCLUDED.is_owned, is_client = EXCLUDED.is_client
        """, bm)
        if LEGACY_TABLE:
            await conn.executemany("""
                INSERT INTO social_media_feeds (tweet_id, content, author, created_at, sentiment,
                                                sentiment_score, follower_count, user_location)
                VALUES ($1,$2,$3,$4,$5,$6,$7,$8)
                ON CONFLICT (tweet_id) DO UPDATE SET follower_count = EXCLUDED.follower_count
            """, [(t["tweet_id"], t["text"], t["author_id"] or t["author_handle"],
                   t["created_at"].astimezone(dt.timezone.utc).replace(tzinfo=None) if t["created_at"] else None,
                   t["sentiment"] or "Not scored", t["sentiment_score"], t["followers"], t["location"] or "Unknown")
                  for t in tweets])


# ─────────────────────────────────────────────────────────────────────────────
# Collector
# ─────────────────────────────────────────────────────────────────────────────
class FatalAPIError(Exception):
    pass


class XCollector:
    def __init__(self, api_key: str, pool: asyncpg.Pool, brands: dict[str, dict],
                 http: Optional[httpx.AsyncClient] = None):
        self.api_key = api_key
        self.pool = pool
        self.brands = brands
        self.matcher = BrandMatcher(brands)
        self.http = http or httpx.AsyncClient(timeout=30)
        self.sem = asyncio.Semaphore(CONCURRENCY)
        self.stats = Counter()
        self.fatal: Optional[str] = None
        self.seen_ids: set[str] = set()

    async def fetch_page(self, params: dict) -> Optional[dict]:
        for attempt in range(MAX_RETRIES + 1):
            if self.fatal:
                return None
            try:
                r = await self.http.get(SEARCH_URL, headers={"X-API-Key": self.api_key}, params=params)
            except httpx.RequestError as exc:
                wait = 2 ** attempt + random.random()
                log.warning(f"Network error ({exc!r}); retry in {wait:.1f}s")
                await asyncio.sleep(wait)
                continue
            if r.status_code == 200:
                return r.json()
            if r.status_code in (401, 402, 403):
                # bad key / out of credits / forbidden — retrying only burns time
                self.fatal = f"HTTP {r.status_code}: {r.text[:200]}"
                raise FatalAPIError(self.fatal)
            if r.status_code == 429 or r.status_code >= 500:
                retry_after = r.headers.get("Retry-After")
                wait = float(retry_after) if retry_after and retry_after.isdigit() else 2 ** attempt + random.random()
                log.warning(f"HTTP {r.status_code}; retry in {wait:.1f}s ({attempt + 1}/{MAX_RETRIES})")
                await asyncio.sleep(min(wait, 60))
                continue
            log.error(f"HTTP {r.status_code} for query {params.get('query', '')[:80]}…: {r.text[:200]}")
            return None
        return None

    async def run_query(self, q: dict, since: dt.datetime) -> Optional[dt.datetime]:
        """Pages one query until: no next page, page cap, run-wide tweet cap, or tweets older than since.
        Returns the newest tweet time seen (for since_time state)."""
        async with self.sem:
            query = full_query(q, since)
            cursor, pages, newest, kept = "", 0, None, []
            seen_cursors = set()
            while pages < MAX_PAGES and self.stats["fetched"] < MAX_TWEETS and not self.fatal:
                params = {"query": query, "queryType": "Latest"}
                if cursor:
                    params["cursor"] = cursor
                data = await self.fetch_page(params)
                pages += 1
                self.stats["pages"] += 1
                if not data:
                    break
                raw = data.get("tweets") or []
                self.stats["fetched"] += len(raw)
                oldest_on_page = None
                for t in raw:
                    tw = parse_tweet(t)
                    if not tw:
                        continue
                    if tw["created_at"]:
                        newest = max(newest, tw["created_at"]) if newest else tw["created_at"]
                        oldest_on_page = min(oldest_on_page, tw["created_at"]) if oldest_on_page else tw["created_at"]
                    if tw["is_retweet"] and not INCLUDE_RETWEETS:
                        continue
                    if tw["tweet_id"] in self.seen_ids and q["kind"] == "brand":
                        continue                                    # already matched by another brand query
                    enrich(tw, self.matcher, q.get("topic"))
                    if not tw["brands"] and q["kind"] == "brand":
                        self.stats["dropped_no_brand"] += 1         # matched X's index but none of our terms
                        continue
                    self.seen_ids.add(tw["tweet_id"])
                    kept.append(tw)
                cursor = data.get("next_cursor") or ""
                if (not data.get("has_next_page") or not cursor or cursor in seen_cursors or not raw
                        or (oldest_on_page and oldest_on_page < since)):
                    break
                seen_cursors.add(cursor)
                await asyncio.sleep(0.3)
            if pages >= MAX_PAGES:
                log.info(f"  page cap hit for {q['key']} ({', '.join(q['brands'][:4]) or q.get('topic')}) — "
                         "older tweets in this window will be picked up by the next run's overlap only if recent")
            if kept:
                await save_tweets(self.pool, kept, self.brands)
            self.stats["stored"] += len(kept)
            label = ", ".join(q["brands"][:4]) + ("…" if len(q["brands"]) > 4 else "") if q["brands"] else q.get("topic")
            log.info(f"  [{label}] pages={pages} kept={len(kept)}")
            async with self.pool.acquire() as conn:
                await conn.execute("""
                    INSERT INTO x_intel.query_state (query_key, query_body, last_tweet_time, last_run_at, last_count)
                    VALUES ($1,$2,$3,now(),$4)
                    ON CONFLICT (query_key) DO UPDATE SET query_body = EXCLUDED.query_body,
                        last_tweet_time = GREATEST(x_intel.query_state.last_tweet_time, EXCLUDED.last_tweet_time),
                        last_run_at = now(), last_count = EXCLUDED.last_count
                """, q["key"], q["body"], newest, len(kept))
            return newest

    async def run(self) -> Counter:
        queries = build_queries(self.brands)
        async with self.pool.acquire() as conn:
            state = await load_state(conn)
        now = now_utc()
        floor = now - dt.timedelta(hours=MAX_LOOKBACK_H)
        log.info(f"{len(self.brands)} brands → {len(queries)} queries; caps: {MAX_PAGES} pages/query, "
                 f"{MAX_TWEETS} tweets/run")
        tasks = []
        for q in queries:
            last = state.get(q["key"])
            since = (last - dt.timedelta(minutes=OVERLAP_MIN)) if last else now - dt.timedelta(hours=INITIAL_LOOKBACK_H)
            tasks.append(self.run_query(q, max(since, floor)))
        results = await asyncio.gather(*tasks, return_exceptions=True)
        for r in results:
            if isinstance(r, Exception) and not isinstance(r, FatalAPIError):
                log.error(f"Query failed: {r!r}")
                self.stats["query_errors"] += 1
        self.stats["queries"] = len(queries)
        if self.stats["fetched"] >= MAX_TWEETS:
            log.warning(f"Per-run cap of {MAX_TWEETS} tweets reached — remaining pages skipped")
        return self.stats


# ─────────────────────────────────────────────────────────────────────────────
# Alerts
# ─────────────────────────────────────────────────────────────────────────────
async def send_alerts(pool: asyncpg.Pool, http: httpx.AsyncClient):
    if not SLACK_WEBHOOK:
        return
    async with pool.acquire() as conn:
        spikes = await conn.fetch("SELECT brand, mentions, baseline_avg, z_score FROM x_intel.spikes "
                                  "WHERE z_score >= 3 AND mentions >= 20 ORDER BY z_score DESC LIMIT 5")
        neg = await conn.fetch("SELECT brand, author_handle, author_followers, text, url FROM x_intel.negative_watch "
                               "WHERE author_followers >= 50000 OR engagement >= 200 LIMIT 5")
    lines = [f":chart_with_upwards_trend: *{r['brand']}* spike — {r['mentions']} mentions today vs "
             f"{r['baseline_avg']} usual (z={r['z_score']})" for r in spikes]
    lines += [f":warning: *{r['brand']}* negative from @{r['author_handle']} ({r['author_followers']:,} followers): "
              f"{r['text'][:160]} {r['url']}" for r in neg]
    if lines:
        try:
            await http.post(SLACK_WEBHOOK, json={"text": "*MediaPulse X alerts*\n" + "\n".join(lines)})
            log.info(f"Sent {len(lines)} alert line(s) to Slack")
        except Exception as exc:
            log.warning(f"Slack alert failed: {exc!r}")


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────
async def main() -> int:
    if not API_KEY or not RAW_DB_URL:
        log.error("Missing environment variables: X_BEARER_TOKEN (twitterapi.io key) and DATABASE_URL are required")
        return 1
    brands = load_brands()
    pool = await asyncpg.create_pool(dsn=clean_db_url(RAW_DB_URL), min_size=1, max_size=CONCURRENCY + 2,
                                     command_timeout=60)
    run_id, status, note = None, "ok", None
    stats: Counter = Counter()
    try:
        async with pool.acquire() as conn:
            await ensure_schema(conn)
            run_id = await conn.fetchval("INSERT INTO x_intel.runs (status) VALUES ('running') RETURNING run_id")
        async with httpx.AsyncClient(timeout=30) as http:
            collector = XCollector(API_KEY, pool, brands, http)
            try:
                stats = await collector.run()
            finally:
                stats = collector.stats
            if collector.fatal:
                status, note = "failed", collector.fatal
                log.error(f"Stopped early: {collector.fatal} (check the key / credits at twitterapi.io)")
            await send_alerts(pool, http)
    except Exception as exc:
        status, note = "failed", repr(exc)
        log.exception("Run crashed")
    finally:
        cost = round(stats["fetched"] / 1000 * COST_PER_1K, 4)
        if run_id:
            try:
                async with pool.acquire() as conn:
                    await conn.execute("""
                        UPDATE x_intel.runs SET finished_at = now(), status = $2, queries = $3, pages = $4,
                            tweets_fetched = $5, tweets_stored = $6, dropped_no_brand = $7, est_cost_usd = $8, note = $9
                        WHERE run_id = $1
                    """, run_id, status, stats["queries"], stats["pages"], stats["fetched"], stats["stored"],
                        stats["dropped_no_brand"], cost, note)
            except Exception:
                log.exception("Could not record run")
        await pool.close()
        log.info(f"=== Done: status={status} queries={stats['queries']} pages={stats['pages']} "
                 f"fetched={stats['fetched']} stored={stats['stored']} dropped_no_brand={stats['dropped_no_brand']} "
                 f"est_cost=${cost} ===")
    return 0 if status == "ok" else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
