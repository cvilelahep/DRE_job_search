#!/usr/bin/env python3
"""
Daily monitor for academic job openings in the Diário da República (2.ª série).

What it does
  1. Reads the DRE RSS feed(s), e.g. https://files.diariodarepublica.pt/rss/serie2&parte=e.xml
     (Part E = universities / polytechnics; the feed only holds the current day's issue).
  2. Keeps entries that are academic *openings* (not hirings, renewals, rankings or
     public consultations) based on the title + short description.
     Then keeps only those in your field (default: Física / physics), checking the
     feed text first and the PDF's summary / "área disciplinar" clauses second.
  3. For each new opening, downloads the PDF, extracts its text and pulls out the
     key facts: institution, summary, contract type, deadline, where to apply,
     requirements and selection criteria.
  4. Skips entries reported in earlier runs, prints a report, and optionally sends
     an email and/or a macOS notification.

Dependencies: Python 3.9+, `requests`, `pypdf`, `cryptography`
              (pip install requests pypdf cryptography)   # DRE's PDFs are AES-encrypted

Environment variables
  DRE_FEED_URLS      comma-separated feed URLs (required)
  DRE_STATE_FILE     default ~/.dre-jobs/seen.json
  DRE_PDF_DIR        where PDFs are saved, default ~/.dre-jobs/pdfs
  DRE_FETCH_PDFS     "1" (default) to download/parse PDFs, "0" to use feed text only
  DRE_FIELD_TERMS    comma-separated field keywords, accents optional (default "fisica";
                     use e.g. "fisica,quimica" or "" for all fields)
  DRE_STRICT_FIELD   "1" to drop openings whose field can't be verified (PDF unavailable)
  DRE_NOTIFY         "1" to show a macOS notification
  Email (optional): SMTP_HOST, SMTP_PORT (587; 465 = SSL), SMTP_USER, MAIL_TO (comma-separated),
                    MAIL_FROM (default SMTP_USER), and the password via EITHER
                    SMTP_PASS_KEYCHAIN=<macOS Keychain service name> (recommended) OR SMTP_PASS.
                    Run with --test-email to send a test message.
  If sending fails, the openings are NOT marked as seen, so the next run retries them.
"""

import hashlib
import io
import os
import re
import smtplib
import subprocess
import sys
import json
import unicodedata
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta
from email.message import EmailMessage
from functools import lru_cache
from pathlib import Path
from urllib.parse import urljoin

import requests

# --------------------------------------------------------------------------
# Config
# --------------------------------------------------------------------------

FEED_URLS = [u.strip() for u in os.environ.get("DRE_FEED_URLS", "").split(",") if u.strip()]
HOME_DIR = Path("~/.dre-jobs").expanduser()
STATE_FILE = Path(os.environ.get("DRE_STATE_FILE", HOME_DIR / "seen.json")).expanduser()
PDF_DIR = Path(os.environ.get("DRE_PDF_DIR", HOME_DIR / "pdfs")).expanduser()
FETCH_PDFS = os.environ.get("DRE_FETCH_PDFS", "1") == "1"
# Some servers answer plain scripts with an HTML page, so present browser-like headers.
SESSION = requests.Session()
SESSION.headers.update({
    "User-Agent": ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"),
    "Accept": "application/pdf,application/xml,text/xml,*/*;q=0.8",
    "Accept-Language": "pt-PT,pt;q=0.9,en;q=0.8",
    "Referer": "https://diariodarepublica.pt/",
})

# Matched against accent-stripped, lowercased text. Handles masculine/feminine forms.
ROLE_RE = re.compile(r"""
      professor(?:a)?\s+(?:catedratic|associad|auxiliar|adjunt|coordenador|titular|convidad)
    | investigador(?:a)?\s+(?:auxiliar|principal|coordenador)
    | doutorad
    | assistente\s+(?:de\s+investigacao|convidad)
    | carreira\s+(?:docente|de\s+investigacao)
    | \becdu\b | \becpdesp\b
""", re.X)

# The entry must also look like an *opening*...
OPENING_RE = re.compile(r"\b(?:abertura|aberto|concurso|procedimento concursal|recrutamento|candidaturas?)\b")

# ...and must not be a result, ranking or consultation.
NEGATIVE_RE = re.compile(
    r"consulta publica|projeto de regulamento|homologacao|"
    r"lista (?:unitaria )?de (?:ordenacao|classificacao)|ordenacao final|"
    r"agrupamento de escolas|escola basica|escola secundaria"
)

# Field filter. "fisica" also matches astrofísica, geofísica, biofísica, física médica,
# engenharia física, etc. Phrases below are removed first so "Educação Física",
# "pessoa física", "atividade física" ... are NOT mistaken for physics.
_FIELD_RAW = os.environ.get("DRE_FIELD_TERMS", "fisica")
STRICT_FIELD = os.environ.get("DRE_STRICT_FIELD") == "1"
FIELD_EXCLUDE_RE = re.compile(
    r"\b(?:educacao|atividades?|aptidao|aptidoes|pessoas?|medicina|reabilitacao|"
    r"capacidades?|saude|exercicio|condicao|cultura|motricidade)\s+fisicas?\b")

# Extra safety net when a feed mixes in non-academic bodies. [] disables.
INSTITUTION_HINTS = [
    "universidade", "politecnic", "instituto", "escola superior", "faculdade",
    "fct", "laboratorio", "centro de investigacao",
]


# --------------------------------------------------------------------------
# Text helpers
# --------------------------------------------------------------------------

def clean(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def fold(text: str) -> str:
    """Lowercase and strip accents while keeping the SAME length, so spans found
    in the folded text can be used to slice the original text."""
    return "".join(unicodedata.normalize("NFKD", c)[0] for c in text).lower()


FIELD_TERMS = [fold(t.strip()) for t in _FIELD_RAW.split(",") if t.strip()]


# --------------------------------------------------------------------------
# Feed
# --------------------------------------------------------------------------

FEED_HEADER_PROFILES = [
    {"User-Agent": "curl/8.4.0", "Accept": "*/*"},   # plain client first
    dict(SESSION.headers),                            # then browser-like
]


def is_pdf_link(link: str) -> bool:
    return link.lower().split("?")[0].endswith(".pdf")


def parse_feed(content: bytes):
    root = ET.fromstring(content)
    local = lambda tag: tag.split("}", 1)[-1]

    for item in root.iter():
        if local(item.tag) not in ("item", "entry"):
            continue
        d = {"id": "", "title": "", "link": "", "summary": "", "published": ""}
        for child in item:
            t = local(child.tag)
            if t == "title":
                d["title"] = clean(child.text)
            elif t == "link":
                d["link"] = clean(child.attrib.get("href") or child.text)
            elif t in ("description", "summary", "content"):
                d["summary"] = clean(re.sub(r"<[^>]+>", " ", child.text or ""))
            elif t in ("pubDate", "published", "updated"):
                d["published"] = clean(child.text)
            elif t in ("guid", "id"):
                d["id"] = clean(child.text)
        d["id"] = d["id"] or d["link"] or hashlib.sha1(d["title"].encode()).hexdigest()
        m = re.search(r"(\d{4})-(\d{2})-(\d{2})\s*$", d["title"])
        d["pub_date"] = date(*map(int, m.groups())) if m else date.today()
        yield d


def fetch_feed(url: str) -> list:
    """Some servers hand out different links depending on the client, so try each header
    profile and keep the result with the most direct PDF links."""
    best, best_score = [], -1
    for headers in FEED_HEADER_PROFILES:
        r = requests.get(url, headers=headers, timeout=30)
        r.raise_for_status()
        entries = list(parse_feed(r.content))
        score = sum(is_pdf_link(e["link"]) for e in entries)
        if entries and score > best_score:
            best, best_score = entries, score
        if entries and score == len(entries):
            break
    return best


def is_relevant(entry: dict) -> bool:
    blob = fold(clean(f"{entry['title']} {entry['summary']}"))
    if NEGATIVE_RE.search(blob):
        return False
    if not (ROLE_RE.search(blob) and OPENING_RE.search(blob)):
        return False
    if INSTITUTION_HINTS and not any(h in blob for h in INSTITUTION_HINTS):
        return False
    return True


# "...na área científica de Química", "Área Disciplinar de Enfermagem", "área de Educação Física"
FIELD_STATED_RE = re.compile(
    r"\bareas?\s+(?:disciplinar(?:es)?|cientifica|de conhecimento|de especializacao|de)\s+\w")


def field_match(text: str):
    """Return the matched word (e.g. 'Física', 'Astrofísica') or None."""
    if not FIELD_TERMS:
        return "any field"
    t = clean(text)
    f = FIELD_EXCLUDE_RE.sub(lambda m: " " * len(m.group()), fold(t))
    for term in FIELD_TERMS:
        m = re.search(rf"\w*{re.escape(term)}\w*", f)
        if m:
            return t[m.start():m.end()]
    return None


def apply_field_filter(entries: list) -> list:
    """Feed text first, then PDF summary/area clauses. Unverifiable entries are kept
    (and flagged) unless DRE_STRICT_FIELD=1, so a blocked PDF never hides a job."""
    if not FIELD_TERMS:
        return entries
    kept = []
    for e in entries:
        hit, src = field_match(f"{e['title']} {e['summary']}"), "feed"
        d = e.get("details")
        if not hit and d:
            hit, src = field_match(d.get("field_text", "")), "PDF"
        if hit:
            e["field_hit"] = f"{hit} (found in {src})"
            kept.append(e)
        elif (e.get("pdf_error") or e.get("no_pdf")) and not STRICT_FIELD:
            if FIELD_STATED_RE.search(fold(clean(f"{e['title']} {e['summary']}"))):
                continue  # the feed text names a field and it isn't ours
            e["field_unverified"] = True
            kept.append(e)
    return kept


# --------------------------------------------------------------------------
# Portuguese business-day arithmetic (indicative deadlines)
# --------------------------------------------------------------------------

def _easter(y: int) -> date:
    a, b, c = y % 19, y // 100, y % 100
    d, e = b // 4, b % 4
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i, k = c // 4, c % 4
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    month = (h + l - 7 * m + 114) // 31
    day = ((h + l - 7 * m + 114) % 31) + 1
    return date(y, month, day)


@lru_cache(maxsize=None)
def pt_holidays(y: int) -> frozenset:
    e = _easter(y)
    fixed = [(1, 1), (4, 25), (5, 1), (6, 10), (8, 15), (10, 5), (11, 1),
             (12, 1), (12, 8), (12, 25)]
    return frozenset([date(y, m, d) for m, d in fixed] +
                     [e - timedelta(days=2), e, e + timedelta(days=60)])


def is_business_day(d: date) -> bool:
    return d.weekday() < 5 and d not in pt_holidays(d.year)


def add_business_days(start: date, n: int) -> date:
    d, count = start, 0
    while count < n:
        d += timedelta(days=1)
        if is_business_day(d):
            count += 1
    return d


def compute_deadline(pub: date, n: int, kind: str):
    """Deadline counted from the day AFTER publication. Indicative only."""
    if kind == "uteis":
        return add_business_days(pub, n)
    if kind in ("seguidos", "corridos", "consecutivos", "de calendario"):
        d = pub + timedelta(days=n)
        while not is_business_day(d):  # a deadline falling on a non-working day rolls forward
            d += timedelta(days=1)
        return d
    return None


# --------------------------------------------------------------------------
# PDF download + extraction
# --------------------------------------------------------------------------

HEADER_PROFILES = [
    dict(SESSION.headers),                                   # browser-like
    {"User-Agent": "curl/8.4.0", "Accept": "*/*"},           # minimal, curl-like
]


def _is_pdf(content: bytes) -> bool:
    return b"%PDF" in content[:1024]


def _download_pdf(url: str) -> bytes:
    """Return real PDF bytes or raise an error that says exactly what came back."""
    last, requested = None, url
    for headers in HEADER_PROFILES:
        target = requested
        for _ in range(2):  # an HTML page may link/redirect to the real PDF; follow once
            r = requests.get(target, headers=headers, timeout=60, allow_redirects=True)
            r.raise_for_status()
            if _is_pdf(r.content):
                return r.content
            last = r
            m = (re.search(rb"""(?:href|src)=["']([^"']+\.pdf[^"']*)["']""", r.content, re.I)
                 or re.search(rb"""url=([^"'>\s]+\.pdf[^"'>\s]*)""", r.content, re.I))
            if not m:
                break
            target = urljoin(r.url, m.group(1).decode("utf-8", "ignore"))
    debug = HOME_DIR / "debug"
    debug.mkdir(parents=True, exist_ok=True)
    saved = debug / (requested.rsplit("/", 1)[-1] + ".html")
    saved.write_bytes(last.content)
    hint = ""
    if "dr/detalhe" in requested or "dr/detalhe" in last.url or b"OutSystems" in last.content[:4000]:
        hint = " This is DRE's JavaScript web app, so there is no PDF behind this link."
    raise RuntimeError(f"not a PDF. Requested {requested} -> got {last.url} "
                       f"(HTTP {last.status_code}, {last.headers.get('Content-Type', '?')}).{hint} "
                       f"Saved to {saved}")


def pdf_to_text(content: bytes) -> str:
    from pypdf import PdfReader  # imported lazily so the feed part works without it
    try:
        reader = PdfReader(io.BytesIO(content))
        if reader.is_encrypted:
            reader.decrypt("")  # DRE PDFs are encrypted with an empty user password
        return "\n".join((p.extract_text() or "") for p in reader.pages)
    except Exception as exc:
        if "cryptography" in str(exc).lower():
            raise RuntimeError("DRE PDFs are AES-encrypted; run: pip install cryptography") from exc
        raise


def save_pdf(content: bytes, url: str, pub: date) -> None:
    PDF_DIR.mkdir(parents=True, exist_ok=True)
    (PDF_DIR / f"{pub:%Y-%m-%d}_{url.rsplit('/', 1)[-1]}").write_bytes(content)


def strip_page_noise(text: str) -> str:
    """Remove running headers/footers (short lines repeated on every page)."""
    lines = [l.strip() for l in text.splitlines()]
    freq = {}
    for l in lines:
        freq[l] = freq.get(l, 0) + 1
    keep = [l for l in lines
            if l and not re.fullmatch(r"\d+/\d+", l) and not (freq[l] >= 3 and len(l) < 80)]
    return "\n".join(keep)


def _shorten(s: str, n: int) -> str:
    s = s.strip()
    if len(s) <= n:
        return s
    return s[:n].rsplit(" ", 1)[0] + " …"


def extract_details(raw: str, pub: date) -> dict:
    head = clean(raw[:2500])               # first page header, before noise removal
    body = clean(strip_page_noise(raw))
    fb = fold(body)
    d = {}

    m = re.search(r"2\.ª série\s+(.+?)\s+(?:Aviso|Despacho|Edital|Declaração|Deliberação|"
                  r"Regulamento|Anúncio)\b", head)
    if m:
        d["institution"] = m.group(1)

    m = re.search(r"Sum[áa]rio:\s*(.+?)\s+1\s*[—–-]\s", head + " ")
    if m:
        d["summary"] = m.group(1)

    m = re.search(r"contrato de trabalho[^,;.]{0,120}", fb)
    if m:
        d["contract"] = body[m.start():m.end()]

    m = re.search(r"prazo de (\d{1,3})(?:\s*\([^)]*\))?\s*dias"
                  r"(?:\s+(uteis|seguidos|corridos|consecutivos|de calendario))?", fb)
    if m:
        n, kind = int(m.group(1)), m.group(2)
        d["deadline_days"] = n
        d["deadline_kind"] = {"uteis": "úteis", None: "(tipo não indicado)"}.get(kind, kind)
        d["deadline_date"] = compute_deadline(pub, n, kind) if kind else None

    m = re.search(r"prazo adicional de (\d{1,3})(?:\s*\([^)]*\))?\s*dias"
                  r"(?:\s+(uteis|seguidos|corridos|consecutivos|de calendario))?", fb)
    if m:
        n, kind = int(m.group(1)), m.group(2)
        d["extension_days"] = n
        d["extension_kind"] = {"uteis": "úteis", None: "(tipo não indicado)"}.get(kind, kind)
        d["extension_date"] = compute_deadline(pub, n, kind) if kind else None
        i = fb.find("foi publicado")
        ref = re.search(r"n\.o\s*(\d+/\d{4}(?:/\d+)?)", fb[i:i + 120]) if i >= 0 else None
        if ref:
            d["amends"] = ref.group(1)
    elif re.search(r"retifica(?:cao|se)|prorrogacao do prazo", fb[:1500]):
        d["amendment"] = True

    m = re.search(r"requisitos especiais[^:]{0,80}:\s*(.{20,500})", fb)
    if m:
        req = body[m.start(1):m.end(1)]
        nxt = re.search(r"\s\d{1,2}\s[—–-]\s", req[5:])  # next top-level point, e.g. "5 — "
        if nxt:
            req = req[:5 + nxt.start()]
        d["requirements"] = _shorten(req, 320)

    urls = [u.rstrip(".,;)") for u in re.findall(r"https?://[^\s\]>]+", body)]
    skip = ("legislacao", "dre.pt", "diariodarepublica", "dgsi", "eur-lex", "protecao-de-dados")
    prefer = ("concurso", "candidatur", "recrut", "emprego", "job", "career", "plataforma", "apply", "bep")
    good = [u for u in urls if not any(s in u.lower() for s in skip)]
    pick = next((u for u in good if any(p in u.lower() for p in prefer)), good[0] if good else None)
    if pick:
        d["apply_url"] = pick
    m = re.search(r"[\w.+-]+@[\w-]+(?:\.[\w-]+)+", body)
    if m:
        d["email"] = m.group(0)

    areas = [body[m.start():m.start() + 200] for m in re.finditer(
        r"area(?:s)? (?:disciplinar(?:es)?|cientifica|de conhecimento|de especializacao)\b", fb)][:4]
    if areas:
        d["area"] = _shorten(re.split(r"[;.,]", areas[0])[0], 110)
    d["field_text"] = " ".join([d.get("summary", "")] + areas + [d.get("requirements", "")])

    i = fb.find("criterios de selecao")
    if i >= 0:
        seg = body[i:i + 1800]
        pairs = re.findall(r"([A-Za-zÀ-ÿ][^:;()]{4,90}?)\s*\((\d{1,3}(?:[,.]\d+)?)\s?%\)", seg)
        crit, seen = [], set()
        for label, pct in pairs:
            label = label.strip(" ,-—")
            if label not in seen:
                seen.add(label)
                crit.append(f"{label} {pct}%")
        if crit:
            d["criteria"] = crit[:6]
    return d


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

def format_entry(e: dict) -> str:
    d = e.get("details", {})
    short_title = re.split(r"\s+-\s+Di[áa]rio", e["title"])[0]
    out = [f"• {short_title}" + (f" — {d['institution']}" if d.get("institution") else "")]
    out.append(f"  {d.get('summary') or e['summary']}")
    if d.get("area"):
        out.append(f"  Field: {d['area']}")
    if e.get("field_hit"):
        out.append(f"  Field match: {e['field_hit']}")
    if e.get("field_unverified"):
        out.append("  ⚠ Field NOT verified (full notice unavailable) — open the link to check")
    if d.get("contract"):
        out.append(f"  Contract: {d['contract']}")
    if d.get("extension_days"):
        line = f"  ⚠ EXTENSION of an earlier call" + (f" (Aviso n.º {d['amends']})" if d.get("amends") else "")
        line += f": +{d['extension_days']} dias {d['extension_kind']} from publication"
        if d.get("extension_date"):
            line += f" → approx. {d['extension_date']:%Y-%m-%d}"
        out.append(line)
    elif d.get("amendment"):
        out.append("  ⚠ Correction/amendment notice — see the original call for full details")
    if d.get("deadline_days"):
        line = f"  Deadline: {d['deadline_days']} dias {d['deadline_kind']} after publication"
        if d.get("deadline_date"):
            line += f" → approx. {d['deadline_date']:%Y-%m-%d} (indicative; check the notice)"
        out.append(line)
    if d.get("apply_url"):
        out.append(f"  Apply: {d['apply_url']}")
    if d.get("email"):
        out.append(f"  Contact: {d['email']}")
    if d.get("requirements"):
        out.append(f"  Requirements: {d['requirements']}")
    if d.get("criteria"):
        out.append("  Criteria: " + "; ".join(d["criteria"]))
    if e.get("no_pdf"):
        out.append("  ℹ The feed gives only DRE's web page for this notice, so deadline, "
                   "requirements etc. could not be extracted automatically.")
    elif e.get("pdf_error"):
        out.append(f"  (PDF could not be read: {e['pdf_error']})")
    out.append(f"  {'PDF' if is_pdf_link(e['link']) else 'Link'}: {e['link']}")
    return "\n".join(out)


def format_report(entries: list) -> str:
    scope = f" [field: {', '.join(FIELD_TERMS)}]" if FIELD_TERMS else ""
    head = f"{len(entries)} new academic opening(s){scope} — Diário da República, {datetime.now():%Y-%m-%d}\n"
    return head + "\n" + "\n\n".join(format_entry(e) for e in entries) + "\n"


def _smtp_password() -> str:
    service = os.environ.get("SMTP_PASS_KEYCHAIN")
    if service:
        out = subprocess.run(
            ["security", "find-generic-password", "-a", os.environ.get("SMTP_USER", ""),
             "-s", service, "-w"], capture_output=True, text=True)
        if out.returncode != 0:
            raise RuntimeError(f"password not found in Keychain (service '{service}', "
                               f"account '{os.environ.get('SMTP_USER', '')}')")
        return out.stdout.strip()
    return os.environ.get("SMTP_PASS", "")


def email_configured() -> bool:
    return bool(os.environ.get("SMTP_HOST") and os.environ.get("MAIL_TO"))


def send_email(body: str, subject: str):
    """Returns None if email isn't configured, True on success, False on failure."""
    if not email_configured():
        return None
    try:
        host, port = os.environ["SMTP_HOST"], int(os.environ.get("SMTP_PORT", "587"))
        user = os.environ.get("SMTP_USER", "")
        to = [a.strip() for a in os.environ["MAIL_TO"].split(",") if a.strip()]
        msg = EmailMessage()
        msg["Subject"] = subject
        msg["From"] = os.environ.get("MAIL_FROM", user or "dre-bot@localhost")
        msg["To"] = ", ".join(to)
        msg.set_content(body)
        if port == 465:
            s = smtplib.SMTP_SSL(host, port, timeout=30)
        else:
            s = smtplib.SMTP(host, port, timeout=30)
        with s:
            s.ehlo()
            if port != 465 and s.has_extn("starttls"):
                s.starttls()
                s.ehlo()
            if user:
                s.login(user, _smtp_password())
            s.send_message(msg)
        return True
    except Exception as exc:
        print(f"Email failed: {exc}", file=sys.stderr)
        return False


def notify_macos(n: int) -> None:
    if os.environ.get("DRE_NOTIFY") == "1" and sys.platform == "darwin":
        script = f'display notification "{n} new academic opening(s)" with title "Diário da República"'
        subprocess.run(["osascript", "-e", script], check=False)


# --------------------------------------------------------------------------
# State + main
# --------------------------------------------------------------------------

def load_seen() -> set:
    try:
        return set(json.loads(STATE_FILE.read_text()))
    except (FileNotFoundError, json.JSONDecodeError):
        return set()


def save_seen(seen: set) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(sorted(seen)))


WARNED_LINK: list = []


def main() -> int:
    if "--test-email" in sys.argv:
        if not email_configured():
            print("Email not configured (need SMTP_HOST and MAIL_TO).", file=sys.stderr)
            return 2
        ok = send_email("Test message from dre_academic_jobs.py — email is working.",
                        "DRE monitor: test email")
        print("Test email sent." if ok else "Test email FAILED (see above).")
        return 0 if ok else 1
    if not FEED_URLS:
        print("No feed URLs configured. Set DRE_FEED_URLS.", file=sys.stderr)
        return 2

    seen, new = load_seen(), []
    for url in FEED_URLS:
        try:
            for e in fetch_feed(url):
                if not e["link"].lower().endswith(".pdf") and not WARNED_LINK:
                    WARNED_LINK.append(e["link"])
                    print(f"Note: feed link is not a direct PDF link, e.g. {e['link']} "
                          f"(PDF details will be unavailable for such entries)", file=sys.stderr)
                if e["id"] not in seen and is_relevant(e):
                    new.append(e)
                seen.add(e["id"])
        except Exception as exc:
            print(f"Failed to read {url}: {exc}", file=sys.stderr)

    if FETCH_PDFS:
        for e in new:
            if not is_pdf_link(e["link"]):
                e["no_pdf"] = True  # feed only gives DRE's web-app page; nothing to download
                continue
            try:
                e["_pdf"] = _download_pdf(e["link"])
                e["details"] = extract_details(pdf_to_text(e["_pdf"]), e["pub_date"])
            except Exception as exc:  # still use the feed text
                e["pdf_error"] = str(exc)[:300]

    new = apply_field_filter(new)
    for e in new:  # keep only the PDFs of entries we report
        if e.get("_pdf"):
            save_pdf(e["_pdf"], e["link"], e["pub_date"])

    if new:
        report = format_report(new)
        print(report)
        sent = send_email(report, f"DRE: {len(new)} new academic opening(s)"
                                  + (f" [{', '.join(FIELD_TERMS)}]" if FIELD_TERMS else ""))
        if sent is False:  # don't lose them: report again on the next run
            for e in new:
                seen.discard(e["id"])
            print("Email not sent; these openings will be reported again next run.", file=sys.stderr)
        notify_macos(len(new))
    else:
        print("No new matching openings.")
    save_seen(seen)
    return 0


if __name__ == "__main__":
    sys.exit(main())
