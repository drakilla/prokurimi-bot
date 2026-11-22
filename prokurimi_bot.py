# -*- coding: utf-8 -*-
"""
Prokurimi Bot - njofton ne Telegram per tenderet e reja ne e-Prokurimi (Kosove).

Kategorite e tendereve:
  TCC    - koncerte/evente: zerim, LED/ekrane, skene/bina, ndricim skenik, festivale...
  AI     - AI dhe sherbime digjitale per institucione: AI, perkthim, transkriptim,
           softuer, digjitalizim, platforma, website...
  BILETA - shitje/sisteme biletash, regjistrim dhe kontroll hyrjeje ne evente

Grante dhe subvencione: ndjek faqet e KIESA, MINTI, Ministrise se Ekonomise, platformes se
financimit te OJQ-ve, komunave, GIZ, Helvetas, LuxDev, KCSF etj. dhe te njofton per thirrjet e reja.

Komandat ne Telegram (pergjigjet ne kontrollin e ardhshem, brenda 10 min):
  /status   a po punon boti dhe statistikat
  /tenderet tenderet e hapur qe te perkasin
  /grantet  grantet e fundit qe gjeti

Perdorimi:
  python prokurimi_bot.py --setup      # vendos token-in e Telegram dhe chat_id
  python prokurimi_bot.py --test       # dergon nje mesazh prove
  python prokurimi_bot.py              # nje kontroll (kete e ekzekuton Task Scheduler)
  python prokurimi_bot.py --dry-run    # kontroll pa derguar asgje, shfaq ne ekran

Vetem librari standarde te Python 3 - nuk ka nevoje per pip install.
"""
import html
import json
import os
import re
import ssl
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
from datetime import datetime, timedelta

BASE = "https://e-prokurimi.rks-gov.net/SPIN_PROD/application/ipn/DocumentManagement/"
LIST_URL = BASE + "NewPreglediDokumenataFrm.aspx"
DETAIL_URL = BASE + "DokumentPodaciFrm.aspx?id={id}"

HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(HERE, "config.json")
STATE_PATH = os.path.join(HERE, "state.json")
LOG_PATH = os.path.join(HERE, "bot.log")

DEFAULT_CONFIG = {
    "telegram_token": "",
    "chat_id": "",
    # Sa mesazhe per cdo tender te ri (1 = vetem mesazhi kryesor, 3 = kryesori + 2 kujtesa)
    "alert_repeats": 3,
    # Kujtesa para afatit (dite)
    "deadline_reminders_days": [3, 1],
    # Llojet e njoftimeve qe ndiqen (B05 = Njoftim per kontrate = tender i ri)
    "notice_types": ["B05"],
    # Nese serveri i e-Prokurimit ka certifikate te paplote, provo pa verifikim (vetem lexim publik)
    "allow_unverified_ssl_fallback": True,
    # Fjale shtese qe i shton vete (pa diakritike, shkronja te vogla), p.sh. "dj", "karaoke"
    "extra_keywords_tcc": [],
    "extra_keywords_ai": [],
    "extra_keywords_bileta": [],
    # Mesazhi ditor "boti punon" (ora; null = pa mesazh ditor)
    "heartbeat_hour": 9,
    # Sa shpesh kontrollohen faqet e granteve (ore)
    "grants_every_hours": 3,
    # Faqet qe ndiqen per grante/subvencione (mund te shtosh te tjera)
    "grant_sources": [
        {"name": "KIESA - Shpalljet", "url": "https://kiesa.rks-gov.net/page.aspx?id=1,134"},
        {"name": "MINTI - Shpalljet", "url": "https://minti.rks-gov.net/shpalljet/"},
        {"name": "MINTI - Lajme", "url": "https://minti.rks-gov.net/lajme/"},
        {"name": "Ministria e Ekonomise", "url": "https://me.rks-gov.net/"},
        {"name": "Platforma e financimit publik (OJQ)", "url": "https://ojqfinancime.rks-gov.net/"},
        {"name": "Komuna e Prishtines", "url": "https://prishtina.rks-gov.net/"},
        {"name": "Komuna e Gjakoves", "url": "https://gjakova.rks-gov.net/"},
        {"name": "Komuna e Podujeves", "url": "https://podujeve.rks-gov.net/"},
        {"name": "Komuna e Fushe Kosoves", "url": "https://fushekosove.rks-gov.net/"},
        {"name": "Komuna e Lipjanit", "url": "https://lipjan.rks-gov.net/"},
        {"name": "Komuna e Mitrovices Jugore", "url": "https://mitroviceejugut.rks-gov.net/"},
        {"name": "Kosovo Funding (thirrje, GIZ etj.)", "url": "https://www.kosovofunding.org/"},
        {"name": "LuxDev - Lajme", "url": "https://luxdev.lu/en/news"},
        {"name": "KCSF - Grante", "url": "https://kcsfoundation.org/en/grants/"},
    ],
}

# ---------------------------------------------------------------- matching

def norm(s):
    s = unicodedata.normalize("NFD", s or "")
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return s.lower()

TCC_PATTERNS = [
    r"\bled\b", r"\bekran", r"video ?wall", r"\bsken(a|e|es|en|at|ave|ik|ike)?\b",
    r"\bbin(a|e|es|en|at)\b", r"\bpodium", r"\btruss", r"\bzerim", r"\baudio",
    r"\bzanor", r"(sistem|pajisje)\w* (te |per )?(zerit|zerimit|zanor)", r"altoparlant",
    r"mikrofon", r"\bmikser", r"skenik", r"\bkoncert", r"\bfestival", r"manifestim",
    r"\bevent", r"\beveniment", r"ceremoni", r"\bfestim", r"\bfest(a|en|es)\b", r"\bshfaqj",
    r"projektor", r"audio-?vizuel", r"kabin\w* (e |te )?perkthim", r"perkthim simultan",
    r"dit(a|en|es) e pavaresis", r"viti i ri", r"\bdj\b", r"\bsound\b", r"\bstage\b",
    r"transmetim", r"ndricim\w* dekorativ", r"dekorim\w* .{0,60}(fest|fundvit|vit\w* (te |e )?ri)",
    r"organizim\w* (i |e |te )?(aktivitet|ngjarj|festiv|koncert|manifest|ceremoni|event|evenim|feste|festim)",
]
TCC_EXCLUDE = [
    r"ndricim\w* publik", r"\brrug", r"\bllamb", r"semafor", r"trotuar", r"ndricues",
    r"ndricimit led", r"ndricim led", r"skenar", r"\bskaner", r"mamograf", r"rentgen",
    r"dhurat", r"suvenir", r"pako",
]
TCC_STRONG = [r"\bkoncert", r"\bfestival", r"\bsken(a|e|es)\b", r"\bzerim", r"skenik", r"\bevent",
              r"manifestim", r"dekorativ", r"dekorim"]
TCC_CPV = ["923", "922", "92000000", "7995", "3232", "3234", "3235", "51313", "51314", "39154"]

AI_PATTERNS = [
    r"intel[ie]gj[ie]nc\w* artificial", r"artificial intelligence", r"chat ?bot",
    r"asistent\w* virtual", r"machine learning", r"\bllm\b", r"\bgpt", r"automatizim",
    r"perkthim", r"transkript", r"titrim", r"lektur", r"di(gj|xh|g)?[ie]tali[sz]im",
    r"platform\w* (digjital|dixhital|elektronik|online|ueb|web)", r"softuer", r"software", r"softwer",
    r"aplikacion", r"\bweb\b", r"ueb[- ]?faqe", r"web[- ]?faqe", r"website", r"faqe\w* (se |te )?internet",
    r"sistem\w* informativ", r"\bocr\b", r"njohje\w* (e |te )?(zerit|fytyr|teksti)",
    r"analiz\w* (e |te )?(te )?dhenave", r"\bbig data", r"\bcloud\b", r"\bportal",
    r"e-?sherbim", r"\bdi(gj|xh)ital\w* (e |te )?(sherbim|dokument|arkiv)", r"menaxhim\w* (e |te )?dokument",
    r"zhvillim\w*\W.{0,50}(sistem|softuer|aplikacion|platform|modul|ueb|web)",
]
AI_EXCLUDE = [
    r"pleh", r"\bbar\w* artificial", r"insemin", r"dhemb", r"\bfush", r"mamograf", r"rentgen",
    r"perkthim simultan", r"kabin\w* (e |te )?perkthim",
]
AI_CPV = ["7221", "7222", "7223", "7224", "7226", "7231", "7232", "7233", "7953", "7954", "7955"]

BILETA_PATTERNS = [
    r"\bbilet", r"\bticket", r"\bbiletari", r"sistem\w* (per |te |i )?(shitje|regjistrim|rezervim)",
    r"kontroll\w* (i |e |te )?hyrj", r"akreditim", r"regjistrim\w* (i |e |te )?(pjesemarres|vizitor)",
    r"\bqr\b", r"rezervim\w* online", r"shitje\w* online",
]
BILETA_EXCLUDE = [r"avion", r"ajror", r"udhetim", r"transport", r"autobus", r"parking", r"\bsms\b"]
BILETA_STRONG = [r"\bevent", r"koncert", r"festival", r"teat[eë]r", r"stadium", r"\bkinem"]


def _match(title, cpv, patterns, exclude, cpv_prefixes, strong=None, extra=None):
    t = norm(title)
    hits = []
    for p in patterns:
        m = re.search(p, t)
        if m:
            hits.append(m.group(0).strip()[:25])
    hits += [k for k in (extra or []) if k and norm(k) in t]
    cpv_code = (cpv or "").split(" ")[0].replace("-", "")
    cpv_hit = any(cpv_code.startswith(c) for c in cpv_prefixes) if cpv_code else False
    if not hits and not cpv_hit:
        return []
    if any(re.search(x, t) for x in exclude):
        if not (strong and any(re.search(s, t) for s in strong)):
            return []
    labels = list(dict.fromkeys(hits))
    if cpv_hit:
        labels.append("FPP " + (cpv or "")[:10])
    return labels


def classify(title, cpv, cfg):
    cats = {}
    tcc = _match(title, cpv, TCC_PATTERNS, TCC_EXCLUDE, TCC_CPV, TCC_STRONG, cfg.get("extra_keywords_tcc"))
    if tcc:
        cats["TCC"] = tcc
    ai = _match(title, cpv, AI_PATTERNS, AI_EXCLUDE, AI_CPV, None, cfg.get("extra_keywords_ai"))
    # "AI" me shkronja te medha (ne shqip "ai" = "ai/ajo", prandaj kerkohet vetem i shkruar AI)
    if re.search(r"\bAI\b", title or "") and not any(re.search(x, norm(title)) for x in AI_EXCLUDE):
        ai = (ai or []) + ["AI"]
    if ai:
        cats["AI"] = ai
    bil = _match(title, cpv, BILETA_PATTERNS, BILETA_EXCLUDE, [], BILETA_STRONG, cfg.get("extra_keywords_bileta"))
    if bil:
        cats["BILETA"] = bil
    return cats

# ---------------------------------------------------------------- http

def log(msg):
    line = "%s  %s" % (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), msg)
    try:
        print(line)
    except Exception:
        pass
    try:
        if os.path.exists(LOG_PATH) and os.path.getsize(LOG_PATH) > 2_000_000:
            os.replace(LOG_PATH, LOG_PATH + ".old")
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def http_get(url, cfg, timeout=60):
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) ProkurimiBot/1.0",
        "Accept-Language": "sq,en;q=0.8",
    })
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read().decode("utf-8", errors="replace")
    except urllib.error.URLError as e:
        if isinstance(getattr(e, "reason", None), ssl.SSLError) and cfg.get("allow_unverified_ssl_fallback"):
            log("KUJDES: certifikata SSL nuk u verifikua, po provoj pa verifikim (vetem lexim publik).")
            ctx = ssl._create_unverified_context()
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
                return r.read().decode("utf-8", errors="replace")
        raise


def telegram(cfg, method, params):
    url = "https://api.telegram.org/bot%s/%s" % (cfg["telegram_token"], method)
    data = urllib.parse.urlencode(params).encode("utf-8")
    req = urllib.request.Request(url, data=data)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode("utf-8"))


def send(cfg, text):
    if not cfg.get("telegram_token") or not cfg.get("chat_id"):
        log("Telegram nuk eshte konfiguruar - mesazhi nuk u dergua:\n" + text)
        return False
    for attempt in range(3):
        try:
            res = telegram(cfg, "sendMessage", {
                "chat_id": cfg["chat_id"], "text": text, "parse_mode": "HTML",
                "disable_web_page_preview": "true",
            })
            if res.get("ok"):
                return True
            log("Telegram gabim: %s" % res)
        except Exception as e:
            log("Telegram gabim (%s): %s" % (attempt + 1, e))
        time.sleep(3)
    return False

# ---------------------------------------------------------------- parsing

TOKEN_RE = re.compile(
    r"On-line njoftimet\s+(?P<date>\d{2}\.\d{2}\.\d{4})"
    r"|<h2[^>]*>\s*(?:<a[^>]*>[^<]*</a>)?\s*(?P<type>[^<]+?)\s*</h2>"
    r"|<a href='DokumentPodaciFrm\.aspx\?id=(?P<id>\d+)'>\s*\d+\.\s*(?P<title>.*?)</a>",
    re.S,
)


def parse_list(page):
    items, seen = [], set()
    date = typ = None
    for m in TOKEN_RE.finditer(page):
        if m.group("date"):
            date = m.group("date")
        elif m.group("type"):
            typ = html.unescape(m.group("type")).strip()
        elif m.group("id"):
            i = m.group("id")
            if i in seen:
                continue
            seen.add(i)
            title = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", m.group("title")))).strip()
            items.append({"id": i, "date": date, "type": typ or "", "title": title})
    return items


def _span(page, sid):
    m = re.search(r'<span[^>]*id="uiDokumentPodaci_%s"[^>]*>(.*?)</span>' % sid, page, re.S)
    if not m:
        return ""
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", m.group(1)))).strip()


def parse_detail(page):
    return {
        "buyer": _span(page, "uiNarucitelj"),
        "code": _span(page, "uiBrojObjave"),
        "title": _span(page, "uiNaslov"),
        "kind": _span(page, "uiVrstaUgovora"),
        "cpv": _span(page, "uiCpv"),
        "procedure": _span(page, "uiVrstaPostupka"),
        "value": _span(page, "uiProcijenjenaVrijednost"),
        "deadline": _span(page, "uiRokZaDostavuVrijeme"),
    }


def parse_deadline(s):
    for fmt in ("%d.%m.%Y %H:%M", "%d.%m.%Y"):
        try:
            return datetime.strptime((s or "").strip(), fmt)
        except ValueError:
            pass
    return None

# ---------------------------------------------------------------- messages

ICON = {"TCC": "\U0001F3A4", "AI": "\U0001F916", "BILETA": "\U0001F39F"}
NAME = {"TCC": "TCC (evente / zërim / LED)", "AI": "AI / shërbime digjitale", "BILETA": "Bileta / regjistrim në evente"}


def esc(s):
    return html.escape(s or "", quote=False)


def format_alert(item, det, cats, header="TENDER I RI"):
    cat_line = " + ".join("%s %s" % (ICON[c], NAME[c]) for c in cats)
    lines = [
        "<b>%s</b> - %s" % (header, cat_line),
        "",
        "<b>%s</b>" % esc(det.get("title") or item["title"]),
        "\U0001F3DB %s" % esc(det.get("buyer") or "-"),
    ]
    if det.get("value"):
        lines.append("\U0001F4B6 Vlera e parashikuar: <b>%s €</b>" % esc(det["value"]))
    if det.get("deadline"):
        lines.append("⏰ Afati: <b>%s</b>" % esc(det["deadline"]))
    if det.get("procedure"):
        lines.append("\U0001F4CB %s" % esc(det["procedure"]))
    if det.get("cpv"):
        lines.append("\U0001F3F7 FPP: %s" % esc(det["cpv"][:90]))
    lines.append("\U0001F4C5 Publikuar: %s" % esc(item.get("date") or "-"))
    kw = list(dict.fromkeys(k for v in cats.values() for k in v))
    if kw:
        lines.append("\U0001F50E Pse: %s" % esc(", ".join(kw)[:150]))
    lines.append("")
    lines.append('\U0001F517 <a href="%s">Hape në e-Prokurimi</a>' % DETAIL_URL.format(id=item["id"]))
    return "\n".join(lines)


def remaining_text(delta):
    hours = int(delta.total_seconds() // 3600)
    if hours < 24:
        return "edhe %d orë" % max(hours, 1)
    days = hours // 24
    return "edhe %d ditë" % days if days > 1 else "edhe 1 ditë"

# ---------------------------------------------------------------- state

def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def load_config():
    cfg = dict(DEFAULT_CONFIG)
    cfg.update(load_json(CONFIG_PATH, {}))
    # Ne GitHub Actions / server: token-i dhe chat_id vijne nga variablat e ambientit (Secrets)
    if os.environ.get("TELEGRAM_TOKEN"):
        cfg["telegram_token"] = os.environ["TELEGRAM_TOKEN"].strip()
    if os.environ.get("TELEGRAM_CHAT_ID"):
        cfg["chat_id"] = os.environ["TELEGRAM_CHAT_ID"].strip()
    return cfg

# ---------------------------------------------------------------- main run

def run(cfg, dry_run=False, fetch=http_get, now=None, state=None):
    """Kontrolli i tendereve ne e-Prokurimi. Kthen numrin e tendereve te reja qe perputhen."""
    now = now or datetime.now()
    own_state = state is None
    if own_state:
        state = load_json(STATE_PATH, {})
    seen = set(state.get("seen", []))
    matches = state.get("matches", {})
    first_run = not state.get("first_run_done")
    types = tuple(cfg.get("notice_types") or ["B05"])

    page = fetch(LIST_URL, cfg)
    items = parse_list(page)
    if not items:
        raise RuntimeError("Lista e njoftimeve doli bosh - ndoshta faqja ndryshoi ose nuk u hap.")
    tenders = [it for it in items if it["type"].startswith(types)]
    new = [it for it in tenders if it["id"] not in seen]
    log("Lista: %d njoftime, %d tendera (%s), %d te rinj" % (len(items), len(tenders), "/".join(types), len(new)))

    found = []
    for it in new:
        title_cats = classify(it["title"], "", cfg)
        if first_run and not title_cats:
            # Ne nisje ka ~300 tendera ne liste: detajet merren vetem per ata qe perputhen me titull.
            seen.add(it["id"])
            continue
        # Per tenderet e rinj detajet (FPP, vlera, afati) merren per te gjithe, qe te kapen
        # edhe ata ku titulli s'e thote qarte por kodi FPP po.
        try:
            det = parse_detail(fetch(DETAIL_URL.format(id=it["id"]), cfg))
        except Exception as e:
            log("Detajet deshtuan per %s: %s" % (it["id"], e))
            if not title_cats:
                continue  # provo perseri ne kontrollin e ardhshem
            det = {}
        cats = classify(det.get("title") or it["title"], det.get("cpv", ""), cfg) or title_cats
        seen.add(it["id"])
        if not cats:
            continue
        dl = parse_deadline(det.get("deadline"))
        if first_run and dl and dl < now:
            continue  # ne nisje, mos dergo tendera qe kane skaduar
        found.append((it, det, cats))
        matches[it["id"]] = {
            "title": det.get("title") or it["title"], "buyer": det.get("buyer", ""),
            "deadline": det.get("deadline", ""), "value": det.get("value", ""),
            "cats": list(cats), "reminded": [],
        }

    if first_run:
        intro = ("✅ <b>Prokurimi Bot u ndez.</b> Tenderë të hapur që të përkasin nga 10 ditët e fundit: %d. "
                 "Tani e tutje të shkruaj sapo të dalë diçka e re." % len(found))
        if dry_run:
            log(intro)
        else:
            send(cfg, intro)

    for it, det, cats in found:
        msg = format_alert(it, det, cats, header="TENDER I HAPUR" if first_run else "TENDER I RI")
        if dry_run:
            log("\n" + msg + "\n")
            continue
        send(cfg, msg)
        if not first_run:
            for n in range(max(0, int(cfg.get("alert_repeats", 1)) - 1)):
                time.sleep(2)
                send(cfg, "\U0001F514 <b>%s</b> - %s (afati %s)" % (
                    "KUJTESË" if n else "TENDER I RI", esc((det.get("title") or it["title"])[:80]),
                    esc(det.get("deadline") or "-")))

    # kujtesat para afatit
    for tid, m in list(matches.items()):
        dl = parse_deadline(m.get("deadline"))
        if not dl:
            continue
        if dl < now - timedelta(days=2):
            matches.pop(tid, None)
            continue
        for d in sorted(cfg.get("deadline_reminders_days", [])):
            key = str(d)
            if key in m.get("reminded", []):
                continue
            if timedelta(0) < dl - now <= timedelta(days=d):
                if first_run:
                    # mesazhi i nisjes e tregon afatin; mos dergo kujtese menjehere pas tij
                    m.setdefault("reminded", []).extend(str(x) for x in cfg.get("deadline_reminders_days", []) if x >= d)
                    continue
                text = ("⏳ <b>KUJTESË: afati mbyllet %s</b>\n<b>%s</b>\n\U0001F3DB %s\n⏰ %s\n"
                        '\U0001F517 <a href="%s">Hape</a>') % (
                    remaining_text(dl - now), esc(m["title"]), esc(m.get("buyer")),
                    esc(m.get("deadline")), DETAIL_URL.format(id=tid))
                # shëno edhe kujtesat më të gjata si të dërguara, që të mos vijnë dy njëherësh
                for d2 in cfg.get("deadline_reminders_days", []):
                    if d2 >= d and str(d2) not in m.setdefault("reminded", []):
                        m["reminded"].append(str(d2))
                if dry_run:
                    log(text)
                else:
                    send(cfg, text)
                m.setdefault("reminded", []).append(key)

    # ruaj gjendjen (mbaj vetem ID-te qe jane ende ne liste + disa te fundit)
    current_ids = {it["id"] for it in items}
    seen = {s for s in seen if s in current_ids}
    state.update({"seen": sorted(seen), "matches": matches, "first_run_done": True,
                  "last_run": now.strftime("%Y-%m-%d %H:%M")})
    day = stats_for(state, now)
    day["checks"] = day.get("checks", 0) + 1
    day["new_tenders"] = day.get("new_tenders", 0) + (0 if first_run else len(new))
    day["matches"] = day.get("matches", 0) + (0 if first_run else len(found))
    if own_state and not dry_run:
        save_json(STATE_PATH, state)
    log("Perfundoi: %d tendera qe te perkasin." % len(found))
    return len(found)


# ---------------------------------------------------------------- grante / subvencione

CALL_RE = [
    r"thirrj", r"\bgrant", r"subvencion", r"skem\w* (e |te )?grant", r"(mbeshtetje|perkrahje)\w* financiare",
    r"\bfinancim", r"\bkonkurs", r"ftes\w* publike", r"open call", r"call for (proposal|application|expression|submission)",
    r"\bfunding", r"challenge fund", r"request for (offer|proposal|quotation)", r"\bfond\w* (per|i|e)\b",
    r"aplikim\w* (per|online)", r"\bapply\b",
]
CALL_EXCLUDE = [
    r"lista (e )?(perfundimtare|preliminare|perfituesve|fituesve)", r"\brezultat", r"vendim\w* per (perfitues|fitues)",
    r"pyetjet e shpeshta", r"\bfaq\b", r"\braport", r"perfituesit", r"anetar\w* (te|e) komision", r"vleresues",
]
GRANT_TAGS = {
    "TCC": [r"kultur", r"kreativ", r"\bart\b|\barti\b|artist", r"muzik", r"\bevent", r"festival", r"koncert", r"turiz",
            r"manifestim", r"audiovizuel", r"\bfilm", r"creative", r"culture", r"\brini|youth"],
    "AI": [r"digji?tal", r"\btik\b", r"\bict\b", r"inovacion", r"innovation", r"teknologji", r"technology", r"\bai\b",
           r"artificial", r"start-?up", r"softuer", r"software", r"\bdigital"],
    "BIZ": [r"nmvm", r"\bsme", r"biznes", r"ndermarrj", r"enterprise", r"business", r"kompani", r"eksport"],
}
GRANT_SKIP = [r"bujq", r"blegtor", r"fermer", r"pemetar", r"agri", r"pylltar", r"bletar", r"vreshtar", r"sport\w* (i |e )?(klub|federat)"]
GRANT_ICON = {"TCC": "\U0001F3A4 TCC", "AI": "\U0001F916 AI", "BIZ": "\U0001F3E2 Biznes"}

LINK_RE = re.compile(r"<a\s[^>]*?href\s*=\s*[\"']([^\"'#]+)[\"'][^>]*>(.*?)</a>", re.S | re.I)


def extract_links(page, base_url):
    out, seen = [], set()
    for href, inner in LINK_RE.findall(page or ""):
        text = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", inner))).strip()
        url = urllib.parse.urljoin(base_url, html.unescape(href.strip()))
        if not url.startswith("http"):
            continue
        if len(text) < 15:
            # p.sh. linqe te dokumenteve ku teksti eshte "Shkarko": perdor emrin e skedarit
            fname = urllib.parse.unquote(url.rstrip("/").split("/")[-1])
            fname = re.sub(r"\.(pdf|docx?|xlsx?)$", "", fname, flags=re.I).replace("-", " ").replace("_", " ")
            if len(fname) >= 15 and not re.fullmatch(r"[0-9A-F ]+", fname, re.I):
                text = fname
            else:
                continue
        if url in seen:
            continue
        seen.add(url)
        out.append((url, text[:250]))
    return out


def classify_grant(text, url=""):
    t = norm(text + " " + urllib.parse.unquote(url).replace("-", " ").replace("_", " "))
    if not any(re.search(r, t) for r in CALL_RE):
        return []
    if any(re.search(r, t) for r in CALL_EXCLUDE):
        return []
    tags = [k for k, pats in GRANT_TAGS.items() if any(re.search(r, t) for r in pats)]
    if not tags:
        return []
    if any(re.search(r, t) for r in GRANT_SKIP) and not ({"TCC", "AI"} & set(tags)):
        return []
    return tags


def run_grants(cfg, state, dry_run=False, fetch=http_get, now=None):
    now = now or datetime.now()
    g = state.setdefault("grants", {"seen": {}, "last": "", "recent": [], "broken": {}})
    last = g.get("last")
    if last:
        try:
            if now - datetime.strptime(last, "%Y-%m-%d %H:%M") < timedelta(hours=float(cfg.get("grants_every_hours", 3))):
                return 0
        except ValueError:
            pass
    g["last"] = now.strftime("%Y-%m-%d %H:%M")
    alerts, newly_broken, fixed = 0, [], []
    for src in cfg.get("grant_sources", []):
        name, url = src.get("name", src.get("url")), src.get("url")
        if not url:
            continue
        try:
            links = extract_links(fetch(url, cfg), url)
            if not links:
                raise RuntimeError("faqja nuk ka linqe")
        except Exception as e:
            log("Grante: %s nuk u hap: %s" % (name, e))
            cnt = g["broken"].get(url, 0) + 1
            g["broken"][url] = cnt
            if cnt == 3:
                newly_broken.append(name)
            continue
        if g["broken"].pop(url, 0) >= 3:
            fixed.append(name)
        known = g["seen"].get(url)
        current = [u for u, _ in links]
        if known is None:
            g["seen"][url] = current[-800:]  # vizita e pare: vetem mbaj mend, mos dergo
            log("Grante: %s - %d linqe te regjistruara" % (name, len(current)))
            continue
        known_set = set(known)
        for link, text in links:
            if link in known_set:
                continue
            tags = classify_grant(text, link)
            if not tags:
                continue
            alerts += 1
            msg = ("\U0001F4B0 <b>THIRRJE / GRANT I RI</b> - %s\n\n<b>%s</b>\n\U0001F3DB %s\n\U0001F517 <a href=\"%s\">Hape</a>"
                   % (" + ".join(GRANT_ICON[t] for t in tags), esc(text), esc(name), html.escape(link)))
            g["recent"] = ([{"date": now.strftime("%d.%m.%Y"), "text": text, "src": name, "url": link, "tags": tags}]
                           + g.get("recent", []))[:20]
            if dry_run:
                log(msg)
            else:
                send(cfg, msg)
                if int(cfg.get("alert_repeats", 1)) > 1:
                    time.sleep(2)
                    send(cfg, "\U0001F514 <b>GRANT I RI</b> - %s" % esc(text[:90]))
        g["seen"][url] = (known + [u for u in current if u not in known_set])[-800:]
    if newly_broken and not dry_run:
        send(cfg, "⚠️ Këto faqe grantesh nuk po hapen (mund të kenë ndryshuar adresë): %s" % esc(", ".join(newly_broken)))
    if fixed and not dry_run:
        send(cfg, "✅ U rikthyen: %s" % esc(", ".join(fixed)))
    stats_for(state, now)["grant_alerts"] = stats_for(state, now).get("grant_alerts", 0) + alerts
    return alerts

# ---------------------------------------------------------------- statistika, mesazhi ditor, komandat

def stats_for(state, when):
    st = state.setdefault("stats", {})
    key = when.strftime("%Y-%m-%d")
    for k in sorted(st)[:-10]:
        st.pop(k, None)
    return st.setdefault(key, {})


def open_matches(state, now):
    out = []
    for tid, m in state.get("matches", {}).items():
        dl = parse_deadline(m.get("deadline"))
        if dl and dl > now:
            out.append((dl, tid, m))
    return sorted(out)


def status_text(state, now):
    today = stats_for(state, now)
    y = state.get("stats", {}).get((now - timedelta(days=1)).strftime("%Y-%m-%d"), {})
    g = state.get("grants", {})
    broken = [u for u, c in g.get("broken", {}).items() if c >= 3]
    lines = [
        "✅ <b>Boti punon</b>",
        "Kontrolli i fundit: %s" % esc(state.get("last_run", "-")),
        "Sot: %d kontrolle, %d tenderë të rinj të shqyrtuar, %d që të përkasin, %d grante të reja"
        % (today.get("checks", 0), today.get("new_tenders", 0), today.get("matches", 0), today.get("grant_alerts", 0)),
        "Dje: %d kontrolle, %d tenderë të rinj, %d që të përkasin"
        % (y.get("checks", 0), y.get("new_tenders", 0), y.get("matches", 0)),
        "Tenderë të hapur që i ndjek: %d (shkruaj /tenderet)" % len(open_matches(state, now)),
        "Faqe grantesh: %d, kontrolli i fundit %s" % (len(g.get("seen", {})), esc(g.get("last", "-"))),
    ]
    if state.get("fail_count", 0):
        lines.append("⚠️ e-Prokurimi nuk u hap në %d kontrollet e fundit" % state["fail_count"])
    if broken:
        lines.append("⚠️ Faqe grantesh që nuk hapen: %d" % len(broken))
    return "\n".join(lines)


def tenders_text(state, now):
    items = open_matches(state, now)
    if not items:
        return "Asnjë tender i hapur që të përket për momentin."
    lines = ["<b>Tenderët e hapur që të përkasin (%d)</b>" % len(items)]
    for dl, tid, m in items[:25]:
        cats = " ".join(ICON.get(c, "") for c in m.get("cats", []))
        lines.append('%s <a href="%s">%s</a> - %s, afati %s%s' % (
            cats, DETAIL_URL.format(id=tid), esc(m["title"][:70]), esc(m.get("buyer", "")[:40]),
            esc(m.get("deadline", "")), (", %s €" % esc(m["value"])) if m.get("value") else ""))
    return "\n".join(lines)


def grants_text(state):
    rec = state.get("grants", {}).get("recent", [])
    if not rec:
        return "Ende asnjë grant i ri (boti njofton vetëm për thirrjet që dalin pas ndezjes)."
    return "<b>Grantet e fundit</b>\n" + "\n".join(
        '%s <a href="%s">%s</a> (%s)' % (esc(r["date"]), html.escape(r["url"]), esc(r["text"][:80]), esc(r["src"])) for r in rec[:15])


def handle_commands(cfg, state, now):
    if not cfg.get("telegram_token") or not cfg.get("chat_id"):
        return
    try:
        res = telegram(cfg, "getUpdates", {"offset": state.get("tg_offset", 0), "timeout": 0})
    except Exception as e:
        log("Komandat: %s" % e)
        return
    for u in res.get("result", []):
        state["tg_offset"] = u["update_id"] + 1
        msg = u.get("message") or {}
        if str(msg.get("chat", {}).get("id")) != str(cfg["chat_id"]):
            continue
        cmd = (msg.get("text") or "").strip().split("@")[0].lower()
        if cmd in ("/status", "status", "a po punon"):
            send(cfg, status_text(state, now))
        elif cmd in ("/tenderet", "tenderet"):
            send(cfg, tenders_text(state, now))
        elif cmd in ("/grantet", "grantet"):
            send(cfg, grants_text(state))
        elif cmd in ("/start", "/help", "ndihme"):
            send(cfg, "Komandat: /status - a po punon boti, /tenderet - tenderët e hapur, /grantet - grantet e fundit.\n"
                      "Përgjigjja vjen brenda 10 minutave (në kontrollin e ardhshëm).")


def heartbeat(cfg, state, now):
    hour = cfg.get("heartbeat_hour")
    if hour is None or now.hour < int(hour):
        return
    today = now.strftime("%Y-%m-%d")
    if state.get("last_heartbeat") == today:
        return
    state["last_heartbeat"] = today
    send(cfg, "☀️ " + status_text(state, now))


def run_all(cfg, dry_run=False, fetch=http_get, now=None):
    now = now or datetime.now()
    state = load_json(STATE_PATH, {})
    try:
        run(cfg, dry_run=dry_run, fetch=fetch, now=now, state=state)
        if state.get("fail_count", 0) >= 6 and not dry_run:
            send(cfg, "✅ e-Prokurimi u hap përsëri, boti vazhdon normalisht.")
        state["fail_count"] = 0
    except Exception as e:
        state["fail_count"] = state.get("fail_count", 0) + 1
        stats_for(state, now)["errors"] = stats_for(state, now).get("errors", 0) + 1
        log("GABIM te tenderet: %r" % e)
        if state["fail_count"] == 6 and not dry_run:
            send(cfg, "⚠️ Boti nuk po e hap e-Prokurimin prej rreth 1 ore. Kontrollo internetin; "
                      "do të të njoftoj kur të rregullohet.")
    try:
        run_grants(cfg, state, dry_run=dry_run, fetch=fetch, now=now)
    except Exception as e:
        log("GABIM te grantet: %r" % e)
    if not dry_run:
        handle_commands(cfg, state, now)
        heartbeat(cfg, state, now)
        save_json(STATE_PATH, state)

# ---------------------------------------------------------------- setup

def setup():
    cfg = load_config()
    print("\n=== Prokurimi Bot - konfigurimi ===\n")
    print("1) Ne Telegram hap @BotFather, shkruaj /newbot dhe kopjo token-in qe te jep.")
    if cfg.get("telegram_token"):
        print("   (Ke nje token te ruajtur - shtyp vetem Enter per ta mbajtur.)")
    token = input("   Ngjite token-in ketu: ").strip()
    changed = bool(token) and token != cfg.get("telegram_token")
    if token:
        cfg["telegram_token"] = token
    if not cfg.get("telegram_token"):
        print("   Nuk dhe token.")
        sys.exit(1)
    try:
        me = telegram(cfg, "getMe", {})
    except Exception as e:
        me = {"ok": False, "error": str(e)}
    if not me.get("ok"):
        print("   Token-i nuk funksionon: %s" % me)
        sys.exit(1)
    uname = me["result"].get("username")
    if cfg.get("chat_id") and not changed:
        save_json(CONFIG_PATH, cfg)
        print("   Boti @%s eshte i lidhur tashme (chat_id %s)." % (uname, cfg["chat_id"]))
        return
    print("\n2) Hap botin tend @%s ne Telegram dhe shtyp START (ose shkruaj /start)." % uname)
    input("   Pasi ta besh, shtyp Enter ketu...")
    chat_id = None
    for _ in range(10):
        upd = telegram(cfg, "getUpdates", {})
        for u in reversed(upd.get("result", [])):
            msg = u.get("message") or u.get("channel_post") or {}
            if msg.get("chat", {}).get("id"):
                chat_id = msg["chat"]["id"]
                break
        if chat_id:
            break
        time.sleep(3)
    if not chat_id:
        print("   Nuk e gjeta bisedën. Sigurohu qe e shtype START te boti dhe provo perseri.")
        sys.exit(1)
    cfg["chat_id"] = str(chat_id)
    save_json(CONFIG_PATH, cfg)
    send(cfg, "✅ Prokurimi Bot eshte lidhur. Do te te njoftoj per tenderet e TCC dhe AI.")
    print("\n   Gati! Te erdhi mesazh prove ne Telegram. chat_id = %s\n" % chat_id)


def main():
    args = sys.argv[1:]
    if "--pythonw" in args:
        p = os.path.join(os.path.dirname(sys.executable), "pythonw.exe")
        print(p if os.path.exists(p) else sys.executable)
        return
    if "--setup" in args:
        setup()
        return
    cfg = load_config()
    if "--test" in args:
        ok = send(cfg, "\U0001F514 Prove nga Prokurimi Bot - njoftimet funksionojne.")
        print("U dergua." if ok else "Nuk u dergua - shiko bot.log")
        return
    try:
        run_all(cfg, dry_run="--dry-run" in args)
    except Exception as e:
        log("GABIM: %r" % e)
        sys.exit(1)


if __name__ == "__main__":
    main()
