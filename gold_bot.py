# -*- coding: utf-8 -*-
"""
ربات تلگرام: ساخت خودکار تصویر قیمت لحظه‌ای طلا و ارسال به کانال.

اجرا:
    pip install -r requirements.txt
    python gold_bot.py            # اجرای دائمی (ارسال هر N دقیقه)
    python gold_bot.py --once     # فقط یک‌بار ارسال
    python gold_bot.py --preview  # فقط ساخت عکس preview.png (بدون ارسال)
    python gold_bot.py --loop 340 # روی سرور: ارسال دقیق هر N دقیقه تا ۳۴۰ دقیقه
"""
import io, os, sys, socket, json, base64, time, random, shlex, logging
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import requests
import jdatetime
from PIL import Image, ImageDraw, ImageFont, ImageFilter, features

# ───────────────────────── تنظیمات ─────────────────────────
def load_env(paths=(".env", "settings.txt")):
    for path in paths:
        if os.path.exists(path):
            for line in open(path, encoding="utf-8-sig"):
                line = line.split("#")[0].strip() if "=" in line else ""
                if line:
                    k, v = line.split("=", 1)
                    os.environ.setdefault(k.strip(), v.strip())
load_env()

BOT_TOKEN   = os.getenv("BOT_TOKEN", "")
CHANNEL_ID  = os.getenv("CHANNEL_ID", "")
INTERVAL    = int(os.getenv("INTERVAL_MINUTES", "10"))
BRAND_NAME  = os.getenv("BRAND_NAME", "وهان زر")
BRAND_SLOG  = os.getenv("BRAND_SLOGAN", "تجربه لذت‌بخش خرید")
FOOTER_TEXT = os.getenv("FOOTER_TEXT", "")
PRICE_API   = os.getenv("PRICE_API_URL", "")
START_HOUR  = int(os.getenv("START_HOUR", "10"))   # شروع ارسال (وقت تهران)
END_HOUR    = int(os.getenv("END_HOUR", "20"))     # پایان ارسال؛ برای تمام روز START_HOUR=0 و END_HOUR=24
PROXY_URL   = os.getenv("PROXY_URL", "")          # فقط برای اتصال به تلگرام، مثل socks5h://127.0.0.1:10808
DEMO        = os.getenv("DEMO", "0") == "1"
TZ          = ZoneInfo("Asia/Tehran")
ABSHODE_DIVISOR = float(os.getenv("ABSHODE_DIVISOR", "4.3318"))   # مثلاً 4.3318 اگر قیمت پنل مثقالی بود

FONT_BOLD = "fonts/Parastoo-Bold.ttf"
FONT_REG  = "fonts/Parastoo-Regular.ttf"
LOGO_PATH = "logo.png"   # اختیاری: لوگوی شما (مربعی، PNG)

# عنوان آیتم‌ها به ترتیب نمایش (تطبیق با عنوان محصول در پنل، بدون حساسیت به فاصله/نیم‌فاصله/«آ»)
ITEMS = [
    "ابشده نقد فردایی",
    "آبشده نقد پسفردایی",
    "تمام سکه ۸۶",
    "تمام سکه تاریخ پایین",
    "نیم سکه ۸۶",
    "ربع سکه ۸۶",
]

def unit_label(key, p):
    u = (p or {}).get("unit")
    if u is None:
        u = "gram" if key.startswith("ابشده") else "number"
    return "قیمت هر گرم" if u == "gram" else "قیمت هر عدد"

def norm(t):
    t = str(t).replace("ي", "ی").replace("ك", "ک").replace("آ", "ا").replace("\u200c", "")
    t = t.translate(str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789"))
    return "".join(t.split())

# ───────────────────── دریافت قیمت‌ها ─────────────────────
def _to_int(v):
    try:
        v = int(float(v))
        return v if v > 0 else None      # -1 یعنی قیمت غیرفعال
    except (TypeError, ValueError):
        return None

def parse_curl(path="request.txt"):
    """خواندن آدرس/هدرها/توکن از متنی که با Copy as cURL (bash) کپی شده."""
    txt = open(path, encoding="utf-8-sig").read().strip()
    if '^"' in txt:                                   # فرمت cmd ویندوز
        txt = (txt.replace("^\\^\"", "\x00")             # ^\^"  → کوتیشن داخلی
                  .replace("^\r\n", " ").replace("^\n", " ")  # ادامه‌ی خط
                  .replace('^"', '"').replace("^^", "^").replace("^%", "%")
                  .replace("\x00", '\\"'))
    else:                                              # فرمت bash
        txt = txt.replace("\\\r\n", " ").replace("\\\n", " ")
    parts = shlex.split(txt)
    url, method, body, headers = None, None, None, {}
    skip = {"accept-encoding", "content-length", "host", "connection"}
    i = 1 if parts and parts[0] == "curl" else 0
    while i < len(parts):
        a = parts[i]
        nxt = parts[i + 1] if i + 1 < len(parts) else ""
        if a in ("-H", "--header"):
            k, _, v = nxt.partition(":")
            if k.strip().lower() not in skip:
                headers[k.strip()] = v.strip()
            i += 2
        elif a in ("-b", "--cookie"):
            headers["Cookie"] = nxt; i += 2
        elif a in ("-X", "--request"):
            method = nxt.upper(); i += 2
        elif a in ("--data-raw", "--data", "-d", "--data-binary"):
            body = nxt; i += 2
        elif a.startswith("http"):
            url = a; i += 1
        else:
            i += 1
    if url and url.split("?")[0].lower().endswith((".js", ".css", ".png", ".jpg", ".svg", ".woff", ".woff2", ".html", ".ico")):
        raise RuntimeError("request.txt مربوط به یک فایل ظاهری سایت است (js/css/عکس)، نه قیمت‌ها. "
                           "درخواستی را کپی کنید که جوابش JSON و شامل products و buy_price است.")
    if not url:
        raise RuntimeError("آدرس در request.txt پیدا نشد؛ دوباره Copy as cURL (bash) را بزنید.")
    return url, method or ("POST" if body else "GET"), headers, body

class AuthError(RuntimeError):
    """توکن ورود پنل منقضی/نامعتبر است."""

def fetch_prices():
    if os.getenv("REQUEST_CURL"):                       # روی سرور: cURL از Secret خوانده می‌شود
        open("request.txt", "w", encoding="utf-8").write(os.environ["REQUEST_CURL"])
    """
    خروجی: {norm(عنوان): {"sell": عدد|None, "buy": عدد|None}}
    sell = «فروش به شما» (قیمتی که مشتری می‌خرد = buy_price پنل)
    buy  = «خرید از شما» (قیمتی که مشتری می‌فروشد = sell_price پنل)
    """
    if DEMO:
        base = [26_265_000, 26_266_000, 269_100_000, 258_300_000, 142_300_000, 76_100_000]
        out = {}
        for t, v in zip(ITEMS, base):
            v = round(v + random.randint(-30, 30) * (v // 100_000), -3)
            out[norm(t)] = {"sell": v, "buy": round(v - v * 0.0022, -3)}
        return out

    if not PRICE_API and not os.path.exists("request.txt"):
        raise RuntimeError("فایل request.txt پیدا نشد. راهنمای README (بخش ۴) را ببینید.")

    if PRICE_API.startswith("file:"):                       # برای تست آفلاین
        data = json.load(open(PRICE_API[5:], encoding="utf-8"))
    elif os.path.exists("request.txt"):                     # روش ساده: cURL کپی‌شده از مرورگر
        url, method, headers, body = parse_curl("request.txt")
        r = requests.request(method, url, headers=headers, data=body, timeout=20)
        if r.status_code in (401, 403, 419):
            raise AuthError(f"پنل دسترسی را رد کرد (HTTP {r.status_code}): توکن ورود منقضی شده؛ "
                            "cURL تازه‌ی درخواست products را در Secret به نام REQUEST_CURL بگذارید.")
        if r.status_code >= 400:
            raise RuntimeError(f"پنل خطا داد: HTTP {r.status_code}")
        try:
            data = r.json()
        except ValueError:
            raise AuthError(f"پنل به‌جای قیمت‌ها صفحه‌ی دیگری داد (HTTP {r.status_code}, "
                            f"{r.headers.get('content-type','?')}); احتمالاً توکن ورود منقضی شده.")
    else:
        headers = {"Accept": "application/json", "User-Agent": "Mozilla/5.0"}
        if os.getenv("PRICE_API_AUTH"):   headers["Authorization"] = os.getenv("PRICE_API_AUTH")
        if os.getenv("PRICE_API_COOKIE"): headers["Cookie"] = os.getenv("PRICE_API_COOKIE")
        r = requests.get(PRICE_API, headers=headers, timeout=20)
        r.raise_for_status()
        data = r.json()

    cats = data["data"] if isinstance(data, dict) and "data" in data else data
    found = {}
    for cat in cats:
        for p in cat.get("products", []):
            if p.get("is_active", True):
                k = norm(p["title"])
                div = ABSHODE_DIVISOR if k.startswith("ابشده") else 1
                sell = _to_int(p.get("buy_price")) if p.get("is_buy_active", True) else None
                buy  = _to_int(p.get("sell_price")) if p.get("is_sell_active", True) else None
                found[k] = {"unit": p.get("unit"),
                            "sell": int(round(sell / div, -3)) if sell else None,
                            "buy":  int(round(buy / div, -3)) if buy else None}
    missing = [t for t in ITEMS if norm(t) not in found]
    if missing:
        logging.warning("این آیتم‌ها در پنل پیدا نشدند: %s", missing)
    return found

# ───────────────────── متن فارسی ─────────────────────
HAS_RAQM = features.check("raqm")
if not HAS_RAQM:
    import arabic_reshaper
    from bidi.algorithm import get_display

_fonts = {}
def font(path, size):
    key = (path, size)
    if key not in _fonts:
        try:
            _fonts[key] = ImageFont.truetype(path, size)
        except OSError:
            logging.warning("فونت %s پیدا نشد؛ از فونت جایگزین استفاده می‌شود.", path)
            fb = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
            _fonts[key] = ImageFont.truetype(fb, size)
    return _fonts[key]

def fa_digits(s):
    return str(s).translate(str.maketrans("0123456789,", "۰۱۲۳۴۵۶۷۸۹,"))

def money(n):
    return fa_digits(f"{int(n):,}")

def draw_text(d, xy, text, f, fill, anchor="rm"):
    """رسم متن فارسی (راست‌به‌چپ) با شکل‌دهی صحیح حروف."""
    if HAS_RAQM:
        d.text(xy, text, font=f, fill=fill, anchor=anchor, direction="rtl", language="fa")
    else:
        t = get_display(arabic_reshaper.reshape(text), base_dir="R")
        d.text(xy, t, font=f, fill=fill, anchor=anchor)

# ───────────────────── طراحی تصویر ─────────────────────
W = 1080
PAD = 56
HEADER_H = 330
ROW_H, ROW_GAP = 150, 22
FOOTER_H = 130

BG_TOP, BG_BOT = (12, 10, 8), (33, 24, 12)
GOLD   = (244, 190, 80)
GOLD_D = (176, 126, 38)
WHITE  = (246, 240, 228)
MUTED  = (165, 152, 128)
UP, DOWN = (92, 214, 140), (240, 98, 98)

def gradient(w, h, top, bot):
    img = Image.new("RGB", (w, h))
    px = ImageDraw.Draw(img)
    for y in range(h):
        t = y / (h - 1)
        px.line([(0, y), (w, y)], fill=tuple(int(top[i] + (bot[i] - top[i]) * t) for i in range(3)))
    return img

def glow(img, center, radius, color, alpha):
    layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(layer).ellipse(
        [center[0]-radius, center[1]-radius, center[0]+radius, center[1]+radius], fill=color + (alpha,))
    layer = layer.filter(ImageFilter.GaussianBlur(radius * 0.55))
    img.paste(layer, (0, 0), layer)

def triangle(d, cx, cy, up, color, s=11):
    pts = [(cx, cy-s), (cx-s, cy+s*0.8), (cx+s, cy+s*0.8)] if up else \
          [(cx, cy+s), (cx-s, cy-s*0.8), (cx+s, cy-s*0.8)]
    d.polygon(pts, fill=color)

def render(prices, prev=None, now=None):
    now = now or datetime.now(TZ)
    n = len(ITEMS)
    H = HEADER_H + n * (ROW_H + ROW_GAP) + FOOTER_H
    img = gradient(W, H, BG_TOP, BG_BOT).convert("RGBA")
    glow(img, (W - 150, 120), 360, (255, 190, 70), 70)
    glow(img, (80, H - 60), 300, (255, 170, 50), 35)
    d = ImageDraw.Draw(img)

    # قاب نازک دور تصویر
    d.rounded_rectangle([18, 18, W-18, H-18], 34, outline=(*GOLD_D, 110), width=2)

    # ── هدر ──
    cx, cy, r = W - PAD - 100, 135, 100
    d.ellipse([cx-r-6, cy-r-6, cx+r+6, cy+r+6], outline=GOLD, width=3)
    d.ellipse([cx-r, cy-r, cx+r, cy+r], fill=(250, 246, 238))
    if os.path.exists(LOGO_PATH):
        logo = Image.open(LOGO_PATH).convert("RGBA")
        box = int(2 * r * 0.78)                      # حفظ نسبت تصویر، جا شدن داخل دایره
        logo.thumbnail((box, box), Image.LANCZOS)
        img.paste(logo, (cx - logo.width // 2, cy - logo.height // 2), logo)
    else:
        draw_text(d, (cx, cy-12), BRAND_NAME, font(FONT_BOLD, 34), (170, 112, 20), "mm")
        draw_text(d, (cx, cy+30), BRAND_SLOG, font(FONT_REG, 16), (120, 100, 70), "mm")

    tx = cx - r - 40
    draw_text(d, (tx, 100), "قیمت لحظه‌ای طلا و سکه", font(FONT_BOLD, 54), WHITE)
    j = jdatetime.datetime.fromgregorian(datetime=now)
    days = ["شنبه","یکشنبه","دوشنبه","سه‌شنبه","چهارشنبه","پنجشنبه","جمعه"]
    months = ["فروردین","اردیبهشت","خرداد","تیر","مرداد","شهریور","مهر","آبان","آذر","دی","بهمن","اسفند"]
    date_txt = f"{days[j.weekday()]} {fa_digits(j.day)} {months[j.month-1]} {fa_digits(j.year)}  |  ساعت {fa_digits(now.strftime('%H:%M'))}"
    draw_text(d, (tx, 170), date_txt, font(FONT_REG, 33), GOLD)

    # جداکننده طلایی
    for x in range(PAD, W - PAD):
        t = abs((x - W/2) / (W/2 - PAD))
        d.point((x, 262), fill=(*GOLD, int(255 * (1 - t**2))))

    # سرستون‌ها
    right_x = W - PAD - 36
    sell_x, buy_x = 460, 185
    hy = HEADER_H - 38
    draw_text(d, (sell_x, hy), "فروش به شما", font(FONT_REG, 29), MUTED, "mm")
    draw_text(d, (buy_x,  hy), "خرید از شما", font(FONT_REG, 29), MUTED, "mm")

    # ── ردیف‌ها ──
    y = HEADER_H
    for title in ITEMS:
        key = norm(title)
        card = [PAD, y, W - PAD, y + ROW_H]
        ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(ov).rounded_rectangle(card, 28, fill=(255, 255, 255, 16), outline=(*GOLD_D, 140), width=2)
        img.alpha_composite(ov)
        d = ImageDraw.Draw(img)
        d.rounded_rectangle([W - PAD - 8, y + 30, W - PAD - 2, y + ROW_H - 30], 4, fill=GOLD)  # خط تاکیدی

        mid = y + ROW_H // 2
        p = prices.get(key) or {}
        draw_text(d, (right_x, mid - 16), title, font(FONT_BOLD, 44), WHITE)
        draw_text(d, (right_x, mid + 32), unit_label(key, p), font(FONT_REG, 25), MUTED)
        for x, field, col in ((sell_x, "sell", GOLD), (buy_x, "buy", WHITE)):
            val = p.get(field)
            if val is None:
                draw_text(d, (x, mid), "—", font(FONT_BOLD, 42), MUTED, "mm")
                continue
            draw_text(d, (x, mid - 10), money(val), font(FONT_BOLD, 42), col, "mm")
            old = (prev or {}).get(key, {}).get(field)     # تغییر نسبت به ارسال قبلی
            if old is not None and val != old:
                diff = val - old
                c = UP if diff > 0 else DOWN
                triangle(d, x - 52, mid + 36, diff > 0, c, 9)
                draw_text(d, (x - 30, mid + 36), money(abs(diff)), font(FONT_REG, 22), c, "lm")
        y += ROW_H + ROW_GAP

    # ── فوتر ──
    draw_text(d, (W//2, H - 70), "قیمت‌ها به تومان می‌باشد و ممکن است لحظه‌ای تغییر کند", font(FONT_REG, 26), MUTED, "mm")
    if FOOTER_TEXT:
        d.text((W//2, H - 36), FOOTER_TEXT, font=font(FONT_BOLD, 26), fill=GOLD, anchor="mm")

    out = io.BytesIO()
    img.convert("RGB").save(out, "PNG", optimize=True)
    out.seek(0)
    return out

# ───────────────────── ارسال به تلگرام ─────────────────────
def send_photo(png, caption=""):
    r = requests.post(
        f"https://api.telegram.org/bot{BOT_TOKEN}/sendPhoto",
        data={"chat_id": CHANNEL_ID, "caption": caption},
        files={"photo": ("gold.png", png, "image/png")}, timeout=60,
        proxies={"http": PROXY_URL, "https": PROXY_URL} if PROXY_URL else None)
    r.raise_for_status()

def safe(e):
    msg = str(e)
    return msg.replace(BOT_TOKEN, "XXX") if BOT_TOKEN else msg

def run_once(prev):
    prices = fetch_prices()
    png = render(prices, prev)
    send_photo(png)
    return prices

def in_window(now):
    end = 24 if END_HOUR in (0, 24) else END_HOUR
    return START_HOUR <= now.hour < end

def next_start(now):
    t = now.replace(hour=START_HOUR, minute=0, second=0, microsecond=0)
    return t if t > now else t + timedelta(days=1)

def single_instance():
    """جلوگیری از اجرای هم‌زمان دو نسخه (ارسال تکراری)."""
    global _lock
    _lock = socket.socket()
    try:
        _lock.bind(("127.0.0.1", 47653))
    except OSError:
        print("ربات از قبل در حال اجراست."); sys.exit(0)

def gh(level, msg):
    """نمایش خطا/هشدار در صفحه‌ی Actions گیت‌هاب."""
    if os.getenv("GITHUB_ACTIONS"):
        print(f"::{level}::" + safe(msg).replace("%", "%25").replace("\n", "%0A"), flush=True)
    else:
        print(safe(msg), flush=True)

def next_slot(now):
    """نوبت بعدی ارسال، روی مضرب‌های INTERVAL دقیقه (مثلاً ۱۰:۰۰، ۱۰:۱۰، ...)."""
    base = now.replace(second=0, microsecond=0)
    m = (base.minute // INTERVAL + 1) * INTERVAL
    return base.replace(minute=0) + timedelta(minutes=m)

def dispatch_next_run():
    """درخواست اجرای بعدی workflow (برای ادامه‌ی بی‌وقفه بعد از سقف ۶ ساعته‌ی گیت‌هاب)."""
    tok, repo = os.getenv("GITHUB_TOKEN"), os.getenv("GITHUB_REPOSITORY")
    wf, ref = os.getenv("GH_WORKFLOW_FILE", "gold.yml"), os.getenv("GITHUB_REF_NAME", "main")
    if not (tok and repo):
        return
    try:
        r = requests.post(f"https://api.github.com/repos/{repo}/actions/workflows/{wf}/dispatches",
                          headers={"Authorization": f"Bearer {tok}", "Accept": "application/vnd.github+json"},
                          json={"ref": ref}, timeout=20)
        print("اجرای بعدی درخواست شد." if r.status_code == 204 else f"درخواست اجرای بعدی ناموفق: {r.status_code}")
    except Exception as e:
        print("درخواست اجرای بعدی ناموفق:", e)

# ───────────── گفت‌وگو با مدیر در تلگرام (دریافت cURL تازه) ─────────────
ADMIN_ID = os.getenv("ADMIN_CHAT_ID", "").strip()   # اختیاری؛ اگر خالی باشد صاحب کانال مدیر است
ADMIN_IDS = set()
STORE_NAME = "panel_request.txt"
_upd_offset = None
_status = {"last_ok": None, "last_err": None}

def tg(method, files=None, **data):
    r = requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}", data=data, files=files, timeout=40,
                      proxies={"http": PROXY_URL, "https": PROXY_URL} if PROXY_URL else None)
    j = r.json()
    if not j.get("ok"):
        raise RuntimeError(f"Telegram {method}: {j.get('description')}")
    return j["result"]

def resolve_admins():
    """مدیر = ADMIN_CHAT_ID، یا اگر نبود، سازنده و ادمین‌های انسانی کانال."""
    global ADMIN_ID
    if ADMIN_ID:
        ADMIN_IDS.add(ADMIN_ID); return
    try:
        for m in tg("getChatAdministrators", chat_id=CHANNEL_ID):
            u = m.get("user", {})
            if u.get("is_bot"):
                continue
            ADMIN_IDS.add(str(u["id"]))
            if m.get("status") == "creator":
                ADMIN_ID = str(u["id"])
        if not ADMIN_ID and ADMIN_IDS:
            ADMIN_ID = sorted(ADMIN_IDS)[0]
        print(f"مدیرها از کانال پیدا شدند: {len(ADMIN_IDS)} نفر", flush=True)
    except Exception as e:
        print("پیدا کردن مدیر کانال ناموفق:", safe(e), flush=True)

def say(text):
    if ADMIN_ID:
        try: tg("sendMessage", chat_id=ADMIN_ID, text=text)
        except Exception as e: print("ارسال پیام به مدیر ناموفق:", safe(e))

def tg_download(file_id):
    path = tg("getFile", file_id=file_id)["file_path"]
    r = requests.get(f"https://api.telegram.org/file/bot{BOT_TOKEN}/{path}", timeout=40,
                     proxies={"http": PROXY_URL, "https": PROXY_URL} if PROXY_URL else None)
    r.raise_for_status()
    return r.content.decode("utf-8-sig", "replace")

def load_saved_curl():
    """cURL ذخیره‌شده را از پیام سنجاق‌شده‌ی چت مدیر با ربات می‌خواند."""
    global ADMIN_ID
    for cid in [ADMIN_ID] + sorted(ADMIN_IDS - {ADMIN_ID}):
        if not cid:
            continue
        try:
            pin = tg("getChat", chat_id=cid).get("pinned_message") or {}
            doc = pin.get("document") or {}
            if doc.get("file_name") == STORE_NAME:
                os.environ["REQUEST_CURL"] = tg_download(doc["file_id"])
                ADMIN_ID = cid
                print("cURL ذخیره‌شده از تلگرام خوانده شد.", flush=True)
                return True
        except Exception as e:
            print("خواندن cURL ذخیره‌شده ناموفق:", safe(e), flush=True)
    return False

def save_curl(text):
    m = tg("sendDocument", chat_id=ADMIN_ID, caption="🔐 درخواست پنل ذخیره شد. این پیام را از سنجاق برندارید.",
           files={"document": (STORE_NAME, text.encode("utf-8"), "text/plain")})
    try: tg("unpinAllChatMessages", chat_id=ADMIN_ID)
    except Exception: pass
    tg("pinChatMessage", chat_id=ADMIN_ID, message_id=m["message_id"], disable_notification=True)

def try_new_curl(text, who=None):
    old = os.environ.get("REQUEST_CURL")
    os.environ["REQUEST_CURL"] = text
    try:
        prices = fetch_prices()
        n = sum(1 for v in prices.values() if v.get("sell") or v.get("buy"))
        if not n:
            raise RuntimeError("قیمتی در جواب پیدا نشد؛ مطمئن شوید cURL مال درخواست products است.")
    except Exception as e:
        if old is not None: os.environ["REQUEST_CURL"] = old
        say("❌ این کد کار نکرد:\n" + safe(e)[:400])
        return False
    save_curl(text)
    say(f"✅ کد جدید ذخیره شد و کار می‌کند ({n} قیمت خوانده شد). ارسال‌ها ادامه پیدا می‌کند.")
    return True

def poll_admin():
    """پیام‌های مدیر را می‌خواند. اگر cURL جدید آمد و کار کرد، True برمی‌گرداند."""
    global _upd_offset, ADMIN_ID
    if not ADMIN_IDS:
        return False
    try:
        kw = {"timeout": 0, "allowed_updates": json.dumps(["message"])}
        if _upd_offset is not None: kw["offset"] = _upd_offset
        ups = tg("getUpdates", **kw)
    except Exception as e:
        print("خواندن پیام‌های تلگرام ناموفق:", safe(e), flush=True); return False
    parts, got, sender = [], False, None
    for u in ups:
        _upd_offset = u["update_id"] + 1
        m = u.get("message") or {}
        cid = str(m.get("chat", {}).get("id"))
        if m.get("chat", {}).get("type") != "private" or cid not in ADMIN_IDS:
            continue
        txt = m.get("text") or ""
        doc = m.get("document")
        if doc and doc.get("file_size", 0) < 200_000:
            try: txt = tg_download(doc["file_id"])
            except Exception as e: say("❌ فایل خوانده نشد: " + safe(e)[:200]); continue
        if txt.lstrip().lower().startswith("curl"):
            parts, sender = [txt], cid                       # شروع یک cURL تازه
        elif parts and not txt.startswith("/"):
            parts.append(txt)                   # تکه‌های بعدی وقتی تلگرام متن بلند را چند پیام کرده
        elif txt.startswith("/status"):
            say(f"آخرین ارسال موفق: {_status['last_ok'] or '—'}\nآخرین خطا: {_status['last_err'] or '—'}")
        elif txt.startswith("/start") or txt:
            say("سلام! وقتی لاگین پنل منقضی شد، متن «Copy as cURL (bash)» درخواست products را همین‌جا بفرستید "
                "(یا به‌صورت فایل txt). /status وضعیت را می‌گوید.")
    if parts:
        ADMIN_ID = sender or ADMIN_ID          # پیام‌ها و ذخیره در چت همان مدیری که کد را فرستاد
        got = try_new_curl("\n".join(parts))
    return got

def sleep_until(t):
    """تا زمان t صبر می‌کند و در این مدت هر دقیقه پیام‌های مدیر را چک می‌کند."""
    while True:
        poll_admin()
        left = (t - datetime.now(TZ)).total_seconds()
        if left <= 0:
            return
        time.sleep(min(left, 60))

GOOD_MORNING = os.getenv("GOOD_MORNING", "1") == "1"

# ───────────────────── محتوای متنوع کانال ─────────────────────
import content
ALERT_PCT  = float(os.getenv("ALERT_PCT", "0.5"))     # هشدار تغییر محسوس قیمت (درصد نسبت به نوبت قبل)
DATA_FILE  = "data/day.json"                          # قیمت باز و بسته‌ی روز (عمومی است، محرمانه نیست)
SCHEDULE   = [(12, 0, "tip"), (14, 0, "quiz"), (17, 0, "poll"),
              ((END_HOUR - 1) % 24, 60 - INTERVAL, "summary")]       # ساعت تهران
DAYS   = ["شنبه","یکشنبه","دوشنبه","سه‌شنبه","چهارشنبه","پنجشنبه","جمعه"]
MONTHS = ["فروردین","اردیبهشت","خرداد","تیر","مرداد","شهریور","مهر","آبان","آذر","دی","بهمن","اسفند"]

def fa_date(now):
    j = jdatetime.datetime.fromgregorian(datetime=now)
    return f"{DAYS[j.weekday()]} {fa_digits(j.day)} {MONTHS[j.month-1]} {fa_digits(j.year)}"

def foot(text):
    return text + (f"\n\n{FOOTER_TEXT}" if FOOTER_TEXT else "")

def post(method, what, **kw):
    try:
        tg(method, chat_id=CHANNEL_ID, **kw)
        print(f"{what} ارسال شد ✔", flush=True)
    except Exception as e:
        gh("warning", f"{what} ارسال نشد: {e}")

def in_slot(now, h, m):
    t = now.replace(hour=h, minute=m, second=0, microsecond=0)
    return t <= now < t + timedelta(minutes=INTERVAL)

def today_index(now, n):
    return now.date().toordinal() % n

# ── نگهداری قیمت باز/بسته‌ی روز ──
def load_data():
    try:
        return json.load(open(DATA_FILE, encoding="utf-8"))
    except Exception:
        return {}

_data = None
def data():
    global _data
    if _data is None:
        _data = load_data()
    return _data

def save_data(why):
    os.makedirs(os.path.dirname(DATA_FILE), exist_ok=True)
    raw = json.dumps(data(), ensure_ascii=False, indent=1)
    open(DATA_FILE, "w", encoding="utf-8").write(raw)
    tok, repo = os.getenv("GITHUB_TOKEN"), os.getenv("GITHUB_REPOSITORY")
    if not (tok and repo):
        return
    url = f"https://api.github.com/repos/{repo}/contents/{DATA_FILE}"
    h = {"Authorization": f"Bearer {tok}", "Accept": "application/vnd.github+json"}
    try:
        ref = os.getenv("GITHUB_REF_NAME", "main")
        cur = requests.get(url, headers=h, params={"ref": ref}, timeout=20)
        body = {"message": f"data: {why}", "branch": ref,
                "content": base64.b64encode(raw.encode("utf-8")).decode()}
        if cur.status_code == 200:
            body["sha"] = cur.json()["sha"]
        r = requests.put(url, headers=h, json=body, timeout=20)
        if r.status_code not in (200, 201):
            gh("warning", f"ذخیره‌ی {DATA_FILE} ناموفق: HTTP {r.status_code}")
    except Exception as e:
        gh("warning", f"ذخیره‌ی {DATA_FILE} ناموفق: {e}")

def record_open(prices, now):
    d = data()
    if (d.get("open") or {}).get("date") != now.date().isoformat():
        d["open"] = {"date": now.date().isoformat(), "prices": prices}
        save_data("open " + now.date().isoformat())

def change_lines(old, new):
    lines = []
    for title in ITEMS:
        k = norm(title)
        a = ((old or {}).get(k) or {}).get("sell")
        b = ((new or {}).get(k) or {}).get("sell")
        if not b:
            continue
        if not a:
            lines.append(f"▫️ {title}: {money(b)}")
            continue
        pct = (b - a) / a * 100
        sign = "🔺" if pct > 0.005 else ("🔻" if pct < -0.005 else "⚪️")
        pct_txt = fa_digits(f"{abs(pct):.2f}").replace(".", "٫")
        lines.append(f"{sign} {title}: {money(b)}  ({pct_txt}٪)")
    return lines

# ── پست‌ها ──
def send_good_morning(prices, now):
    text = (f"☀️ صبح بخیر\n\nامروز {fa_date(now)}\n\n"
            f"🌼 {BRAND_NAME} آماده‌ی خدمت‌رسانی به شماست.\n"
            f"قیمت لحظه‌ای طلا و سکه از ساعت {fa_digits(START_HOUR)} تا {fa_digits(END_HOUR % 24 or 24)} 👇")
    close = data().get("close") or {}
    if prices and close.get("date") and close["date"] < now.date().isoformat():
        lines = change_lines(close.get("prices"), prices)
        if lines:
            text += "\n\n📊 شروع امروز نسبت به پایان روز قبل:\n" + "\n".join(lines)
    post("sendMessage", "پیام صبح بخیر", text=foot(text))

def send_tip(now):
    title, body = content.TIPS[today_index(now, len(content.TIPS))]
    post("sendMessage", "نکته‌ی آموزشی", text=foot(f"💡 نکته‌ی امروز: {title}\n\n{body}"))

def send_quiz(now):
    q, opts, correct, why = content.QUIZZES[today_index(now, len(content.QUIZZES))]
    post("sendPoll", "مسابقه", question=f"🧠 مسابقه‌ی امروز: {q}",
         options=json.dumps([{"text": o} for o in opts], ensure_ascii=False),
         type="quiz", correct_option_id=correct, explanation=why, is_anonymous=True)

def send_poll(now):
    q, opts = content.POLLS[today_index(now, len(content.POLLS))]
    post("sendPoll", "نظرسنجی", question=f"📊 {q}",
         options=json.dumps([{"text": o} for o in opts], ensure_ascii=False), is_anonymous=True)

def send_summary(prices, now):
    op = data().get("open") or {}
    base = op.get("prices") if op.get("date") == now.date().isoformat() else None
    lines = change_lines(base, prices)
    head = "🌙 خلاصه‌ی قیمت‌های امروز" + ("، نسبت به شروع روز" if base else "")
    text = (f"{head}\n{fa_date(now)}\n\n" + "\n".join(lines) +
            f"\n\nفردا ساعت {fa_digits(START_HOUR)} با قیمت‌های جدید در خدمت شما هستیم. شب خوش 🌙")
    post("sendMessage", "خلاصه‌ی روز", text=foot(text))
    data()["close"] = {"date": now.date().isoformat(), "prices": prices}
    save_data("close " + now.date().isoformat())

def maybe_alert(prev, prices, now):
    if not prev or ALERT_PCT <= 0:
        return
    last = _status.get("last_alert")
    if last and now - last < timedelta(minutes=30):
        return
    moved = []
    for title in ITEMS:
        k = norm(title)
        a, b = (prev.get(k) or {}).get("sell"), (prices.get(k) or {}).get("sell")
        if a and b and abs(b - a) / a * 100 >= ALERT_PCT:
            moved.append(title)
    if moved:
        lines = [l for l in change_lines(prev, prices) if any(t in l for t in moved)]
        _status["last_alert"] = now
        post("sendMessage", "هشدار تغییر قیمت", text=foot("⚡️ تغییر محسوس قیمت در چند دقیقه‌ی اخیر\n\n" + "\n".join(lines)))

def before_photo(prices, now):
    record_open(prices, now)
    if GOOD_MORNING and not _status.get("gm") and in_slot(now, START_HOUR, 0):
        _status["gm"] = True
        send_good_morning(prices, now)
        time.sleep(3)

def after_photo(prev, prices, now):
    maybe_alert(prev, prices, now)
    for h, m, kind in SCHEDULE:
        key = f"done_{kind}"
        if _status.get(key) or not in_slot(now, h, m):
            continue
        _status[key] = True
        time.sleep(3)
        if kind == "tip":       send_tip(now)
        elif kind == "quiz":    send_quiz(now)
        elif kind == "poll":    send_poll(now)
        elif kind == "summary": send_summary(prices, now)

def run_loop(max_minutes):
    """برای سرور: داخل یک اجرا، سر هر INTERVAL دقیقه دقیقاً ارسال می‌کند."""
    deadline = datetime.now(TZ) + timedelta(minutes=max_minutes)
    resolve_admins()
    if not ADMIN_IDS:
        gh("warning", "مدیری پیدا نشد؛ دریافت کد جدید از تلگرام خاموش است.")
    load_saved_curl()
    now = datetime.now(TZ)
    if not in_window(now):
        start = next_start(now)
        if start > deadline - timedelta(minutes=30):
            poll_admin(); print("خارج از ساعت کاری؛ کاری برای انجام نیست."); return 0
        print("منتظر شروع ساعت کاری:", start.strftime("%H:%M"), flush=True)
        sleep_until(start)

    prev, fails, waiting_auth = None, 0, False
    while True:
        now = datetime.now(TZ)
        if not in_window(now):
            print("پایان ساعت کاری.", flush=True); return 0
        if waiting_auth:
            # منتظر کد جدید از مدیر؛ هر دقیقه چک می‌شود
            if poll_admin():
                waiting_auth = False
                continue
            if datetime.now(TZ) + timedelta(minutes=1) > deadline:
                dispatch_next_run(); return 0
            time.sleep(60); continue
        for attempt in range(3):
            try:
                prices = fetch_prices()
                before_photo(prices, now)
                send_photo(render(prices, prev))
                try:
                    after_photo(prev, prices, now)
                except Exception as e:
                    gh("warning", f"محتوای اضافه ارسال نشد: {e}")
                prev = prices
                _status["last_ok"] = datetime.now(TZ).strftime("%H:%M")
                print(_status["last_ok"], "ارسال شد ✔", flush=True)
                fails = 0
                break
            except AuthError as e:
                _status["last_err"] = str(e)
                gh("warning", str(e))
                if not ADMIN_ID:
                    gh("error", str(e)); return 1
                say("⚠️ لاگین پنل منقضی شد و ارسال قیمت‌ها متوقف است.\n"
                    "پنل را باز کنید، F12 ← Network ← درخواست products ← Copy as cURL (bash) "
                    "و متنش را همین‌جا بفرستید. بلافاصله ادامه می‌دهم.")
                waiting_auth = True
                break
            except Exception as e:
                _status["last_err"] = safe(e)[:300]
                gh("warning", f"تلاش {attempt + 1} ناموفق: {e}")
                time.sleep(45)
        else:
            fails += 1
            if fails >= 6:
                msg = "یک ساعت است ارسال انجام نمی‌شود. آخرین خطا: " + (_status["last_err"] or "")
                gh("error", msg); say("⚠️ " + msg); return 1
        if waiting_auth:
            continue
        nxt = next_slot(datetime.now(TZ))
        if nxt > deadline:
            print("سقف زمان این اجرا رسید؛ اجرای بعدی ادامه می‌دهد.", flush=True)
            dispatch_next_run(); return 0
        sleep_until(nxt)

def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
    if "--preview" in sys.argv:
        data = render(fetch_prices()).read()
        open("preview.png", "wb").write(data)
        print("preview.png ساخته شد"); return
    if "--loop" in sys.argv:
        i = sys.argv.index("--loop")
        mins = int(sys.argv[i + 1]) if i + 1 < len(sys.argv) else 340
        sys.exit(run_loop(mins))
    if "--once" in sys.argv:
        if "--windowed" in sys.argv and not in_window(datetime.now(TZ)):
            print("خارج از ساعت کاری؛ ارسال نشد."); return
        try:
            run_once(None); print("ارسال شد ✔")
        except Exception as e:
            gh("error", f"خطا: {e}"); sys.exit(1)
        return

    single_instance()
    logging.info("ربات شروع شد؛ ساعت کاری %02d:00 تا %02d:00 (وقت تهران)", START_HOUR, END_HOUR % 24 if END_HOUR else 24)
    prev = None
    while True:
        now = datetime.now(TZ)
        if in_window(now):
            try:
                prev = run_once(prev)
                logging.info("ارسال شد ✔")
            except Exception as e:
                logging.error("خطا: %s", safe(e))
            time.sleep(INTERVAL * 60)
        else:
            nxt = next_start(now)
            logging.info("خارج از ساعت کاری؛ شروع بعدی %s", nxt.strftime("%Y-%m-%d %H:%M"))
            prev = None
            time.sleep(max(30, min((nxt - now).total_seconds(), 600)))

if __name__ == "__main__":
    main()
