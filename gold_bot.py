# -*- coding: utf-8 -*-
"""
ربات تلگرام: ساخت خودکار تصویر قیمت لحظه‌ای طلا و ارسال به کانال.

اجرا:
    pip install -r requirements.txt
    python gold_bot.py            # اجرای دائمی (ارسال هر N دقیقه)
    python gold_bot.py --once     # فقط یک‌بار ارسال
    python gold_bot.py --preview  # فقط ساخت عکس preview.png (بدون ارسال)
"""
import io, os, sys, socket, json, time, random, shlex, logging
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
        if r.status_code in (401, 403):
            raise RuntimeError("دسترسی رد شد (توکن منقضی شده). cURL تازه را در request.txt بگذارید.")
        r.raise_for_status()
        data = r.json()
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

def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
    if "--preview" in sys.argv:
        data = render(fetch_prices()).read()
        open("preview.png", "wb").write(data)
        print("preview.png ساخته شد"); return
    if "--once" in sys.argv:
        if "--windowed" in sys.argv and not in_window(datetime.now(TZ)):
            print("خارج از ساعت کاری؛ ارسال نشد."); return
        try:
            run_once(None); print("ارسال شد ✔")
        except Exception as e:
            print("خطا:", safe(e)); sys.exit(1)
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
