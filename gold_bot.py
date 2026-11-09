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
import io, os, re, sys, socket, json, base64, hmac, hashlib, time, random, shlex, logging
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

LABELS = {"ابشده نقد فردایی": "آبشده فردایی", "آبشده نقد پسفردایی": "آبشده پس‌فردایی"}

def label(title):
    return LABELS.get(title, title)

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

# ── منبع قیمت: سایت وهان زر (Supabase) ──
PRICE_SOURCE = os.getenv("PRICE_SOURCE", "panel")          # site | panel
SITE_API     = os.getenv("SITE_API_URL", "")               # https://xxxx.supabase.co
SITE_KEY     = os.getenv("SITE_API_KEY", "")               # کلید عمومی (publishable)؛ محرمانه نیست
SITE_MAP = {"gold_farda": ("ابشده نقد فردایی", "gram"), "gold_pasfarda": ("آبشده نقد پسفردایی", "gram"),
            "emami": ("تمام سکه ۸۶", "number"), "emami_old": ("تمام سکه تاریخ پایین", "number"),
            "nim": ("نیم سکه ۸۶", "number"), "rob": ("ربع سکه ۸۶", "number")}

def fetch_site_prices():
    r = requests.post(f"{SITE_API.rstrip('/')}/rest/v1/rpc/channel_prices",
                      headers={"apikey": SITE_KEY, "Content-Type": "application/json"}, json={}, timeout=20)
    if r.status_code >= 400:
        raise RuntimeError(f"سایت خطا داد: HTTP {r.status_code}")
    d = r.json()
    if d.get("stale"):
        raise RuntimeError("قیمت‌های سایت به‌روز نیستند (فید قیمت سایت متوقف شده)؛ عکس ارسال نشد.")
    out = {}
    for code, (title, unit) in SITE_MAP.items():
        v = (d.get("items") or {}).get(code) or {}
        sell, buy = _to_int(v.get("sell")), _to_int(v.get("buy"))
        if sell or buy:
            out[norm(title)] = {"unit": unit, "sell": sell, "buy": buy}
    if not out:
        raise RuntimeError("سایت قیمتی برنگرداند.")
    return out

LAST_RAW = {}

def fetch_prices():
    if PRICE_SOURCE == "site" and not DEMO:
        return fetch_site_prices()
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
    if not isinstance(cats, list):
        raise RuntimeError("جواب پنل فهرست محصولات نیست؛ احتمالاً cURL مال درخواست products نیست.")
    found = {}
    LAST_RAW.clear()
    for cat in cats:
        for p in cat.get("products", []):
            if p.get("is_active", True):
                k = norm(p["title"])
                div = ABSHODE_DIVISOR if k.startswith("ابشده") else 1
                sell = _to_int(p.get("buy_price")) if p.get("is_buy_active", True) else None
                buy  = _to_int(p.get("sell_price")) if p.get("is_sell_active", True) else None
                LAST_RAW[k] = {"sell": sell, "buy": buy}          # قیمت خام پنل (آبشده مثقالی) برای سایت
                found[k] = {"unit": p.get("unit"),
                            "sell": int(round(sell / div, -3)) if sell else None,
                            "buy":  int(round(buy / div, -3)) if buy else None}
    # بدون هیچ قیمتی، عکس پر از «—» و خلاصه‌ی خالی ارسال نشود
    if not any(found.get(norm(t), {}).get("sell") or found.get(norm(t), {}).get("buy") for t in ITEMS):
        raise RuntimeError("پنل برای هیچ‌کدام از آیتم‌ها قیمت برنگرداند؛ عکس ارسال نشد.")
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

BG_TOP, BG_BOT = (14, 6, 8), (44, 10, 18)
GOLD   = (238, 72, 92)     # رنگ تأکید (قرمز یاقوتی)
GOLD_D = (150, 28, 48)
WHITE  = (246, 240, 228)
MUTED  = (178, 152, 158)
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

TRUST_TEXT = os.getenv("TRUST_TEXT", "")      # نشان‌های اعتماد تأییدشده، جدا با «،»
PANEL_BG   = (255, 255, 255, 14)
CARD_LINE  = (*GOLD_D, 120)

def _card(img, box, fill=PANEL_BG, outline=CARD_LINE, radius=26, width=2):
    ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(ov).rounded_rectangle(box, radius, fill=fill, outline=outline, width=width)
    img.alpha_composite(ov)
    return ImageDraw.Draw(img)

def _pill(img, cx, cy, text, f, fg, bg, pad_x=22, h=46):
    w = int(img_text_width(text, f)) + 2 * pad_x
    d = _card(img, [cx - w // 2, cy - h // 2, cx + w // 2, cy + h // 2], fill=bg, outline=None, radius=h // 2)
    draw_text(d, (cx, cy), text, f, fg, "mm")
    return d, w

def img_text_width(text, f):
    if not HAS_RAQM:
        text = get_display(arabic_reshaper.reshape(text), base_dir="R")
    return f.getlength(text)

def money_fa(n):
    return money(n).replace(",", "٬")

def pct_fa(a, b):
    pct = (b - a) / a * 100
    return fa_digits(f"{abs(pct):.2f}").replace(".", "٫") + "٪", pct > 0

def render(prices, prev=None, now=None):
    """تصویر قیمت: بخش آبشده (گرم + مظنه‌ی مثقال) و بخش سکه، با تغییر نسبت به مبنا (شروع امروز)."""
    now = now or datetime.now(TZ)
    gold = [t for t in ITEMS if label(t).startswith("آبشده")]
    coins = [t for t in ITEMS if t not in gold]
    HEAD, SEC, COLS, R1, R2, GAP, FOOT = 300, 74, 56, 172, 128, 16, 250
    H = (HEAD + COLS + (SEC + len(gold) * (R1 + GAP) if gold else 0)
         + (SEC + len(coins) * (R2 + GAP) if coins else 0) + FOOT)
    img = gradient(W, H, BG_TOP, BG_BOT).convert("RGBA")
    glow(img, (W - 120, 90), 380, (230, 40, 70), 60)
    glow(img, (60, H - 120), 320, (230, 40, 70), 30)
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([18, 18, W - 18, H - 18], 34, outline=(*GOLD_D, 110), width=2)

    # ── هدر: لوگو، عنوان، تاریخ، نشان به‌روزرسانی ──
    cx, cy, r = W - PAD - 92, 140, 92
    d.ellipse([cx - r - 7, cy - r - 7, cx + r + 7, cy + r + 7], outline=GOLD, width=3)
    d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=(250, 246, 238))
    if os.path.exists(LOGO_PATH):
        logo = Image.open(LOGO_PATH).convert("RGBA")
        box = int(2 * r * 0.78)
        logo.thumbnail((box, box), Image.LANCZOS)
        img.paste(logo, (cx - logo.width // 2, cy - logo.height // 2), logo)
    else:
        draw_text(d, (cx, cy), BRAND_NAME, font(FONT_BOLD, 34), (170, 112, 20), "mm")
    tx = cx - r - 38
    draw_text(d, (tx, 92), "نرخ لحظه‌ای آبشده و سکه", font(FONT_BOLD, 56), WHITE)
    draw_text(d, (tx, 158), f"{BRAND_NAME}  |  {fa_date(now)}", font(FONT_REG, 32), GOLD)
    upd = f"آخرین به‌روزرسانی  {fa_digits(now.strftime('%H:%M'))}"
    f_upd = font(FONT_BOLD, 28)
    pw = int(img_text_width(upd, f_upd)) + 74
    d = _card(img, [tx - pw, 204, tx, 252], fill=(92, 214, 140, 34), outline=(92, 214, 140, 150), radius=24)
    d.ellipse([tx - 38, 220, tx - 22, 236], fill=UP)
    draw_text(d, (tx - 50, 228), upd, f_upd, WHITE)
    for x in range(PAD, W - PAD):
        t = abs((x - W / 2) / (W / 2 - PAD))
        d.point((x, HEAD - 14), fill=(*GOLD, int(255 * (1 - t ** 2))))

    sell_x, buy_x, name_x = 470, 190, W - PAD - 34
    y = HEAD
    f_col = font(FONT_BOLD, 27)
    for x, txt in ((sell_x, "فروش به شما"), (buy_x, "خرید از شما")):
        d, _ = _pill(img, x, y + 22, txt, f_col, MUTED, (255, 255, 255, 18), h=42)
    y += COLS

    def section(y, title, sub):
        dd = ImageDraw.Draw(img)
        dd.rounded_rectangle([W - PAD - 10, y + 18, W - PAD, y + 54], 4, fill=GOLD)
        draw_text(dd, (W - PAD - 26, y + 36), title, font(FONT_BOLD, 38), GOLD)
        tw = img_text_width(title, font(FONT_BOLD, 38))
        draw_text(dd, (W - PAD - 46 - tw, y + 40), sub, font(FONT_REG, 26), MUTED)
        return y + SEC

    def row(y, title, h, mithqal):
        key = norm(title)
        p = prices.get(key) or {}
        dd = _card(img, [PAD, y, W - PAD, y + h])
        mid = y + h // 2
        top = mid - (24 if mithqal else 18)
        vy = top if mithqal else mid
        draw_text(dd, (name_x, top - 10), label(title), font(FONT_BOLD, 44 if mithqal else 40), WHITE)
        base = ((prev or {}).get(key) or {}).get("sell")
        if base and p.get("sell") and abs(p["sell"] - base) / base >= 0.00005:
            txt, up = pct_fa(base, p["sell"])
            col = UP if up else DOWN
            f_ch = font(FONT_BOLD, 25)
            cw = int(img_text_width(txt, f_ch)) + 62
            dd = _card(img, [name_x - cw, top + 26, name_x, top + 66], fill=(*col, 40), outline=None, radius=20)
            triangle(dd, name_x - 24, top + 46, up, col, 8)
            draw_text(dd, (name_x - 42, top + 46), txt, f_ch, col, "rm")
        else:
            draw_text(dd, (name_x, top + 46), unit_label(key, p), font(FONT_REG, 25), MUTED)
        raw = LAST_RAW.get(key) or {}
        for x, field, colr in ((sell_x, "sell", GOLD), (buy_x, "buy", WHITE)):
            val = p.get(field)
            if not val:
                draw_text(dd, (x, vy), "—", font(FONT_BOLD, 44), MUTED, "mm"); continue
            draw_text(dd, (x, vy), money_fa(val), font(FONT_BOLD, 46 if mithqal else 42), colr, "mm")
            if mithqal:
                m = raw.get(field) or round(val * ABSHODE_DIVISOR, -3)
                draw_text(dd, (x, top + 54), f"مثقال  {money_fa(m)}", font(FONT_REG, 27), MUTED, "mm")
        return y + h + GAP

    if gold:
        y = section(y, "طلای آبشده", "۱۸ عیار (۷۵۰)  •  قیمت هر گرم")
        for t in gold:
            y = row(y, t, R1, True)
    if coins:
        y = section(y, "سکه بهار آزادی", "قیمت هر عدد")
        for t in coins:
            y = row(y, t, R2, False)

    # ── فوتر: اعتماد و تماس ──
    fy = H - FOOT + 6
    d = _card(img, [PAD, fy, W - PAD, H - 92], fill=(*GOLD, 22), outline=(*GOLD, 150), radius=28)
    trust = [t.strip() for t in TRUST_TEXT.split("،") if t.strip()]
    if trust:
        draw_text(d, (W // 2, fy + 42), "   •   ".join(trust), font(FONT_BOLD, 28), GOLD, "mm")
    cy2, f_c = fy + (100 if trust else 75), font(FONT_BOLD, 34)
    phone = f"ثبت سفارش  {fa_digits(ORDER_PHONE)}" if ORDER_PHONE else ""
    link = f"t.me/{CHANNEL_ID[1:]}" if CHANNEL_ID.startswith("@") else ""
    if phone and link:
        draw_text(d, (W // 2 + 30, cy2), phone, f_c, WHITE, "lm")
        d.text((W // 2, cy2), "|", font=f_c, fill=MUTED, anchor="mm")
        d.text((W // 2 - 30, cy2), link, font=f_c, fill=WHITE, anchor="rm")
    elif phone or link:
        draw_text(d, (W // 2, cy2), phone or link, f_c, WHITE, "mm")
    draw_text(d, (W // 2, H - 56), "قیمت‌ها به تومان است  •  تغییرات نسبت به شروع امروز", font(FONT_REG, 25), MUTED, "mm")
    out = io.BytesIO()
    img.convert("RGB").save(out, "PNG", optimize=True)
    out.seek(0)
    return out

# ───────────────────── ارسال به تلگرام ─────────────────────
# ── رشد کانال: دکمه‌ی «ارسال برای دوستان» و لینک عضویت زیر پست‌ها ──
from urllib.parse import quote
SHARE_BUTTON = os.getenv("SHARE_BUTTON", "1") == "1"
ORDER_PHONE  = os.getenv("ORDER_PHONE", "")                   # شماره‌ی ثبت سفارش در کپشن
SITE_URL     = os.getenv("SITE_URL", "")                      # دکمه‌ی «خرید آنلاین»
CHANNEL_LINK = os.getenv("CHANNEL_LINK") or (f"https://t.me/{CHANNEL_ID.lstrip('@')}" if CHANNEL_ID.startswith("@") else "")
SHARE_TEXT = os.getenv("SHARE_TEXT", f"قیمت لحظه‌ای طلا، آبشده و سکه در کانال {BRAND_NAME} 👇")
PHOTO_CAPTION = os.getenv("PHOTO_CAPTION",
    f"📊 نرخ لحظه‌ای آبشده و سکه | {BRAND_NAME}"
    + (f"\n☎️ ثبت سفارش: {ORDER_PHONE} | تحویل حضوری با فاکتور" if ORDER_PHONE else "")
    + (f"\n🛒 خرید و فروش آنلاین با همین قیمت‌ها: {SITE_URL}" if SITE_URL else "")
    + (f"\n🔗 عضویت در کانال: {CHANNEL_LINK}" if CHANNEL_LINK else ""))

ADDRESS_TEXT = os.getenv("ADDRESS_TEXT", "")

def price_caption(prices, now):
    """کپشن متنی هر عکس: قیمت‌ها قابل جستجو و کپی، و در فهرست چت‌ها هم دیده می‌شوند."""
    fmt = lambda n: money(n).replace(",", "٬") if n else "—"
    lines = [f"📊 نرخ آبشده و سکه | {BRAND_NAME}",
             f"🕒 {fa_digits(now.strftime('%H:%M'))} | {fa_date(now)}  (تومان)", ""]
    for title in ITEMS:
        p = prices.get(norm(title)) or {}
        if not (p.get("sell") or p.get("buy")):
            continue
        name = label(title)
        lines.append(f"🔸 {name}" + (" (هر گرم ۱۸ عیار)" if name.startswith("آبشده") else ""))
        lines.append(f"     فروش به شما {fmt(p.get('sell'))} | خرید از شما {fmt(p.get('buy'))}")
        raw = LAST_RAW.get(norm(title)) or {}
        if name.startswith("آبشده") and raw.get("sell"):
            lines.append(f"     مظنه‌ی مثقال: {fmt(raw['sell'])}")
    lines.append("")
    if ORDER_PHONE:  lines.append(f"☎️ ثبت سفارش: {ORDER_PHONE} | تحویل حضوری با فاکتور و کد ری‌گیری")
    if ADDRESS_TEXT: lines.append(f"📍 {ADDRESS_TEXT}")
    if CHANNEL_LINK: lines.append(f"🔗 {CHANNEL_LINK}")
    return "\n".join(lines)[:1024]

def share_markup():
    if not ((SHARE_BUTTON and CHANNEL_LINK) or SITE_URL):
        return None
    if not (SHARE_BUTTON and CHANNEL_LINK):
        return json.dumps({"inline_keyboard": [[{"text": "🛒 خرید آنلاین", "url": SITE_URL}]]}, ensure_ascii=False)
    url = f"https://t.me/share/url?url={quote(CHANNEL_LINK)}&text={quote(SHARE_TEXT)}"
    row = [{"text": "📤 ارسال برای دوستان", "url": url}]
    if SITE_URL:
        row.insert(0, {"text": "🛒 خرید آنلاین", "url": SITE_URL})
    return json.dumps({"inline_keyboard": [row]}, ensure_ascii=False)

def send_photo(png, caption=None):
    data = {"chat_id": CHANNEL_ID, "caption": PHOTO_CAPTION if caption is None else caption}
    if share_markup():
        data["reply_markup"] = share_markup()
    r = requests.post(
        f"https://api.telegram.org/bot{BOT_TOKEN}/sendPhoto",
        data=data,
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

HOLIDAYS = {d.strip() for d in os.getenv("HOLIDAYS", "").split(",") if d.strip()}   # مثل 2026-11-20,2026-12-01

def closed_day(d):
    """جمعه و تعطیلات رسمی بازار بسته است."""
    return d.weekday() == 4 or d.isoformat() in HOLIDAYS

def in_window(now):
    end = 24 if END_HOUR in (0, 24) else END_HOUR
    return START_HOUR <= now.hour < end and not closed_day(now.date())

def next_start(now):
    t = now.replace(hour=START_HOUR, minute=0, second=0, microsecond=0)
    if t <= now:
        t += timedelta(days=1)
    while closed_day(t.date()):
        t += timedelta(days=1)
    return t

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

# ── ورود دوباره به پنل با کد پیامکی (بدون F12) ──
PANEL_MOBILE = os.getenv("PANEL_MOBILE", "").strip()
_otp = {"mobile": PANEL_MOBILE, "verify": None}
EN_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")

def _panel_auth(path, payload):
    """درخواست به auth/... پنل با همان هدرهای cURL ذخیره‌شده (بدون کوکی قدیمی)."""
    open("request.txt", "w", encoding="utf-8").write(os.environ["REQUEST_CURL"])
    url, _, headers, _ = parse_curl("request.txt")
    base = url.split("?")[0].rsplit("/products", 1)[0]
    h = {k: v for k, v in headers.items() if k.lower() not in ("cookie", "content-type")}
    if _otp["verify"]:
        h = {k: v for k, v in h.items() if k.lower() != "x-verify"}
        h["X-Verify"] = _otp["verify"]
    r = requests.post(f"{base}/auth/{path}", headers=h, json=payload, timeout=20)
    if r.headers.get("x-verify-token"):
        _otp["verify"] = r.headers["x-verify-token"]
    return r

def send_otp(mobile=None):
    mobile = (mobile or _otp["mobile"]).translate(EN_DIGITS).strip()
    if not mobile:
        say("برای ورود خودکار، یک‌بار بفرستید: /login 09xxxxxxxxx")
        return False
    _otp["mobile"] = mobile
    try:
        r = _panel_auth("send-otp", {"mobile": mobile})
    except Exception as e:
        say("❌ درخواست کد ورود ناموفق: " + safe(e)[:200]); return False
    if r.status_code >= 300:
        say(f"❌ پنل کد ورود نفرستاد (HTTP {r.status_code}). /login را دوباره بفرستید."); return False
    say("📩 کد ۴ رقمی ورود پنل قدیری پیامک شد. همان ۴ رقم را همین‌جا بفرستید.")
    return True

def curl_with_token(text, token, verify=None):
    """cURL قبلی با کوکی ورود تازه (و X-Verify تازه اگر پنل داده باشد)."""
    if "access_token_web=" in text:
        text = re.sub(r"access_token_web=[^;'\"\s^]+", "access_token_web=" + token, text, count=1)
    else:
        text = text.rstrip() + f" -b 'access_token_web={token}'"
    if verify:
        text = re.sub(r"(?i)(x-verify:\s*)[^'\"\^]+", lambda m: m.group(1) + verify, text, count=1)
    return text

def login_with_code(code):
    if not _otp["mobile"]:
        say("اول /login 09xxxxxxxxx را بفرستید."); return False
    try:
        r = _panel_auth("token", {"code": code, "mobile": _otp["mobile"]})
    except Exception as e:
        say("❌ ورود ناموفق: " + safe(e)[:200]); return False
    token = r.cookies.get("access_token_web")
    if r.status_code >= 300 or not token:
        say(f"❌ کد قبول نشد (HTTP {r.status_code}). دوباره بفرستید یا /login برای کد جدید.")
        return False
    return try_new_curl(curl_with_token(os.environ["REQUEST_CURL"], token, _otp["verify"]))

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
        elif txt.startswith("/login"):
            send_otp(txt[6:].strip() or None)
        elif txt.strip().translate(EN_DIGITS).isdigit() and len(txt.strip()) == 4:
            got = login_with_code(txt.strip().translate(EN_DIGITS)) or got
        elif txt.startswith("/status"):
            say(f"آخرین ارسال موفق: {_status['last_ok'] or '—'}\nآخرین خطا: {_status['last_err'] or '—'}"
                + (f"\nآخرین به‌روزرسانی سایت: {_status.get('site_ok') or '—'}" if SITE_SYNC else ""))
        elif txt.startswith("/start") or txt:
            say("سلام! وقتی لاگین پنل منقضی شد، خودم کد پیامکی می‌گیرم؛ فقط کد ۴ رقمی را همین‌جا بفرستید.\n"
                "/login 09xxxxxxxxx  گرفتن کد ورود جدید\n/status  وضعیت")
    if parts:
        ADMIN_ID = sender or ADMIN_ID          # پیام‌ها و ذخیره در چت همان مدیری که کد را فرستاد
        got = try_new_curl("\n".join(parts))
    return got

# ── ارسال قیمت پنل به سایت وهان زر (هر دقیقه) ──
SITE_SYNC = os.getenv("SITE_SYNC", "0") == "1"
SITE_CODES = {"ابشده نقد فردایی": "gold_farda", "آبشده نقد پسفردایی": "gold_pasfarda", "تمام سکه ۸۶": "emami",
              "تمام سکه تاریخ پایین": "emami_old", "نیم سکه ۸۶": "nim", "ربع سکه ۸۶": "rob"}

def push_site():
    """آخرین قیمت خام پنل را با امضای توکن ربات به سایت می‌فرستد. سایت در نبود آن از فید بازار استفاده می‌کند."""
    if not (SITE_SYNC and SITE_API and SITE_KEY and BOT_TOKEN and LAST_RAW):
        return
    raw = {}
    for title, code in SITE_CODES.items():
        v = LAST_RAW.get(norm(title))
        if v and (v.get("sell") or v.get("buy")):
            raw[code] = {"sell": v.get("sell"), "buy": v.get("buy")}
    if not raw:
        return
    payload = json.dumps(raw, separators=(",", ":"), ensure_ascii=False)
    ts = int(time.time())
    sig = hmac.new(BOT_TOKEN.encode(), f"{ts}.{payload}".encode(), hashlib.sha256).hexdigest()
    try:
        r = requests.post(f"{SITE_API.rstrip('/')}/rest/v1/rpc/ingest_panel_prices",
                          headers={"apikey": SITE_KEY, "Content-Type": "application/json"},
                          json={"p_payload": payload, "p_ts": ts, "p_sig": sig}, timeout=20)
        if r.status_code >= 400:
            _status["site_err"] = f"HTTP {r.status_code}: {r.text[:120]}"
            if not _status.get("site_warned"):
                gh("warning", "ارسال قیمت به سایت ناموفق: " + _status["site_err"]); _status["site_warned"] = True
        else:
            _status["site_ok"] = datetime.now(TZ).strftime("%H:%M")
    except Exception as e:
        _status["site_err"] = safe(e)[:120]

def heartbeat():
    """وضعیت ربات (بدون هیچ اطلاعات محرمانه) برای عیب‌یابی."""
    if not (SITE_API and SITE_KEY):
        return
    st = {k: _status.get(k) for k in ("last_ok", "last_err", "site_ok", "site_err", "waiting_auth")}
    st["raw_items"] = len(LAST_RAW)
    st["now"] = datetime.now(TZ).strftime("%H:%M")
    try:
        requests.post(f"{SITE_API.rstrip('/')}/rest/v1/rpc/bot_heartbeat",
                      headers={"apikey": SITE_KEY, "Content-Type": "application/json"},
                      json={"p": {k: (safe(str(v))[:200] if isinstance(v, str) else v) for k, v in st.items()}}, timeout=10)
    except Exception:
        pass

def site_tick():
    """بین نوبت‌های عکس، هر دقیقه قیمت تازه‌ی پنل را برای سایت می‌فرستد."""
    if not SITE_SYNC or _status.get("waiting_auth"):
        return
    try:
        fetch_prices()
        push_site()
    except Exception as e:
        _status["site_err"] = safe(e)[:120]
    heartbeat()

def sleep_until(t):
    """تا زمان t صبر می‌کند و در این مدت هر دقیقه پیام‌های مدیر را چک می‌کند."""
    first = True
    while True:
        poll_admin()
        if not first and in_window(datetime.now(TZ)):
            site_tick()
        first = False
        left = (t - datetime.now(TZ)).total_seconds()
        if left <= 0:
            return
        time.sleep(min(left, 60))

GOOD_MORNING = os.getenv("GOOD_MORNING", "1") == "1"

# ───────────────────── محتوای متنوع کانال ─────────────────────
import content
ALERT_PCT  = float(os.getenv("ALERT_PCT", "0.5"))     # هشدار تغییر محسوس قیمت (درصد نسبت به نوبت قبل)
DATA_FILE  = "data/day.json"                          # قیمت باز و بسته‌ی روز (عمومی است، محرمانه نیست)
SCHEDULE   = [(12, 0, "tip"), (14, 0, "quiz"), (17, 0, "poll"), (18, 30, "invite"),
              ((END_HOUR - 1) % 24, 60 - INTERVAL, "summary")]       # ساعت تهران
DAYS   = ["شنبه","یکشنبه","دوشنبه","سه‌شنبه","چهارشنبه","پنجشنبه","جمعه"]
MONTHS = ["فروردین","اردیبهشت","خرداد","تیر","مرداد","شهریور","مهر","آبان","آذر","دی","بهمن","اسفند"]

def fa_date(now):
    j = jdatetime.datetime.fromgregorian(datetime=now)
    return f"{DAYS[j.weekday()]} {fa_digits(j.day)} {MONTHS[j.month-1]} {fa_digits(j.year)}"

def foot(text):
    tail = [f"🔗 {BRAND_NAME} | عضویت: {CHANNEL_LINK}"] if CHANNEL_LINK else ([FOOTER_TEXT] if FOOTER_TEXT else [])
    if ORDER_PHONE:  tail.insert(0, f"☎️ ثبت سفارش: {ORDER_PHONE}")
    if ADDRESS_TEXT: tail.insert(1 if ORDER_PHONE else 0, f"📍 {ADDRESS_TEXT}")
    return text + ("\n\n" + "\n".join(tail) if tail else "")

def post(method, what, **kw):
    if share_markup() and "reply_markup" not in kw:
        kw["reply_markup"] = share_markup()
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

def day_base(now):
    """قیمت‌های اولین ارسال امروز؛ با شروع دوباره‌ی اجرا هم از بین نمی‌رود."""
    op = data().get("open") or {}
    return op.get("prices") if op.get("date") == now.date().isoformat() else None

def week_start(d):
    return d - timedelta(days=(d.weekday() + 2) % 7)      # هفته‌ی ایرانی از شنبه

def record_open(prices, now):
    d = data()
    if (d.get("open") or {}).get("date") != now.date().isoformat():
        d["open"] = {"date": now.date().isoformat(), "prices": prices}
        if (d.get("week_open") or {}).get("week") != week_start(now.date()).isoformat():
            d["week_open"] = {"week": week_start(now.date()).isoformat(), "date": now.date().isoformat(),
                              "prices": prices}
        save_data("open " + now.date().isoformat())

def change_lines(old, new):
    lines = []
    for title in ITEMS:
        k = norm(title)
        side = "sell" if ((new or {}).get(k) or {}).get("sell") else "buy"
        a = ((old or {}).get(k) or {}).get(side)
        b = ((new or {}).get(k) or {}).get(side)
        if not b:
            continue
        if not a:
            lines.append(f"▫️ {label(title)}: {money(b)}")
            continue
        pct = (b - a) / a * 100
        sign = "🔺" if pct > 0.005 else ("🔻" if pct < -0.005 else "⚪️")
        pct_txt = fa_digits(f"{abs(pct):.2f}").replace(".", "٫")
        lines.append(f"{sign} {label(title)}: {money(b)}  ({pct_txt}٪)")
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

def send_invite(now):
    """هفته‌ای یک‌بار (پنجشنبه) دعوت از اعضا برای معرفی کانال به دیگران."""
    if now.weekday() != 3:      # ۳ = پنجشنبه
        return
    text = ("🤝 اگه قیمت‌های لحظه‌ای و نکته‌های کانال براتون مفیده،\n"
            "لطفاً کانال رو برای خانواده و دوستانی که اهل خرید طلا هستن بفرستید.\n\n"
            "با زدن دکمه‌ی پایین، در یک لحظه می‌تونید کانال رو براشون ارسال کنید 👇")
    post("sendMessage", "دعوت هفتگی", text=foot(text))

def send_summary(prices, now):
    op = data().get("open") or {}
    base = op.get("prices") if op.get("date") == now.date().isoformat() else None
    lines = change_lines(base, prices)
    if not lines:
        gh("warning", "خلاصه‌ی روز خالی بود و ارسال نشد."); return
    head = "🌙 خلاصه‌ی قیمت‌های امروز" + ("، نسبت به شروع روز" if base else "")
    nxt = next_start(now)
    when = "فردا" if nxt.date() == now.date() + timedelta(days=1) else fa_date(nxt).split()[0]
    wk = data().get("week_open") or {}
    if (week_start(nxt.date()) != week_start(now.date()) and wk.get("week") == week_start(now.date()).isoformat()
            and wk.get("date") != now.date().isoformat()):
        week = change_lines(wk.get("prices"), prices)
        if week:
            lines += ["", "📅 جمع‌بندی هفته (نسبت به شروع هفته):"] + week
    text = (f"{head}\n{fa_date(now)}\n\n" + "\n".join(lines) +
            f"\n\n{when} ساعت {fa_digits(START_HOUR)} با قیمت‌های جدید در خدمت شما هستیم. شب خوش 🌙")
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
        lines = [l for l in change_lines(prev, prices) if any(label(t) in l for t in moved)]
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
        elif kind == "invite":  send_invite(now)
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
    elif now.minute % INTERVAL or now.second > 30:
        # اجرای ادامه‌دهنده وسط روز: عکس تکراری چند دقیقه بعد از عکس قبلی نفرستد؛ صبر تا نوبت بعدی
        nxt = next_slot(now)
        if nxt <= deadline:
            print("منتظر نوبت بعدی:", nxt.strftime("%H:%M"), flush=True)
            sleep_until(nxt)

    prev, fails, waiting_auth = None, 0, False
    while True:
        now = datetime.now(TZ)
        if not in_window(now):
            print("پایان ساعت کاری.", flush=True); return 0
        if waiting_auth:
            # منتظر کد جدید از مدیر؛ هر دقیقه چک می‌شود
            if poll_admin():
                waiting_auth = False
                _status["waiting_auth"] = False
                _status.pop("auth_since", None)
                continue
            since = _status.get("auth_since")
            if since and not _status.get("outage_posted") and datetime.now(TZ) - since > timedelta(minutes=30):
                _status["outage_posted"] = True
                post("sendMessage", "اعلام توقف",
                     text=foot("⏸ به‌روزرسانی قیمت‌ها موقتاً متوقف است و به‌زودی برقرار می‌شود.\n"
                               "برای استعلام قیمت و ثبت سفارش با ما تماس بگیرید."))
            if datetime.now(TZ) + timedelta(minutes=1) > deadline:
                dispatch_next_run(); return 0
            heartbeat()
            time.sleep(60); continue
        for attempt in range(3):
            try:
                prices = fetch_prices()
                push_site()
                before_photo(prices, now)
                send_photo(render(prices, day_base(now) or prev), price_caption(prices, now))
                try:
                    after_photo(prev, prices, now)
                except Exception as e:
                    gh("warning", f"محتوای اضافه ارسال نشد: {e}")
                prev = prices
                _status.pop("auth_since", None)
                if _status.pop("outage_posted", False):
                    post("sendMessage", "اعلام ادامه", text=foot("✅ اعلام قیمت‌ها دوباره برقرار شد. از همراهی شما سپاسگزاریم."))
                _status["last_ok"] = datetime.now(TZ).strftime("%H:%M")
                print(_status["last_ok"], "ارسال شد ✔", flush=True)
                fails = 0
                break
            except AuthError as e:
                _status["last_err"] = str(e)
                gh("warning", str(e))
                if not ADMIN_ID:
                    gh("error", str(e)); return 1
                say("⚠️ لاگین پنل منقضی شد و ارسال قیمت‌ها متوقف است.")
                send_otp()
                waiting_auth = True
                _status["waiting_auth"] = True
                _status.setdefault("auth_since", datetime.now(TZ))
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
