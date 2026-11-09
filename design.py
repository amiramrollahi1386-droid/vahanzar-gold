import io, os
from PIL import Image, ImageDraw

W, H = 1080, 1350
PAD = 48
BG_T, BG_B = (12, 11, 10), (31, 25, 19)
GOLD, GOLD_D = (228, 188, 112), (128, 98, 56)
IVORY, MUTED = (247, 241, 228), (170, 158, 138)
SELL_FILL = (255, 235, 190, 14)


def render(g, prices, prev, now):
    img = g.gradient(W, H, BG_T, BG_B).convert("RGBA")
    g.glow(img, (W // 2, 520), 460, (212, 160, 70), 34)
    d = ImageDraw.Draw(img)
    F = g.font
    B, R = g.FONT_BOLD, g.FONT_REG
    T = lambda xy, t, f, c, a="rm": g.draw_text(d, xy, t, f, c, a)

    def fit(text, size, maxw, bold=True):
        while size > 24 and g.img_text_width(text, F(B if bold else R, size)) > maxw:
            size -= 2
        return F(B if bold else R, size)

    def num(x, y, v, size, col, maxw, a="mm"):
        if not v:
            T((x, y), "—", F(B, size), MUTED, a); return
        t = g.money_fa(v)
        T((x, y), t, fit(t, size, maxw), col, a)

    def chip(rx, cy, key, size=28):
        base = ((prev or {}).get(key) or {}).get("sell"); cur = (prices.get(key) or {}).get("sell")
        if not (base and cur) or abs(cur - base) / base < 0.00005:
            return
        txt, up = g.pct_fa(base, cur)
        col = g.UP if up else g.DOWN
        f = F(B, size); w = int(g.img_text_width(txt, f)) + 64; h = size + 22
        dd = g._card(img, [rx - w, cy - h // 2, rx, cy + h // 2], fill=(*col, 40), outline=(*col, 120), radius=h // 2, width=2)
        g.triangle(dd, rx - 26, cy, up, col, 9)
        g.draw_text(dd, (rx - 46, cy), txt, f, col, "rm")

    def mith(key, field):
        p = prices.get(key) or {}
        if not p.get(field):
            return None
        return (g.LAST_RAW.get(key) or {}).get(field) or round(p[field] * g.ABSHODE_DIVISOR, -3)

    def pill(cx, cy, text, size, fg, bg):
        f = F(B, size); w = int(g.img_text_width(text, f)) + 40; h = size + 18
        dd = g._card(img, [cx - w // 2, cy - h // 2, cx + w // 2, cy + h // 2], fill=bg, outline=None, radius=h // 2)
        g.draw_text(dd, (cx, cy), text, f, fg, "mm")

    # frame
    d.rounded_rectangle([20, 20, W - 20, H - 20], 36, outline=(*GOLD_D, 140), width=2)

    # header
    r, cx, cy = 64, W - PAD - 64, 98
    d.ellipse([cx - r - 6, cy - r - 6, cx + r + 6, cy + r + 6], outline=GOLD, width=3)
    d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=(250, 246, 238))
    if os.path.exists(g.LOGO_PATH):
        lg = Image.open(g.LOGO_PATH).convert("RGBA"); lg.thumbnail((int(r * 1.56),) * 2, Image.LANCZOS)
        img.paste(lg, (cx - lg.width // 2, cy - lg.height // 2), lg)
    tx = cx - r - 30
    T((tx, 66), g.BRAND_NAME, F(B, 62), GOLD)
    T((tx, 130), g.fa_date(now), F(R, 34), IVORY)
    upd = f"آخرین به‌روزرسانی  {g.fa_digits(now.strftime('%H:%M'))}"
    f = F(B, 28); w = int(g.img_text_width(upd, f)) + 70
    dd = g._card(img, [PAD, 62, PAD + w, 114], fill=(255, 255, 255, 16), outline=(*GOLD_D, 150), radius=26)
    dd.ellipse([PAD + w - 40, 80, PAD + w - 24, 96], fill=GOLD)
    g.draw_text(dd, (PAD + w - 52, 88), upd, f, IVORY, "rm")
    note = "قیمت‌ها به تومان" + ("  •  تغییرات نسبت به شروع امروز" if prev else "")
    g.draw_text(dd, (PAD + 6, 142), note, F(R, 25), MUTED, "lm")
    for x in range(PAD, W - PAD):
        t = abs((x - W / 2) / (W / 2 - PAD))
        d.point((x, 174), fill=(*GOLD, int(255 * (1 - t ** 3))))

    gold = [t for t in g.ITEMS if g.label(t).startswith("آبشده") and (prices.get(g.norm(t)) or {})]
    coins = [t for t in g.ITEMS if not g.label(t).startswith("آبشده") and (prices.get(g.norm(t)) or {})]
    y = 190

    # hero
    gap = 10
    def grams(x, yy, key, fld, size, col):
        v = (prices.get(key) or {}).get(fld)
        T((x, yy), "هر گرم  " + g.money_fa(v) if v else "هر گرم  —", F(B, size), col, "mm")

    if gold:
        key = g.norm(gold[0]); p = prices[key]
        top, bot = y, y + 450
        d = g._card(img, [PAD, top, W - PAD, bot], fill=(228, 188, 112, 22), outline=(*GOLD, 200), radius=34, width=3)
        T((W - PAD - 36, top + 50), g.label(gold[0]), F(B, 56), IVORY)
        T((W - PAD - 36 - int(g.img_text_width(g.label(gold[0]), F(B, 56))) - 30, top + 56), "مظنه هر مثقال", F(R, 30), MUTED)
        chip(PAD + 170, top + 50, key)
        pill(W - PAD - 36 - 80, top + 112, "فروش به شما", 30, (24, 18, 8), GOLD)
        num(W // 2 + 20, top + 186, mith(key, "sell"), 118, GOLD, W - 2 * PAD - 60)
        grams(W // 2, top + 284, key, "sell", 42, IVORY)
        d.line([(PAD + 36, top + 318), (W - PAD - 36, top + 318)], fill=(*GOLD_D, 150), width=2)
        pill(W - PAD - 36 - 80, top + 372, "خرید از شما", 30, IVORY, (255, 255, 255, 30))
        num(480, top + 358, mith(key, "buy"), 58, IVORY, 520)
        grams(480, top + 410, key, "buy", 36, MUTED)
        y = bot + gap

    if len(gold) > 1:
        key = g.norm(gold[1]); p = prices[key]
        top, bot = y, y + 210
        d = g._card(img, [PAD, top, W - PAD, bot], fill=(255, 255, 255, 12), outline=(*GOLD_D, 170), radius=28)
        T((W - PAD - 32, top + 36), g.label(gold[1]), F(B, 40), IVORY)
        T((W - PAD - 32 - int(g.img_text_width(g.label(gold[1]), F(B, 40))) - 24, top + 40), "مظنه مثقال", F(R, 28), MUTED)
        chip(PAD + 170, top + 36, key, 24)
        T((W - PAD - 32, top + 82), "فروش به شما", F(B, 26), GOLD)
        T((500, top + 82), "خرید از شما", F(B, 26), MUTED)
        num(W - PAD - 32, top + 120, mith(key, "sell"), 52, GOLD, 400, "rm")
        num(500, top + 120, mith(key, "buy"), 46, IVORY, 380, "rm")
        grams(W - PAD - 32 - 190, top + 174, key, "sell", 40, IVORY)
        grams(500 - 190, top + 174, key, "buy", 40, MUTED)
        y = bot + gap

    if coins:
        th = 168
        cw = (W - 2 * PAD - gap) // 2
        for i, t in enumerate(coins):
            row, col = divmod(i, 2)
            alone = i == len(coins) - 1 and len(coins) % 2 == 1
            x2 = W - PAD if alone else W - PAD - col * (cw + gap)
            x1 = PAD if alone else x2 - cw
            top = y + row * (th + gap)
            key = g.norm(t); p = prices[key]
            d = g._card(img, [x1, top, x2, top + th], fill=(255, 255, 255, 12), outline=(*GOLD_D, 170), radius=26)
            T((x2 - 24, top + 34), g.label(t), F(B, 32), IVORY)
            chip(x1 + 160, top + 34, key, 24)
            for yy, fld, sz, col, lab in ((top + 88, "sell", 50, GOLD, "فروش به شما"), (top + 138, "buy", 40, MUTED, "خرید از شما")):
                T((x2 - 24, yy), lab, F(R, 24), col)
                lw = int(g.img_text_width(lab, F(R, 24)))
                v = p.get(fld)
                if v:
                    t2 = g.money_fa(v); T((x1 + 24, yy), t2, fit(t2, sz, x2 - x1 - lw - 72), col, "lm")
                else:
                    T((x1 + 24, yy), "—", F(B, sz), col, "lm")
        y += ((len(coins) + 1) // 2) * (th + gap)

    # footer
    fy = H - 96
    trust = [t.strip() for t in g.TRUST_TEXT.split("،") if t.strip()]
    if trust:
        t = "  •  ".join(trust)
        T((W // 2, fy), t, fit(t, 28, W - 2 * PAD - 20), GOLD, "mm")
    f = F(B, 36); cy2 = fy + 48
    phone = f"ثبت سفارش  {g.fa_digits(g.ORDER_PHONE)}" if g.ORDER_PHONE else ""
    link = f"t.me/{g.CHANNEL_ID.lstrip('@')}" if g.CHANNEL_ID.startswith("@") else ""
    if phone and link:
        T((W // 2 + 30, cy2), phone, f, IVORY, "lm")
        d.text((W // 2, cy2), "|", font=f, fill=MUTED, anchor="mm")
        d.text((W // 2 - 30, cy2), link, font=f, fill=IVORY, anchor="rm")
    elif phone or link:
        T((W // 2, cy2), phone or link, f, IVORY, "mm")

    out = io.BytesIO(); img.convert("RGB").save(out, "PNG", optimize=True); out.seek(0)
    return out
