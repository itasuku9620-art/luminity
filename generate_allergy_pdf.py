# generate_allergy_pdf.py
from io import BytesIO
from datetime import datetime
import os

from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib import colors
from reportlab.lib.units import mm
from reportlab.platypus import (
    SimpleDocTemplate,
    Table,
    TableStyle,
    Paragraph,
    Spacer,
)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.graphics.shapes import Drawing
from reportlab.graphics.barcode import qr


# ============================================================
# ★ 日本語フォント登録
# ============================================================
def _register_japanese_font() -> str:
    """
    日本語 TrueType フォントがあれば登録してフォント名を返す。
    なければ Helvetica を使う。
    """
    font_path = os.environ.get("LUMINITY_PDF_FONT", "fonts/NotoSansJP-Regular.ttf")
    if os.path.exists(font_path):
        try:
            pdfmetrics.registerFont(TTFont("JP", font_path))
            return "JP"
        except Exception:
            pass
    return "Helvetica"


# ============================================================
# ★ アレルゲン分類（最新）
# 　特定原材料8品目 ＋ その他20品目
# ============================================================
PRIMARY_8 = [
    "卵",
    "乳",
    "小麦",
    "えび",
    "かに",
    "くるみ",
    "そば",
    "落花生（ピーナッツ）",
]

SECONDARY_20 = [
    "アーモンド",
    "あわび",
    "いか",
    "いくら",
    "オレンジ",
    "カシューナッツ",
    "キウイフルーツ",
    "牛肉",
    "ごま",
    "さけ",
    "さば",
    "大豆",
    "鶏肉",
    "バナナ",
    "豚肉",
    "もも",
    "やまいも",
    "りんご",
    "ゼラチン",
    "マカダミアナッツ",  # ← まつたけ削除、マカダミア追加
]


# ============================================================
# ★ ◯ / × / - を判定する
# ============================================================
def _normalize_mark(val) -> str:
    """
    Googleシートの値を 'circle' / 'cross' / 'dash' に正規化する
    """
    if val is None:
        return "dash"

    s = str(val).strip()
    if s == "":
        return "dash"

    su = s.upper()

    # ◯ 系
    if s in ("◯", "○", "〇", "●", "✔", "✓"):
        return "circle"
    if su in ("O", "TRUE", "YES", "1"):
        return "circle"
    if s in ("有", "あり", "含む", "o"):
        return "circle"

    # × 系
    if s in ("×", "✕", "✖"):
        return "cross"
    if su in ("X", "FALSE", "NO", "0"):
        return "cross"
    if s in ("無", "なし", "不使用"):
        return "cross"

    # 不明系
    if s in ("-", "－", "ー", "—", "不明"):
        return "dash"

    return "dash"


def _build_mark_paragraph(raw, style_circle, style_cross, style_dash):
    mark = _normalize_mark(raw)
    if mark == "circle":
        return Paragraph("◯", style_circle)
    if mark == "cross":
        return Paragraph("×", style_cross)
    return Paragraph("-", style_dash)


# ============================================================
# ★ 列幅を自動計算して A4 横の印刷幅に収める
# ============================================================
def calc_col_widths(num_cols: int):
    usable_width = 297 * mm - (15 * mm * 2)  # A4横 - マージン左右
    menu_col_width = 45 * mm

    if num_cols <= 1:
        return [menu_col_width]

    remain = usable_width - menu_col_width
    per = remain / (num_cols - 1)

    return [menu_col_width] + [per] * (num_cols - 1)


# ============================================================
# ★ PDF生成本体
# ============================================================
def build_allergy_pdf(
    store: dict,
    rows: list,
    primary_allergens: list,
    other_allergens: list,
    allergy_url: str | None = None,
) -> bytes:

    buffer = BytesIO()
    font_name = _register_japanese_font()

    # PDF 設定
    doc = SimpleDocTemplate(
        buffer,
        pagesize=landscape(A4),
        leftMargin=15 * mm,
        rightMargin=15 * mm,
        topMargin=12 * mm,
        bottomMargin=12 * mm,
    )

    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle("NormalJP", fontName=font_name, fontSize=9, leading=11))
    styles.add(ParagraphStyle("MenuJP", fontName=font_name, fontSize=8, leading=10, wordWrap="CJK"))
    styles.add(ParagraphStyle("CellJP", fontName=font_name, fontSize=8, leading=9, alignment=1, wordWrap="CJK"))
    styles.add(ParagraphStyle("Circle", parent=styles["NormalJP"], fontSize=8, alignment=1, textColor=colors.red))
    styles.add(ParagraphStyle("Cross", parent=styles["NormalJP"], fontSize=8, alignment=1, textColor=colors.green))
    styles.add(ParagraphStyle("Dash", parent=styles["NormalJP"], fontSize=8, alignment=1, textColor=colors.gray))
    styles.add(ParagraphStyle("SubHeading", fontName=font_name, fontSize=11, spaceBefore=6, spaceAfter=4))

    story = []

    # ============================================================
    # ヘッダー（ロゴ・店名・QR）
    # ============================================================
    logo = Paragraph("<b>Luminity</b>", ParagraphStyle("Logo", fontName=font_name, fontSize=16))
    title = Paragraph(f"{store.get('店舗名','')}　アレルギー表",
                      ParagraphStyle("Title", fontName=font_name, fontSize=12))

    if allergy_url:
        qr_code = qr.QrCodeWidget(allergy_url)
        bounds = qr_code.getBounds()
        size = 28 * mm
        d = Drawing(size, size, transform=[size/(bounds[2]-bounds[0]), 0, 0, size/(bounds[3]-bounds[1]), 0, 0])
        d.add(qr_code)
        qr_img = d
    else:
        qr_img = ""

    header = Table([[logo, title, qr_img]], colWidths=[35*mm, None, 35*mm])
    header.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,-1), colors.HexColor("#ffe9b3")),
        ("VALIGN", (0,0), (-1,-1), "MIDDLE"),
        ("LEFTPADDING", (0,0), (-1,-1), 6),
        ("RIGHTPADDING", (0,0), (-1,-1), 6),
    ]))

    story.append(header)
    story.append(Spacer(1, 4 * mm))

    # ============================================================
    # 特定原材料 8品目
    # ============================================================
    story.append(Paragraph("特定原材料 8品目", styles["SubHeading"]))

    ordered_primary = [a for a in primary_allergens if a in PRIMARY_8]

    primary_header = [Paragraph("メニュー", styles["MenuJP"])] + [
        Paragraph(a, styles["CellJP"]) for a in ordered_primary
    ]

    primary_data = [primary_header]

    for r in rows:
        row_list = [Paragraph(str(r.get("メニュー","")), styles["MenuJP"])]
        for a in ordered_primary:
            row_list.append(
                _build_mark_paragraph(r.get(a), styles["Circle"], styles["Cross"], styles["Dash"])
            )
        primary_data.append(row_list)

    col_widths_primary = calc_col_widths(len(primary_header))

    primary_table = Table(primary_data, colWidths=col_widths_primary, repeatRows=1)
    primary_table.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#fff2cc")),
        ("WORDWRAP", (0,0), (-1,-1), "CJK"),
        ("GRID", (0,0), (-1,-1), 0.4, colors.gray),
        ("VALIGN", (0,0), (-1,-1), "MIDDLE"),
    ]))

    story.append(primary_table)
    story.append(Spacer(1, 6 * mm))

    # ============================================================
    # その他 20品目
    # ============================================================
    story.append(Paragraph("その他 20品目", styles["SubHeading"]))

    ordered_other = [a for a in other_allergens if a in SECONDARY_20]

    other_header = [Paragraph("メニュー", styles["MenuJP"])] + [
        Paragraph(a, styles["CellJP"]) for a in ordered_other
    ]

    other_data = [other_header]

    for r in rows:
        row_list = [Paragraph(str(r.get("メニュー","")), styles["MenuJP"])]
        for a in ordered_other:
            row_list.append(
                _build_mark_paragraph(r.get(a), styles["Circle"], styles["Cross"], styles["Dash"])
            )
        other_data.append(row_list)

    col_widths_other = calc_col_widths(len(other_header))

    other_table = Table(other_data, colWidths=col_widths_other, repeatRows=1)
    other_table.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#fff7da")),
        ("WORDWRAP", (0,0), (-1,-1), "CJK"),
        ("GRID", (0,0), (-1,-1), 0.4, colors.gray),
        ("VALIGN", (0,0), (-1,-1), "MIDDLE"),
    ]))

    story.append(other_table)
    story.append(Spacer(1, 6 * mm))

    # ============================================================
    # 備考
    # ============================================================
    notes = ["【備考】"]
    if store.get("備考"):
        notes.append(store.get("備考"))
    notes.append("・原材料や工場の製造ラインにより、完全なアレルゲン除去は保証できません。")
    notes.append("・店舗ごとの取り扱い状況により、メニュー・原材料は変更される場合があります。")

    story.append(Paragraph("<br/>".join(notes), styles["NormalJP"]))

    story.append(Spacer(1, 4 * mm))

    # ============================================================
    # フッター
    # ============================================================
    updated = store.get("更新日") or store.get("最終更新") or ""
    generated = datetime.now().strftime("%Y-%m-%d %H:%M")

    footer = Paragraph(
        f"更新日：{updated}　　生成日：{generated}",
        ParagraphStyle("Footer", fontName=font_name, fontSize=7, alignment=2)
    )
    story.append(footer)

    #生成
    doc.build(story)
    pdf_data = buffer.getvalue()
    buffer.close()
    return pdf_data

