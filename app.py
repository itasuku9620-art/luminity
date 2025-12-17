# app.py — Luminity (Flask + SQLite + Google Sheets)
# Sprint2: マイアレルゲン保存/UI、/search 安全度、投稿MVP、店舗ページ連動、通報キュー、同意→表エイリアス
# + Auth強化（試行制限 / パス再設定 / メール認証 / Remember me）
# + Admin: /admin/login, /admin/logout, /admin/users 一覧/編集/退会, /admin/reports, /admin/dashboard
# + Shortcut: /login/admin → /admin/login, /login?admin=1 でも /admin/login へ
# + PR#2: オーナー申請審査UI /admin/claims、ユーザー申請 /store/<id>/claim

from __future__ import annotations

# app.py（抜粋）
from flask import Flask, send_from_directory

from io import BytesIO
from flask import send_file, url_for
from generate_allergy_pdf import build_allergy_pdf

import os, re, json, unicodedata, secrets, sqlite3, shutil, base64, time, smtplib
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from email.message import EmailMessage
from itsdangerous import URLSafeTimedSerializer, BadSignature, SignatureExpired
from werkzeug.security import generate_password_hash, check_password_hash

from flask import (
    Flask, abort, flash, g, redirect, render_template,
    request, session, url_for, jsonify
)
from werkzeug.utils import secure_filename
from dotenv import load_dotenv


import json, os
from google.oauth2 import service_account

def load_google_credentials(scopes=None):
    if scopes is None:
        scopes = [
            "https://www.googleapis.com/auth/spreadsheets.readonly",
            "https://www.googleapis.com/auth/drive.readonly",
        ]

    cred_json = os.environ.get("GOOGLE_CREDENTIALS_JSON")
    if not cred_json:
        raise RuntimeError("環境変数 GOOGLE_CREDENTIALS_JSON が設定されていません")

    try:
        info = json.loads(cred_json)
    except Exception as e:
        raise RuntimeError("GOOGLE_CREDENTIALS_JSON が不正な JSON です") from e

    return service_account.Credentials.from_service_account_info(
        info,
        scopes=scopes,
    )



# ============== ENV / APP ==============
APP_ROOT = Path(__file__).resolve().parent
load_dotenv(APP_ROOT / ".env", override=True)

SECRET_KEY = os.getenv("SECRET_KEY", "change_me_to_random_32bytes")
GOOGLE_MAPS_API_KEY = os.getenv("GOOGLE_MAPS_API_KEY", "")
SHEET_ID = (os.getenv("SHEET_ID") or os.getenv("GOOGLE_SHEETS_SPREADSHEET_ID") or "").strip()

CREDS_PATH_ENV = os.getenv("GSPREAD_CREDENTIALS_JSON", "credentials.json").strip()
CREDS_FILE = Path(CREDS_PATH_ENV if os.path.isabs(CREDS_PATH_ENV) else APP_ROOT / CREDS_PATH_ENV).resolve()

# --- Admin bootstrap env ---
ADMIN_EMAIL = (os.getenv("ADMIN_EMAIL") or "").strip().lower()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD")
ADMIN_PASSWORD_HASH = os.getenv("ADMIN_PASSWORD_HASH")

app = Flask(__name__)
app.secret_key = SECRET_KEY
app.permanent_session_lifetime = timedelta(days=int(os.getenv("REMEMBER_ME_DAYS", "30")))
_REQUIRE_VERIFY = os.getenv("REQUIRE_EMAIL_VERIFICATION", "0") == "1"

# ============== UPLOADS ==============
AVATAR_DIR = APP_ROOT / "static" / "uploads" / "avatars"
POST_DIR   = APP_ROOT / "static" / "uploads" / "posts"
for d in (AVATAR_DIR, POST_DIR):
    d.mkdir(parents=True, exist_ok=True)

ALLOWED_IMAGE_EXTS = {"png", "jpg", "jpeg", "webp"}
MAX_UPLOAD_MB = 5

# --- 追加: ルート安全登録（既存あれば置き換え、なければ追加） ---
# --- 追加（存在しなければ定義）: ルート上書き安全登録器 ---
try:
    _register_or_override  # 既存があればそのまま使う
except NameError:
    def _register_or_override(rule: str, endpoint: str, view_func, methods=("GET",)):
        if endpoint in app.view_functions:
            app.view_functions.pop(endpoint, None)
        app.add_url_rule(rule, endpoint, view_func, methods=list(methods))

# --- 追加: ウェルカム（スプラッシュ）画面 ---
def _welcome_view():
    return render_template("welcome.html")

def _home_with_welcome():
    # 初回だけウェルカム。2回目以降は従来どおり検索へ
    if not session.get("seen_welcome"):
        session["seen_welcome"] = True
        return render_template("welcome.html")
    return _home_redirect_legacy()

# 既存があれば置換、無ければ追加
_register_or_override("/welcome", "welcome", _welcome_view, ("GET",))
_register_or_override("/",        "home",    _home_with_welcome, ("GET",))

def _allowed_image(filename: str) -> bool:
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_IMAGE_EXTS

def _avatar_relpath(uid: int, ext: str) -> str:
    return f"uploads/avatars/user_{uid}.{ext}"

def _get_unread_count(uid: int) -> int:
    row = get_db().execute(
        "SELECT COUNT(*) AS c FROM notifications WHERE user_id=? AND read_at IS NULL", (uid,)
    ).fetchone()
    return int(row["c"]) if row else 0

def send_email(to_addr: str, subject: str, body: str) -> bool:
    """SMTP設定がなければログ出力だけして終了（壊さない）"""
    host = os.getenv("SMTP_HOST"); port = int(os.getenv("SMTP_PORT") or 0)
    user = os.getenv("SMTP_USER"); pwd = os.getenv("SMTP_PASS")
    sender = os.getenv("SMTP_FROM") or (user or "noreply@example.com")
    if not host or not port:
        app.logger.info("[MAIL-DRYRUN] to=%s subj=%s body=%s", to_addr, subject, body)
        return False
    try:
        msg = EmailMessage()
        msg["Subject"] = subject
        msg["From"] = sender
        msg["To"] = to_addr
        msg.set_content(body)
        with smtplib.SMTP(host, port, timeout=10) as s:
            if os.getenv("SMTP_STARTTLS", "1") != "0":
                s.starttls()
            if user and pwd:
                s.login(user, pwd)
            s.send_message(msg)
        return True
    except Exception as e:
        app.logger.warning("MAIL SEND FAIL: %s", e)
        return False

def enqueue_notifications(store_id: int, kind: str, item_id: int, title: str, exclude_user_id: Optional[int] = None):
    """お気に入り登録者に通知を作成。メールは設定時のみ送信。"""
    db = get_db()
    fav_uids = [int(r["user_id"]) for r in db.execute(
        "SELECT DISTINCT user_id FROM favorites WHERE store_id=?", (store_id,)
    ).fetchall()]
    if exclude_user_id is not None:
        fav_uids = [u for u in fav_uids if u != exclude_user_id]
    if not fav_uids:
        return

    db.executemany(
        "INSERT INTO notifications(user_id,kind,store_id,item_id,title) VALUES (?,?,?,?,?)",
        [(u, kind, store_id, item_id, title) for u in fav_uids]
    )
    db.commit()

    # 任意：メール通知
    for u in fav_uids:
        pref = db.execute("SELECT email_posts, email_announcements FROM user_notify_pref WHERE user_id=?", (u,)).fetchone()
        need_mail = (kind == "post" and pref and pref["email_posts"]) or \
                    (kind == "announcement" and pref and pref["email_announcements"])
        if not need_mail:
            continue
        urow = db.execute("SELECT email, name FROM users WHERE id=?", (u,)).fetchone()
        if not urow or not (urow["email"] or "").strip():
            continue
        url = url_for("store_detail", store_id=store_id, _external=True)
        subject = "[Luminity] お気に入り店舗の新着" + ("投稿" if kind == "post" else "お知らせ")
        body = f"{title}\n\n店舗ページ：{url}"
        send_email(urow["email"], subject, body)

def _save_avatar(file_storage, uid: int) -> Optional[str]:
    if not file_storage or not file_storage.filename:
        return None
    filename = secure_filename(file_storage.filename)
    if not _allowed_image(filename):
        raise ValueError("許可されていない画像形式です（png/jpg/jpeg/webp）")
    file_storage.stream.seek(0, 2)
    size = file_storage.stream.tell()
    file_storage.stream.seek(0)
    if size > MAX_UPLOAD_MB * 1024 * 1024:
        raise ValueError(f"画像サイズは {MAX_UPLOAD_MB}MB までです")
    ext = filename.rsplit(".", 1)[1].lower()
    rel = _avatar_relpath(uid, ext)
    abs_path = APP_ROOT / "static" / rel
    for p in AVATAR_DIR.glob(f"user_{uid}.*"):
        try: p.unlink()
        except Exception: pass
    file_storage.save(abs_path)
    return rel

def _save_claim_evidence(file_storage, claim_id: int) -> Optional[str]:
    if not file_storage or not file_storage.filename:
        return None
    filename = secure_filename(file_storage.filename)
    if not _allowed_image(filename):
        raise ValueError("証憑は png/jpg/jpeg/webp のみ対応です")
    file_storage.stream.seek(0, 2)
    size = file_storage.stream.tell()
    file_storage.stream.seek(0)
    if size > MAX_UPLOAD_MB * 1024 * 1024:
        raise ValueError(f"ファイルサイズは {MAX_UPLOAD_MB}MB までです")
    ext = filename.rsplit(".", 1)[1].lower()
    rel = f"uploads/claims/{claim_id}/evidence.{ext}"
    abs_path = APP_ROOT / "static" / rel
    abs_path.parent.mkdir(parents=True, exist_ok=True)
    file_storage.save(abs_path)
    return rel

# ============== gspread 可否 ==============
# ================= gspread 認証 =================

HAS_GSPREAD = True

try:
    import gspread
    from google.oauth2.service_account import Credentials
    from gspread.exceptions import APIError as GSpreadAPIError
except Exception as e:
    print("gspread import error:", e)
    HAS_GSPREAD = False
    GSpreadAPIError = Exception


# ============== アレルギー表 解析 ==============
ALLERGEN_CANDIDATES = set("""
卵,鶏卵,乳,乳成分,小麦,そば,蕎麦,落花生,ピーナッツ,えび,海老,かに,蟹,くるみ,胡桃,アーモンド,
ごま,胡麻,大豆,カシューナッツ,あわび,いか,いくら,オレンジ,キウイ,牛肉,さけ,さば,ゼラチン,バナナ,豚肉,まつたけ,もも,やまいも,りんご
""".replace("\n","").split(","))

MENU_HEADER_ALIASES = {"メニュー","メニュー名","商品","商品名","料理名","品名","Menu","menu","品"}
ALLERGY_HEADER_ALIASES = {"アレルゲン","アレルゲン名","Allergen","allergen","アレルギー","アレルギー項目"}

def _to_symbol(v: object) -> str:
    s = (str(v).strip() if v is not None else ""); sl = s.lower()
    if s in ("○","◯") or sl in ("true","ok","o","yes","可","有","あり","含む"): return "◯"
    if s in ("×","✕","x","X") or sl in ("false","ng","no","不可","無","なし","不使用"): return "✕"
    return "－"

def _parse_any_table(values):
    if not values:
        return [], [], 0
    headers = [str(h).strip() for h in values[0]]
    data = [r for r in values[1:] if any((c or "").strip() for c in r)]

    def _numlike(s: str) -> bool:
        s = (s or "").strip()
        return bool(re.fullmatch(r"\d+", s))
    if headers and len(headers) > 1:
        cells = [h for h in headers[1:] if str(h).strip()]
        if cells:
            num_ratio = sum(1 for h in cells if _numlike(h)) / len(cells)
            if num_ratio >= 0.6 and data:
                headers = [headers[0]] + [str(c).strip() for c in data[0]]
                data = data[1:]

    if not headers:
        return [], [], 0

    allergen_idx = None
    for i, h in enumerate(headers):
        hh = str(h).strip()
        if hh in ALLERGY_HEADER_ALIASES or re.sub(r"\s", "", hh) in {"アレルゲン","アレルギー","アレルギー項目"}:
            allergen_idx = i
            break

    first_col_vals = [str(r[0]).strip() for r in data[:30] if len(r) > 0 and str(r[0]).strip()]
    hit = sum(1 for v in first_col_vals if re.sub(r"\s", "", v) in ALLERGEN_CANDIDATES)
    vertical_by_values = bool(first_col_vals) and (hit / len(first_col_vals) >= 0.4)

    def score_rows(rows, allergens):
        non_unknown = sum(1 for r in rows for a in allergens if r.get(a) in ("◯", "✕"))
        return len(allergens) * 100 + non_unknown

    outA, allergensA, scoreA = [], [], 0
    h0 = headers[0]
    if allergen_idx is None and not vertical_by_values:
        allergensA = []
        for h in headers[1:]:
            hh = str(h).strip()
            if not hh: continue
            if (hh in ALLERGEN_CANDIDATES) or (re.sub(r"\s","",hh) in ALLERGEN_CANDIDATES):
                allergensA.append(hh)
        if not allergensA:
            allergensA = [h for h in headers[1:] if str(h).strip()]
        allergensA = allergensA[:28]
        for r in data:
            rec = dict(zip(headers, r))
            menu = (rec.get(h0) or "").strip()
            if not menu: continue
            row = {"menu": menu}
            for a in allergensA:
                row[a] = _to_symbol(rec.get(a))
            if any(row[a] != "－" for a in allergensA):
                outA.append(row)
        if outA and allergensA:
            scoreA = score_rows(outA, allergensA)

    outB, allergensB, scoreB = [], [], 0
    if allergen_idx is not None or vertical_by_values:
        ai = allergen_idx if allergen_idx is not None else 0
        menu_cols = [headers[j] for j in range(len(headers)) if j != ai and str(headers[j]).strip()]
        aller_rows = []
        for r in data[:28]:
            if not any((c or "").strip() for c in r): continue
            name = str(r[ai]).strip() if ai < len(r) else ""
            if not name: continue
            vals = []
            for j in range(len(headers)):
                if j == ai: continue
                if j < len(r): vals.append(_to_symbol(r[j]))
            aller_rows.append((name, vals))
        allergensB = [name for name,_ in aller_rows]
        for j, mcol in enumerate(menu_cols):
            row = {"menu": mcol}
            for name, vals in aller_rows:
                row[name] = vals[j] if j < len(vals) else "－"
            if any(row.get(a) != "－" for a in allergensB):
                outB.append(row)
        if outB and allergensB:
            scoreB = score_rows(outB, allergensB)

    outC, allergensC, scoreC = [], [], 0
    if not (scoreA or scoreB):
        allergensC = [h for h in headers[1:] if str(h).strip()][:28]
        for r in data:
            rec = dict(zip(headers, r))
            menu = (rec.get(h0) or "").strip()
            if not menu: continue
            row = {"menu": menu}
            for a in allergensC:
                row[a] = _to_symbol(rec.get(a))
            if any(row[a] != "－" for a in allergensC):
                outC.append(row)
        if outC and allergensC:
            scoreC = score_rows(outC, allergensC)

    best = max([(scoreA,outA,allergensA),(scoreB,outB,allergensB),(scoreC,outC,allergensC)], key=lambda x:x[0])
    return best[1], best[2], best[0]

# ============== ユーティリティ ==============
def to_float(x) -> Optional[float]:
    if x is None: return None
    s = unicodedata.normalize("NFKC", str(x)).strip()
    if s == "" or s.lower() in {"nan","none","null","-"}: return None
    s = s.replace("°","").replace("，",".").replace("．",".")
    try: return float(s)
    except Exception: return None

def static_img(path: Optional[str]) -> str:
    p = (path or "").strip()
    return url_for("static", filename=f"img/{p}") if p else url_for("static", filename="img/placeholder.jpg")

# ============== DB ==============
DATABASE = APP_ROOT / "users.db"

def get_db() -> sqlite3.Connection:
    if "db" not in g:
        g.db = sqlite3.connect(DATABASE)
        g.db.row_factory = sqlite3.Row
    return g.db

@app.teardown_appcontext
def close_db(_exc=None) -> None:
    db = g.pop("db", None)
    if db is not None: db.close()
    

        
@app.route("/admin/posts")
def admin_posts():
    """
    投稿/コメントのモデレーション一覧
    クエリ:
      type=posts|comments（既定: posts）
      q=       本文/ユーザーID/ストアID の部分一致
      hidden=0|1|all （既定0=表示中）
      sort=new|old （既定new）
      limit=200
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()
    t = (request.args.get("type") or "posts").strip()
    if t not in ("posts", "comments"):
        t = "posts"

    q = (request.args.get("q") or "").strip()
    hidden = (request.args.get("hidden") or "0").strip()
    sort = (request.args.get("sort") or "new").strip()
    try:
        limit = max(1, min(1000, int(request.args.get("limit") or "200")))
    except Exception:
        limit = 200

    rows = []
    total = 0

    if t == "posts":
        if _table_exists("posts"):
            where = []
            params = []
            # 論理削除は常に除外
            where.append("deleted_at IS NULL")
            if hidden in ("0", "1"):
                where.append("hidden = ?")
                params.append(1 if hidden == "1" else 0)
            if q:
                where.append("(CAST(user_id AS TEXT) LIKE ? OR CAST(store_id AS TEXT) LIKE ? OR COALESCE(content,'') LIKE ?)")
                like = f"%{q}%"
                params += [like, like, like]

            sql = "SELECT id, user_id, store_id, content, hidden, created_at FROM posts"
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY created_at " + ("DESC" if sort == "new" else "ASC")
            sql += " LIMIT ?"
            params.append(limit)
            rows = db.execute(sql, params).fetchall()
            total = len(rows)
        else:
            rows, total = [], 0

    else:  # comments
        if _table_exists("post_comments"):
            where = []
            params = []
            where.append("deleted_at IS NULL")
            if hidden in ("0", "1"):
                where.append("hidden = ?")
                params.append(1 if hidden == "1" else 0)
            if q:
                where.append("(CAST(user_id AS TEXT) LIKE ? OR CAST(post_id AS TEXT) LIKE ? OR COALESCE(comment,'') LIKE ?)")
                like = f"%{q}%"
                params += [like, like, like]

            sql = ("SELECT id, post_id, user_id, comment, hidden, created_at "
                   "FROM post_comments")
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY created_at " + ("DESC" if sort == "new" else "ASC")
            sql += " LIMIT ?"
            params.append(limit)
            rows = db.execute(sql, params).fetchall()
            total = len(rows)
        else:
            rows, total = [], 0

    return render_template(
        "admin_posts.html",
        type=t, rows=rows, total=total,
        q=q, hidden=hidden, sort=sort, limit=limit
    )

@app.route("/admin/posts/mod", methods=["POST"])
def admin_posts_mod():
    """
    行アクション:
      type=posts|comments
      action=hide|unhide|soft_delete
      id=（対象のID）
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    # CSRF
    _ = request.form.get("csrf_token")  # base 側の csrf_token() が検証する前提（無ければ後方互換で通す）

    t = (request.form.get("type") or "posts").strip()
    act = (request.form.get("action") or "").strip()
    try:
        target_id = int(request.form.get("id") or "0")
    except Exception:
        target_id = 0

    if t not in ("posts", "comments") or target_id <= 0:
        flash("不正なリクエストです。", "error")
        return redirect(url_for("admin_posts", type=t))

    db = get_db()

    if t == "posts" and _table_exists("posts"):
        if act == "hide":
            db.execute("UPDATE posts SET hidden=1 WHERE id=? AND deleted_at IS NULL", (target_id,))
        elif act == "unhide":
            db.execute("UPDATE posts SET hidden=0 WHERE id=? AND deleted_at IS NULL", (target_id,))
        elif act == "soft_delete":
            db.execute("UPDATE posts SET deleted_at=CURRENT_TIMESTAMP WHERE id=? AND deleted_at IS NULL", (target_id,))
        db.commit()

    elif t == "comments" and _table_exists("post_comments"):
        if act == "hide":
            db.execute("UPDATE post_comments SET hidden=1 WHERE id=? AND deleted_at IS NULL", (target_id,))
        elif act == "unhide":
            db.execute("UPDATE post_comments SET hidden=0 WHERE id=? AND deleted_at IS NULL", (target_id,))
        elif act == "soft_delete":
            db.execute("UPDATE post_comments SET deleted_at=CURRENT_TIMESTAMP WHERE id=? AND deleted_at IS NULL", (target_id,))
        db.commit()

    # 監査ログ（存在すれば記録）
    try:
        if _table_exists("admin_audit_logs"):
            admin_id = session.get("admin_id")
            ua = request.headers.get("User-Agent", "")
            ip = request.headers.get("X-Forwarded-For") or request.remote_addr or ""
            payload = json.dumps({"type": t, "action": act, "id": target_id}, ensure_ascii=False)
            get_db().execute(
                "INSERT INTO admin_audit_logs(admin_id, action, target, diff_json, ip, ua, created_at) "
                "VALUES(?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)",
                (admin_id, "moderate", f"{t}:{target_id}", payload, ip, ua)
            )
            get_db().commit()
    except Exception:
        pass

    # 復帰
    flash("更新しました。", "success")
    return redirect(url_for("admin_posts", type=t))


def _migrate_users_columns() -> None:
    db = get_db()
    cols = {r["name"] for r in db.execute("PRAGMA table_info(users)").fetchall()}

    # 必須列を順次追加（何度呼んでもOK）
    desired = [
        ("name",           "TEXT"),
        ("password_hash",  "TEXT"),
        ("avatar_path",    "TEXT"),
        ("phone",          "TEXT"),
        ("bio",            "TEXT"),
        ("email_verified", "INTEGER NOT NULL DEFAULT 0"),
        ("deleted_at",     "TIMESTAMP"),
        # ★ created_at は ALTER では DEFAULT を付けない（SQLite 制約）
        ("created_at",     "TIMESTAMP"),
    ]
    for col, decl in desired:
        if col not in cols:
            db.execute(f"ALTER TABLE users ADD COLUMN {col} {decl}")
    db.commit()

    # 既存行：NULL は現在時刻で埋める
    try:
        db.execute("UPDATE users SET created_at = COALESCE(created_at, CURRENT_TIMESTAMP)")
        db.commit()
    except Exception:
        pass

    # 以後の INSERT で created_at が NULL のまま入った場合に自動で埋めるトリガ
    db.executescript("""
        CREATE TRIGGER IF NOT EXISTS trg_users_created_at_default
        AFTER INSERT ON users
        WHEN NEW.created_at IS NULL
        BEGIN
          UPDATE users SET created_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
        END;
    """)
    db.commit()

@app.route("/admin/stores")
def admin_stores():
    """
    ストア別サマリ（閲覧用）
    - Sheetsの店舗一覧を基準に、favorites / reviews / store_announcements / store_claims をマージ
    - クエリ:
        q=（名称/カテゴリ/住所の部分一致）
        sort=fav_desc|review_desc|rating_desc|id_asc|id_desc
        limit=200
        cat=<カテゴリ完全一致>
        ann=1       （お知らせありのみ）
        claims=1    （申請ありのみ）
        reviews=1   （レビューありのみ）
        favs=1      （お気に入りありのみ）
        min_rating=<0.0-5.0>
        export=csv  （CSVエクスポート）
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    # --- Sheets から店舗マスタ ---
    stores_raw = []
    try:
        stores_raw = list(get_all_stores_from_sheet_cached() or [])
    except Exception:
        stores_raw = []

    # 正規化
    stores_master = []
    cats_set = set()
    for s in stores_raw:
        sid = s.get("id") or s.get("store_id")
        try:
            sid_int = int(str(sid)) if sid is not None and str(sid).strip() != "" else None
        except Exception:
            sid_int = None
        name = s.get("name") or s.get("store_name") or (f"店舗#{sid}" if sid_int else "(不明)")
        cat  = s.get("category") or s.get("カテゴリ") or ""
        addr = s.get("address") or s.get("住所") or ""
        if cat.strip():
            cats_set.add(cat.strip())
        stores_master.append({"id": sid_int, "name": name, "category": cat, "address": addr})

    categories = sorted(cats_set)

    # --- ローカル集計（存在しないテーブルはスキップ） ---
    fav_map = {}
    if _table_exists("favorites"):
        for r in db.execute("SELECT store_id, COUNT(*) AS c FROM favorites GROUP BY store_id").fetchall():
            try:
                fav_map[int(r["store_id"])] = int(r["c"])
            except Exception:
                pass

    review_count_map, review_avg_map = {}, {}
    if _table_exists("reviews"):
        for r in db.execute(
            "SELECT store_id, COUNT(*) AS c, AVG(rating) AS a FROM reviews GROUP BY store_id"
        ).fetchall():
            try:
                sid = int(r["store_id"])
                review_count_map[sid] = int(r["c"])
                review_avg_map[sid] = round(float(r["a"]), 2) if r["a"] is not None else None
            except Exception:
                continue

    ann_map = {}
    if _table_exists("store_announcements"):
        try:
            for r in db.execute(
                "SELECT store_id, MAX(created_at) AS last FROM store_announcements GROUP BY store_id"
            ).fetchall():
                ann_map[int(r["store_id"])] = r["last"]
        except Exception:
            pass

    claim_map = {}
    if _table_exists("store_claims"):
        try:
            for r in db.execute("SELECT store_id, COUNT(*) AS c FROM store_claims GROUP BY store_id").fetchall():
                claim_map[int(r["store_id"])] = int(r["c"])
        except Exception:
            pass

    # --- クエリ取得 ---
    q = (request.args.get("q") or "").strip().lower()
    sort = (request.args.get("sort") or "fav_desc").strip()
    try:
        limit = max(1, min(1000, int(request.args.get("limit") or "200")))
    except Exception:
        limit = 200

    cat = (request.args.get("cat") or "").strip()
    flag_ann    = (request.args.get("ann") or "") in ("1", "true", "yes", "on")
    flag_claims = (request.args.get("claims") or "") in ("1", "true", "yes", "on")
    flag_reviews= (request.args.get("reviews") or "") in ("1", "true", "yes", "on")
    flag_favs   = (request.args.get("favs") or "") in ("1", "true", "yes", "on")
    try:
        min_rating = float(request.args.get("min_rating") or "0")
    except Exception:
        min_rating = 0.0

    # --- マージ & フィルタ ---
    rows = []
    for s in stores_master:
        sid = s["id"]
        fav = fav_map.get(sid, 0) if sid is not None else 0
        rcount = review_count_map.get(sid, 0) if sid is not None else 0
        ravg = review_avg_map.get(sid) if sid is not None else None
        has_ann = bool(ann_map.get(sid)) if sid is not None else False
        claims  = claim_map.get(sid, 0) if sid is not None else 0

        # 部分一致検索
        hay = " ".join([s.get("name",""), s.get("category",""), s.get("address","")]).lower()
        if q and q not in hay:
            continue
        # カテゴリ完全一致
        if cat and (s.get("category","").strip() != cat):
            continue
        # フラグ
        if flag_ann and not has_ann:
            continue
        if flag_claims and not (claims > 0):
            continue
        if flag_reviews and not (rcount > 0):
            continue
        if flag_favs and not (fav > 0):
            continue
        if min_rating > 0 and (ravg is None or ravg < min_rating):
            continue

        rows.append({
            "id": sid,
            "name": s["name"],
            "category": s["category"],
            "address": s["address"],
            "favorites": fav,
            "reviews": rcount,
            "rating": ravg,
            "has_announcement": has_ann,
            "claims": claims,
        })

    # --- ソート ---
    def key_fav(x):     return (-x["favorites"], x["id"] or 0)
    def key_rev(x):     return (-x["reviews"],   x["id"] or 0)
    def key_rating(x):  return (-(x["rating"] or 0.0), x["id"] or 0)
    def key_id_asc(x):  return (x["id"] or 0)
    def key_id_desc(x): return (-(x["id"] or 0))

    sort_map = {
        "fav_desc": key_fav,
        "review_desc": key_rev,
        "rating_desc": key_rating,
        "id_asc": key_id_asc,
        "id_desc": key_id_desc,
    }
    rows.sort(key=sort_map.get(sort, key_fav))
    rows = rows[:limit]

    # --- CSV エクスポート ---
    if (request.args.get("export") or "") == "csv":
        import csv, io
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["id","name","category","address","favorites","reviews","rating","has_announcement","claims"])
        for r in rows:
            w.writerow([
                r["id"], r["name"], r["category"], r["address"],
                r["favorites"], r["reviews"], r["rating"] if r["rating"] is not None else "",
                1 if r["has_announcement"] else 0, r["claims"]
            ])
        from flask import Response
        return Response(
            buf.getvalue(),
            mimetype="text/csv; charset=utf-8",
            headers={"Content-Disposition": "attachment; filename=stores_summary.csv"},
        )

    return render_template(
        "admin_stores.html",
        rows=rows, q=q, sort=sort, limit=limit,
        cat=cat, categories=categories,
        flag_ann=flag_ann, flag_claims=flag_claims,
        flag_reviews=flag_reviews, flag_favs=flag_favs,
        min_rating=min_rating
    )


def init_db() -> None:
    db = get_db()
    # init_db() 内の最初の CREATE TABLE ブロックの users をこれに差し替え
    db.executescript("""
         CREATE TABLE IF NOT EXISTS users(
           id INTEGER PRIMARY KEY AUTOINCREMENT,
           email TEXT UNIQUE,
           password_hash TEXT,
           email_verified INTEGER DEFAULT 0,
           deleted_at TIMESTAMP,
           created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
         );
        CREATE TABLE IF NOT EXISTS favorites(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          user_id INTEGER NOT NULL,
          store_id INTEGER NOT NULL,
          UNIQUE(user_id, store_id)
        );
        CREATE TABLE IF NOT EXISTS reviews(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          user_id INTEGER NOT NULL,
          store_id INTEGER NOT NULL,
          rating INTEGER NOT NULL CHECK(rating BETWEEN 1 AND 5),
          comment TEXT,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
     """)

    _migrate_users_columns()

    db.execute("""
        CREATE TABLE IF NOT EXISTS user_allergens(
          user_id   INTEGER NOT NULL,
          allergen  TEXT    NOT NULL,
          severity  TEXT    NOT NULL CHECK(severity IN ('strict','medium','loose')),
          PRIMARY KEY(user_id, allergen)
        )
    """); db.commit()
    db.execute("""
        CREATE TABLE IF NOT EXISTS user_allergen_others(
          user_id  INTEGER NOT NULL,
          label    TEXT    NOT NULL,
          severity TEXT    NOT NULL CHECK(severity IN ('strict','medium','loose')),
          PRIMARY KEY(user_id, label)
        )
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS posts(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          store_id INTEGER NOT NULL,
          user_id  INTEGER NOT NULL,
          rating   INTEGER NOT NULL CHECK(rating BETWEEN 1 AND 5),
          body     TEXT,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS post_photos(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          post_id INTEGER NOT NULL,
          path TEXT NOT NULL,
          ord  INTEGER NOT NULL DEFAULT 0,
          width INTEGER,
          height INTEGER
        );
        CREATE TABLE IF NOT EXISTS post_comments(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          post_id INTEGER NOT NULL,
          user_id INTEGER NOT NULL,
          body TEXT NOT NULL,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS post_likes(
          user_id INTEGER NOT NULL,
          post_id INTEGER NOT NULL,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          PRIMARY KEY(user_id, post_id)
        );
        CREATE TABLE IF NOT EXISTS hashtags(
          tag  TEXT PRIMARY KEY,
          uses INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS post_tags(
          post_id INTEGER NOT NULL,
          tag     TEXT NOT NULL,
          PRIMARY KEY(post_id, tag)
        );
        CREATE VIRTUAL TABLE IF NOT EXISTS posts_fts USING fts5(
          body, content='posts', content_rowid='id', tokenize='unicode61'
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS reports(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          kind TEXT NOT NULL CHECK(kind IN ('store','post','allergy')),
          target_id INTEGER NOT NULL,
          reason TEXT NOT NULL,
          body TEXT,
          status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','triaged','done','ignored')),
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          handled_at TIMESTAMP
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS store_claims(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          store_id   INTEGER NOT NULL,
          user_id    INTEGER NOT NULL,
          name       TEXT,
          email      TEXT,
          phone      TEXT,
          position   TEXT,
          message    TEXT,
          evidence_path TEXT,
          status     TEXT NOT NULL DEFAULT 'pending' CHECK(status IN ('pending','approved','rejected')),
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          handled_at TIMESTAMP
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS store_announcements(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          store_id  INTEGER NOT NULL,
          user_id   INTEGER NOT NULL,
          title     TEXT    NOT NULL,
          body      TEXT,
          link_url  TEXT,
          pin_until TIMESTAMP,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS notifications(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          user_id   INTEGER NOT NULL,
          kind      TEXT    NOT NULL CHECK(kind IN ('post','announcement')),
          store_id  INTEGER NOT NULL,
          item_id   INTEGER NOT NULL,
          title     TEXT,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          read_at   TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS user_notify_pref(
          user_id INTEGER PRIMARY KEY,
          email_posts INTEGER NOT NULL DEFAULT 0,
          email_announcements INTEGER NOT NULL DEFAULT 0
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS auth_throttle(
          identifier TEXT PRIMARY KEY,
          fail_count INTEGER NOT NULL DEFAULT 0,
          locked_until TIMESTAMP
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS admins(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          email TEXT UNIQUE NOT NULL,
          password_hash TEXT NOT NULL,
          name TEXT,
          last_login TIMESTAMP
        );
    """); db.commit()
    
    db.executescript("""
        CREATE TABLE IF NOT EXISTS store_overrides(
          store_id   INTEGER NOT NULL,
          key        TEXT    NOT NULL,
          value      TEXT,
          updated_by INTEGER,
          updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          PRIMARY KEY(store_id, key)
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS safety_overrides(
          store_id   INTEGER PRIMARY KEY,
          safe       TEXT CHECK(safe IN ('ok','warn','ng')),
          trust      TEXT CHECK(trust IN ('high','mid','low','pending')),
          note       TEXT,
          updated_by INTEGER,
          updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """); db.commit()
    
    db.executescript("""
        CREATE TABLE IF NOT EXISTS global_announcements(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          title     TEXT    NOT NULL,
          body      TEXT,
          link_url  TEXT,
          pin_until TIMESTAMP,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          created_by INTEGER
        );
    """); db.commit()

    db.executescript("""
        CREATE TABLE IF NOT EXISTS admin_audit_logs(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          admin_id INTEGER,
          action   TEXT NOT NULL,
          target   TEXT,
          payload_json TEXT,
          ip       TEXT,
          ua       TEXT,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """); db.commit()

    _bootstrap_admin_if_needed()
    _migrate_moderation_columns()
    _migrate_admins_role()
    _migrate_store_claims()



def _table_exists(name: str) -> bool:
    db = get_db()
    row = db.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?",
        (name,)
    ).fetchone()
    return bool(row)

@app.route("/admin/metrics")
def admin_metrics():
    """
    軽量KPIパネル（閲覧専用）。
    - ユーザー/投稿の合計
    - 直近7日の新規ユーザー・投稿
    - 直近14日の通報件数（reports が無ければ0）
    - お気に入り上位店舗（favorites が無ければ空）
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    # 合計値（テーブルがない場合は0）
    total_users = total_posts = total_comments = 0
    try:
        if _table_exists("users"):
            total_users = db.execute("SELECT COUNT(*) AS c FROM users WHERE deleted_at IS NULL").fetchone()["c"]
    except Exception:
        pass
    try:
        if _table_exists("posts"):
            total_posts = db.execute("SELECT COUNT(*) AS c FROM posts").fetchone()["c"]
    except Exception:
        pass
    try:
        if _table_exists("post_comments"):
            total_comments = db.execute("SELECT COUNT(*) AS c FROM post_comments").fetchone()["c"]
    except Exception:
        pass

    # 直近7日の新規ユーザー
    days7 = _last_n_dates(7)
    new_users_7d = []
    if _table_exists("users"):
        rows = db.execute(
            "SELECT strftime('%Y-%m-%d', created_at) AS d, COUNT(*) AS c "
            "FROM users WHERE created_at >= date('now','-6 day') "
            "GROUP BY d"
        ).fetchall()
        m = {r["d"]: int(r["c"]) for r in rows if r["d"]}
        new_users_7d = [{"date": d, "count": m.get(d, 0)} for d in days7]
    else:
        new_users_7d = [{"date": d, "count": 0} for d in days7]

    # 直近7日の投稿数
    new_posts_7d = []
    if _table_exists("posts"):
        rows = db.execute(
            "SELECT strftime('%Y-%m-%d', created_at) AS d, COUNT(*) AS c "
            "FROM posts WHERE created_at >= date('now','-6 day') "
            "GROUP BY d"
        ).fetchall()
        m = {r["d"]: int(r["c"]) for r in rows if r["d"]}
        new_posts_7d = [{"date": d, "count": m.get(d, 0)} for d in days7]
    else:
        new_posts_7d = [{"date": d, "count": 0} for d in days7]

    # 直近14日の通報件数
    days14 = _last_n_dates(14)
    reports_14d = []
    if _table_exists("reports"):
        rows = db.execute(
            "SELECT strftime('%Y-%m-%d', created_at) AS d, COUNT(*) AS c "
            "FROM reports WHERE created_at >= date('now','-13 day') "
            "GROUP BY d"
        ).fetchall()
        m = {r["d"]: int(r["c"]) for r in rows if r["d"]}
        reports_14d = [{"date": d, "count": m.get(d, 0)} for d in days14]
    else:
        reports_14d = [{"date": d, "count": 0} for d in days14]

    # お気に入り上位店舗
    top_favs = []
    store_names = {}
    try:
        # 店名辞書（Sheetsキャッシュ優先）
        for s in get_all_stores_from_sheet_cached():
            sid = str(s.get("id") or s.get("store_id") or "")
            if sid:
                store_names[sid] = s.get("name") or s.get("store_name") or f"店舗#{sid}"
    except Exception:
        pass

    if _table_exists("favorites"):
        rows = db.execute(
            "SELECT store_id, COUNT(*) AS c FROM favorites GROUP BY store_id ORDER BY c DESC LIMIT 10"
        ).fetchall()
        for r in rows:
            sid = str(r["store_id"])
            top_favs.append({
                "store_id": r["store_id"],
                "name": store_names.get(sid, f"店舗#{sid}"),
                "count": int(r["c"])
            })
            
        # 直近7日の新規ユーザー
    days7 = _last_n_dates(7)
    new_users_7d = []

    # ここで列の存在を保証（無ければ追加）
    _ensure_column('users', 'created_at', 'created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP')

    if _table_exists("users"):
        rows = db.execute(
            "SELECT strftime('%Y-%m-%d', created_at) AS d, COUNT(*) AS c "
            "FROM users WHERE created_at >= date('now','-6 day') "
            "GROUP BY d"
        ).fetchall()
        m = {r["d"]: int(r["c"]) for r in rows if r["d"]}
        new_users_7d = [{"date": d, "count": m.get(d, 0)} for d in days7]
    else:
        new_users_7d = [{"date": d, "count": 0} for d in days7]


    return render_template(
        "admin_metrics.html",
        total_users=total_users,
        total_posts=total_posts,
        total_comments=total_comments,
        new_users_7d=new_users_7d,
        new_posts_7d=new_posts_7d,
        reports_14d=reports_14d,
        top_favs=top_favs
    )

def _last_n_dates(n: int) -> list:
    """今日を含む直近 n 日の 'YYYY-MM-DD' 配列（古い→新しい順）"""
    import datetime as _dt
    today = _dt.date.today()
    days = [(today - _dt.timedelta(days=i)).strftime("%Y-%m-%d") for i in range(n - 1, -1, -1)]
    return days

def _migrate_store_claims() -> None:
    """
    既存 store_claims を審査UIで扱えるように最低限の列を安全に追加。
    何度呼んでも安全（存在チェック→ALTER）。
    """
    db = get_db()
    if not _table_exists("store_claims"):
        return
    cols = {r["name"] for r in db.execute("PRAGMA table_info(store_claims)").fetchall()}

    # よくある列名を追加（なければ）
    add_cols = [
        ("status",        "TEXT"),                      # 'pending' | 'approved' | 'rejected'
        ("applicant_name","TEXT"),
        ("applicant_email","TEXT"),
        ("proof_image",   "TEXT"),                      # 証憑画像パス or URL
        ("note",          "TEXT"),
        ("verdict_note",  "TEXT"),
        ("decided_by",    "INTEGER"),
        ("decided_at",    "TIMESTAMP"),
        ("created_at",    "TIMESTAMP"),                 # 既存行は下で埋める
    ]
    for col, decl in add_cols:
        if col not in cols:
            db.execute(f"ALTER TABLE store_claims ADD COLUMN {col} {decl}")
    db.commit()

    # 既存行の created_at を埋め、status 未設定は pending に寄せる
    db.execute("UPDATE store_claims SET created_at = COALESCE(created_at, CURRENT_TIMESTAMP)")
    try:
        db.execute("UPDATE store_claims SET status = COALESCE(NULLIF(status,''),'pending')")
    except Exception:
        pass
    db.commit()

def _bootstrap_admin_if_needed():
    """ENVから管理者を1件以上用意。ADMIN_EMAIL が設定されていればそれを最優先。"""
    db = get_db()
    row = db.execute("SELECT COUNT(*) AS c FROM admins").fetchone()
    if row and int(row["c"]) > 0 and not ADMIN_EMAIL:
        return

    email = ADMIN_EMAIL or "admin@example.com"
    if ADMIN_PASSWORD_HASH:
        ph = ADMIN_PASSWORD_HASH.strip()
    else:
        pwd = ADMIN_PASSWORD or secrets.token_urlsafe(10)
        ph = generate_password_hash(pwd)
        if not ADMIN_PASSWORD and not ADMIN_PASSWORD_HASH:
            app.logger.warning("[ADMIN] 初期管理者を作成しました email=%s / temp_password=%s  ※本番は必ず変更してください", email, pwd)

    cur = db.execute("SELECT id FROM admins WHERE email=?", (email,))
    if cur.fetchone():
        db.execute("UPDATE admins SET password_hash=? WHERE email=?", (ph, email))
    else:
        db.execute("INSERT INTO admins(email,password_hash,name) VALUES (?,?,?)", (email, ph, "Administrator"))
    db.commit()
    
def _migrate_admins_role() -> None:
    """admins テーブルに role 列を追加し、既存データを初期化する"""
    db = get_db()
    # role 列が無ければ追加
    cols = {r["name"] for r in db.execute("PRAGMA table_info(admins)").fetchall()}
    if "role" not in cols:
        db.execute("ALTER TABLE admins ADD COLUMN role TEXT")  # super / moderator / support
        db.commit()

    # まだ role が入っていない行にデフォルトを入れる
    rows = db.execute("SELECT id, role FROM admins ORDER BY id ASC").fetchall()
    if not rows:
        return
    # すでに誰か super が居るか
    has_super = any((r["role"] or "").strip() == "super" for r in rows)

    if not has_super:
        # 最小IDを super、他は support にしておく（初期ブートストラップ）
        first_id = int(rows[0]["id"])
        db.execute("UPDATE admins SET role='super' WHERE id=?", (first_id,))
        if len(rows) > 1:
            db.execute("UPDATE admins SET role='support' WHERE id <> ? AND (role IS NULL OR role='')", (first_id,))
        db.commit()
    else:
        # 未設定(None/空文字)の行だけ support を入れる
        db.execute("UPDATE admins SET role='support' WHERE (role IS NULL OR role='')")
        db.commit()

# ============== セッション前処理 ==============
@app.before_request
def _before() -> None:
    init_db()
    session.permanent = True
    if "user_id" not in session:
        session["user_id"] = 1  # ゲストID
    db = get_db()
    db.execute("INSERT OR IGNORE INTO users(id,email) VALUES (?,?)",
               (session["user_id"], session.get("user_email","")))
    db.commit()

# ============== Admin helpers ==============
def admin_logged_in() -> bool:
    return bool(session.get("admin_id"))

def require_admin():
    if not admin_logged_in():
        nxt = request.path
        return redirect(url_for("admin_login", next=nxt))
    return None

def admin_flash_not_logged():
    flash("管理者ログインが必要です。", "error")

# ============== CSRF & Jinja ==============
def _ensure_csrf() -> str:
    t = session.get("_csrf_token")
    if not t:
        t = secrets.token_urlsafe(16)
        session["_csrf_token"] = t
    return t

def _ensure_column(table: str, col: str, decl: str) -> None:
    """SQLite: 既存テーブルにカラムが無ければ ALTER TABLE で追加。何度呼んでもOK。"""
    db = get_db()
    cols = {r["name"] for r in db.execute(f"PRAGMA table_info({table})").fetchall()}
    if col not in cols:
        db.execute(f"ALTER TABLE {table} ADD COLUMN {decl}")
        db.commit()

def _current_admin_role() -> str:
    """現在ログイン中の管理者ロール（未ログイン/不明は空文字）。"""
    aid = session.get("admin_id")
    if not aid:
        return ""
    db = get_db()
    row = db.execute("SELECT COALESCE(role,'super') AS role FROM admins WHERE id=?", (aid,)).fetchone()
    return (row["role"] if row else "") or ""


# パス接頭辞ごとの許可ロール
_RBAC_RULES = [
    ("/admin/stores/", ["super"]),            # override / safety は super のみ
    ("/admin/tags",    ["super"]),            # タグ統合等は super のみ
    ("/admin/announcements", ["super"]),      # 全体お知らせ
    ("/admin/logs",    ["super"]),            # 監査ログ
    ("/admin/admins",  ["super"]),            # 管理者一覧/ロール編集
    ("/admin/users",   ["super", "support"]), # 一般ユーザー管理
    ("/admin/sheets",  ["super", "support"]), # Sheets キャッシュ操作
    ("/admin/posts",   ["super", "moderator"]),
    ("/admin/comments",["super", "moderator"]),
    ("/admin/reports", ["super", "moderator"]),  # 通報（あれば）
    # ダッシュボード /admin は全ロールOK
]


@app.before_request
def _rbac_gate():
    """
    /admin/* でのロールチェック。
    - 未ログインは各ルートの require_admin に任せる
    - super は常に通す
    - 該当ルールが無ければ通す（=既存との後方互換優先）
    """
    path = request.path or ""
    if not path.startswith("/admin/"):
        return
    if path in ("/admin/login", "/admin/logout"):
        return

    role = _current_admin_role()
    if not role:  # 未ログインは各ビュー関数の guard に任せる
        return
    if role == "super":
        return

    for prefix, allowed in _RBAC_RULES:
        if path.startswith(prefix):
            if role not in allowed:
                flash("この操作を行う権限がありません。", "error")
                return redirect(url_for("admin_dashboard"))
            break

@app.route("/admin/admins", methods=["GET", "POST"])
def admin_admins():
    """管理者一覧とロール変更。super のみ。"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard

    # super 以外はダッシュボードへ
    if _current_admin_role() != "super":
        flash("このページは super 管理者のみが利用できます。", "error")
        return redirect(url_for("admin_dashboard"))

    db = get_db()

    if request.method == "POST":
        _ = _ensure_csrf()
        aid = int(request.form.get("id"))
        role = (request.form.get("role") or "").strip()
        if role not in ("super", "moderator", "support"):
            flash("不正なロールです。", "error")
            return redirect(url_for("admin_admins"))
        db.execute("UPDATE admins SET role=? WHERE id=?", (role, aid))
        db.commit()
        flash("ロールを更新しました。", "success")
        return redirect(url_for("admin_admins"))

    rows = db.execute("SELECT id, email, name, role, last_login FROM admins ORDER BY id ASC").fetchall()
    return render_template("admin_admins.html", rows=rows, my_id=session.get("admin_id"))


def _migrate_moderation_columns() -> None:
    """モデレーション用の新規カラム（後方互換）。"""
    # posts に hidden_at / hidden_by
    _ensure_column("posts", "hidden_at", "hidden_at TIMESTAMP")
    _ensure_column("posts", "hidden_by", "hidden_by INTEGER")
    # post_comments に hidden_at / hidden_by
    _ensure_column("post_comments", "hidden_at", "hidden_at TIMESTAMP")
    _ensure_column("post_comments", "hidden_by", "hidden_by INTEGER")
    # users に投稿停止の期限
    _ensure_column("users", "post_ban_until", "post_ban_until TIMESTAMP")

       
def _sanitize_for_audit(d: dict) -> dict:
    """ログに残す前に秘匿フィールドをマスク。"""
    out = {}
    for k, v in (d or {}).items():
        if k.lower() in ("csrf_token",):
            continue
        if "password" in k.lower() or "token" in k.lower() or "secret" in k.lower():
            out[k] = "***"
        else:
            out[k] = v
    return out



def _send_mail_safely(to_addr: str, subject: str, body: str) -> None:
    """SMTP設定が無ければログ出力で代替。既存 send_email があればそれを使う。"""
    try:
        if to_addr and "send_email" in globals() and callable(globals()["send_email"]):
            globals()["send_email"](to_addr, subject, body)
        else:
            current_app.logger.info(f"[MAIL] to={to_addr} subj={subject}\n{body}")
    except Exception:
        current_app.logger.exception("mail send failed")

@app.route("/admin/claims/decide", methods=["POST"])
def admin_claims_decide():
    """
    action=approve|reject, id, message(任意)
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    _ = request.form.get("csrf_token")  # base 側の csrf_token() 想定（無ければ互換のためスルー）

    action = (request.form.get("action") or "").strip()
    try:
        cid = int(request.form.get("id") or "0")
    except Exception:
        cid = 0
    message = (request.form.get("message") or "").strip()

    if action not in ("approve","reject") or cid <= 0:
        flash("不正なリクエストです。", "error")
        return redirect(url_for("admin_claims"))

    db = get_db()
    if not _table_exists("store_claims"):
        flash("store_claims テーブルがありません。", "error")
        return redirect(url_for("admin_claims"))

    # 申請の取得
    row = db.execute("SELECT * FROM store_claims WHERE id=?", (cid,)).fetchone()
    if not row:
        flash("申請が見つかりません。", "error")
        return redirect(url_for("admin_claims"))

    # 申請者メール（列になければ users から）
    applicant_email = row.get("applicant_email")
    if (not applicant_email) and _table_exists("users") and row.get("user_id"):
        u = db.execute("SELECT email FROM users WHERE id=?", (row["user_id"],)).fetchone()
        if u:
            applicant_email = u["email"]

    # 更新
    status_val = "approved" if action == "approve" else "rejected"
    sets, params = [], []
    if "status" in {c["name"] for c in db.execute("PRAGMA table_info(store_claims)")}:
        sets.append("status=?"); params.append(status_val)
    if "verdict_note" in row.keys():
        sets.append("verdict_note=?"); params.append(message)
    if "decided_by" in row.keys():
        sets.append("decided_by=?"); params.append(session.get("admin_id"))
    if "decided_at" in row.keys():
        sets.append("decided_at=CURRENT_TIMESTAMP")
    upd = "UPDATE store_claims SET " + ", ".join(sets) + " WHERE id=?"
    params.append(cid)
    db.execute(upd, params)
    db.commit()

    # 監査ログ
    try:
        if _table_exists("admin_audit_logs"):
            payload = json.dumps({"claim_id": cid, "action": action, "message": message}, ensure_ascii=False)
            db.execute(
                "INSERT INTO admin_audit_logs(admin_id, action, target, diff_json, ip, ua, created_at) "
                "VALUES(?,?,?,?,?,?,CURRENT_TIMESTAMP)",
                (session.get("admin_id"), "claim_decide", f"store_claim:{cid}",
                 payload, request.headers.get("X-Forwarded-For") or request.remote_addr or "",
                 request.headers.get("User-Agent",""))
            )
            db.commit()
    except Exception:
        pass

    # 申請者へメール
    try:
        if applicant_email:
            subj = f"[Luminity] オーナー申請が{('承認' if action=='approve' else '却下')}されました"
            body = (
                f"この度は店舗オーナー申請（ID: {cid} / 店舗ID: {row.get('store_id')}) をいただきありがとうございます。\n"
                f"審査結果: {('承認' if action=='approve' else '却下')}\n"
                + (f"メッセージ: {message}\n" if message else "")
                + "\n本メールに心当たりがない場合は破棄してください。"
            )
            _send_mail_safely(applicant_email, subj, body)
    except Exception:
        pass

    flash("審査結果を反映しました。", "success")
    # 現在のフィルタを維持して戻る
    return redirect(url_for("admin_claims", status=request.args.get("status") or "pending"))

@app.before_request
def _audit_capture_admin_post():
    """/admin/* の POST を自動ロギング。ログインや静的などは除外。"""
    try:
        path = request.path or ""
        if request.method != "POST":
            return
        if not path.startswith("/admin/"):
            return
        # 除外ルート（ログイン/ログアウトなど資格情報を扱うもの）
        if path in ("/admin/login", "/admin/logout"):
            return
        # 最低限の情報
        action = (request.form.get("action") or request.endpoint or request.method).lower()
        payload = _sanitize_for_audit(request.form.to_dict(flat=True))
        admin_audit(action=action, target=path, payload=payload)
    except Exception as e:
        app.logger.info("audit_capture_skip: %s", e)
        return
        
@app.route("/admin/logs")
def admin_logs():
    """
    監査ログ一覧 / 検索 / CSVエクスポート
    GET:
      ?q=...（action/target/UA に部分一致）
      &admin_id=123
      &limit=200
      &export=csv で CSV ダウンロード
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard

    db = get_db()
    q = (request.args.get("q") or "").strip()
    admin_id = (request.args.get("admin_id") or "").strip()
    try:
        limit = max(1, min(1000, int(request.args.get("limit") or "200")))
    except Exception:
        limit = 200

    conds, params = [], []
    if q:
        conds.append("(action LIKE ? OR target LIKE ? OR ua LIKE ?)")
        like = f"%{q}%"
        params += [like, like, like]
    if admin_id:
        conds.append("admin_id = ?")
        params.append(int(admin_id))
    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    rows = db.execute(
        f"""SELECT id, admin_id, action, target, payload_json, ip, ua, created_at
              FROM admin_audit_logs {where}
             ORDER BY id DESC
             LIMIT ?""",
        (*params, limit)
    ).fetchall()

    if request.args.get("export") == "csv":
        # CSV 生成
        import csv, io
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["id","admin_id","action","target","payload_json","ip","ua","created_at"])
        for r in rows:
            w.writerow([r["id"], r["admin_id"], r["action"], r["target"], r["payload_json"], r["ip"], r["ua"], r["created_at"]])
        from flask import Response
        return Response(
            buf.getvalue(),
            mimetype="text/csv; charset=utf-8",
            headers={"Content-Disposition": "attachment; filename=audit_logs.csv"},
        )

    return render_template("admin_logs.html", rows=rows, q=q, admin_id=admin_id, limit=limit)

def admin_audit(action: str, target: Optional[str] = None, payload: Optional[dict] = None) -> None:
    """監査ログを1行記録。失敗してもアプリは止めない。"""
    try:
        db = get_db()
        db.execute(
            "INSERT INTO admin_audit_logs(admin_id, action, target, payload_json, ip, ua) "
            "VALUES(?,?,?,?,?,?)",
            (
                session.get("admin_id"),
                action[:120],
                (target or "")[:300],
                json.dumps(payload or {}, ensure_ascii=False),
                request.headers.get("X-Forwarded-For", request.remote_addr or ""),
                request.headers.get("User-Agent", "")[:300],
            ),
        )
        db.commit()
    except Exception as e:
        app.logger.info("audit_log_failed: %s", e)

# =========================
# Hashtag 管理ヘルパー
# =========================
def _recalc_hashtag_counts(target_tags: Optional[List[str]] = None) -> None:
    """
    hashtags.uses を post_tags の実数に同期する。
    target_tags が指定された場合は、そのタグだけ再計算（なければ全量）。
    """
    db = get_db()
    if target_tags:
        # 対象タグの現行カウントを取得して upsert
        q_marks = ",".join(["?"] * len(target_tags))
        rows = db.execute(
            f"SELECT tag, COUNT(*) AS c FROM post_tags WHERE tag IN ({q_marks}) GROUP BY tag",
            tuple(target_tags),
        ).fetchall()
        found = {r["tag"]: r["c"] for r in rows}
        for t in target_tags:
            c = int(found.get(t, 0))
            db.execute(
                "INSERT INTO hashtags(tag, uses) VALUES(?, ?) "
                "ON CONFLICT(tag) DO UPDATE SET uses=excluded.uses",
                (t, c),
            )
        db.commit()
    else:
        # 全量再計算
        rows = db.execute("SELECT tag, COUNT(*) AS c FROM post_tags GROUP BY tag").fetchall()
        for r in rows:
            db.execute(
                "INSERT INTO hashtags(tag, uses) VALUES(?, ?) "
                "ON CONFLICT(tag) DO UPDATE SET uses=excluded.uses",
                (r["tag"], int(r["c"])),
            )
        # post_tags に存在しないタグを 0 に（必要なら削除してもよいが安全のため残す）
        known = {r["tag"] for r in rows}
        ghost = db.execute("SELECT tag FROM hashtags").fetchall()
        for g in ghost:
            if g["tag"] not in known:
                db.execute(
                    "UPDATE hashtags SET uses=0 WHERE tag=?",
                    (g["tag"],),
                )
        db.commit()

def _notify_all_users(kind: str, store_id: int, item_id: int, title: str) -> int:
    """全ユーザーに notifications を作る（簡易版）。戻り値は作成件数。"""
    db = get_db()
    users = db.execute("SELECT id FROM users WHERE deleted_at IS NULL").fetchall()
    count = 0
    for u in users:
        try:
            db.execute(
                "INSERT INTO notifications(user_id, kind, store_id, item_id, title) VALUES(?,?,?,?,?)",
                (u["id"], kind, store_id, item_id, title[:200])
            )
            count += 1
        except Exception:
            # UNIQUE制約がある場合などはスキップ（今回は無し想定）
            pass
    db.commit()
    return count

@app.route("/admin/announcements", methods=["GET", "POST"])
def admin_announcements():
    """
    グローバルお知らせの作成/一覧/削除/ピン期間設定。
    POST:
      - action=new     : 新規作成して全ユーザーに通知
      - action=delete  : 削除
      - action=pin     : pin_until(ISO) を設定
      - action=unpin   : pin_until をNULLに
    GET:
      - ?q=...（タイトル部分一致）
      - ?active=1（現在ピン有効なものだけ）
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    if request.method == "POST":
        _ = _ensure_csrf()
        act = (request.form.get("action") or "").strip()

        try:
            if act == "new":
                title = (request.form.get("title") or "").strip()
                body  = (request.form.get("body") or "").strip()
                link  = (request.form.get("link_url") or "").strip() or None
                pin   = (request.form.get("pin_until") or "").strip() or None
                if not title:
                    raise ValueError("タイトルを入力してください。")
                cur = db.execute(
                    "INSERT INTO global_announcements(title, body, link_url, pin_until, created_by) "
                    "VALUES(?,?,?,?,?)",
                    (title, body, link, pin, session.get("admin_id"))
                )
                ann_id = cur.lastrowid
                db.commit()
                # 通知投入（kind='announcement', store_id=0）
                made = _notify_all_users(kind="announcement", store_id=0, item_id=ann_id, title=title)
                flash(f"お知らせを作成し、{made}件の通知を作成しました。", "success")
                return redirect(url_for("admin_announcements"))

            elif act == "delete":
                ann_id = int(request.form.get("id"))
                db.execute("DELETE FROM global_announcements WHERE id=?", (ann_id,))
                # 通知は履歴として残す（必要なら同時削除も可）
                db.commit()
                flash("お知らせを削除しました。", "success")
                return redirect(url_for("admin_announcements"))

            elif act == "pin":
                ann_id = int(request.form.get("id"))
                pin = (request.form.get("pin_until") or "").strip() or None
                db.execute("UPDATE global_announcements SET pin_until=? WHERE id=?", (pin, ann_id))
                db.commit()
                flash("ピン期間を更新しました。", "success")
                return redirect(url_for("admin_announcements"))

            elif act == "unpin":
                ann_id = int(request.form.get("id"))
                db.execute("UPDATE global_announcements SET pin_until=NULL WHERE id=?", (ann_id,))
                db.commit()
                flash("ピンを解除しました。", "success")
                return redirect(url_for("admin_announcements"))

            else:
                flash("不明な操作です。", "error")
                return redirect(url_for("admin_announcements"))

        except Exception as e:
            app.logger.info("admin_announcements error: %s", e)
            flash(str(e), "error")
            return redirect(url_for("admin_announcements"))

    # ---- GET 一覧 ----
    q = (request.args.get("q") or "").strip()
    active = request.args.get("active")
    conds, params = [], []
    if q:
        conds.append("title LIKE ?"); params.append(f"%{q}%")
    if active:
        conds.append("(pin_until IS NOT NULL AND datetime(pin_until) >= datetime('now'))")
    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    rows = db.execute(
        f"SELECT id, title, body, link_url, pin_until, created_at FROM global_announcements "
        f"{where} ORDER BY id DESC LIMIT 200",
        tuple(params)
    ).fetchall()

    return render_template("admin_announcements_global.html", rows=rows, q=q, active=bool(active))

# =========================
# /admin/tags : 一覧＆操作
# =========================
@app.route("/admin/tags", methods=["GET", "POST"])
def admin_tags():
    """
    ハッシュタグの一覧・検索・操作（リネーム/マージ/削除/件数同期）。
    GET:  ?q=...&sort=uses_desc|name_asc  &limit=200
    POST: action in {rename, merge, delete, recalc}
          - rename: old -> new（単独リネーム）
          - merge : src -> dst（複数を1つへ統合; 今回は1つずつの簡易版）
          - delete: 指定タグを削除（post_tags と hashtags）
          - recalc: 件数を同期（target を指定すれば部分同期）
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    if request.method == "POST":
        _ = _ensure_csrf()
        action = (request.form.get("action") or "").strip()
        try:
            if action == "rename":
                old = (request.form.get("old") or "").strip()
                new = (request.form.get("new") or "").strip()
                if not old or not new:
                    raise ValueError("old/new を入力してください。")
                # post_tags を更新（重複は UNIQUE 制約が無いのでそのまま集約される）
                db.execute("UPDATE post_tags SET tag=? WHERE tag=?", (new, old))
                # hashtags 行を upsert（uses は後で同期）
                db.execute(
                    "INSERT INTO hashtags(tag, uses) VALUES(?, 0) "
                    "ON CONFLICT(tag) DO NOTHING",
                    (new,),
                )
                db.execute("DELETE FROM hashtags WHERE tag=?", (old,))
                db.commit()
                _recalc_hashtag_counts([new])
                flash(f"#{old} を #{new} にリネームしました。", "success")
                return redirect(url_for("admin_tags"))

            elif action == "merge":
                src = (request.form.get("src") or "").strip()
                dst = (request.form.get("dst") or "").strip()
                if not src or not dst or src == dst:
                    raise ValueError("src/dst を正しく入力してください。")
                # まず dst を作っておく
                db.execute(
                    "INSERT INTO hashtags(tag, uses) VALUES(?, 0) "
                    "ON CONFLICT(tag) DO NOTHING",
                    (dst,),
                )
                # マージ：post_tags のタグを書き換え
                db.execute("UPDATE post_tags SET tag=? WHERE tag=?", (dst, src))
                # src のメタは削除
                db.execute("DELETE FROM hashtags WHERE tag=?", (src,))
                db.commit()
                _recalc_hashtag_counts([dst])
                flash(f"#{src} を #{dst} にマージしました。", "success")
                return redirect(url_for("admin_tags"))

            elif action == "delete":
                tag = (request.form.get("tag") or "").strip()
                if not tag:
                    raise ValueError("tag を指定してください。")
                db.execute("DELETE FROM post_tags WHERE tag=?", (tag,))
                db.execute("DELETE FROM hashtags WHERE tag=?", (tag,))
                db.commit()
                flash(f"#{tag} を削除しました。", "success")
                return redirect(url_for("admin_tags"))

            elif action == "recalc":
                target = (request.form.get("target") or "").strip()
                if target:
                    _recalc_hashtag_counts([target])
                    flash(f"#{target} の件数を同期しました。", "success")
                else:
                    _recalc_hashtag_counts(None)
                    flash("すべてのタグ件数を同期しました。", "success")
                return redirect(url_for("admin_tags"))

            else:
                flash("不明なアクションです。", "error")
        except Exception as e:
            app.logger.info("admin_tags error: %s", e)
            flash(str(e), "error")
            return redirect(url_for("admin_tags"))

    # ---- GET 一覧表示 ----
    q = (request.args.get("q") or "").strip()
    sort = (request.args.get("sort") or "uses_desc").strip()
    try:
        limit = max(1, min(500, int(request.args.get("limit") or "200")))
    except Exception:
        limit = 200

    conds, params = [], []
    if q:
        conds.append("tag LIKE ?")
        params.append(f"%{q}%")
    where = (" WHERE " + " AND ".join(conds)) if conds else ""

    order = "uses DESC, tag ASC" if sort == "uses_desc" else "tag ASC"
    rows = db.execute(
        f"SELECT tag, uses FROM hashtags {where} ORDER BY {order} LIMIT ?",
        (*params, limit),
    ).fetchall()

    return render_template("admin_tags.html", rows=rows, q=q, sort=sort, limit=limit)

@app.route("/admin/comments")
def admin_comments():
    """コメントのモデレーション一覧"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard

    db = get_db()
    q = (request.args.get("q") or "").strip()
    user_id = (request.args.get("user_id") or "").strip()
    post_id = (request.args.get("post_id") or "").strip()
    status = (request.args.get("status") or "visible").strip()  # visible/hidden/all

    conds, params = [], []
    if status == "visible":
        conds.append("c.hidden_at IS NULL")
    elif status == "hidden":
        conds.append("c.hidden_at IS NOT NULL")

    if user_id:
        conds.append("c.user_id = ?"); params.append(int(user_id))
    if post_id:
        conds.append("c.post_id = ?"); params.append(int(post_id))
    if q:
        conds.append("(c.body LIKE ?)"); params.append(f"%{q}%")

    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    sql = f"""
      SELECT c.id, c.post_id, c.user_id, c.body, c.created_at, c.hidden_at,
             u.name AS user_name, u.email AS user_email
        FROM post_comments c
        LEFT JOIN users u ON u.id = c.user_id
        {where}
       ORDER BY c.id DESC
       LIMIT 200
    """
    rows = db.execute(sql, tuple(params)).fetchall()
    return render_template("admin_comments.html",
                           rows=rows, q=q, user_id=user_id, post_id=post_id, status=status)


@app.route("/admin/comments/<int:cid>/hide", methods=["POST"])
def admin_comments_hide(cid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    db.execute("UPDATE post_comments SET hidden_at=CURRENT_TIMESTAMP, hidden_by=? WHERE id=?",
               (session.get("admin_id"), cid))
    db.commit()
    flash("コメントを非表示にしました。", "success")
    return redirect(request.referrer or url_for("admin_comments"))


@app.route("/admin/comments/<int:cid>/unhide", methods=["POST"])
def admin_comments_unhide(cid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    db.execute("UPDATE post_comments SET hidden_at=NULL, hidden_by=NULL WHERE id=?", (cid,))
    db.commit()
    flash("コメントの非表示を解除しました。", "success")
    return redirect(request.referrer or url_for("admin_comments"))


@app.route("/admin/comments/<int:cid>/delete", methods=["POST"])
def admin_comments_delete(cid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    db.execute("DELETE FROM post_comments WHERE id=?", (cid,))
    db.commit()
    flash("コメントを削除しました。", "success")
    return redirect(request.referrer or url_for("admin_comments"))

@app.route("/admin/posts/<int:pid>/hide", methods=["POST"])
def admin_posts_hide(pid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    db.execute("UPDATE posts SET hidden_at=CURRENT_TIMESTAMP, hidden_by=? WHERE id=?",
               (session.get("admin_id"), pid))
    db.commit()
    flash("投稿を非表示にしました。", "success")
    return redirect(request.referrer or url_for("admin_posts"))


@app.route("/admin/posts/<int:pid>/unhide", methods=["POST"])
def admin_posts_unhide(pid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    db.execute("UPDATE posts SET hidden_at=NULL, hidden_by=NULL WHERE id=?", (pid,))
    db.commit()
    flash("投稿の非表示を解除しました。", "success")
    return redirect(request.referrer or url_for("admin_posts"))


@app.route("/admin/posts/<int:pid>/delete", methods=["POST"])
def admin_posts_delete(pid: int):
    """完全削除（関連レコードも削除）※取り消し不可"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged(); return guard
    _ = _ensure_csrf()
    db = get_db()
    try:
        db.execute("DELETE FROM post_photos WHERE post_id=?", (pid,))
        db.execute("DELETE FROM post_comments WHERE post_id=?", (pid,))
        db.execute("DELETE FROM post_likes WHERE post_id=?", (pid,))
        db.execute("DELETE FROM post_tags WHERE post_id=?", (pid,))
        # FTS を使っていればここで同期削除しても良い（存在しない場合に備えて try）
        try:
            db.execute("DELETE FROM posts_fts WHERE rowid=?", (pid,))
        except Exception:
            pass
        db.execute("DELETE FROM posts WHERE id=?", (pid,))
        db.commit()
        flash("投稿を削除しました。", "success")
    except Exception as e:
        app.logger.info("admin_posts_delete error: %s", e)
        flash("削除に失敗しました。ログを確認してください。", "error")
    return redirect(request.referrer or url_for("admin_posts"))


@app.context_processor
def inject_globals() -> Dict[str, Any]:
    def _notify_unread():
        try:
            return _get_unread_count(int(session.get("user_id", 1)))
        except Exception:
            return 0
    return {
        "csrf_token": _ensure_csrf,
        "GOOGLE_MAPS_API_KEY": GOOGLE_MAPS_API_KEY,
        "notify_unread_count": _notify_unread,
        "admin_logged_in": admin_logged_in
    }

@app.template_filter("markclass")
def markclass(v):
    if v is None: return "na"
    s = str(v).strip().lower()
    if v is True or s in {"true","1","○","◯","o","ok","可","yes"}: return "ok"
    if v is False or s in {"false","0","×","x","ng","不可","no"}: return "ng"
    return "na"

@app.template_filter("stars")
def stars(n):
    try: n = int(n)
    except Exception: n = 0
    return "★"*n + "☆"*(5-n)

_HASHTAG_RE = re.compile(r'(?<!\w)#([^\s#]{1,50})')
@app.template_filter("linkify_tags")
def linkify_tags(text: str):
    if not text: return ""
    def _repl(m):
        tag = m.group(1)
        return f'<a href="{url_for("tag_page", tag=tag)}">#{tag}</a>'
    return re.sub(_HASHTAG_RE, _repl, text)

# ============== My-Allergens ==============
ALLERGENS_JP = [
    "卵","乳","小麦","そば","落花生","えび","かに",
    "アーモンド","あわび","いか","いくら","オレンジ","カシューナッツ",
    "キウイ","牛肉","くるみ","さけ","さば","大豆","鶏肉",
    "バナナ","豚肉","まつたけ","もも","やまいも","りんご","ゼラチン","ごま"
]
SEVERITY_LABELS = {"strict":"厳格","medium":"中","loose":"ゆるめ"}

def get_user_allergens(user_id: int) -> dict:
    cur = get_db().execute("SELECT allergen,severity FROM user_allergens WHERE user_id=?", (user_id,))
    return {r["allergen"]: r["severity"] for r in cur.fetchall()}

def get_user_allergen_others(user_id: int) -> List[Dict[str,str]]:
    cur = get_db().execute("SELECT label,severity FROM user_allergen_others WHERE user_id=?", (user_id,))
    return [{"label": r["label"], "severity": r["severity"]} for r in cur.fetchall()]

def get_user_allergens_combined(user_id: int) -> dict:
    base = get_user_allergens(user_id)
    for row in get_user_allergen_others(user_id):
        label = (row["label"] or "").strip()
        sev   = row["severity"]
        if sev not in ("strict","medium","loose") or not label: continue
        parts = [p.strip() for p in re.split(r"[、,／/,・\s]+", label) if p.strip()]
        for p in parts: base[p] = sev
    return base

def set_user_allergens(user_id: int, form) -> None:
    db = get_db()
    selected = form.getlist("allergen")
    rows = []
    for a in selected:
        sev = form.get(f"severity_{a}", "strict")
        if sev not in ("strict","medium","loose"): continue
        rows.append((user_id,a,sev))
    db.execute("DELETE FROM user_allergens WHERE user_id=?", (user_id,))
    if rows:
        db.executemany("INSERT OR REPLACE INTO user_allergens(user_id,allergen,severity) VALUES (?,?,?)", rows)

    db.execute("DELETE FROM user_allergen_others WHERE user_id=?", (user_id,))
    labels = form.getlist("other_label")
    sevs   = form.getlist("other_severity")
    others = []
    for label, sev in zip(labels, sevs):
        label = (label or "").strip()
        if not label or sev not in ("strict","medium","loose"): continue
        others.append((user_id,label,sev))
    if others:
        db.executemany("INSERT OR REPLACE INTO user_allergen_others(user_id,label,severity) VALUES (?,?,?)", others)
    db.commit()

# ============== Sheets ==============
def _authorize_main_sheet_client():
    """メイン（店舗一覧）用の Google Sheets クライアント取得"""
    if not HAS_GSPREAD:
        raise RuntimeError("gspread が未インストールです。")

    scope = ["https://www.googleapis.com/auth/spreadsheets.readonly"]

    creds = load_google_credentials()
    client = gspread.authorize(creds)
    return client

    



def _to_int_or_none(x) -> Optional[int]:
    try:
        s = str(x).strip()
        if not s: return None
        return int(float(s))
    except Exception:
        return None

def compute_open_info(row: Dict[str, Any]) -> Tuple[str, str]:
    start = (row.get("営業開始") or "").strip()
    end   = (row.get("営業終了") or "").strip()
    closed= (row.get("定休日") or "").strip()
    if closed: return ("休", f"定休日：{closed}")
    if start or end: return ("営", f"{start}〜{end}")
    return ("", "")

def get_all_stores_from_sheet() -> List[Dict[str, Any]]:
    if not SHEET_ID: raise RuntimeError("SHEET_ID が未設定です。")
    client = _authorize_main_sheet_client()
    try:
        svc_email = json.loads(Path(CREDS_FILE).read_text())["client_email"]
    except Exception:
        svc_email = "unknown"
    app.logger.info("SHEET_ID at runtime = %s", SHEET_ID)
    app.logger.info("Service Account used = %s  (creds=%s)", svc_email, CREDS_FILE)

    ws = client.open_by_key(SHEET_ID).sheet1
    records: List[Dict[str, Any]] = ws.get_all_records()

    cleaned: List[Dict[str, Any]] = []
    for row in records:
        row["店舗ID"] = _to_int_or_none(row.get("店舗ID"))
        row["lat"] = to_float(row.get("緯度"))
        row["lng"] = to_float(row.get("経度"))
        row["open_status"], row["open_hint"] = compute_open_info(row)
        for k in ("画像ファイル名","InstagramURL","メニューURL","電話番号","ReservationURL","公式サイトURL","アレルギー表URL"):
            row[k] = (row.get(k) or "").strip()
        cleaned.append(row)
    return cleaned

def _fetch_store_overrides_dict() -> dict:
    """全オーバーライドを {str(store_id): {key: value}} にして返す。"""
    db = get_db()
    rows = db.execute("SELECT store_id, key, value FROM store_overrides").fetchall()
    by_store = {}
    for r in rows:
        sid = str(r["store_id"])
        by_store.setdefault(sid, {})[r["key"]] = r["value"]
    return by_store


def _apply_overrides_to_stores(base_list: list) -> list:
    """Sheetsのリストにオーバーライドを当てて返す（毎回最新）。"""
    if not base_list:
        return []
    ov = _fetch_store_overrides_dict()
    out = []
    for s in base_list:
        sid = str(s.get("id") or s.get("store_id") or "")
        merged = dict(s)
        if sid and sid in ov:
            # 型が必要そうな項目は軽くキャストを試みる（失敗時は文字列のまま）
            for k, v in ov[sid].items():
                if k in ("lat", "lng"):
                    try:
                        merged[k] = float(v)
                        continue
                    except Exception:
                        pass
                merged[k] = v
        out.append(merged)
    return out


def get_store_with_overrides(store_id: int):
    """単体取得（Sheetsキャッシュ → オーバーライド適用）"""
    base = get_all_stores_from_sheet_cached()
    sid = str(store_id)

    for s in base:
        # シート側の可能性に全て対応
        possible_ids = [
            s.get("店舗ID"),
            s.get("id"),
            s.get("store_id"),
            s.get("店ID"),       # 将来のため
            s.get("StoreID")     # 将来のため
        ]

        for key in possible_ids:
            if key is not None and str(key).strip() == sid:
                return s

    return None


# ===== Sheets 読み取りキャッシュ層 =====
_SHEETS_CACHE = {"stores": {"ts": 0.0, "data": None}}
SHEETS_CACHE_TTL = int(os.getenv("SHEETS_CACHE_TTL", "120"))

# Adminから一時的にTTLを上書きできるようにする（NoneでENV既定を使用）
_SHEETS_TTL_OVERRIDE: Optional[int] = None

def _current_sheets_ttl() -> int:
    return (_SHEETS_TTL_OVERRIDE if _SHEETS_TTL_OVERRIDE is not None else SHEETS_CACHE_TTL)

def get_all_stores_from_sheet_cached(ttl: Optional[int] = None, force: bool = False):
    """
    Sheets → メモリキャッシュ読み取り。
    - ttl が None の場合は _current_sheets_ttl() を使用（ENV or 管理画面の上書き値）。
    - force=True のときはAPIを叩いて結果をキャッシュへ保存（429時はフォールバック）。
    - 返却時に store_overrides を毎回マージして最新状態を返す。
    """
    ttl_val = _current_sheets_ttl() if ttl is None else int(ttl)
    now = time.time()
    cached = _SHEETS_CACHE["stores"]

    def _with_overrides(data):
        try:
            return _apply_overrides_to_stores(data or [])
        except Exception as e:
            app.logger.info("apply overrides failed: %s", e)
            return data or []

    # キャッシュ利用条件
    if (not force) and cached["data"] is not None and now - cached["ts"] < ttl_val:
        return _with_overrides(cached["data"])

    backoffs = [0, 0.6, 1.2]
    last_exc = None
    for d in backoffs:
        if d:
            time.sleep(d)
        try:
            data = get_all_stores_from_sheet()      # Sheets 生データ
            _SHEETS_CACHE["stores"] = {"ts": time.time(), "data": data}
            return _with_overrides(data)
        except Exception as e:
            last_exc = e
            msg = str(e)
            is_quota = (isinstance(e, GSpreadAPIError) and "429" in msg) or ("429" in msg)
            if is_quota and cached["data"] is not None:
                app.logger.warning("Sheets quota exceeded; serve cached result (with overrides).")
                return _with_overrides(cached["data"])
            continue
    raise last_exc

@app.route("/admin/stores/<int:store_id>/override", methods=["GET", "POST"])
def admin_store_override(store_id: int):
    """店舗メタのローカル上書き。値が空なら削除扱い。"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    if request.method == "POST":
        _ = _ensure_csrf()
        action = (request.form.get("action") or "set").strip()
        key = (request.form.get("key") or "").strip()
        val = (request.form.get("value") or "").strip()
        aid = session.get("admin_id")

        if action == "clear_all":
            db.execute("DELETE FROM store_overrides WHERE store_id=?", (store_id,))
            db.commit()
            flash("この店舗のオーバーライドを全て削除しました。", "success")
            return redirect(url_for("admin_store_override", store_id=store_id))

        if not key:
            flash("キーを入力してください。", "error")
            return redirect(url_for("admin_store_override", store_id=store_id))

        if action == "delete" or val == "":
            db.execute("DELETE FROM store_overrides WHERE store_id=? AND key=?", (store_id, key))
            db.commit()
            flash(f"「{key}」のオーバーライドを削除しました。", "success")
            return redirect(url_for("admin_store_override", store_id=store_id))

        # upsert
        db.execute("""
            INSERT INTO store_overrides(store_id, key, value, updated_by)
            VALUES (?,?,?,?)
            ON CONFLICT(store_id, key) DO UPDATE SET
              value=excluded.value,
              updated_by=excluded.updated_by,
              updated_at=CURRENT_TIMESTAMP
        """, (store_id, key, val, aid))
        db.commit()
        flash(f"「{key}」を更新しました。", "success")
        return redirect(url_for("admin_store_override", store_id=store_id))

    # GET
    store = get_store_with_overrides(store_id)  # 表示は適用後
    if not store:
        flash("店舗が見つかりません。", "error")
        return redirect(url_for("admin_dashboard"))

    overrides = db.execute(
        "SELECT key, value, updated_by, updated_at FROM store_overrides WHERE store_id=? ORDER BY key",
        (store_id,)
    ).fetchall()
    # 推奨キー（ヒント）
    recommended_keys = [
        ("closed", "0/1（1で休業）"),
        ("open", "HH:MM"),
        ("close", "HH:MM"),
        ("name", "店舗名 上書き"),
        ("address", "住所 上書き"),
        ("category", "カテゴリ 上書き"),
        ("lat", "緯度（数値）"),
        ("lng", "経度（数値）"),
        ("note", "補足テキスト"),
    ]
    return render_template(
        "admin_store_override.html",
        store=store,
        store_id=store_id,
        overrides=overrides,
        recommended_keys=recommended_keys
    )

# ============== レビュー集計 ==============
def get_ratings_map() -> Dict[int, Dict[str, Any]]:
    cur = get_db().execute("""
        SELECT store_id,
               ROUND(AVG(rating),1) AS app_rating,
               COUNT(*) AS app_review_count
          FROM reviews
         GROUP BY store_id
    """)
    res: Dict[int, Dict[str, Any]] = {}
    for r in cur.fetchall():
        res[int(r["store_id"])] = {
            "app_rating": float(r["app_rating"]) if r["app_rating"] is not None else 0.0,
            "app_review_count": int(r["app_review_count"]),
        }
    return res

# ============== お気に入り集計 ==============
def get_favorite_counts_map() -> Dict[int, int]:
    cur = get_db().execute("SELECT store_id, COUNT(*) AS c FROM favorites GROUP BY store_id")
    return {int(r["store_id"]): int(r["c"]) for r in cur.fetchall()}

def merge_ratings(stores: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rmap = get_ratings_map()
    for s in stores:
        sid = s.get("店舗ID") or s.get("id")
        meta = rmap.get(sid or 0, {"app_rating":0.0,"app_review_count":0})
        s["app_rating"] = meta["app_rating"]
        s["app_review_count"] = meta["app_review_count"]
    return stores

def get_store_by_id(store_id: int) -> Optional[Dict[str, Any]]:
    for s in merge_ratings(get_all_stores_from_sheet_cached()):
        if s.get("店舗ID") == store_id:
            return s
    return None

# ============== 安全度判定 ==============
def _fetch_allergy_table_by_store(store: dict) -> Tuple[List[Dict[str,str]], List[str]]:
    """店舗ごとのアレルギー表を Google Sheets / URL から取得"""
    if not HAS_GSPREAD:
        return [], []

    scope = [
        "https://www.googleapis.com/auth/spreadsheets.readonly",
        "https://www.googleapis.com/auth/drive.readonly",
    ]

    creds = load_google_credentials()
    client = gspread.authorize(creds)

    def _extract_key_from_url(url: str):
        m = re.search(r"/d/([a-zA-Z0-9-_]+)", (url or ""))
        return m.group(1) if m else None

    key_to_use = _extract_key_from_url(store.get("アレルギー表URL") or "")
    try:
        if key_to_use:
            sh = client.open_by_key(key_to_use); ws = sh.sheet1
        else:
            sh = client.open_by_key(SHEET_ID)
            try: ws = sh.worksheet(str(store.get("店舗名") or "").strip())
            except Exception: ws = sh.sheet1
    except Exception:
        return [], []
    values = ws.get_all_values() or []
    rows, allergens, _ = _parse_any_table(values)
    return rows, allergens

def evaluate_safety_for_user(store: dict, user_allergens: dict):
    rows, allergens = _fetch_allergy_table_by_store(store)
    if not user_allergens or not rows or not allergens:
        return ("warn", None, "low")
    targets = [a for a in user_allergens.keys() if a in allergens]
    if not targets: return ("warn", None, "low")
    total=0; unknown=0; any_ok=False; all_ng=True
    for r in rows:
        row_has_ng=False; row_has_unknown=False; row_all_known_ok=True
        for a in targets:
            v = (r.get(a) or "－").strip(); total += 1
            if v in ("－","—",""): unknown += 1; row_has_unknown=True
            if v in ("◯","○","●","有","あり","含む"): row_has_ng=True; row_all_known_ok=False
            elif v in ("✕","×","不可","無","なし","不使用","No","NO"): pass
            else: row_all_known_ok=False
        if row_all_known_ok and not row_has_unknown: any_ok=True
        if not row_has_ng: all_ng=False
    safe = "ok" if any_ok else ("ng" if all_ng else "warn")
    unk_ratio = (unknown/total) if total else 1.0
    trust = "high" if unk_ratio <= .05 else ("medium" if unk_ratio <= .25 else "low")
    fresh_days = None
    for k in ("最終更新","更新日","LastUpdated","updated_at"):
        v = (store.get(k) or "").strip() if isinstance(store.get(k), str) else None
        if not v: continue
        from datetime import timezone, timedelta as td
        JST = timezone(td(hours=+9))
        for fmt in ("%Y-%m-%d","%Y/%m/%d","%Y.%m.%d","%m/%d/%Y"):
            try:
                dt = datetime.strptime(v, fmt).replace(tzinfo=JST)
                fresh_days = (datetime.now(JST).date() - dt.date()).days
                break
            except Exception: pass
        if fresh_days is not None: break
    return (safe, fresh_days, trust)

def _unknown_ratio_all(rows: List[Dict[str,str]]) -> float:
    total = 0; unknown = 0
    for r in rows:
        for k, v in r.items():
            if k == "menu": continue
            total += 1
            s = ("" if v is None else str(v)).strip()
            if s in ("", "－", "-", "—", "不明", "unknown"):
                unknown += 1
    return (unknown/total) if total else 1.0

def _calc_trust_score(unknown_ratio: float, fresh_days: Optional[int]) -> float:
    if fresh_days is None:
        staleness = 0.30
    elif fresh_days <= 7:
        staleness = 0.00
    elif fresh_days <= 30:
        staleness = 0.05
    elif fresh_days <= 90:
        staleness = 0.10
    elif fresh_days <= 180:
        staleness = 0.20
    else:
        staleness = 0.40
    score = 1.0 - float(unknown_ratio) - float(staleness)
    return max(0.0, min(1.0, round(score, 2)))

# ============== プロフィール ==============
def get_profile(uid: int) -> dict:
    row = get_db().execute("SELECT id,email,name,avatar_path,phone,bio FROM users WHERE id=?", (uid,)).fetchone()
    if not row:
        return {"id":uid, "email":"", "name":"ゲストユーザー", "avatar_url":"", "phone":"", "bio":""}
    avatar_url = url_for("static", filename=row["avatar_path"]) if row["avatar_path"] else ""
    return {
        "id": row["id"], "email": row["email"] or "",
        "name": row["name"] or "ゲストユーザー",
        "avatar_url": avatar_url,
        "phone": row["phone"] or "",
        "bio": row["bio"] or "",
    }

def update_profile(uid: int, name: str, email: str, phone: str, bio: str, avatar_rel: Optional[str], remove_avatar: bool) -> None:
    db = get_db()
    if remove_avatar:
        db.execute("UPDATE users SET avatar_path=NULL WHERE id=?", (uid,))
    if avatar_rel:
        db.execute("UPDATE users SET avatar_path=? WHERE id=?", (avatar_rel, uid))
    db.execute("UPDATE users SET name=?, email=?, phone=?, bio=? WHERE id=?", (name, email, phone, bio, uid))
    db.commit()
    session["user_email"] = email
    session["user_name"] = name

# ============== Posts helpers ==============
def extract_tags(text: str) -> List[str]:
    seen, tags = set(), []
    for raw in _HASHTAG_RE.findall(text or ""):
        tag = raw.strip().strip('#').replace('　',' ').strip()
        norm = unicodedata.normalize('NFKC', tag).strip('、。,.!！？」」)]） ')
        if norm and norm not in seen:
            seen.add(norm); tags.append(norm)
    return tags[:20]

def is_store_official(store_id: int) -> bool:
    db = get_db()
    row = db.execute("SELECT 1 FROM store_claims WHERE store_id=? AND status='approved' LIMIT 1",
                     (store_id,)).fetchone()
    return bool(row)

def user_can_announce(uid: int, store_id: int) -> bool:
    db = get_db()
    row = db.execute(
        "SELECT 1 FROM store_claims WHERE store_id=? AND user_id=? AND status='approved' LIMIT 1",
        (store_id, uid)
    ).fetchone()
    return bool(row)

def _save_post_images(files, post_id: int) -> List[Tuple[str,int]]:
    saved = []
    base = POST_DIR / f"{post_id}"
    if base.exists():
        shutil.rmtree(base)
    base.mkdir(parents=True, exist_ok=True)
    ord_idx = 0
    for fs in files:
        if not fs or not fs.filename: continue
        filename = secure_filename(fs.filename)
        if not _allowed_image(filename): continue
        fs.stream.seek(0,2); size = fs.stream.tell(); fs.stream.seek(0)
        if size > MAX_UPLOAD_MB * 1024 * 1024: continue
        ext = filename.rsplit(".",1)[1].lower()
        rel = f"uploads/posts/{post_id}/photo_{ord_idx}.{ext}"
        abs_path = APP_ROOT / "static" / rel
        fs.save(abs_path)
        saved.append((rel, ord_idx))
        ord_idx += 1
        if ord_idx >= 10: break
    return saved

# ============== Auth helpers（追記） ==============
def get_or_create_user_by_email(email: str, name: str = "") -> int:
    email = (email or "").strip().lower()
    db = get_db()
    row = db.execute("SELECT id, name FROM users WHERE email=?", (email,)).fetchone()
    if row:
        uid = int(row["id"])
        if name and not (row["name"] or "").strip():
            db.execute("UPDATE users SET name=? WHERE id=?", (name, uid))
            db.commit()
        return uid
    cur = db.execute("INSERT INTO users(email, name) VALUES (?, ?)", (email, name or "ユーザー"))
    db.commit()
    return int(cur.lastrowid)

def set_user_password(uid: int, raw_password: str | None):
    ph = generate_password_hash(raw_password) if raw_password else None
    db = get_db()
    db.execute("UPDATE users SET password_hash=? WHERE id=?", (ph, uid))
    db.commit()

def _decode_jwt_noverify(token: str) -> dict:
    try:
        parts = (token or "").split(".")
        if len(parts) < 2:
            return {}
        payload_b64 = parts[1] + "=="
        data = base64.urlsafe_b64decode(payload_b64.encode("utf-8"))
        import json as _json
        return _json.loads(data.decode("utf-8"))
    except Exception:
        return {}

def _token_serializer() -> URLSafeTimedSerializer:
    return URLSafeTimedSerializer(app.secret_key, salt="auth-salt")

def make_token(email: str, purpose: str) -> str:
    return _token_serializer().dumps({"email": email.strip().lower(), "purpose": purpose})

def verify_token(token: str, purpose: str, max_age: int) -> str | None:
    try:
        data = _token_serializer().loads(token, max_age=max_age)
        if data.get("purpose") != purpose:
            return None
        return (data.get("email") or "").strip().lower()
    except (BadSignature, SignatureExpired):
        return None

def _throttle_key(email: str | None) -> str:
    return f"e:{(email or '').strip().lower()}" if email else f"ip:{request.remote_addr or ''}"

def throttle_check(email: str | None) -> int:
    row = get_db().execute(
        "SELECT locked_until FROM auth_throttle WHERE identifier=?", (_throttle_key(email),)
    ).fetchone()
    if not row or not row["locked_until"]:
        return 0
    try:
        until = datetime.fromisoformat(str(row["locked_until"]))
    except Exception:
        return 0
    delta = (until - datetime.utcnow()).total_seconds()
    return int(delta) if delta > 0 else 0

def throttle_fail(email: str | None, window_fails: int = 5, lock_minutes: int = 15):
    db = get_db()
    ident = _throttle_key(email)
    row = db.execute("SELECT fail_count FROM auth_throttle WHERE identifier=?", (ident,)).fetchone()
    if row:
        fail = int(row["fail_count"]) + 1
        locked_until = None
        if fail >= window_fails:
            locked_until = (datetime.utcnow() + timedelta(minutes=lock_minutes)).isoformat()
            fail = 0
        db.execute("UPDATE auth_throttle SET fail_count=?, locked_until=? WHERE identifier=?", (fail, locked_until, ident))
    else:
        db.execute("INSERT INTO auth_throttle(identifier, fail_count, locked_until) VALUES (?,?,NULL)", (ident, 1))
    db.commit()

def throttle_clear(email: str | None):
    db = get_db()
    db.execute("DELETE FROM auth_throttle WHERE identifier=?", (_throttle_key(email),))
    db.commit()

def send_verify_email(email: str):
    token = make_token(email, "verify")
    url = url_for("verify_email", token=token, _external=True)
    subject = "[Luminity] メールアドレスの確認"
    body = f"以下のリンクをクリックしてメールアドレスを確認してください（24時間有効）\n{url}"
    send_email(email, subject, body)

def send_reset_email(email: str):
    token = make_token(email, "reset")
    url = url_for("reset_password", token=token, _external=True)
    subject = "[Luminity] パスワード再設定のご案内"
    body = f"パスワード再設定はこちら（60分有効）\n{url}"
    send_email(email, subject, body)

def _home_redirect_legacy():
    return redirect(url_for("search"))

@app.route("/search")
def search():
    q = (request.args.get("q") or "").strip()

    import traceback
    try:
        stores = merge_ratings(get_all_stores_from_sheet_cached())
    except Exception as e:
        print("🔥 ERROR while loading stores from Google Sheets 🔥")
        traceback.print_exc()
        raise

    uid = int(session.get("user_id", 1))
    db = get_db()
    fav_ids = {int(r["store_id"]) for r in db.execute("SELECT store_id FROM favorites WHERE user_id=?", (uid,)).fetchall()}
    fav_counts = get_favorite_counts_map()

    if q:
        ql = q.lower()
        stores = [s for s in stores if any(ql in (str(s.get(k) or "")).lower() for k in ("店舗名","住所","カテゴリ"))]
    for s in stores:
        fname = (s.get("画像ファイル名") or "").strip()
        s["image_url"] = static_img(fname)
        s["lat"] = to_float(s.get("緯度")); s["lng"] = to_float(s.get("経度"))
        s["sid"] = s.get("店舗ID") or s.get("id")

        sid = s["sid"]
        try:
            sid_int = int(sid) if sid is not None else None
        except Exception:
            sid_int = None
        s["fav"] = bool(sid_int and (sid_int in fav_ids))
        s["fav_count"] = int(fav_counts.get(sid_int or 0, 0))

    return render_template("search.html", stores=stores, google_api_key=GOOGLE_MAPS_API_KEY)

# ---------- Register flow ----------
@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        name = (request.form.get("name") or "").strip()
        email = (request.form.get("email") or "").strip().lower()
        address = (request.form.get("address") or "").strip()
        allergens = request.form.getlist("allergens")
        others = request.form.getlist("others")
        no_allergy = request.form.get("no_allergy") == "true"

        session["reg_name"] = name
        session["reg_email"] = email
        session["reg_address"] = address

        return render_template(
            "register_step2.html",
            name=name, email=email, address=address,
            allergens=allergens or [],
            others=others or [],
            no_allergy=no_allergy
        )
    return render_template("register_step1.html")

@app.route("/register_complete", methods=["POST"])
def register_complete():
    name = (session.get("reg_name") or "").strip() or "ユーザー"
    email = (session.get("reg_email") or "").strip().lower()

    allergens = [s for s in (request.form.get("allergens") or "").split(",") if s]
    others = [s for s in (request.form.get("others") or "").split(",") if s]
    no_allergy = (request.form.get("no_allergy") or "").lower() in ("true","1","yes","on")

    if not email:
        flash("メールアドレスが確認できません。最初からやり直してください。", "error")
        return redirect(url_for("register"))

    uid = get_or_create_user_by_email(email, name)

    row = get_db().execute("SELECT password_hash FROM users WHERE id=?", (uid,)).fetchone()
    if not row or not (row["password_hash"] or ""):
        tmp = secrets.token_urlsafe(12)
        set_user_password(uid, tmp)
        try:
            send_reset_email(email)
        except Exception:
            pass

    db = get_db()
    db.execute("DELETE FROM user_allergens WHERE user_id=?", (uid,))
    if not no_allergy and allergens:
        db.executemany(
            "INSERT OR REPLACE INTO user_allergens(user_id,allergen,severity) VALUES (?,?,?)",
            [(uid, a, "strict") for a in allergens]
        )
    db.execute("DELETE FROM user_allergen_others WHERE user_id=?", (uid,))
    if others:
        db.executemany(
            "INSERT OR REPLACE INTO user_allergen_others(user_id,label,severity) VALUES (?,?,?)",
            [(uid, o, "strict") for o in others]
        )
    db.commit()

    session.clear()
    session["user_id"] = uid
    session["user_email"] = email
    session["user_name"] = name
    flash("登録が完了しました。プロフィールは後から編集できます。", "success")
    return redirect(url_for("mypage"))

# ---------- Store ----------
@app.route("/store/<int:store_id>")
def store_detail(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    store["image_url"] = static_img((store.get("画像ファイル名") or "").strip())
    links = {
        "instagram": bool(store.get("InstagramURL")),
        "menu":      bool(store.get("メニューURL")),
        "phone":     bool(store.get("電話番号")),
        "reserve":   bool(store.get("ReservationURL")),
        "official":  bool(store.get("公式サイトURL")),
    }
    db = get_db()
    latest_posts = db.execute("""
        SELECT p.id, p.rating, p.created_at,
               (SELECT path FROM post_photos WHERE post_id=p.id ORDER BY ord ASC LIMIT 1) AS first_photo
          FROM posts p
         WHERE p.store_id=?
         ORDER BY p.created_at DESC
         LIMIT 3
    """, (store_id,)).fetchall()
    post_count = db.execute(
        "SELECT COUNT(*) AS c FROM posts WHERE store_id=?",
        (store_id,)
    ).fetchone()["c"]

    official = is_store_official(store_id)
    can_post_announce = user_can_announce(int(session.get("user_id", 1)), store_id)

    annos = db.execute("""
        SELECT id, title, body, link_url, created_at
          FROM store_announcements
         WHERE store_id=?
         ORDER BY (pin_until IS NOT NULL) DESC, created_at DESC
         LIMIT 3
    """, (store_id,)).fetchall()
    anno_count = db.execute(
        "SELECT COUNT(*) AS c FROM store_announcements WHERE store_id=?",
        (store_id,)
    ).fetchone()["c"]

    fav_row = db.execute("SELECT COUNT(*) AS c FROM favorites WHERE store_id=?", (store_id,)).fetchone()
    favorite_count = int(fav_row["c"]) if fav_row else 0

    return render_template(
        "store_detail.html",
        store=store,
        links=links,
        store_id=store_id,
        latest_posts=latest_posts,
        post_count=post_count,
        is_official=official,
        can_post_announce=can_post_announce,
        latest_annos=annos,
        anno_count=anno_count,
        favorite_count=favorite_count
    )

# --- 追加: オーナー申請（ユーザー側） ---
@app.route("/store/<int:store_id>/claim", methods=["GET","POST"])
def store_claim(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    uid = int(session.get("user_id", 1))
    if uid == 1:
        # ゲストはログインへ誘導
        flash("オーナー申請にはログインが必要です。", "error")
        return redirect(url_for("login", next=url_for("store_claim", store_id=store_id)))

    db = get_db()
    if request.method == "POST":
        _ = _ensure_csrf()
        name = (request.form.get("name") or "").strip()
        email = (request.form.get("email") or "").strip()
        phone = (request.form.get("phone") or "").strip()
        position = (request.form.get("position") or "").strip()
        message = (request.form.get("message") or "").strip()

        cur = db.execute("""
            INSERT INTO store_claims(store_id,user_id,name,email,phone,position,message,status)
            VALUES (?,?,?,?,?,?,?, 'pending')
        """, (store_id, uid, name, email, phone, position, message))
        claim_id = int(cur.lastrowid)

        # 証憑ファイル保存（任意）
        try:
            ev_rel = _save_claim_evidence(request.files.get("evidence"), claim_id)
            if ev_rel:
                db.execute("UPDATE store_claims SET evidence_path=? WHERE id=?", (ev_rel, claim_id))
        except ValueError as e:
            flash(str(e), "error")

        db.commit()
        flash("オーナー申請を送信しました。審査結果をお待ちください。", "success")
        return redirect(url_for("store_detail", store_id=store_id))

    existing = db.execute("""
        SELECT id, status, created_at, handled_at
          FROM store_claims
         WHERE store_id=? AND user_id=?
         ORDER BY created_at DESC
         LIMIT 1
    """, (store_id, uid)).fetchone()
    return render_template("store_claim.html", store=store, store_id=store_id, existing=existing)

@app.route("/store/<int:store_id>/posts")
def store_posts(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    db = get_db()
    posts = db.execute("""
        SELECT p.id, p.rating, p.created_at,
               (SELECT path FROM post_photos WHERE post_id=p.id ORDER BY ord ASC LIMIT 1) AS first_photo
          FROM posts p
         WHERE p.store_id=?
         ORDER BY p.created_at DESC
         LIMIT 200
    """, (store_id,)).fetchall()
    return render_template("store_posts.html", store=store, posts=posts, store_id=store_id)

@app.route("/favorite/<int:store_id>", methods=["POST"])
def favorite(store_id: int):
    _ = _ensure_csrf()
    uid = int(session.get("user_id", 1))
    db = get_db()
    row = db.execute("SELECT id FROM favorites WHERE user_id=? AND store_id=?", (uid, store_id)).fetchone()
    if row:
        db.execute("DELETE FROM favorites WHERE id=?", (row["id"],))
        db.commit(); flash("お気に入りを解除しました。","info")
    else:
        db.execute("INSERT OR IGNORE INTO favorites(user_id,store_id) VALUES (?,?)", (uid, store_id))
        db.commit(); flash("お気に入りに追加しました。","success")
    return redirect(request.referrer or url_for("store_detail", store_id=store_id))

@app.route("/favorites", endpoint="favorites")
def favorites_index(): return redirect(url_for("mypage") + "#favorites")

@app.route("/reviews/<int:store_id>", methods=["GET","POST"])
def reviews(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    db = get_db()
    if request.method == "POST":
        _ = _ensure_csrf()
        try: rating = int(request.form.get("rating","0"))
        except Exception: rating = 0
        comment = (request.form.get("comment") or "").strip()
        if 1 <= rating <= 5:
            db.execute("INSERT INTO reviews(user_id,store_id,rating,comment) VALUES (?,?,?,?)",
                       (int(session.get("user_id",1)), store_id, rating, comment))
            db.commit(); flash("レビューを投稿しました。","success")
            return redirect(url_for("reviews", store_id=store_id))
        else:
            flash("評価は1〜5で入力してください。","error")
    cur = db.execute("SELECT rating,comment,created_at FROM reviews WHERE store_id=? ORDER BY created_at DESC", (store_id,))
    reviews_list = cur.fetchall()
    rmeta = get_ratings_map().get(store_id, {"app_rating":0.0,"app_review_count":0})
    store["app_rating"] = rmeta["app_rating"]; store["app_review_count"] = rmeta["app_review_count"]
    return render_template("reviews.html", store=store, reviews_list=reviews_list, store_id=store_id)

@app.route("/qr/<key>")
def qr_redirect(key: str):
    url = QR.get(key)
    if not url:
        return abort(404)
    return redirect(url, code=302)
    


# --- Allergy pages ---
@app.route("/allergy/<int:store_id>/agreement")
def allergy_agreement(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    return render_template("agreement.html", store=store, store_id=store_id,
                           allergy_sheet_url=store.get("アレルギー表URL") or "", exclude_allergens=[])

@app.route("/allergy_pdf/<int:store_id>")
def allergy_pdf(store_id: int):
    """
    店舗ごとのアレルギー表を PDF 化用にレンダリングするページ
    """

    print("📄 /allergy_pdf called with store_id =", store_id)

    # Store 取得
    store = get_store_with_overrides(store_id)

    if not store:
        print("❌ Store not found for store_id:", store_id)
        return "Store not found", 404

    print("✅ Store found:", store.get("店舗名") or store.get("name"))

    # アレルギー行データ取得
    try:
        rows, allergens = _fetch_allergy_table_by_store(store)
        print("✅ Allergy table rows:", len(rows))
    except Exception as e:
        print("❌ Error fetching allergy table:", e)
        return f"Error loading allergy table: {e}", 500

    # 主7品目
    main7 = ["卵", "乳", "小麦", "えび", "かに", "そば", "落花生（ピーナッツ）"]

    primary = [a for a in allergens if any(m in a for m in main7)]
    other = [a for a in allergens if a not in primary]

    return render_template(
        "allergy_pdf.html",
        page_title=f"アレルギー表（{store.get('店舗名', store.get('name', ''))}）",
        store=store,
        rows=rows,
        primary_allergens=primary,
        other_allergens=other,
    )

@app.route("/allergy/<int:store_id>/agreement/next", endpoint="agreement_next")
def agreement_next(store_id: int):
    return redirect(url_for("allergy", store_id=store_id))

@app.route("/allergy/<int:store_id>")
def allergy(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    if not HAS_GSPREAD: raise RuntimeError("gspread が未インストールです。")
    rows, allergens = _fetch_allergy_table_by_store(store)
    store_ctx = {"id": store_id, "name": store.get("店舗名") or store.get("name") or ""}
    return render_template("allergy_table.html", store=store_ctx, rows=rows, allergens=allergens,
                           user_allergens=get_user_allergens_combined(int(session.get('user_id',1))))

# --- PDF Allergy Table Page ---
# ===============================


# --- Safety API ---
@app.route("/api/safety/<int:store_id>")
def api_safety(store_id: int):
    """
    レスポンス: {safe, fresh_days, trust}
    - safe: ok|warn|ng
    - fresh_days: int（データ鮮度日数の目安）
    - trust: high|mid|low|pending
    管理画面の safety_overrides があれば、それで safe/trust を上書き。
    """
    # 1) まず既存の計算ロジックがあれば利用（関数名は無ければ NameError）
    safe, trust, fresh_days = "ok", "pending", 999
    base = None
    try:
        # プロジェクトによって関数名が違う場合に備え2候補
        base = compute_safety_for_store(store_id)  # type: ignore[name-defined]
    except Exception:
        try:
            base = _compute_safety_for_store(store_id)  # type: ignore[name-defined]
        except Exception:
            base = None

    if isinstance(base, dict):
        safe = base.get("safe", safe)
        trust = base.get("trust", trust)
        try:
            fresh_days = int(base.get("fresh_days", fresh_days))
        except Exception:
            pass
    else:
        # 2) フォールバック（スタブ）
        #    キャッシュの最終取得時刻からの経過日で fresh_days を算出
        ts = (_SHEETS_CACHE.get("stores", {}) or {}).get("ts")
        if ts:
            try:
                fresh_days = max(0, int((time.time() - float(ts)) / 86400))
            except Exception:
                fresh_days = 999
        else:
            fresh_days = 999
        # safe/trust は暫定
        safe = "ok"
        trust = "pending"

    # 3) 手動オーバーライドで上書き
    ov = _get_safety_override(store_id)
    if ov:
        if ov["safe"]:
            safe = ov["safe"]
        if ov["trust"]:
            trust = ov["trust"]

    return jsonify({"safe": safe, "fresh_days": int(fresh_days), "trust": trust})


@app.route("/admin/stores/<int:store_id>/safety", methods=["GET", "POST"])
def admin_store_safety(store_id: int):
    """安全度/トラストの手動補正UI。"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    if request.method == "POST":
        _ = _ensure_csrf()
        action = (request.form.get("action") or "save").strip()
        if action == "clear":
            db.execute("DELETE FROM safety_overrides WHERE store_id=?", (store_id,))
            db.commit()
            flash("手動補正をクリアしました。", "success")
            return redirect(url_for("admin_store_safety", store_id=store_id))

        safe = (request.form.get("safe") or "").strip() or None
        trust = (request.form.get("trust") or "").strip() or None
        note = (request.form.get("note") or "").strip() or None
        aid = session.get("admin_id")

        db.execute("""
            INSERT INTO safety_overrides(store_id, safe, trust, note, updated_by)
            VALUES (?,?,?,?,?)
            ON CONFLICT(store_id) DO UPDATE SET
              safe=excluded.safe,
              trust=excluded.trust,
              note=excluded.note,
              updated_by=excluded.updated_by,
              updated_at=CURRENT_TIMESTAMP
        """, (store_id, safe, trust, note, aid))
        db.commit()
        flash("手動補正を保存しました。", "success")
        return redirect(url_for("admin_store_safety", store_id=store_id))

    # GET
    # 表示用：現在の計算値 & オーバーライド
    current = None
    try:
        current = json.loads(api_safety.__wrapped__(store_id).get_data(as_text=True))  # type: ignore
    except Exception:
        # 直接呼びが難しい場合はキャッシュから概算
        current = {"safe": "ok", "trust": "pending", "fresh_days": 999}

    ov = _get_safety_override(store_id)
    store = get_store_with_overrides(store_id)

    return render_template(
        "admin_store_safety.html",
        store=store,
        store_id=store_id,
        current=current,
        override=ov
    )

# --- My Page ---
@app.route("/mypage")
def mypage():
    uid = int(session.get("user_id", 1))
    db = get_db()
    fav_ids = {int(r["store_id"]) for r in db.execute("SELECT store_id FROM favorites WHERE user_id=?", (uid,)).fetchall()}
    stores = merge_ratings(get_all_stores_from_sheet_cached())
    fav_stores: List[Dict[str, Any]] = []
    for s in stores:
        sid = s.get("店舗ID") or s.get("id")
        if sid is None or int(sid) not in fav_ids: continue
        s["image_url"] = static_img((s.get("画像ファイル名") or "").strip())
        s["lat"] = to_float(s.get("緯度")); s["lng"] = to_float(s.get("経度")); s["sid"] = int(sid)
        fav_stores.append(s)
    profile = get_profile(uid)
    return render_template("mypage.html",
        profile=profile, fav_stores=fav_stores, google_api_key=GOOGLE_MAPS_API_KEY,
        allergens=ALLERGENS_JP, current_allergens=get_user_allergens(uid),
        other_allergens=get_user_allergen_others(uid), severity_labels=SEVERITY_LABELS
    )

@app.route("/mypage/allergens", methods=["POST"])
def mypage_save_allergens():
    _ = _ensure_csrf()
    uid = int(session.get("user_id",1))
    set_user_allergens(uid, request.form)
    flash("マイアレルゲンを保存しました。","success")
    return redirect(url_for("mypage") + "#allergens")

@app.route("/mypage/profile", methods=["GET","POST"])
def mypage_profile():
    uid = int(session.get("user_id",1))
    if request.method == "POST":
        _ = _ensure_csrf()
        name  = (request.form.get("name")  or "").strip() or "ゲストユーザー"
        email = (request.form.get("email") or "").strip()
        phone = (request.form.get("phone") or "").strip()
        bio   = (request.form.get("bio")   or "").strip()
        remove = request.form.get("remove_avatar") == "1"
        avatar_rel = None
        try:
            if "avatar" in request.files and request.files["avatar"].filename:
                avatar_rel = _save_avatar(request.files["avatar"], uid)
        except ValueError as e:
            flash(str(e), "error")
            return redirect(url_for("mypage_profile"))
        update_profile(uid, name, email, phone, bio, avatar_rel, remove)
        flash("プロフィールを更新しました。","success")
        return redirect(url_for("mypage") + "#profile")
    return render_template("profile_edit.html", profile=get_profile(uid))

# --- Posts MVP ---
@app.route("/posts/new", methods=["GET","POST"])
def post_new():
    uid = int(session.get("user_id",1))
    db = get_db()
    store_id = int(request.args.get("store") or request.form.get("store_id") or 0)

    if request.method == "POST":
        _ = _ensure_csrf()
        try:
            rating = int(request.form.get("rating","0"))
        except Exception:
            rating = 0
        body = (request.form.get("body") or "").strip()
        if not (1 <= rating <= 5):
            flash("評価（1〜5）が必須です。","error")
            return redirect(request.url)
        if store_id <= 0:
            flash("店舗IDが不正です。","error")
            return redirect(request.url)

        cur = db.execute("INSERT INTO posts(store_id,user_id,rating,body) VALUES (?,?,?,?)",
                         (store_id, uid, rating, body))
        post_id = cur.lastrowid

        files = request.files.getlist("photos")
        saved = _save_post_images(files, post_id)
        if saved:
            db.executemany("INSERT INTO post_photos(post_id,path,ord) VALUES (?,?,?)",
                           [(post_id, rel, ord_) for rel, ord_ in saved])

        tags = extract_tags(body)
        if tags:
            db.executemany("INSERT OR IGNORE INTO hashtags(tag,uses) VALUES (?,0)", [(t,) for t in tags])
            db.executemany("INSERT OR IGNORE INTO post_tags(post_id,tag) VALUES (?,?)", [(post_id,t) for t in tags])
            db.executemany("UPDATE hashtags SET uses = uses + 1 WHERE tag = ?", [(t,) for t in tags])

        try:
            db.execute("INSERT INTO posts_fts(rowid, body) VALUES (?,?)", (post_id, body))
        except Exception:
            pass

        db.commit()

        store = get_store_by_id(store_id) or {}
        title = f"{store.get('店舗名') or store.get('name') or '店舗'}に新しい体験談が投稿されました。"
        enqueue_notifications(store_id, "post", post_id, title, exclude_user_id=uid)

        flash("投稿を作成しました。","success")
        return redirect(url_for("post_detail", post_id=post_id))

    store = get_store_by_id(store_id) if store_id else None
    return render_template("post_new.html", store=store, store_id=store_id)

@app.route("/p/<int:post_id>")
def post_detail(post_id: int):
    db = get_db()
    p = db.execute("SELECT * FROM posts WHERE id=?", (post_id,)).fetchone()
    if not p: abort(404)
    photos = db.execute("SELECT * FROM post_photos WHERE post_id=? ORDER BY ord ASC", (post_id,)).fetchall()
    comments = db.execute("""
        SELECT c.body, c.created_at, u.name
          FROM post_comments c LEFT JOIN users u ON u.id=c.user_id
         WHERE c.post_id=? ORDER BY c.created_at ASC
    """,(post_id,)).fetchall()
    tags = [r["tag"] for r in db.execute("SELECT tag FROM post_tags WHERE post_id=? ORDER BY tag",(post_id,)).fetchall()]

    store_name = ""
    store_id = int(p["store_id"])
    store = get_store_by_id(store_id)
    if store:
        store_name = store.get("店舗名") or store.get("name") or ""

    return render_template("post_detail.html", post=p, photos=photos, comments=comments, tags=tags,
                           store_id=store_id, store_name=store_name)

@app.route("/api/posts/<int:post_id>/comments", methods=["POST"])
def post_add_comment(post_id: int):
    _ = _ensure_csrf()
    uid = int(session.get("user_id",1))
    body = (request.form.get("body") or "").strip()
    if not body:
        flash("コメントを入力してください。","error")
        return redirect(url_for("post_detail", post_id=post_id))
    db = get_db()
    if not db.execute("SELECT 1 FROM posts WHERE id=?", (post_id,)).fetchone():
        abort(404)
    db.execute("INSERT INTO post_comments(post_id,user_id,body) VALUES (?,?,?)", (post_id, uid, body))
    db.commit()
    flash("コメントを追加しました。","success")
    return redirect(url_for("post_detail", post_id=post_id) + "#comments")

@app.route("/feed")
def feed():
    db = get_db()
    posts = db.execute("SELECT * FROM posts ORDER BY created_at DESC LIMIT 60").fetchall()
    stores = { (s.get("店舗ID") or 0): (s.get("店舗名") or s.get("name") or "")
               for s in get_all_stores_from_sheet() }
    cards = []
    for p in posts:
        pid = int(p["id"])
        photos = db.execute("SELECT path FROM post_photos WHERE post_id=? ORDER BY ord ASC", (pid,)).fetchall()
        first = photos[0]["path"] if photos else ""
        name = stores.get(int(p["store_id"]), "")
        cards.append({"id":pid, "store_id":int(p["store_id"]), "store_name":name,
                      "rating":int(p["rating"]), "first_photo": first, "created_at": p["created_at"]})
    return render_template("feed.html", cards=cards)

@app.route("/tags/<path:tag>")
def tag_page(tag: str):
    tag = unicodedata.normalize("NFKC", tag).strip()
    db = get_db()
    posts = db.execute("""
        SELECT p.*
          FROM post_tags t JOIN posts p ON p.id=t.post_id
         WHERE t.tag=? ORDER BY p.created_at DESC
    """,(tag,)).fetchall()
    stores = { (s.get("店舗ID") or 0): (s.get("店舗名") or s.get("name") or "")
               for s in get_all_stores_from_sheet() }
    cards = []
    for p in posts:
        pid = int(p["id"])
        photos = db.execute("SELECT path FROM post_photos WHERE post_id=? ORDER BY ord ASC", (pid,)).fetchall()
        first = photos[0]["path"] if photos else ""
        name = stores.get(int(p["store_id"]), "")
        cards.append({"id":pid, "store_id":int(p["store_id"]), "store_name":name,
                      "rating":int(p["rating"]), "first_photo": first, "created_at": p["created_at"]})
    uses = db.execute("SELECT uses FROM hashtags WHERE tag=?", (tag,)).fetchone()
    uses_cnt = int(uses["uses"]) if uses else 0
    return render_template("tag_posts.html", tag=tag, uses=uses_cnt, cards=cards)

# --- Reports (通報) ---
REPORT_REASONS = [
    ("menu_changed", "メニュー／原材料が変更されている"),
    ("allergen_wrong", "アレルギー表の内容が誤っている／不明瞭"),
    ("cross_contam", "コンタミネーション（同一器具・同一油など）の懸念"),
    ("store_closed", "閉店／営業時間情報が違う"),
    ("spam", "スパム／不適切な投稿"),
    ("other", "その他"),
]

@app.route("/report", methods=["GET", "POST"])
def report_new():
    uid = int(session.get("user_id", 1))
    db = get_db()
    if request.method == "POST":
        _ = _ensure_csrf()
        kind = (request.form.get("kind") or "").strip()
        target_id = int(request.form.get("target_id") or 0)
        reason = (request.form.get("reason") or "").strip()
        body = (request.form.get("body") or "").strip()
        if kind not in ("store","post","allergy") or target_id <= 0:
            flash("通報対象が不正です。", "error")
            return redirect(url_for("home"))
        if reason == "":
            flash("理由を選択してください。", "error")
            return redirect(url_for("report_new") + f"?kind={kind}&id={target_id}")
        db.execute(
            "INSERT INTO reports(kind,target_id,reason,body,status) VALUES (?,?,?,?, 'open')",
            (kind, target_id, reason, body)
        )
        db.commit()
        flash("ご報告ありがとうございます。内容を確認し、必要に応じて反映します。", "success")
        if kind == "store":
            return redirect(url_for("store_detail", store_id=target_id))
        if kind == "post":
            return redirect(url_for("post_detail", post_id=target_id))
        if kind == "allergy":
            return redirect(url_for("allergy", store_id=target_id))
        return redirect(url_for("home"))
    kind = (request.args.get("kind") or "").strip()
    target_id = int(request.args.get("id") or 0)
    title = "通報"
    back_url = url_for("home")
    if kind == "store":
        store = get_store_by_id(target_id) or {}
        title = f"通報：{store.get('店舗名') or store.get('name') or '店舗'}"
        back_url = url_for("store_detail", store_id=target_id)
    elif kind == "post":
        title = f"通報：投稿 #{target_id}"
        back_url = url_for("post_detail", post_id=target_id)
    elif kind == "allergy":
        store = get_store_by_id(target_id) or {}
        title = f"通報：アレルギー表（{store.get('店舗名') or store.get('name') or '店舗'}）"
        back_url = url_for("allergy", store_id=target_id)
    return render_template("report_new.html",
                           kind=kind, target_id=target_id, title=title,
                           reasons=REPORT_REASONS, back_url=back_url)

# ─────────────── Admin: Reports（管理者のみ） ───────────────

@app.route("/admin/reports/<int:rid>/status", methods=["POST"])
def admin_reports_update(rid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()
    new_status = (request.form.get("status") or "").strip()
    if new_status not in ("open","triaged","done","ignored"):
        flash("不正なステータスです。", "error")
        return redirect(url_for("admin_reports"))
    db = get_db()
    db.execute("UPDATE reports SET status=?, handled_at=CURRENT_TIMESTAMP WHERE id=?",
               (new_status, rid))
    db.commit()
    flash("更新しました。", "success")
    return redirect(request.referrer or url_for("admin_reports"))

def csrf_validate_if_present():
    tok = (request.form.get("csrf_token") or request.headers.get("X-CSRF-Token") or "").strip()
    if tok:
        if tok != session.get("_csrf_token"):
            abort(400, "CSRF token invalid")

@app.route("/admin/sheets/cache/clear", methods=["POST"])
def admin_sheets_cache_clear():
    """メモリキャッシュを即時クリア"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()
    _SHEETS_CACHE["stores"] = {"ts": 0.0, "data": None}
    flash("Sheetsキャッシュをクリアしました。", "success")
    return redirect(request.referrer or url_for("admin_dashboard"))


@app.route("/admin/sheets/refresh", methods=["POST"])
def admin_sheets_refresh():
    """強制再読込（429時は古いキャッシュへフォールバック）"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()
    try:
        data = get_all_stores_from_sheet_cached(force=True)
        flash(f"Sheetsを再読込しました（{len(data) if isinstance(data, list) else 'N/A'}件）。", "success")
    except Exception as e:
        app.logger.info("Sheets refresh failed: %s", e)
        flash("再読込に失敗しました。ログをご確認ください。", "error")
    return redirect(request.referrer or url_for("admin_dashboard"))


@app.route("/admin/sheets/cache/ttl", methods=["POST"])
def admin_sheets_set_ttl():
    """TTL の一時上書き。未入力/負値でリセット（ENVに戻す）。単位: 秒"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()

    raw = (request.form.get("ttl") or "").strip()
    global _SHEETS_TTL_OVERRIDE
    try:
        if raw == "" or int(raw) < 0:
            _SHEETS_TTL_OVERRIDE = None
            flash(f"TTLをリセットしました（ENV {SHEETS_CACHE_TTL}s を使用）。", "info")
        else:
            _SHEETS_TTL_OVERRIDE = int(raw)
            flash(f"TTLを {_SHEETS_TTL_OVERRIDE} 秒に上書きしました。", "success")
    except Exception:
        flash("TTLは整数（秒）で入力してください。", "error")
    return redirect(request.referrer or url_for("admin_dashboard"))

# --------------------------
# 公式お知らせ：承認店舗のみ作成可
# --------------------------
@app.route("/store/<int:store_id>/announce/new", methods=["GET", "POST"])
def announce_new(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    uid = int(session.get("user_id", 1))
    if not user_can_announce(uid, store_id):
        flash("この店舗のお知らせを作成する権限がありません。", "error")
        return redirect(url_for("store_detail", store_id=store_id))

    if request.method == "POST":
        _ = _ensure_csrf()
        title = (request.form.get("title") or "").strip()
        body  = (request.form.get("body") or "").strip()
        link  = (request.form.get("link_url") or "").strip()
        if not title:
            flash("タイトルは必須です。", "error")
            return redirect(request.url)
        db = get_db()
        cur = db.execute("""
            INSERT INTO store_announcements(store_id,user_id,title,body,link_url)
            VALUES (?,?,?,?,?)
        """, (store_id, uid, title, body, link or None))
        anno_id = cur.lastrowid
        db.commit()

        ttl = f"{store.get('店舗名') or store.get('name') or '店舗'}からお知らせ：{title}"
        enqueue_notifications(store_id, "announcement", anno_id, ttl, exclude_user_id=uid)

        flash("お知らせを投稿しました。", "success")
        return redirect(url_for("store_detail", store_id=store_id))

    return render_template("announce_new.html", store=store, store_id=store_id)

@app.route("/store/<int:store_id>/announcements")
def announcements_list(store_id: int):
    store = get_store_by_id(store_id) or abort(404)
    db = get_db()
    annos = db.execute("""
        SELECT id, title, body, link_url, created_at
          FROM store_announcements
         WHERE store_id=?
         ORDER BY (pin_until IS NOT NULL) DESC, created_at DESC
         LIMIT 200
    """, (store_id,)).fetchall()
    can_post = user_can_announce(int(session.get("user_id",1)), store_id)
    return render_template("store_announcements.html",
                           store=store, store_id=store_id,
                           annos=annos, can_post=can_post)

# ============== 通知 ==============
@app.route("/notifications")
def notifications():
    uid = int(session.get("user_id", 1))
    db = get_db()
    unread = db.execute("""
        SELECT * FROM notifications
         WHERE user_id=? AND read_at IS NULL
         ORDER BY created_at DESC LIMIT 200
    """, (uid,)).fetchall()
    read = db.execute("""
        SELECT * FROM notifications
         WHERE user_id=? AND read_at IS NOT NULL
         ORDER BY created_at DESC LIMIT 200
    """, (uid,)).fetchall()
    return render_template("notifications.html", unread=unread, read=read)

@app.route("/notifications/<int:nid>/read", methods=["POST"])
def notification_read(nid: int):
    _ = _ensure_csrf()
    uid = int(session.get("user_id", 1))
    db = get_db()
    db.execute("UPDATE notifications SET read_at=CURRENT_TIMESTAMP WHERE id=? AND user_id=?", (nid, uid))
    db.commit()
    return redirect(request.referrer or url_for("notifications"))

@app.route("/notifications/read_all", methods=["POST"])
def notifications_read_all():
    _ = _ensure_csrf()
    uid = int(session.get("user_id", 1))
    db = get_db()
    db.execute("UPDATE notifications SET read_at=CURRENT_TIMESTAMP WHERE user_id=? AND read_at IS NULL", (uid,))
    db.commit()
    flash("すべて既読にしました。", "success")
    return redirect(url_for("notifications"))

# ============== 追加: Favorites API（非破壊） ==============
def get_favorite_count(store_id: int) -> int:
    row = get_db().execute("SELECT COUNT(*) AS c FROM favorites WHERE store_id=?", (store_id,)).fetchone()
    return int(row["c"]) if row else 0

def is_favorited_by_user(uid: int, store_id: int) -> bool:
    row = get_db().execute("SELECT 1 FROM favorites WHERE user_id=? AND store_id=? LIMIT 1", (uid, store_id)).fetchone()
    return bool(row)

@app.route("/api/favorites/count/<int:store_id>")
def api_favorites_count(store_id: int):
    return jsonify({"count": get_favorite_count(store_id)})

@app.route("/api/favorites/toggle/<int:store_id>", methods=["POST"])
def api_favorites_toggle(store_id: int):
    try:
        csrf_validate_if_present()
    except Exception:
        pass
    uid = int(session.get("user_id", 1))
    db = get_db()
    if is_favorited_by_user(uid, store_id):
        db.execute("DELETE FROM favorites WHERE user_id=? AND store_id=?", (uid, store_id))
        db.commit()
        status = "removed"
    else:
        db.execute("INSERT OR IGNORE INTO favorites(user_id,store_id) VALUES (?,?)", (uid, store_id))
        db.commit()
        status = "added"
    return jsonify({"status": status, "count": get_favorite_count(store_id)})

# ============== 認証（ログイン/ログアウト/再設定/検証） ==============
@app.route("/login", methods=["GET", "POST"])
def login():
    # 一般ログインURLから管理者ログインへ誘導（?admin=1 / ?to=admin）
    if request.method == "GET":
        to = (request.args.get("to") or "").strip().lower()
        admin_q = (request.args.get("admin") or "").strip().lower()
        if to == "admin" or admin_q in ("1", "true", "yes", "y", "admin"):
            nxt = request.args.get("next")
            return redirect(url_for("admin_login", next=nxt) if nxt else url_for("admin_login"))
        return render_template("login.html")

    email = (request.form.get("email") or "").strip().lower()
    password = request.form.get("password") or ""
    remember = bool(request.form.get("remember"))

    left = throttle_check(email)
    if left > 0:
        flash(f"試行回数が多すぎます。{left}秒後に再度お試しください。", "error")
        return render_template("login.html")

    db = get_db()
    row = db.execute(
        "SELECT id, name, password_hash, email_verified FROM users WHERE email=?",
        (email,)
    ).fetchone()
    if not row or not row["password_hash"] or not check_password_hash(row["password_hash"], password):
        throttle_fail(email)
        flash("メールまたはパスワードが正しくありません。", "error")
        return render_template("login.html")

    if _REQUIRE_VERIFY and int(row["email_verified"] or 0) == 0:
        send_verify_email(email)
        return render_template("verify_sent.html", email=email)

    throttle_clear(email)
    session.clear()
    session["user_id"] = int(row["id"])
    session["user_email"] = email
    session["user_name"] = row["name"] or ""
    session.permanent = bool(remember)
    flash("ログインしました。", "success")
    return redirect(url_for("mypage"))

@app.route("/firebase_login", methods=["POST"])
def firebase_login():
    try:
        data = request.get_json(force=True) or {}
        id_token = data.get("idToken") or ""
        payload = _decode_jwt_noverify(id_token)
        email = (payload.get("email") or "").strip().lower()
        name = (payload.get("name") or "").strip()
        if not email:
            return "/login", 200
        uid = get_or_create_user_by_email(email, name)
        db = get_db()
        db.execute("UPDATE users SET email_verified=1 WHERE id=?", (uid,))
        db.commit()
        session.clear()
        session["user_id"] = uid
        session["user_email"] = email
        session["user_name"] = name or ""
        return (url_for("mypage"), 200, {"Content-Type": "text/plain; charset=utf-8"})
    except Exception as e:
        app.logger.warning("firebase_login failed: %s", e)
        return "/login", 200

@app.route("/login/forgot", methods=["GET", "POST"])
def forgot_password():
    if request.method == "POST":
        email = (request.form.get("email") or "").strip().lower()
        if email:
            send_reset_email(email)
        return render_template("forgot_done.html", email=email)
    return render_template("forgot_password.html")

@app.route("/reset/<token>", methods=["GET", "POST"], endpoint="reset_password")
def reset_password(token: str):
    email = verify_token(token, "reset", max_age=60*60)
    if not email:
        flash("リンクの有効期限が切れているか不正です。", "error")
        return redirect(url_for("login"))
    if request.method == "POST":
        p1 = request.form.get("password") or ""
        p2 = request.form.get("password2") or ""
        if len(p1) < 8 or p1 != p2:
            flash("パスワードは8文字以上で2回同じものを入力してください。", "error")
            return render_template("reset_password.html", token=token)
        row = get_db().execute("SELECT id FROM users WHERE email=?", (email,)).fetchone()
        if not row:
            flash("アカウントが見つかりません。", "error")
            return redirect(url_for("login"))
        set_user_password(int(row["id"]), p1)
        flash("パスワードを更新しました。ログインしてください。", "success")
        return redirect(url_for("login"))
    return render_template("reset_password.html", token=token)

@app.route("/verify/<token>", methods=["GET"], endpoint="verify_email")
def verify_email(token: str):
    email = verify_token(token, "verify", max_age=60*60*24)
    if not email:
        flash("認証リンクが無効または期限切れです。", "error")
        return redirect(url_for("login"))
    db = get_db()
    db.execute("UPDATE users SET email_verified=1 WHERE email=?", (email,))
    db.commit()
    flash("メールアドレスを確認しました。ログインしてください。", "success")
    return redirect(url_for("login"))

@app.route("/verify/resend", methods=["POST"])
def verify_resend():
    email = (request.form.get("email") or "").strip().lower()
    if email:
        send_verify_email(email)
    return render_template("verify_sent.html", email=email)

def _logout_impl():
    try:
        csrf_validate_if_present()
    except Exception:
        pass
    session.clear()
    next_url = url_for("login") if "login" in app.view_functions else url_for("search")
    resp = redirect(next_url)
    try:
        resp.delete_cookie(app.session_cookie_name, path="/", samesite="Lax")
    except Exception:
        pass
    for name in ("firebase_id_token", "__session", "XSRF-TOKEN", "g_csrf_token"):
        try:
            resp.delete_cookie(name, path="/")
        except Exception:
            pass
    flash("ログアウトしました。", "info")
    return resp

if "logout" not in app.view_functions:
    @app.route("/logout", methods=["POST", "GET"], endpoint="logout")
    def logout():
        return _logout_impl()

if "signout" not in app.view_functions:
    @app.route("/signout", methods=["POST", "GET"], endpoint="signout")
    def signout():
        return _logout_impl()

if os.getenv("FLASK_ENV", "development") != "production":
    @app.route("/dev/login/<int:uid>")
    def dev_login(uid: int):
        session["user_id"] = int(uid)
        db = get_db()
        db.execute(
            "INSERT OR IGNORE INTO users(id,email,name) VALUES (?,?,?)",
            (uid, f"user{uid}@example.com", f"テストユーザー{uid}")
        )
        db.commit()
        flash(f"開発ログイン: user_id={uid}", "info")
        return redirect(request.referrer or url_for("home"))

@app.route("/splash")
def splash():
    next_url = request.args.get("next", "/language?next=/login")
    return render_template("splash.html", next_url=next_url)

@app.route('/language')
def language_select():
    next_url = request.args.get('next', '/login')
    return render_template('language_select.html', next_url=next_url)

# ============== Admin: Auth + Users 管理 ==============
@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        email = (request.form.get("email") or "").strip().lower()
        password = request.form.get("password") or ""
        db = get_db()
        row = db.execute("SELECT id,password_hash,name FROM admins WHERE email=?", (email,)).fetchone()
        if not row or not check_password_hash(row["password_hash"], password):
            flash("管理者のメールまたはパスワードが正しくありません。", "error")
            return render_template("admin_login.html")
        session["admin_id"] = int(row["id"])
        session["admin_email"] = email
        session["admin_name"] = row["name"] or "Admin"
        db.execute("UPDATE admins SET last_login=CURRENT_TIMESTAMP WHERE id=?", (int(row["id"]),))
        db.commit()
        flash("管理者としてログインしました。", "success")
        next_url = request.args.get("next") or url_for("admin_dashboard")
        return redirect(next_url)
    return render_template("admin_login.html")

@app.route("/admin/logout")
def admin_logout():
    for k in ("admin_id", "admin_email", "admin_name"):
        session.pop(k, None)
    flash("管理者をログアウトしました。", "info")
    return redirect(url_for("admin_login"))

# ---- Admin Dashboard ----
def _admin_dashboard_data():
    db = get_db()
    total_users = db.execute("SELECT COUNT(*) AS c FROM users WHERE deleted_at IS NULL").fetchone()["c"]
    total_users_deleted = db.execute("SELECT COUNT(*) AS c FROM users WHERE deleted_at IS NOT NULL").fetchone()["c"]
    total_posts = db.execute("SELECT COUNT(*) AS c FROM posts").fetchone()["c"]
    open_reports = db.execute("SELECT COUNT(*) AS c FROM reports WHERE status='open'").fetchone()["c"]
    pending_claims = db.execute("SELECT COUNT(*) AS c FROM store_claims WHERE status='pending'").fetchone()["c"]

    latest_users = db.execute("""
        SELECT id, email, name, email_verified, deleted_at
          FROM users
         ORDER BY id DESC
         LIMIT 10
    """).fetchall()

    latest_reports = db.execute("""
        SELECT id, kind, target_id, reason, status, created_at
          FROM reports
         ORDER BY created_at DESC
         LIMIT 10
    """).fetchall()

    top_favs = db.execute("""
        SELECT store_id, COUNT(*) AS c
          FROM favorites
         GROUP BY store_id
         ORDER BY c DESC
         LIMIT 10
    """).fetchall()

    stores = get_all_stores_from_sheet_cached()
    store_map = {int(s.get("店舗ID") or 0): (s.get("店舗名") or s.get("name") or f"店舗#{s.get('店舗ID')}") for s in stores}
    top_favorites = [{"store_id": int(r["store_id"]), "name": store_map.get(int(r["store_id"]), f"店舗#{int(r['store_id'])}"), "count": int(r["c"])} for r in top_favs]

    return {
        "total_users": int(total_users or 0),
        "total_users_deleted": int(total_users_deleted or 0),
        "total_posts": int(total_posts or 0),
        "open_reports": int(open_reports or 0),
        "pending_claims": int(pending_claims or 0),
        "latest_users": latest_users,
        "latest_reports": latest_reports,
        "top_favorites": top_favorites,
    }

@app.route("/admin")
def admin_root():
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    data = _admin_dashboard_data()
    return render_template("admin_dashboard.html", **data)


@app.route("/admin/dashboard")
def admin_dashboard():
    """管理ダッシュボード：サマリ + Sheetsキャッシュ状態の表示（TTL/年齢）"""
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()

    # --- サマリ数値 ---
    active_users = db.execute(
        "SELECT COUNT(*) AS c FROM users WHERE deleted_at IS NULL"
    ).fetchone()["c"]

    left_users = db.execute(
        "SELECT COUNT(*) AS c FROM users WHERE deleted_at IS NOT NULL"
    ).fetchone()["c"]

    posts_count = db.execute(
        "SELECT COUNT(*) AS c FROM posts"
    ).fetchone()["c"]

    open_reports = db.execute(
        "SELECT COUNT(*) AS c FROM reports WHERE status='open'"
    ).fetchone()["c"]

    # --- お気に入り上位店舗（store_id, count） ---
    fav_top = db.execute(
        "SELECT store_id, COUNT(*) AS cnt "
        "FROM favorites GROUP BY store_id "
        "ORDER BY cnt DESC LIMIT 10"
    ).fetchall()

    # Sheets から店舗名辞書を用意（フォールバックあり）
    store_names = {}
    try:
        stores = get_all_stores_from_sheet_cached()
        for s in stores or []:
            sid = str(s.get("id") or s.get("store_id") or "")
            if not sid:
                continue
            store_names[sid] = (
                s.get("name")
                or s.get("store_name")
                or f"店舗#{sid}"
            )
    except Exception as e:
        app.logger.info("dashboard: sheets name map failed: %s", e)

    # --- 最新ユーザー / 最新通報 ---
    latest_users = db.execute(
        "SELECT id, name, email, email_verified "
        "FROM users WHERE deleted_at IS NULL "
        "ORDER BY id DESC LIMIT 10"
    ).fetchall()

    latest_reports = db.execute(
        "SELECT id, kind, target_id, reason, status "
        "FROM reports ORDER BY datetime(created_at) DESC LIMIT 10"
    ).fetchall()

    # --- Sheetsキャッシュ情報（表示用） ---
    env_ttl = SHEETS_CACHE_TTL
    ttl_override = _SHEETS_TTL_OVERRIDE
    ttl_current = _current_sheets_ttl()       # 画面表示：実効TTL
    cached = _SHEETS_CACHE.get("stores", {"ts": 0.0, "data": None})
    cache_has = cached.get("data") is not None
    cache_age = 0
    if cached.get("ts"):
        try:
            cache_age = int(time.time() - float(cached["ts"]))
        except Exception:
            cache_age = 0

    # 画面描画
    return render_template(
        "admin_dashboard.html",
        active_users=active_users,
        left_users=left_users,
        posts_count=posts_count,
        open_reports=open_reports,
        fav_top=fav_top,
        store_names=store_names,
        latest_users=latest_users,
        latest_reports=latest_reports,
        # Sheetsキャッシュ表示用
        env_ttl=env_ttl,
        ttl_override=ttl_override,
        ttl_current=ttl_current,
        cache_has=cache_has,
        cache_age=cache_age,
    )


# ---- 追加: Admin Claims（オーナー申請） ----
def _store_name_map() -> Dict[int, str]:
    stores = get_all_stores_from_sheet_cached()
    return {int(s.get("店舗ID") or 0): (s.get("店舗名") or s.get("name") or f"店舗#{s.get('店舗ID')}") for s in stores}

@app.route("/admin/claims")
def admin_claims():
    """
    オーナー申請の審査一覧。
    クエリ: ?status=pending|approved|rejected|all（既定 pending）
           ?q=（store_id / 申請者名 / メール / メモ の部分一致）
           ?limit=200
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()
    if not _table_exists("store_claims"):
        flash("store_claims テーブルが存在しません。", "error")
        return render_template("admin_claims.html", rows=[], status="pending", q="", limit=200)

    # 利用可能な列を取得（柔軟に SELECT を組む）
    cols = {r["name"] for r in db.execute("PRAGMA table_info(store_claims)").fetchall()}
    sel = ["id", "store_id", "user_id"]
    for c in ("status","applicant_name","applicant_email","proof_image","note","verdict_note","created_at","decided_at","decided_by"):
        if c in cols: sel.append(c)

    status = (request.args.get("status") or "pending").strip()
    if status not in ("pending","approved","rejected","all"):
        status = "pending"
    q = (request.args.get("q") or "").strip()
    try:
        limit = max(1, min(1000, int(request.args.get("limit") or "200")))
    except Exception:
        limit = 200

    where, params = [], []
    if "deleted_at" in cols:
        where.append("deleted_at IS NULL")
    if status != "all" and "status" in cols:
        where.append("status = ?")
        params.append(status)
    if q:
        # 動的に存在する列の中から検索対象を作る
        search_fields = []
        if "store_id" in cols: search_fields.append("CAST(store_id AS TEXT)")
        if "applicant_name" in cols: search_fields.append("COALESCE(applicant_name,'')")
        if "applicant_email" in cols: search_fields.append("COALESCE(applicant_email,'')")
        if "note" in cols: search_fields.append("COALESCE(note,'')")
        if not search_fields:
            search_fields = ["CAST(user_id AS TEXT)"]
        like = f"%{q}%"
        where.append("(" + " OR ".join([f"{f} LIKE ?" for f in search_fields]) + ")")
        params += [like]*len(search_fields)

    sql = "SELECT " + ", ".join(sel) + " FROM store_claims"
    if where: sql += " WHERE " + " AND ".join(where)
    order_col = "created_at" if "created_at" in cols else "id"
    sql += f" ORDER BY {order_col} DESC"
    sql += " LIMIT ?"
    params.append(limit)

    rows = db.execute(sql, params).fetchall()

    # users からメール/名前を補完
    has_email_col = "applicant_email" in cols
    has_name_col  = "applicant_name" in cols
    try:
        if rows and _table_exists("users"):
            user_ids = [r["user_id"] for r in rows if r["user_id"]]
            if user_ids:
                umap = {u["id"]: u for u in db.execute(
                    f"SELECT id, email, name FROM users WHERE id IN ({','.join(['?']*len(user_ids))})",
                    user_ids
                ).fetchall()}
                for r in rows:
                    u = umap.get(r["user_id"])
                    if u:
                        if (not has_email_col) or (has_email_col and not r.get("applicant_email")):
                            r["applicant_email"] = u["email"]
                        if (not has_name_col) or (has_name_col and not r.get("applicant_name")):
                            r["applicant_name"] = u.get("name") or ""
    except Exception:
        pass

    return render_template("admin_claims.html", rows=rows, status=status, q=q, limit=limit)

@app.route("/admin/claims/<int:cid>/decision", methods=["POST"])
def admin_claims_decision(cid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()
    action = (request.form.get("action") or "").strip()
    note = (request.form.get("note") or "").strip()
    if action not in ("approve","reject"):
        flash("不正な操作です。", "error")
        return redirect(url_for("admin_claims"))

    new_status = "approved" if action == "approve" else "rejected"
    db = get_db()
    row = db.execute("SELECT id, store_id, user_id, email, name, status FROM store_claims WHERE id=?", (cid,)).fetchone()
    if not row:
        abort(404)
    if row["status"] == new_status:
        flash("既に同じステータスです。", "info")
        return redirect(request.referrer or url_for("admin_claims"))

    db.execute("UPDATE store_claims SET status=?, handled_at=CURRENT_TIMESTAMP WHERE id=?", (new_status, cid))
    db.commit()

    # 申請者へ任意通知
    try:
        if (row["email"] or "").strip():
            st = get_store_by_id(int(row["store_id"])) or {}
            stname = st.get("店舗名") or st.get("name") or f"店舗#{int(row['store_id'])}"
            subject = "[Luminity] オーナー申請の結果"
            if new_status == "approved":
                body = f"{row['name'] or 'ご担当者'} 様\n\n店舗「{stname}」のオーナー申請が承認されました。アプリ内でお知らせ投稿などが可能になりました。"
            else:
                body = f"{row['name'] or 'ご担当者'} 様\n\n店舗「{stname}」のオーナー申請は見送りとなりました。"
            if note:
                body += f"\n\n【メッセージ】\n{note}\n"
            send_email(row["email"], subject, body)
    except Exception as e:
        app.logger.info("claim mail skip: %s", e)

    flash("申請を更新しました。", "success")
    return redirect(request.referrer or url_for("admin_claims"))

@app.route("/admin/users")
def admin_users():
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()
    q = (request.args.get("q") or "").strip()                 # メール/名前 部分一致
    verified = (request.args.get("verified") or "").strip()   # '', '1', '0'
    deleted = (request.args.get("deleted") or "").strip()     # '1' なら退会も表示
    sort = (request.args.get("sort") or "id_desc").strip()    # 'id_desc' / 'id_asc'

    conds, params = [], []
    if deleted != "1":
        conds.append("deleted_at IS NULL")
    if verified in ("0", "1"):
        conds.append("email_verified = ?")
        params.append(1 if verified == "1" else 0)
    if q:
        conds.append("(email LIKE ? OR name LIKE ?)")
        like = f"%{q}%"
        params += [like, like]

    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    order = " ORDER BY id ASC" if sort == "id_asc" else " ORDER BY id DESC"
    sql = f"""SELECT id, email, name, email_verified, deleted_at
              FROM users{where}{order} LIMIT 1000"""
    rows = db.execute(sql, tuple(params)).fetchall()

    # 既存テンプレに渡す追加パラメータ
    return render_template(
        "admin_users.html",
        rows=rows,
        q=q,
        show_deleted=(deleted == "1"),
        verified=verified,
        sort=sort
    )
    
@app.route("/admin/users/<int:uid>/send_reset", methods=["POST"])
def admin_user_send_reset(uid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()

    db = get_db()
    row = db.execute("SELECT email FROM users WHERE id=?", (uid,)).fetchone()
    if not row or not (row["email"] or "").strip():
        flash("メールアドレスが未設定のため送信できません。", "error")
        return redirect(request.referrer or url_for("admin_users"))

    try:
        send_reset_email((row["email"] or "").strip().lower())
        flash("パスワード再設定メールを送信しました。", "success")
    except Exception as e:
        app.logger.info("send_reset failed: %s", e)
        flash("送信に失敗しました。ログを確認してください。", "error")
    return redirect(request.referrer or url_for("admin_users"))

@app.route("/admin/reports")
def admin_reports():
    """通報一覧（検索・絞り込み）。ダッシュボードからのリンク先。
    テンプレート: templates/admin_reports.html
    既存の更新用エンドポイント: admin_reports_update（POST）はそのまま利用します。
    """
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()
    q = (request.args.get("q") or "").strip()
    status = (request.args.get("status") or "open").strip()   # open/triaged/done/ignored/all
    kind = (request.args.get("kind") or "").strip()           # store/post/allergy/''(全て)

    conds, params = [], []

    if status and status != "all":
        conds.append("status = ?")
        params.append(status)

    if kind in ("store", "post", "allergy"):
        conds.append("kind = ?")
        params.append(kind)

    if q:
        like = f"%{q}%"
        conds.append("(reason LIKE ? OR body LIKE ? OR CAST(target_id AS TEXT) LIKE ?)")
        params += [like, like, like]

    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    # open→triaged→others の順で、その中で新しい順
    sql = f"""
        SELECT id, kind, target_id, reason, body, status, created_at, handled_at
          FROM reports
          {where}
         ORDER BY 
           CASE status WHEN 'open' THEN 0 WHEN 'triaged' THEN 1 ELSE 2 END,
           datetime(created_at) DESC
         LIMIT 200
    """
    rows = db.execute(sql, tuple(params)).fetchall()

    return render_template(
        "admin_reports.html",
        rows=rows, q=q, status=status, kind=kind
    )

@app.route("/admin/users/<int:uid>/send_verify", methods=["POST"])
def admin_user_send_verify(uid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()

    db = get_db()
    row = db.execute("SELECT email FROM users WHERE id=?", (uid,)).fetchone()
    if not row or not (row["email"] or "").strip():
        flash("メールアドレスが未設定のため送信できません。", "error")
        return redirect(request.referrer or url_for("admin_users"))

    try:
        send_verify_email((row["email"] or "").strip().lower())
        flash("認証メールを再送しました。", "success")
    except Exception as e:
        app.logger.info("send_verify failed: %s", e)
        flash("送信に失敗しました。ログを確認してください。", "error")
    return redirect(request.referrer or url_for("admin_users"))

@app.route("/admin/users/export.csv")
def admin_users_export():
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard

    db = get_db()
    q = (request.args.get("q") or "").strip()
    verified = (request.args.get("verified") or "").strip()   # '', '1', '0'
    deleted = (request.args.get("deleted") or "").strip()     # '1' なら退会も含む
    sort = (request.args.get("sort") or "id_desc").strip()    # 'id_desc' / 'id_asc'

    conds, params = [], []
    if deleted != "1":
        conds.append("deleted_at IS NULL")
    if verified in ("0", "1"):
        conds.append("email_verified = ?")
        params.append(1 if verified == "1" else 0)
    if q:
        conds.append("(email LIKE ? OR name LIKE ?)")
        like = f"%{q}%"
        params += [like, like]

    where = (" WHERE " + " AND ".join(conds)) if conds else ""
    order = " ORDER BY id ASC" if sort == "id_asc" else " ORDER BY id DESC"
    sql = f"""SELECT id, name, email, email_verified, deleted_at
              FROM users{where}{order}"""

    rows = db.execute(sql, tuple(params)).fetchall()

    # CSV生成
    import io, csv
    from flask import Response
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["id", "name", "email", "email_verified", "deleted_at"])
    for r in rows:
        w.writerow([
            r["id"],
            r["name"] or "",
            r["email"] or "",
            int(r["email_verified"] or 0),
            r["deleted_at"] or ""
        ])
    csv_data = buf.getvalue()
    buf.close()

    filename = f"users_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
    return Response(
        csv_data,
        mimetype="text/csv; charset=utf-8",
        headers={"Content-Disposition": f'attachment; filename="{filename}"'}
    )

@app.route("/admin/users/<int:uid>/edit", methods=["GET", "POST"])
def admin_user_edit(uid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    db = get_db()
    row = db.execute("SELECT id, email, name, email_verified, deleted_at FROM users WHERE id=?", (uid,)).fetchone()
    if not row:
        abort(404)
    if request.method == "POST":
        _ = _ensure_csrf()
        name = (request.form.get("name") or "").strip() or "ユーザー"
        email = (request.form.get("email") or "").strip().lower()
        verify = 1 if (request.form.get("email_verified") == "1") else 0
        new_pw = (request.form.get("new_password") or "").strip()
        try:
            if email:
                db.execute("UPDATE users SET name=?, email=?, email_verified=? WHERE id=?", (name, email, verify, uid))
            else:
                db.execute("UPDATE users SET name=?, email_verified=? WHERE id=?", (name, verify, uid))
            if new_pw:
                if len(new_pw) < 8:
                    flash("パスワードは8文字以上にしてください。", "error")
                    return render_template("admin_edit.html", u=row)
                set_user_password(uid, new_pw)
            db.commit()
            flash("ユーザー情報を更新しました。", "success")
            return redirect(url_for("admin_users"))
        except sqlite3.IntegrityError:
            flash("そのメールアドレスは既に使用されています。", "error")
    u = db.execute("SELECT id, email, name, email_verified, deleted_at FROM users WHERE id=?", (uid,)).fetchone()
    return render_template("admin_edit.html", u=u)

@app.route("/admin/users/<int:uid>/delete", methods=["POST"])
def admin_user_delete(uid: int):
    guard = require_admin()
    if guard:
        admin_flash_not_logged()
        return guard
    _ = _ensure_csrf()
    db = get_db()
    ts = int(time.time())
    cur = db.execute("SELECT email FROM users WHERE id=?", (uid,)).fetchone()
    old_email = (cur["email"] or "deleted") if cur else "deleted"
    new_email = f"deleted+{uid}+{ts}@local.invalid"
    db.execute("UPDATE users SET email=?, password_hash=NULL, deleted_at=CURRENT_TIMESTAMP WHERE id=?", (new_email, uid))
    db.execute("DELETE FROM favorites WHERE user_id=?", (uid,))
    db.commit()
    flash(f"ユーザー {old_email} を退会処理しました。", "success")
    return redirect(url_for("admin_users"))
    
   # ========== ADMIN DASHBOARD (override-safe) ==========
from functools import wraps
from datetime import datetime
from flask import (
    request, session, g, redirect, url_for,
    render_template, flash, jsonify, abort
)
from werkzeug.security import generate_password_hash, check_password_hash

# --- 共通: DBユーティリティは既存の get_db() を使用 ---
# ここでは既に get_db(), init_db() がある前提です。

# --- 0) ルート上書き安全な登録器 -------------------------------------------
def _register_or_override(rule: str, endpoint: str, view_func, methods=("GET",)):
    """同じ endpoint が既にあれば view 関数を差し替え、無ければ追加する。"""
    if endpoint in app.view_functions:
        app.view_functions[endpoint] = view_func
    else:
        app.add_url_rule(rule, endpoint=endpoint, view_func=view_func, methods=list(methods))

# --- 1) admins テーブルの安全な用意 ---------------------------------------
def ensure_admin_tables() -> None:
    db = get_db()
    db.execute("""
        CREATE TABLE IF NOT EXISTS admins(
          id            INTEGER PRIMARY KEY AUTOINCREMENT,
          email         TEXT UNIQUE NOT NULL,
          password_hash TEXT,
          name          TEXT,
          role          TEXT,
          created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          last_login_at TIMESTAMP
        )
    """)
    cols = {r["name"] for r in db.execute("PRAGMA table_info(admins)").fetchall()}
    if "password_hash" not in cols:
        db.execute("ALTER TABLE admins ADD COLUMN password_hash TEXT")
    if "role" not in cols:
        db.execute("ALTER TABLE admins ADD COLUMN role TEXT")
    if "last_login_at" not in cols:
        db.execute("ALTER TABLE admins ADD COLUMN last_login_at TIMESTAMP")
    db.commit()

def _migrate_admins_role():
    """role 空の行に 'admin' を補完（既存互換の緩い移行）。"""
    db = get_db()
    db.execute("UPDATE admins SET role='admin' WHERE (role IS NULL OR role='')")
    db.commit()

def _migrate_store_claims():
    """store_claims の最低限列を補完（無ければ追加）。"""
    db = get_db()
    db.execute("""
        CREATE TABLE IF NOT EXISTS store_claims(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          store_id INTEGER NOT NULL,
          applicant_name TEXT,
          applicant_email TEXT,
          status TEXT,                -- pending / approved / rejected
          note TEXT,
          verdict_note TEXT,
          decided_by INTEGER,
          created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
          decided_at TIMESTAMP
        )
    """)
    cols = {r["name"] for r in db.execute("PRAGMA table_info(store_claims)").fetchall()}
    for col, ddl in (
        ("verdict_note", "ALTER TABLE store_claims ADD COLUMN verdict_note TEXT"),
        ("decided_by",  "ALTER TABLE store_claims ADD COLUMN decided_by INTEGER"),
        ("decided_at",  "ALTER TABLE store_claims ADD COLUMN decided_at TIMESTAMP"),
    ):
        if col not in cols:
            db.execute(ddl)
    db.commit()

def _bootstrap_admin_if_needed():
    """ENVの既定管理者を最低1件確保。"""
    import os
    ensure_admin_tables()
    db = get_db()
    count = db.execute("SELECT COUNT(*) FROM admins").fetchone()[0]
    if count and count > 0:
        return
    email = os.getenv("ADMIN_EMAIL", "admin@luminity.local").strip().lower()
    pw    = os.getenv("ADMIN_PASSWORD", "Luminity-Admin-2025!")
    db.execute(
        "INSERT INTO admins(email, password_hash, name, role) VALUES (?, ?, ?, ?)",
        (email, generate_password_hash(pw), "Administrator", "admin"),
    )
    db.commit()
    app.logger.info("Bootstrap admin created: %s", email)

# --- 2) 最初のリクエスト時に一回だけ初期化 -------------------------------
_BOOTSTRAPPED = False
@app.before_request
def _admin_bootstrap_hook():
    global _BOOTSTRAPPED
    if _BOOTSTRAPPED:
        return
    try:
        ensure_admin_tables()
        _migrate_admins_role()
        _migrate_store_claims()
        _bootstrap_admin_if_needed()
    except Exception as e:
        app.logger.exception("admin bootstrap failed: %s", e)
    finally:
        _BOOTSTRAPPED = True

# --- 3) セッションから管理者をロード ------------------------------------
@app.before_request
def _load_admin_from_session():
    g.admin = None
    aid = session.get("admin_id")
    if aid:
        db = get_db()
        g.admin = db.execute(
            "SELECT id, email, name, role FROM admins WHERE id=?", (aid,)
        ).fetchone()

def admin_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if not g.get("admin"):
            return redirect(url_for("admin_login", next=request.path))
        return fn(*args, **kwargs)
    return wrapper

# --- 4) 認証（上書き安全登録） ------------------------------------------
def _admin_login_get():
    if g.get("admin"):
        return redirect(url_for("admin_dashboard"))
    return render_template("admin_login.html")

def _admin_login_post():
    db = get_db()
    email = (request.form.get("email") or "").strip().lower()
    password = request.form.get("password") or ""
    row = db.execute(
        "SELECT id, email, password_hash, name, role FROM admins WHERE email=?",
        (email,)
    ).fetchone()
    ok = bool(row) and bool(row["password_hash"]) and check_password_hash(row["password_hash"], password)
    if not ok:
        flash("メールアドレスまたはパスワードが正しくありません。", "error")
        return redirect(url_for("admin_login"))
    session["admin_id"] = int(row["id"])
    db.execute("UPDATE admins SET last_login_at=CURRENT_TIMESTAMP WHERE id=?", (row["id"],))
    db.commit()
    flash("管理者としてログインしました。", "success")
    return redirect(request.args.get("next") or url_for("admin_dashboard"))

def _admin_logout_post():
    session.pop("admin_id", None)
    flash("ログアウトしました。", "info")
    return redirect(url_for("admin_login"))

_register_or_override("/admin/login",  "admin_login",       _admin_login_get,  ("GET",))
_register_or_override("/admin/login",  "admin_login_post",  _admin_login_post, ("POST",))
_register_or_override("/admin/logout", "admin_logout",      _admin_logout_post,("POST",))

# --- 5) ダッシュボード（上書き安全登録） --------------------------------
def _admin_root():
    return redirect(url_for("admin_dashboard"))

def _admin_dashboard():
    db = get_db()
    def one(sql, *p):
        r = db.execute(sql, p).fetchone()
        return int(r[0]) if r else 0
    metrics = {
        "users":          one("SELECT COUNT(*) FROM users"),
        "stores":         one("SELECT COUNT(*) FROM stores"),
        "posts":          one("SELECT COUNT(*) FROM posts"),
        "claims_pending": one("SELECT COUNT(*) FROM store_claims WHERE COALESCE(NULLIF(status,''),'pending')='pending'"),
        "reports_open":   one("SELECT COUNT(*) FROM reports WHERE resolved_at IS NULL") if "reports" in {c["name"] for c in db.execute("PRAGMA table_info(reports)").fetchall()} else 0,
    }
    return render_template("admin_dashboard.html", metrics=metrics)

_register_or_override("/admin",            "admin_root",      _admin_root,      ("GET",))
_register_or_override("/admin/dashboard",  "admin_dashboard", _admin_dashboard, ("GET",))

# --- 6) オーナー申請（上書き安全登録） -----------------------------------
def _admin_claims_list():
    db = get_db()
    rows = db.execute("""
        SELECT c.id, c.store_id, s.name AS store_name,
               c.applicant_name, c.applicant_email,
               COALESCE(NULLIF(c.status,''),'pending') AS status,
               c.created_at, c.decided_at, c.note, c.verdict_note
          FROM store_claims c
          LEFT JOIN stores s ON s.id=c.store_id
         ORDER BY c.created_at DESC, c.id DESC
    """).fetchall()
    return render_template("admin_claims.html", rows=rows)

def _admin_claims_decide(claim_id: int):
    db = get_db()
    action = (request.form.get("action") or "").strip()
    note = request.form.get("note") or ""
    if action not in ("approve", "reject"):
        abort(400)
    db.execute("""
        UPDATE store_claims
           SET status=?, verdict_note=?, decided_by=?, decided_at=CURRENT_TIMESTAMP
         WHERE id=?
    """, ("approved" if action=="approve" else "rejected", note, g.admin["id"], claim_id))
    db.commit()
    flash("申請を処理しました。", "success")
    return redirect(url_for("admin_claims"))

_register_or_override("/admin/claims",                     "admin_claims",        _admin_claims_list,   ("GET",))
_register_or_override("/admin/claims/<int:claim_id>/decide","admin_claims_decide", _admin_claims_decide, ("POST",))

# --- 7) Sheets 診断・キャッシュ（上書き安全登録） -----------------------
def _admin_sheets_diagnose():
    import os
    info = {
        "SHEET_ID": bool(os.getenv("SHEET_ID")),
        "CREDS_JSON": bool(os.getenv("GOOGLE_CREDENTIALS_JSON")),
    }
    ok, rows, err = True, [], None
    try:
        # 既存の関数があれば試す（無ければ空表示）
        if "get_all_stores_from_sheet_cached" in globals():
            rows = get_all_stores_from_sheet_cached(force=False)[:5]  # noqa
    except Exception as e:
        ok, err = False, str(e)
    return render_template("admin_sheets_diagnose.html", info=info, ok=ok, err=err, rows=rows)

def _admin_sheets_cache_refresh():
    refreshed, error = False, None
    try:
        if "get_all_stores_from_sheet_cached" in globals():
            get_all_stores_from_sheet_cached(force=True)  # noqa
            refreshed = True
    except Exception as e:
        error = str(e)
    return jsonify({"ok": refreshed, "error": error}), (200 if refreshed else 500)

_register_or_override("/admin/sheets/diagnose",      "admin_sheets_diagnose",      _admin_sheets_diagnose,      ("GET",))
_register_or_override("/admin/sheets/cache/refresh", "admin_sheets_cache_refresh", _admin_sheets_cache_refresh, ("POST",))

# --- 8) 任意: レポート一覧（テーブルがあれば） ---------------------------
def _admin_reports():
    db = get_db()
    if "reports" not in {c["name"] for c in db.execute("PRAGMA table_info(reports)").fetchall()}:
        return render_template("admin_reports.html", rows=[])
    rows = db.execute("""
        SELECT r.id, r.post_id, p.user_id, r.reason, r.created_at, r.resolved_at
          FROM reports r LEFT JOIN posts p ON p.id=r.post_id
         ORDER BY r.created_at DESC
    """).fetchall()
    return render_template("admin_reports.html", rows=rows)

_register_or_override("/admin/reports", "admin_reports", _admin_reports, ("GET",))
# ========== /ADMIN DASHBOARD END ==========
# ===== PATCH: admin posts (schema-flex) =========================
# 既に上の管理者ブロックで _register_or_override と get_db() が使える前提

def _detect_column(cols, candidates):
    for c in candidates:
        if c in cols:
            return c
    return None

def _table_exists(db, name: str) -> bool:
    row = db.execute("SELECT name FROM sqlite_master WHERE type='table' AND name=?", (name,)).fetchone()
    return bool(row)

def _admin_posts_list():
    db = get_db()
    if not _table_exists(db, "posts"):
        # テーブル自体が無い場合でもテンプレの描画は通す
        return render_template("admin_posts.html", rows=[])

    cols = [r["name"] for r in db.execute("PRAGMA table_info(posts)").fetchall()]

    # 列名を動的に検出して標準名（AS 句）に寄せる
    text_col    = _detect_column(cols, ["content", "body", "text", "message", "caption", "description"])
    title_col   = _detect_column(cols, ["title", "subject", "headline"])
    image_col   = _detect_column(cols, ["image_url", "photo_url", "image", "photo"])
    created_col = _detect_column(cols, ["created_at", "created", "createdAt", "ts", "timestamp"])
    user_col    = _detect_column(cols, ["user_id", "userid", "author_id"])
    store_col   = _detect_column(cols, ["store_id", "storeid", "store"])

    fields = ["id"]
    if user_col:    fields.append(f"{user_col} AS user_id")
    if store_col:   fields.append(f"{store_col} AS store_id")
    if title_col:   fields.append(f"{title_col} AS title")
    if text_col:    fields.append(f"{text_col} AS content")      # ← テンプレ側は row.content 参照で統一
    if image_col:   fields.append(f"{image_col} AS image_url")
    if created_col: fields.append(f"{created_col} AS created_at")

    # 少なくとも id はある前提。並び替えは created 相当があればそれを優先
    order_col = created_col or "id"
    sql = f"SELECT {', '.join(fields)} FROM posts ORDER BY {order_col} DESC"

    rows = db.execute(sql).fetchall()

    # store 名を付与（あれば）
    store_name_map = {}
    if store_col and _table_exists(db, "stores"):
        for r in db.execute("SELECT id, name FROM stores"):
            store_name_map[r["id"]] = r["name"]

    out = []
    for r in rows:
        d = dict(r)
        if "store_id" in d:
            d["store_name"] = store_name_map.get(d["store_id"])
        out.append(d)

    return render_template("admin_posts.html", rows=out)

# 既存エンドポイントがあれば置換、無ければ追加
_register_or_override("/admin/posts", "admin_posts", _admin_posts_list, ("GET",))
# ===== /PATCH ===================================================
# ===== Optional PATCH: admin comments (schema-flex) =============
def _admin_comments_list():
    db = get_db()
    # テーブル名は comments / post_comments のどちらかと想定
    table = "comments"
    if not _table_exists(db, table):
        table = "post_comments" if _table_exists(db, "post_comments") else None
    if not table:
        return render_template("admin_comments.html", rows=[])

    cols = [r["name"] for r in db.execute(f"PRAGMA table_info({table})").fetchall()]
    text_col    = _detect_column(cols, ["content", "comment", "body", "text", "message"])
    created_col = _detect_column(cols, ["created_at", "created", "ts", "timestamp"])
    user_col    = _detect_column(cols, ["user_id", "userid", "author_id"])
    post_col    = _detect_column(cols, ["post_id", "postid"])

    fields = ["id"]
    if post_col:    fields.append(f"{post_col} AS post_id")
    if user_col:    fields.append(f"{user_col} AS user_id")
    if text_col:    fields.append(f"{text_col} AS content")
    if created_col: fields.append(f"{created_col} AS created_at")

    order_col = created_col or "id"
    sql = f"SELECT {', '.join(fields)} FROM {table} ORDER BY {order_col} DESC"
    rows = db.execute(sql).fetchall()
    return render_template("admin_comments.html", rows=rows)

_register_or_override("/admin/comments", "admin_comments", _admin_comments_list, ("GET",))

# --- 追加（存在しない場合のみ定義）: ルート上書き安全登録器 ---
try:
    _register_or_override  # 既存定義があればそれを使う
except NameError:
    def _register_or_override(rule: str, endpoint: str, view_func, methods=("GET",)):
        if endpoint in app.view_functions:
            app.view_functions.pop(endpoint, None)
        app.add_url_rule(rule, endpoint, view_func, methods=list(methods))

# --- 追加: ログアウト後は必ずウェルカムへ ---
def _logout_user_view():
    # ユーザー用ログアウト（一般セッション）
    session.clear()
    # 次回 / でウェルカムを出したい場合はフラグを消す（保険）
    session.pop("seen_welcome", None)
    return redirect(url_for("welcome"))  # ← 直接ウェルカムへ

def _admin_logout_view():
    # 管理者用ログアウト（/admin/logout は POST 想定）
    for k in ("admin_id", "admin_email", "admin_role"):
        session.pop(k, None)
    # 一般セッションも念のためクリア
    session.pop("user_id", None)
    session.pop("seen_welcome", None)
    return redirect(url_for("welcome"))  # ← 直接ウェルカムへ

# 既存があれば置換、無ければ追加（後方互換: /logout は GET/POST どちらも許容）
_register_or_override("/logout", "logout", _logout_user_view, ("GET","POST"))
_register_or_override("/admin/logout", "admin_logout", _admin_logout_view, ("POST",))

# ===== /Optional PATCH ==========================================


from flask import send_from_directory, current_app


@app.route("/__debug/routes_check")
def debug_routes_check():
    """
    すべてのルートをチェックし、
    - 呼び出し可能か？
    - endpoint の衝突は？
    - store_id/uid などの変数を適当に埋めてテスト

    を一覧に出すデバッグツール
    """

    import re
    from flask import current_app

    results = []

    for rule in app.url_map.iter_rules():
        endpoint = rule.endpoint
        methods = ",".join(rule.methods - {"HEAD", "OPTIONS"})

        # パラメータ付きルートにテスト用の値を挿入
        url = rule.rule

        # <int:store_id> → 1 に変換
        url = re.sub(r"<int:[^>]+>", "1", url)

        # <int:uid> → 1
        url = re.sub(r"<int:uid>", "1", url)

        # <path:filename> → test.png
        url = re.sub(r"<path:[^>]+>", "test.png", url)

        # <token> → abc
        url = url.replace("<token>", "abc")

        # GET に限定してテストする
        test_url = f"http://127.0.0.1:5000{url}"

        import requests
        try:
            r = requests.get(test_url)
            status = r.status_code
        except Exception as e:
            status = f"ERR: {e}"

        results.append({
            "rule": rule.rule,
            "endpoint": endpoint,
            "methods": methods,
            "test_url": url,
            "status": status
        })

    # HTML 出力
    html = "<h1>Route Usage Check</h1><table border=1 cellpadding=5>"
    html += "<tr><th>Rule</th><th>Endpoint</th><th>Methods</th><th>Test URL</th><th>Status</th></tr>"

    for r in results:
        color = "red" if r["status"] == 404 else "green"
        html += f"<tr><td>{r['rule']}</td><td>{r['endpoint']}</td><td>{r['methods']}</td>"
        html += f"<td>{r['test_url']}</td><td style='color:{color}'>{r['status']}</td></tr>"

    html += "</table>"
    return html

@app.route("/debug/stores")
def debug_stores():
    stores = []
    try:
        for i in range(1, 50):
            s = get_store_with_overrides(i)
            if s:
                stores.append(s)
    except Exception as e:
        return jsonify({"error": str(e)})

    return jsonify(stores=stores)

@app.route("/allergy_pdf_download/<int:store_id>")
def allergy_pdf_download(store_id: int):
    store = get_store_with_overrides(store_id)
    if not store:
        abort(404)

    # アレルギー行データ
    rows, allergens = _fetch_allergy_table_by_store(store)

    # ★ menu → メニュー に変換（転置済みテーブル前提）
    fixed_rows = []
    for r in rows:
        new_row = {"メニュー": r.get("menu", "")}
        for k, v in r.items():
            if k != "menu":
                new_row[k] = v
        fixed_rows.append(new_row)

    # 特定原材料 8品目
    primary_names = [
        "卵",
        "乳",
        "小麦",
        "えび",
        "かに",
        "くるみ",
        "そば",
        "落花生（ピーナッツ）",
    ]
    primary = [a for a in allergens if a in primary_names]
    other = [a for a in allergens if a not in primary]

    # QRコードURL（HTML版アレルギー表）
    allergy_url = url_for("allergy_public", store_id=store_id, _external=True)

    pdf_bytes = build_allergy_pdf(
        store=store,
        rows=fixed_rows,
        primary_allergens=primary,
        other_allergens=other,
        allergy_url=allergy_url,
    )

    filename_base = store.get("店舗名") or store.get("name") or f"store_{store_id}"
    filename = f"allergy_{filename_base}.pdf"

    return send_file(
        BytesIO(pdf_bytes),
        mimetype="application/pdf",
        as_attachment=True,
        download_name=filename,
    )

# --- QR wait page (Render wake-up) ---
@app.route("/qr/<int:store_id>", endpoint="qr_wait")
def qr_wait(store_id: int):
    # storeが存在しないIDなら404
    store = get_store_by_id(store_id) or abort(404)

    # 次に飛ばす先：あなたの現行ルートに合わせる
    # いま存在しているのは「/allergy/<id>/agreement」なのでそれを使う
    next_url = url_for("allergy_agreement", store_id=store_id, _external=True)

    # 参考：トップ（適宜あなたのトップに合わせて変更OK）
    home_url = url_for("index", _external=True) if "index" in app.view_functions else "/"

    return render_template(
        "qr_wait.html",
        store=store,
        store_id=store_id,
        next_url=next_url,
        home_url=home_url,
    )

# ============== Shortcuts ==============
@app.route("/login/admin")
def login_admin_alias():
    nxt = request.args.get("next")
    return redirect(url_for("admin_login", next=nxt) if nxt else url_for("admin_login"))

# ============== Main ==============
if __name__ == "__main__":
    import os
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port)




