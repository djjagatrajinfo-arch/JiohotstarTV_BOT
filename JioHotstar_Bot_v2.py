import asyncio
import base64
import glob
import io
import json
import logging
import os
import random
import re
import string
import threading
import zipfile
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer

import cloudscraper
import requests
from telegram import Update, BotCommand
from telegram.constants import ParseMode
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes

try:
    import cv2
    import numpy as np
    from pyzbar.pyzbar import decode as zbar_decode
    LOCAL_QR_AVAILABLE = True
except Exception:
    LOCAL_QR_AVAILABLE = False

# ==========================================
# CONFIGURATION (Railway & Render Env Vars)
# ==========================================
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
ADMIN_IDS = {
    int(x.strip())
    for x in os.environ.get("ADMIN_IDS", "6177293322").split(",")
    if x.strip().lstrip("-").isdigit()
}

DATA_DIR = os.environ.get("DATA_DIR", "data").strip() or "data"
COOKIES_DIR = os.environ.get("COOKIES_DIR", os.path.join(DATA_DIR, "cookies")).strip()
STATS_FILE = os.path.join(DATA_DIR, "bot_stats.json")
COOKIE_USAGE_FILE = os.path.join(DATA_DIR, "cookie_usage.json")
LOGS_FILE = os.path.join(DATA_DIR, "activation_logs.json")

MAX_USES_PER_COOKIE = int(os.environ.get("MAX_USES_PER_COOKIE", "3") or 3)
DAILY_USER_LIMIT = int(os.environ.get("DAILY_USER_LIMIT", "5") or 5)
IST = timezone(timedelta(hours=5, minutes=30))

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

STORAGE_LOCK = threading.Lock()
_user_quota = {}


# ==========================================
# HEALTHCHECK SERVER (Required for Render Web Service)
# ==========================================
class _HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write(b"OK - JioHotstar Bot Running")

    def log_message(self, format, *args):
        return


def start_health_server():
    port_str = os.environ.get("PORT", "").strip()
    if not port_str.isdigit():
        return
    port = int(port_str)
    try:
        server = HTTPServer(("0.0.0.0", port), _HealthHandler)
        threading.Thread(target=server.serve_forever, daemon=True, name="healthcheck").start()
        logger.info(f"Healthcheck server running on 0.0.0.0:{port}")
    except Exception as e:
        logger.warning(f"Healthcheck server skipped: {e}")


# ==========================================
# HELPERS & STORAGE
# ==========================================
def esc(text) -> str:
    if text is None or text == "":
        return "N/A"
    return str(text).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS


def check_user_quota(uid: int):
    if is_admin(uid):
        return True, 9999
    today = datetime.now(IST).strftime("%Y-%m-%d")
    rec = _user_quota.setdefault(uid, {"date": today, "count": 0})
    if rec["date"] != today:
        rec["date"] = today
        rec["count"] = 0
    rem = DAILY_USER_LIMIT - rec["count"]
    return rem > 0, max(0, rem)


def inc_user_quota(uid: int):
    if is_admin(uid):
        return
    today = datetime.now(IST).strftime("%Y-%m-%d")
    rec = _user_quota.setdefault(uid, {"date": today, "count": 0})
    if rec["date"] != today:
        rec["date"] = today
        rec["count"] = 0
    rec["count"] += 1


def _read_json(path: str, default):
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return default


def _write_json(path: str, data):
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    except Exception as e:
        logger.error(f"Error saving {path}: {e}")


def load_stats():
    with STORAGE_LOCK:
        return _read_json(
            STATS_FILE,
            {
                "total_activations": 0,
                "successful_activations": 0,
                "failed_activations": 0,
                "last_activation": None,
            },
        )


def update_stats(success: bool = True):
    with STORAGE_LOCK:
        stats = _read_json(
            STATS_FILE,
            {
                "total_activations": 0,
                "successful_activations": 0,
                "failed_activations": 0,
                "last_activation": None,
            },
        )
        stats["total_activations"] += 1
        if success:
            stats["successful_activations"] += 1
        else:
            stats["failed_activations"] += 1
        stats["last_activation"] = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S IST")
        _write_json(STATS_FILE, stats)
        return stats


def append_activation_log(entry: dict):
    with STORAGE_LOCK:
        logs = _read_json(LOGS_FILE, [])
        logs.append(entry)
        _write_json(LOGS_FILE, logs[-100:])


def load_logs():
    with STORAGE_LOCK:
        return _read_json(LOGS_FILE, [])


def get_cookie_usage_count(cookie_name: str) -> int:
    with STORAGE_LOCK:
        usage = _read_json(COOKIE_USAGE_FILE, {})
        return int(usage.get(cookie_name, 0))


def increment_cookie_usage(cookie_name: str) -> int:
    with STORAGE_LOCK:
        usage = _read_json(COOKIE_USAGE_FILE, {})
        usage[cookie_name] = int(usage.get(cookie_name, 0)) + 1
        _write_json(COOKIE_USAGE_FILE, usage)
        return usage[cookie_name]


def remove_cookie_usage(cookie_name: str):
    with STORAGE_LOCK:
        usage = _read_json(COOKIE_USAGE_FILE, {})
        if cookie_name in usage:
            usage.pop(cookie_name, None)
            _write_json(COOKIE_USAGE_FILE, usage)


# ==========================================
# COOKIE PARSING & VAULT
# ==========================================
def parse_cookie_content(raw_text: str):
    cookies = {}
    session_token = None
    user_up_token = None
    device_id = None

    stripped = (raw_text or "").strip()
    if stripped.startswith("[") or stripped.startswith("{"):
        try:
            data = json.loads(stripped)
            items = data if isinstance(data, list) else (data.get("cookies") or [data])
            if isinstance(items, list):
                for item in items:
                    if isinstance(item, dict) and item.get("name"):
                        k = str(item["name"]).strip()
                        v = str(item.get("value", "")).strip()
                        cookies[k] = v
                        if k == "sessionUserUP":
                            session_token = v
                        elif k == "userUP":
                            user_up_token = v
                        elif k == "deviceId":
                            device_id = v
        except Exception:
            pass

    if not cookies:
        for line in raw_text.splitlines():
            line = line.strip()
            if not line or (line.startswith("#") and not line.startswith("#HttpOnly_")):
                continue
            if line.startswith("#HttpOnly_"):
                line = line[10:]
            parts = line.split("\t")
            if len(parts) >= 7:
                k = parts[5].strip()
                v = parts[6].strip()
                cookies[k] = v
                if k == "sessionUserUP":
                    session_token = v
                elif k == "userUP":
                    user_up_token = v
                elif k == "deviceId":
                    device_id = v

    if not cookies and "=" in stripped and "\n" not in stripped:
        for pair in stripped.split(";"):
            if "=" in pair:
                k, v = pair.split("=", 1)
                k, v = k.strip(), v.strip()
                cookies[k] = v
                if k == "sessionUserUP":
                    session_token = v
                elif k == "userUP":
                    user_up_token = v
                elif k == "deviceId":
                    device_id = v

    cookie_str = "; ".join(f"{k}={v}" for k, v in cookies.items())
    return cookies, cookie_str, session_token, user_up_token, device_id


def get_available_cookies():
    os.makedirs(COOKIES_DIR, exist_ok=True)
    files = glob.glob(os.path.join(COOKIES_DIR, "*.txt")) + glob.glob(os.path.join(COOKIES_DIR, "*.json"))
    avail = []
    for fp in files:
        fn = os.path.basename(fp)
        if get_cookie_usage_count(fn) < MAX_USES_PER_COOKIE:
            avail.append(fp)
    random.shuffle(avail)
    return avail


def get_cookie_stats():
    os.makedirs(COOKIES_DIR, exist_ok=True)
    files = glob.glob(os.path.join(COOKIES_DIR, "*.txt")) + glob.glob(os.path.join(COOKIES_DIR, "*.json"))
    used = 0
    avail = 0
    for fp in files:
        if get_cookie_usage_count(os.path.basename(fp)) >= MAX_USES_PER_COOKIE:
            used += 1
        else:
            avail += 1
    return {"total": len(files), "available": avail, "used": used}


def delete_cookie_file(filepath: str):
    try:
        fn = os.path.basename(filepath)
        if os.path.exists(filepath):
            os.remove(filepath)
        remove_cookie_usage(fn)
    except Exception as e:
        logger.error(f"Failed deleting {filepath}: {e}")


def clear_all_cookies() -> int:
    os.makedirs(COOKIES_DIR, exist_ok=True)
    files = glob.glob(os.path.join(COOKIES_DIR, "*.txt")) + glob.glob(os.path.join(COOKIES_DIR, "*.json"))
    deleted = 0
    for fp in files:
        delete_cookie_file(fp)
        deleted += 1
    with STORAGE_LOCK:
        _write_json(COOKIE_USAGE_FILE, {})
    return deleted


# ==========================================
# QR SCANNER (Local + Online API Fallback)
# ==========================================
def scan_qr(image_bytes: bytes):
    if LOCAL_QR_AVAILABLE:
        try:
            nparr = np.frombuffer(image_bytes, np.uint8)
            img = cv2.imdecode(nparr, cv2.IMREAD_COLOR)
            if img is not None:
                decoded = zbar_decode(img)
                if not decoded:
                    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
                    _, thresh1 = cv2.threshold(gray, 127, 255, cv2.THRESH_BINARY)
                    decoded = zbar_decode(thresh1)
                if not decoded:
                    thresh2 = cv2.adaptiveThreshold(
                        gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 11, 2
                    )
                    decoded = zbar_decode(thresh2)
                if decoded:
                    return decoded[0].data.decode("utf-8", errors="ignore").strip()
        except Exception as e:
            logger.warning(f"Local QR error: {e}")

    try:
        files = {"file": ("qr.jpg", io.BytesIO(image_bytes), "image/jpeg")}
        r = requests.post("https://api.qrserver.com/v1/read-qr-code/", files=files, timeout=15)
        if r.status_code == 200:
            data = r.json()
            qr_val = (((data or [{}])[0].get("symbol") or [{}])[0]).get("data")
            if qr_val:
                return str(qr_val).strip()
    except Exception as e:
        logger.warning(f"Online QR API error: {e}")

    return None


# ==========================================
# HOTSTAR TV ACTIVATION & ACCOUNT DETAILS
# ==========================================
HOTSTAR_HEADERS = {
    "authority": "www.hotstar.com",
    "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
    "accept-language": "en-MM,en-GB;q=0.9,en-US;q=0.8,en;q=0.7",
    "sec-ch-ua": '"Chromium";v="137", "Not/A)Brand";v="24"',
    "sec-ch-ua-mobile": "?1",
    "sec-ch-ua-platform": '"Android"',
    "sec-fetch-dest": "document",
    "sec-fetch-mode": "navigate",
    "sec-fetch-site": "none",
    "upgrade-insecure-requests": "1",
    "user-agent": (
        "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36"
    ),
}


def _decode_jwt_payload(token: str) -> dict:
    try:
        parts = (token or "").split(".")
        if len(parts) < 2:
            return {}
        pad = parts[1] + "=" * (-len(parts[1]) % 4)
        raw = base64.urlsafe_b64decode(pad).decode("utf-8", errors="ignore")
        return json.loads(raw)
    except Exception:
        return {}


def fetch_hotstar_account_details(scraper, base_headers: dict, token: str, fallback_name: str) -> dict:
    details = {
        "account_name": fallback_name,
        "plan": "JioHotstar",
        "expiry": "N/A",
        "profiles": [],
        "profile_count": 0,
        "devices": [],
        "country": "IN",
    }

    claims = _decode_jwt_payload(token)
    if claims:
        sub_obj = claims.get("sub")
        if isinstance(sub_obj, str) and sub_obj.startswith("{"):
            try:
                sub_obj = json.loads(sub_obj)
            except Exception:
                sub_obj = {}
        if isinstance(sub_obj, dict):
            if sub_obj.get("name"):
                details["account_name"] = str(sub_obj["name"])
            if sub_obj.get("countryCode"):
                details["country"] = str(sub_obj["countryCode"]).upper()
            subs = sub_obj.get("subscriptions") or {}
            if isinstance(subs, dict):
                for region_subs in subs.values():
                    if isinstance(region_subs, list) and region_subs:
                        s0 = region_subs[0]
                        if isinstance(s0, dict):
                            details["plan"] = s0.get("planName") or s0.get("name") or details["plan"]
                            exp_ts = s0.get("expiry") or s0.get("endDate")
                            if isinstance(exp_ts, (int, float)) and exp_ts > 1000000000:
                                ts = int(exp_ts // 1000) if exp_ts > 10**11 else int(exp_ts)
                                details["expiry"] = datetime.fromtimestamp(ts, IST).strftime("%d %b %Y")
                            elif isinstance(exp_ts, str):
                                details["expiry"] = exp_ts[:10]

    for path in ("https://www.hotstar.com/in/mypage", "https://www.hotstar.com/in/settings"):
        try:
            r = scraper.get(path, headers=base_headers, timeout=15)
            if r.status_code == 200 and r.text:
                html = r.text
                prof_matches = re.findall(r'"profileName"\s*:\s*"([^"]{1,35})"', html)
                if not prof_matches:
                    prof_matches = re.findall(r'"name"\s*:\s*"([^"]{1,30})"\s*,\s*"avatarId"', html)
                for p in prof_matches:
                    if p and p not in details["profiles"] and p.lower() not in ("add", "kids"):
                        details["profiles"].append(p)

                plan_m = re.search(r'"(?:planTitle|subscriptionTitle|packName)"\s*:\s*"([^"]{3,45})"', html)
                if plan_m:
                    details["plan"] = plan_m.group(1)

                exp_m = re.search(
                    r'(?:Valid till|Renews on|Expires on|Validity)\s*[:\-]?\s*([0-9]{1,2}\s+[A-Za-z]{3,9}\s+[0-9]{4})',
                    html,
                    re.I,
                )
                if exp_m:
                    details["expiry"] = exp_m.group(1)

                dev_matches = re.findall(r'"(?:deviceName|deviceModel|platformName)"\s*:\s*"([^"]{2,40})"', html)
                for dv in dev_matches:
                    if dv and dv not in details["devices"]:
                        details["devices"].append(dv)
        except Exception:
            pass

    details["profile_count"] = len(details["profiles"])
    if details["profiles"] and details["account_name"] == fallback_name:
        details["account_name"] = details["profiles"][0]
    return details


def normalize_tv_target(raw_input: str):
    s = (raw_input or "").strip()
    if not s:
        return None, None
    if "hotstar.com" in s.lower() and s.lower().startswith("http"):
        m = re.search(r"(?:qr_code|code)=([A-Za-z0-9\-_]+)", s, re.I)
        code_id = m.group(1) if m else s.rstrip("/").split("/")[-1]
        return s, code_id

    clean_code = re.sub(r"[^A-Za-z0-9]", "", s).upper()
    if 4 <= len(clean_code) <= 12:
        return f"https://www.hotstar.com/qr?qr_code={clean_code}", clean_code
    return None, None


def activate_hotstar_tv(qr_url: str, cookie_filepath: str) -> dict:
    try:
        with open(cookie_filepath, "r", encoding="utf-8", errors="ignore") as f:
            raw_text = f.read()
    except Exception as e:
        return {"success": False, "dead": True, "error": f"Read error: {e}"}

    _, cookie_str, session_token, user_up_token, _ = parse_cookie_content(raw_text)
    if not cookie_str:
        return {"success": False, "dead": True, "error": "Invalid/empty cookie file"}

    token = session_token or user_up_token or ""
    if token and "userUP=" not in cookie_str:
        cookie_str += f"; userUP={token}"

    headers = {**HOTSTAR_HEADERS, "cookie": cookie_str}
    scraper = cloudscraper.create_scraper()

    try:
        # 1. Original TV activation GET request FIRST
        resp = scraper.get(qr_url, headers=headers, timeout=30)
        final_url = (resp.url or "").lower()
        body_low = (resp.text or "").lower()

        if resp.status_code in (401, 403) or "/login" in final_url:
            return {"success": False, "dead": True, "error": f"Cookie expired (HTTP {resp.status_code})"}

        if resp.status_code == 200:
            if any(bad in body_low for bad in ("invalid code", "expired code", "invalid qr", "code has expired")):
                return {"success": False, "dead": False, "invalid_code": True, "error": "Invalid or expired TV code"}

            tv_dev_m = re.search(r'"(?:tvDeviceName|targetDevice|deviceName)"\s*:\s*"([^"]{2,40})"', resp.text or "")
            tv_device = tv_dev_m.group(1) if tv_dev_m else "Smart TV"

            fallback_name = os.path.basename(cookie_filepath).replace(".txt", "").replace(".json", "")
            try:
                acc_details = fetch_hotstar_account_details(scraper, headers, token, fallback_name)
            except Exception:
                acc_details = {
                    "account_name": fallback_name,
                    "plan": "JioHotstar",
                    "expiry": "N/A",
                    "profiles": [],
                    "profile_count": 0,
                    "devices": [],
                }

            return {
                "success": True,
                "tv_device": tv_device,
                "details": acc_details,
            }

        return {"success": False, "dead": False, "error": f"Failed with status: {resp.status_code}"}
    except Exception as e:
        return {"success": False, "dead": False, "error": str(e)[:100]}


# ==========================================
# CORE ACTIVATION ORCHESTRATOR
# ==========================================
async def process_activation_request(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    qr_url: str,
    code_id: str,
    input_mode: str,
    status_msg,
):
    user = update.effective_user
    uid = user.id
    username_display = f"@{user.username}" if user.username else f"ID:{uid}"
    user_fullname = user.full_name or user.first_name or "User"

    candidates = get_available_cookies()
    if not candidates:
        await status_msg.edit_text(
            "😔 <b>No Working Cookies in Vault!</b>\n\nAll cookies are exhausted or missing. Ask admin to upload more.",
            parse_mode=ParseMode.HTML,
        )
        update_stats(success=False)
        return

    await status_msg.edit_text(
        f"🔍 <b>Activating JioHotstar TV...</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔑 Mode: <b>{esc(input_mode)}</b> (<code>{esc(code_id)}</code>)\n"
        f"🍪 Checking vault for an active account...",
        parse_mode=ParseMode.HTML,
    )

    for filepath in candidates[:8]:
        filename = os.path.basename(filepath)
        res = await asyncio.to_thread(activate_hotstar_tv, qr_url, filepath)

        if res.get("invalid_code"):
            update_stats(success=False)
            await status_msg.edit_text(
                f"❌ <b>Invalid or Expired TV Code / QR</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━\n"
                f"🆔 Code: <code>{esc(code_id)}</code>\n"
                f"<i>Please refresh the QR/Code on your TV screen and try again.</i>",
                parse_mode=ParseMode.HTML,
            )
            return

        if res.get("dead"):
            delete_cookie_file(filepath)
            continue

        if res.get("success"):
            new_usage = increment_cookie_usage(filename)
            if new_usage >= MAX_USES_PER_COOKIE:
                delete_cookie_file(filepath)

            inc_user_quota(uid)
            _, rem_quota = check_user_quota(uid)
            update_stats(success=True)

            details = res.get("details") or {}
            profiles_list = details.get("profiles") or []
            profiles_str = ", ".join(profiles_list) if profiles_list else "Default Profile"
            devices_list = details.get("devices") or []
            devices_str = ", ".join(devices_list[:4]) if devices_list else res.get("tv_device", "Smart TV")

            append_activation_log({
                "time": datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S IST"),
                "tg_user": f"{user_fullname} ({username_display})",
                "tg_id": uid,
                "cookie_file": filename,
                "account_name": details.get("account_name", "N/A"),
                "plan": details.get("plan", "JioHotstar"),
                "profiles": profiles_str,
                "device": devices_str,
                "code": code_id,
            })

            quota_line = f"\n💫 <b>Remaining Today:</b> <code>{rem_quota}/{DAILY_USER_LIMIT}</code>" if not is_admin(uid) else ""

            result_html = (
                f"✅ <b>JIOHOTSTAR TV ACTIVATED!</b> 🎉\n"
                f"━━━━━━━━━━━━━━━━━━━━━\n"
                f"📺 <b>TV Code / QR:</b> <code>{esc(code_id)}</code>\n"
                f"🖥️ <b>Logged-in Device:</b> <b>{esc(devices_str)}</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━\n"
                f"👤 <b>Account Name:</b> <code>{esc(details.get('account_name', 'N/A'))}</code>\n"
                f"📦 <b>Plan:</b> <b>{esc(details.get('plan', 'JioHotstar'))}</b>\n"
                f"📅 <b>Expiry:</b> <code>{esc(details.get('expiry', 'N/A'))}</code>\n"
                f"👥 <b>Profiles ({details.get('profile_count', len(profiles_list))}):</b> <code>{esc(profiles_str)}</code>\n"
                f"🍪 <b>Cookie Usage:</b> <code>{new_usage}/{MAX_USES_PER_COOKIE}</code>\n"
                f"━━━━━━━━━━━━━━━━━━━━━\n"
                f"🙋‍♂️ <b>Activated By:</b> {esc(user_fullname)} (<code>{esc(username_display)}</code>){quota_line}\n"
                f"━━━━━━━━━━━━━━━━━━━━━\n"
                f"🍿 <i>Your TV is now ready to stream JioHotstar!</i>"
            )
            await status_msg.edit_text(result_html, parse_mode=ParseMode.HTML)
            return

    update_stats(success=False)
    await status_msg.edit_text(
        "❌ <b>Activation Failed</b>\n\nNo working cookies succeeded. Please try again later.",
        parse_mode=ParseMode.HTML,
    )


# ==========================================
# TELEGRAM COMMAND HANDLERS
# ==========================================
async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cstats = get_cookie_stats()
    await update.message.reply_text(
        f"📺 <b>JioHotstar TV Activator Bot</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔹 <b>How to Activate TV (2 Ways):</b>\n"
        f"1️⃣ Send TV screen <b>QR Photo</b> directly\n"
        f"2️⃣ Send <code>/tv ABCD12</code> (TV Code)\n\n"
        f"📂 <b>Vault Status:</b>\n"
        f"• Total Cookies: <code>{cstats['total']}</code>\n"
        f"• Available: <code>{cstats['available']}</code> 🟢\n\n"
        f"👑 <b>Admin Commands:</b>\n"
        f"• <code>/upload</code> (reply to .zip/.txt/.json)\n"
        f"• <code>/stats</code> • <code>/logs</code> • <code>/clearall</code>",
        parse_mode=ParseMode.HTML,
    )


async def tv_or_activate_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    allowed, _ = check_user_quota(uid)
    if not allowed:
        await update.message.reply_text(
            f"⚠️ <b>Daily Limit Reached!</b>\nYou have used all <code>{DAILY_USER_LIMIT}</code> activations today.",
            parse_mode=ParseMode.HTML,
        )
        return

    args = context.args or []
    if not args:
        context.user_data["waiting_for_tv"] = True
        await update.message.reply_text(
            "📺 <b>Activate JioHotstar TV</b>\n\n"
            "📸 Send a <b>photo of your TV QR code</b> OR type your <b>TV code</b> (e.g. <code>ABCD12</code>):",
            parse_mode=ParseMode.HTML,
        )
        return

    qr_url, code_id = normalize_tv_target(args[0])
    if not qr_url:
        await update.message.reply_text(
            "❌ Invalid TV code! Example: <code>/tv ABCD12</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    status_msg = await update.message.reply_text(
        "⏳ <b>Processing TV Code...</b>",
        parse_mode=ParseMode.HTML,
        reply_to_message_id=update.message.message_id,
    )
    await process_activation_request(update, context, qr_url, code_id, "TV Code", status_msg)


async def handle_photo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    is_waiting = context.user_data.get("waiting_for_tv", False)
    is_private = update.effective_chat.type == "private"
    if not is_waiting and not is_private:
        return

    allowed, _ = check_user_quota(uid)
    if not allowed:
        await update.message.reply_text(
            f"⚠️ <b>Daily Limit Reached!</b>\nYou have used all <code>{DAILY_USER_LIMIT}</code> activations today.",
            parse_mode=ParseMode.HTML,
        )
        return

    context.user_data["waiting_for_tv"] = False
    status_msg = await update.message.reply_text(
        "🔍 <b>Scanning QR Code Image...</b>",
        parse_mode=ParseMode.HTML,
        reply_to_message_id=update.message.message_id,
    )

    try:
        photo_file = await update.message.photo[-1].get_file()
        image_bytes = bytes(await photo_file.download_as_bytearray())
        qr_data = await asyncio.to_thread(scan_qr, image_bytes)

        if not qr_data:
            update_stats(success=False)
            await status_msg.edit_text(
                "❌ <b>No QR Code Found</b>\n\nSend a clearer close-up photo of the QR code or use <code>/tv CODE</code>.",
                parse_mode=ParseMode.HTML,
            )
            return

        qr_url, code_id = normalize_tv_target(qr_data)
        if not qr_url:
            update_stats(success=False)
            await status_msg.edit_text(
                "❌ <b>Invalid QR Code</b>\n\nThis is not a valid JioHotstar TV QR code.",
                parse_mode=ParseMode.HTML,
            )
            return

        await process_activation_request(update, context, qr_url, code_id, "QR Scan", status_msg)
    except Exception as e:
        await status_msg.edit_text(f"❌ <b>Error:</b> <code>{esc(str(e)[:120])}</code>", parse_mode=ParseMode.HTML)


async def handle_text_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.user_data.get("waiting_for_tv"):
        return
    context.user_data["waiting_for_tv"] = False
    qr_url, code_id = normalize_tv_target(update.message.text or "")
    if not qr_url:
        await update.message.reply_text(
            "❌ Invalid TV code! Send a valid code like <code>ABCD12</code> or a QR photo.",
            parse_mode=ParseMode.HTML,
        )
        return

    status_msg = await update.message.reply_text(
        "⏳ <b>Processing TV Code...</b>",
        parse_mode=ParseMode.HTML,
        reply_to_message_id=update.message.message_id,
    )
    await process_activation_request(update, context, qr_url, code_id, "TV Code", status_msg)


async def upload_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("🚫 <b>Admin only!</b>", parse_mode=ParseMode.HTML)
        return

    doc = update.message.document or (update.message.reply_to_message.document if update.message.reply_to_message else None)
    if not doc:
        await update.message.reply_text(
            "📎 <b>Usage:</b> Reply to a <code>.zip</code>, <code>.txt</code>, or <code>.json</code> cookie file with <code>/upload</code>.",
            parse_mode=ParseMode.HTML,
        )
        return

    await _save_uploaded_cookies(update, context, doc)


async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    doc = update.message.document
    if not doc:
        return
    fname = (doc.file_name or "").lower()
    if fname.endswith((".zip", ".txt", ".json")):
        await _save_uploaded_cookies(update, context, doc)


async def _save_uploaded_cookies(update: Update, context: ContextTypes.DEFAULT_TYPE, doc):
    fname = (doc.file_name or "").lower()
    if not fname.endswith((".zip", ".txt", ".json")):
        await update.message.reply_text("❌ Only <code>.zip</code>, <code>.txt</code>, or <code>.json</code> files allowed!", parse_mode=ParseMode.HTML)
        return

    status_msg = await update.message.reply_text("📥 <b>Downloading & extracting cookies...</b>", parse_mode=ParseMode.HTML)
    os.makedirs(COOKIES_DIR, exist_ok=True)

    try:
        tg_file = await context.bot.get_file(doc.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())
        added = 0
        skipped = 0

        if fname.endswith(".zip"):
            with zipfile.ZipFile(io.BytesIO(raw_bytes), "r") as zf:
                for member in zf.namelist():
                    if member.endswith("/") or member.startswith("__MACOSX") or os.path.basename(member).startswith("."):
                        continue
                    if not member.lower().endswith((".txt", ".json")):
                        skipped += 1
                        continue
                    content = zf.read(member).decode("utf-8", errors="ignore")
                    _, cstr, _, _, _ = parse_cookie_content(content)
                    if not cstr:
                        skipped += 1
                        continue
                    base = re.sub(r'[<>:"/\\|?*]', "_", os.path.basename(member))
                    dest = os.path.join(COOKIES_DIR, base)
                    if os.path.exists(dest):
                        stem, ext = os.path.splitext(base)
                        rand_s = "".join(random.choices(string.ascii_uppercase + string.digits, k=5))
                        dest = os.path.join(COOKIES_DIR, f"{stem}_{rand_s}{ext}")
                    with open(dest, "w", encoding="utf-8") as out_f:
                        out_f.write(content)
                    added += 1
        else:
            content = raw_bytes.decode("utf-8", errors="ignore")
            _, cstr, _, _, _ = parse_cookie_content(content)
            if not cstr:
                await status_msg.edit_text("❌ Invalid cookie format!", parse_mode=ParseMode.HTML)
                return
            base = re.sub(r'[<>:"/\\|?*]', "_", os.path.basename(doc.file_name or "cookie.txt"))
            dest = os.path.join(COOKIES_DIR, base)
            if os.path.exists(dest):
                stem, ext = os.path.splitext(base)
                rand_s = "".join(random.choices(string.ascii_uppercase + string.digits, k=5))
                dest = os.path.join(COOKIES_DIR, f"{stem}_{rand_s}{ext}")
            with open(dest, "w", encoding="utf-8") as out_f:
                out_f.write(content)
            added = 1

        cstats = get_cookie_stats()
        await status_msg.edit_text(
            f"✅ <b>Upload Complete!</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━\n"
            f"📥 Added: <code>{added}</code>\n"
            f"⏭️ Skipped: <code>{skipped}</code>\n"
            f"📂 Available in Vault: <code>{cstats['available']}</code>",
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        await status_msg.edit_text(f"❌ <b>Upload Error:</b> <code>{esc(str(e)[:120])}</code>", parse_mode=ParseMode.HTML)


async def stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("🚫 <b>Admin only!</b>", parse_mode=ParseMode.HTML)
        return

    st = load_stats()
    cs = get_cookie_stats()
    await update.message.reply_text(
        f"📊 <b>JioHotstar Bot Statistics</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━\n"
        f"📈 <b>Activations:</b>\n"
        f"• Total: <code>{st['total_activations']}</code>\n"
        f"• Successful: <code>{st['successful_activations']}</code> ✅\n"
        f"• Failed: <code>{st['failed_activations']}</code> ❌\n\n"
        f"📁 <b>Cookie Vault:</b>\n"
        f"• Total Files: <code>{cs['total']}</code>\n"
        f"• Available: <code>{cs['available']}</code> 🟢\n"
        f"• Maxed Out: <code>{cs['used']}</code> 🔴\n\n"
        f"🕒 <b>Last Activation:</b> <code>{esc(st.get('last_activation') or 'Never')}</code>",
        parse_mode=ParseMode.HTML,
    )


async def logs_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("🚫 <b>Admin only!</b>", parse_mode=ParseMode.HTML)
        return

    logs = load_logs()
    if not logs:
        await update.message.reply_text("📜 <b>No activation logs yet.</b>", parse_mode=ParseMode.HTML)
        return

    lines = ["📜 <b>Recent TV Activations (Last 10)</b>", "━━━━━━━━━━━━━━━━━━━━━"]
    for idx, item in enumerate(reversed(logs[-10:]), 1):
        lines.append(
            f"<b>{idx}.</b> 🙋‍♂️ {esc(item.get('tg_user'))}\n"
            f"   └ 📦 {esc(item.get('plan'))} | 👥 {esc(item.get('profiles'))}\n"
            f"   └ 🖥️ {esc(item.get('device'))} | 🕒 <code>{esc(item.get('time'))}</code>"
        )
    await update.message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


async def clearall_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("🚫 <b>Admin only!</b>", parse_mode=ParseMode.HTML)
        return

    deleted = clear_all_cookies()
    await update.message.reply_text(
        f"🗑️ <b>Vault Cleared!</b>\nDeleted <code>{deleted}</code> cookie files.",
        parse_mode=ParseMode.HTML,
    )


async def _post_init(app: Application):
    try:
        await app.bot.set_my_commands([
            BotCommand("start", "Start & Vault Status"),
            BotCommand("tv", "Activate TV via Code (e.g. /tv ABCD12)"),
            BotCommand("activate", "Activate TV via QR or Code"),
            BotCommand("upload", "Upload cookie zip/txt (Admin)"),
            BotCommand("stats", "Bot statistics (Admin)"),
            BotCommand("logs", "Recent user login logs (Admin)"),
            BotCommand("clearall", "Clear all cookies (Admin)"),
        ])
    except Exception:
        pass


def main():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN environment variable is missing!")

    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(COOKIES_DIR, exist_ok=True)
    start_health_server()

    print("=" * 55)
    print("  JioHotstar TV Activator Bot (Railway + Render)")
    print("=" * 55)
    print(f"[*] Available Cookies: {get_cookie_stats()['available']}")
    print(f"[*] Admin IDs: {ADMIN_IDS}")

    app = Application.builder().token(BOT_TOKEN).post_init(_post_init).build()

    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("tv", tv_or_activate_command))
    app.add_handler(CommandHandler("activate", tv_or_activate_command))
    app.add_handler(CommandHandler("upload", upload_command))
    app.add_handler(CommandHandler("stats", stats_command))
    app.add_handler(CommandHandler("logs", logs_command))
    app.add_handler(CommandHandler("clearall", clearall_command))

    app.add_handler(MessageHandler(filters.PHOTO, handle_photo))
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_code))

    print("[*] Bot running...")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
