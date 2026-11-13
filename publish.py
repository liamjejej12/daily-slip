#!/usr/bin/env python3
"""
publish.py - keeps the cloud copy of Daily Slip private.

The project on GitHub is public, so the picks, record and learning data are only
ever stored there encrypted (AES-256-GCM, key derived from your passphrase with
PBKDF2-SHA256). The phone page asks for the passphrase once and decrypts in the
browser.

  python3 publish.py decrypt            restore the data files from docs/data.enc
  python3 publish.py encrypt            write docs/data.enc and docs/index.html
  python3 publish.py encrypt --prompt   same, asking for the passphrase (first setup)

The passphrase comes from the SLIP_PASSWORD environment variable (a GitHub secret)
unless --prompt is given.
"""

import base64
import getpass
import hashlib
import json
import os
import sys
from datetime import datetime
from pathlib import Path

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

ROOT = Path(__file__).resolve().parent
DOCS = ROOT / "docs"
BUNDLE = DOCS / "data.enc"
FILES = ["today_best_pick.json", "pick_history.json", "model.json", "alerts.json", "odds_cache.json"]
HASH_FILE = ROOT / ".data_hash"   # fingerprint of what was unlocked, to skip saving when nothing changed
ITERATIONS = 310_000


def b64(b):
    return base64.b64encode(b).decode()


def derive(password, salt):
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=ITERATIONS).derive(password.encode())


def passphrase():
    if "--prompt" in sys.argv:
        pw = getpass.getpass("Passphrase: ")
        if pw != getpass.getpass("Same passphrase again: "):
            sys.exit("The two entries didn't match. Nothing was written.")
        if len(pw) < 12:
            sys.exit("Use at least 12 characters (four random words works well).")
        return pw
    pw = os.environ.get("SLIP_PASSWORD", "")
    if not pw:
        sys.exit("SLIP_PASSWORD is not set.")
    return pw


def view(files):
    """What the page shows on the Record tab, computed once here instead of on the phone."""
    import sports_app as sa
    h = files.get("pick_history.json") or {"days": {}}
    days = [{**h["days"][k], "slip": sa.slip_result(h["days"][k]["picks"], h["days"][k].get("entry"))}
            for k in sorted(h["days"], reverse=True)]
    return {"days": days, "summary": sa.history_summary(h), "model": files.get("model.json"), "areas": sa.areas_report(h),
            "suggestions": sa.suggestions_report(h)}


def page_meta():
    """Everything the phone page needs to run the analysis itself (kept in sync with sports_app.py)."""
    import sports_app as sa
    return {
        "sports": {k: {"label": s["label"], "group": s["group"], "path": list(s["path"]), "sid": s["sid"],
                       "lid": s["lid"], "allowed": s["allowed"]} for k, s in sa.SPORT_BY_KEY.items()},
        "weights": sa.WEIGHTS, "market_weight": sa.MARKET_WEIGHT, "max_total_adj": sa.MAX_TOTAL_ADJ,
        "daily_picks": sa.DAILY_PICKS, "max_per_game": sa.MAX_PER_GAME, "min_entry_ev": sa.MIN_ENTRY_EV,
        "entry_shrink": sa.ENTRY_SHRINK, "max_power_legs": sa.MAX_POWER_LEGS, "prop_cv": sa.PROP_CV,
        "game_clock": sa.GAME_CLOCK, "box_aliases": sa.BOX_ALIASES, "scoreboard_groups": sa.SCOREBOARD_GROUPS,
        "offense_props": sorted(sa.OFFENSE_MATCHUP_PROPS), "pitcher_positions": sorted(sa.PITCHER_POSITIONS),
        "payouts": sa.PAYOUT_TABLES, "scan_times": sa.SCAN_TIMES,
        "ctx_defaults": sa.CTX_DEFAULTS, "ctx_cap": sa.CTX_CAP,
        "hist_nudge": sa.HIST_NUDGE, "more_min_p": sa.MORE_MIN_P, "min_books": sa.MIN_BOOKS,
    }


def build_page():
    """docs/index.html = the same page the Mac app serves, plus cloud.js, which stands in for the server."""
    import sports_app as sa
    config = {"budget": sa.DAILY_CREDIT_BUDGET, "min_ev": sa.MIN_ENTRY_EV, "shrink": sa.ENTRY_SHRINK, "max_power_legs": sa.MAX_POWER_LEGS,
              "leagues": [{"key": s["key"], "label": s["label"], "group": s["group"], "props": list(s["props"])}
                          for s in sa.SPORT_BY_KEY.values()]}
    page = sa.PAGE.replace("__CONFIG__", json.dumps(config))
    page = page.replace("<title>Daily Slip</title>", "<title>Daily Slip</title>\n"
                        '<link rel="apple-touch-icon" href="apple-touch-icon.png">\n'
                        '<link rel="icon" type="image/png" href="favicon.png">', 1)
    hook = "<script>\nconst CONFIG = "
    assert page.count(hook) == 1
    page = page.replace(hook, f"<script>window.CLOUD_META = {json.dumps(page_meta())};</script>\n"
                              f"<script src=\"cloud.js\"></script>\n" + hook)
    (DOCS / "index.html").write_text(page)


def fingerprint(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()


def encrypt():
    pw = passphrase()
    files = {}
    for name in FILES:
        try:
            files[name] = json.loads((ROOT / name).read_text())
        except (OSError, ValueError):
            pass
    if BUNDLE.exists() and HASH_FILE.exists() and HASH_FILE.read_text() == fingerprint(files) and "--prompt" not in sys.argv:
        build_page()                       # nothing new: keep the old bundle so there's nothing to commit
        print("No data changes; bundle left as is.")
        return
    payload = json.dumps({"files": files, "view": view(files),
                          "published": datetime.now().isoformat(timespec="minutes")}).encode()
    salt = os.urandom(16)
    try:                                   # keep the salt so phones can reuse their unlocked key
        salt = base64.b64decode(json.loads(BUNDLE.read_text())["salt"])
    except (OSError, ValueError, KeyError):
        pass
    iv = os.urandom(12)
    ct = AESGCM(derive(pw, salt)).encrypt(iv, payload, None)
    DOCS.mkdir(exist_ok=True)
    BUNDLE.write_text(json.dumps({"v": 1, "kdf": "PBKDF2-SHA256", "iter": ITERATIONS,
                                  "salt": b64(salt), "iv": b64(iv), "ct": b64(ct)}))
    build_page()
    print(f"Encrypted {len(files)} file(s) into docs/data.enc ({BUNDLE.stat().st_size // 1024} KB).")


def decrypt():
    if not BUNDLE.exists():
        print("No docs/data.enc yet; starting fresh.")
        return
    b = json.loads(BUNDLE.read_text())
    try:
        data = AESGCM(derive(passphrase(), base64.b64decode(b["salt"]))).decrypt(
            base64.b64decode(b["iv"]), base64.b64decode(b["ct"]), None)
    except Exception:
        sys.exit("Couldn't decrypt docs/data.enc: the passphrase doesn't match.")
    files = json.loads(data)["files"]
    for name, content in files.items():
        (ROOT / name).write_text(json.dumps(content))
    HASH_FILE.write_text(fingerprint(files))
    print("Restored data files from docs/data.enc.")


if __name__ == "__main__":
    os.chdir(ROOT)
    sys.path.insert(0, str(ROOT))
    {"encrypt": encrypt, "decrypt": decrypt}.get(sys.argv[1] if len(sys.argv) > 1 else "", lambda: sys.exit(__doc__))()
