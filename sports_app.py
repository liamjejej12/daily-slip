#!/usr/bin/env python3
"""
sports_app.py  -  Sports Research Station (local Flask web app)

Type a player, prop and PrizePicks line; the app pulls that player's REAL game
logs from ESPN's free public stats (no key, no cost) and builds a scouting report:

  * Recent trends   - how often they cleared this exact line in their last 5,
                      last 10 and season games, plus averages and a bar chart.
  * Matchup         - next opponent and where that team ranks in points/goals/
                      runs allowed (or scored, for pitcher/goalie props).
  * Verdict         - MORE / LESS lean from a weighted hit rate (L5 25%,
                      L10 40%, season 35%). It is a hit rate, not a win
                      probability, and it does not know about injuries,
                      minutes changes or line movement.

Daily Master Slip: once per day the app spends at most DAILY_CREDIT_BUDGET
Odds API credits pricing PrizePicks lines against DraftKings/FanDuel, picks the
5 best plays (75% de-vigged book odds + 25% ESPN hit rate), and saves them to
today_best_pick.json. Every later visit that day loads the file: 0 credits.

Run:  python3 sports_app.py                      (opens the dashboard)
      python3 sports_app.py --scan               (scan now if today isn't locked)
      python3 sports_app.py --install-schedule   (daily background scans + notification)
      python3 sports_app.py --remove-schedule
"""

import hmac
import json
import math
import secrets
import os
import plistlib
import re
import socket
import subprocess
import sys
import threading
import time
import unicodedata
import warnings
import webbrowser
from datetime import datetime, timezone, timedelta

warnings.filterwarnings("ignore", message=".*OpenSSL.*")   # harmless macOS warning

from pathlib import Path
from statistics import NormalDist, median

import requests
from dotenv import load_dotenv
from flask import Flask, Response, jsonify, request

APP_DIR = Path(__file__).resolve().parent
load_dotenv(APP_DIR / ".env")

ESPN_COMMON = "https://site.web.api.espn.com/apis/common/v3"
ESPN_SITE   = "https://site.api.espn.com/apis"
CACHE_TTL   = 600            # seconds; ESPN data is reused for 10 minutes
WEIGHTS     = {"l5": 0.25, "l10": 0.40, "season": 0.35}

HTTP = requests.Session()
HTTP.headers["User-Agent"] = "Mozilla/5.0 (Sports Research Station)"


# ───────────────────────── Prop formulas (ESPN game-log stat names) ─────────────────────────
def _num(row, key):
    return float(row[key])          # KeyError / ValueError when the stat doesn't apply


def stat(*keys):
    return lambda row: sum(_num(row, k) for k in keys)


def made(key):
    return lambda row: float(row[key].split("-")[0])


def total_bases(row):
    return _num(row, "hits") + _num(row, "doubles") + 2 * _num(row, "triples") + 3 * _num(row, "homeRuns")


def pitching_outs(row):
    whole, _, frac = row["innings"].partition(".")
    return int(whole) * 3 + int(frac or 0)


BASKETBALL = {
    "Points": stat("points"), "Rebounds": stat("totalRebounds"), "Assists": stat("assists"),
    "Pts+Rebs+Asts": stat("points", "totalRebounds", "assists"),
    "Pts+Rebs": stat("points", "totalRebounds"), "Pts+Asts": stat("points", "assists"),
    "Rebs+Asts": stat("totalRebounds", "assists"),
    "3-PT Made": made("threePointFieldGoalsMade-threePointFieldGoalsAttempted"),
    "Steals": stat("steals"), "Blocks": stat("blocks"), "Blks+Stls": stat("blocks", "steals"),
    "Turnovers": stat("turnovers"),
}
FOOTBALL = {
    "Pass Yards": stat("passingYards"), "Pass TDs": stat("passingTouchdowns"),
    "Pass Attempts": stat("passingAttempts"), "Completions": stat("completions"),
    "Interceptions": stat("interceptions"), "Rush Yards": stat("rushingYards"),
    "Rush Attempts": stat("rushingAttempts"), "Receptions": stat("receptions"),
    "Receiving Yards": stat("receivingYards"), "Rush+Rec Yards": stat("rushingYards", "receivingYards"),
}
BASEBALL = {
    "Hits": stat("hits"), "Runs": stat("runs"), "RBIs": stat("RBIs"), "Home Runs": stat("homeRuns"),
    "Total Bases": total_bases, "Hits+Runs+RBIs": stat("hits", "runs", "RBIs"), "Walks": stat("walks"),
    "Stolen Bases": stat("stolenBases"), "Strikeouts": stat("strikeouts"),
    "Pitching Outs": pitching_outs, "Earned Runs Allowed": stat("earnedRuns"), "Hits Allowed": stat("hits"),
}
HOCKEY = {
    "Points": stat("points"), "Goals": stat("goals"), "Assists": stat("assists"),
    "Shots on Goal": stat("shotsTotal"), "Goalie Saves": stat("saves"),
}
SOCCER = {
    "Goals": stat("totalGoals"), "Assists": stat("goalAssists"), "Goal+Assist": stat("totalGoals", "goalAssists"),
    "Shots": stat("totalShots"), "Shots on Target": stat("shotsOnTarget"),
}
# Props where the opponent's OFFENSE is what matters
OFFENSE_MATCHUP_PROPS = {"Pitching Outs", "Earned Runs Allowed", "Hits Allowed", "Goalie Saves"}
PITCHER_POSITIONS = {"SP", "RP", "P"}

# key, label, group, ESPN path, sport id, league id, props, what "allowed" means
SPORTS = [
    ("NBA",   "NBA",                "basketball", ("basketball", "nba"),                     "40",  "46", BASKETBALL, "points"),
    ("WNBA",  "WNBA",               "basketball", ("basketball", "wnba"),                    "40",  "59", BASKETBALL, "points"),
    ("NCAAB", "NCAAB",              "basketball", ("basketball", "mens-college-basketball"), "40",  "41", BASKETBALL, "points"),
    ("NFL",   "NFL",                "football",   ("football", "nfl"),                       "20",  "28", FOOTBALL,   "points"),
    ("NCAAF", "NCAAF",              "football",   ("football", "college-football"),          "20",  "23", FOOTBALL,   "points"),
    ("MLB",   "MLB",                "baseball",   ("baseball", "mlb"),                       "1",   "10", BASEBALL,   "runs"),
    ("NHL",   "NHL",                "hockey",     ("hockey", "nhl"),                         "70",  "90", HOCKEY,     "goals"),
    ("EPL",   "Premier League",     "soccer",     ("soccer", "eng.1"),                       "600", None, SOCCER,     "goals"),
    ("LALIGA", "La Liga",           "soccer",     ("soccer", "esp.1"),                       "600", None, SOCCER,     "goals"),
    ("UCL",   "Champions League",   "soccer",     ("soccer", "uefa.champions"),              "600", None, SOCCER,     "goals"),
    ("MLS",   "MLS",                "soccer",     ("soccer", "usa.1"),                       "600", None, SOCCER,     "goals"),
]
SPORT_BY_KEY = {
    s[0]: {"key": s[0], "label": s[1], "group": s[2], "path": s[3], "sid": s[4], "lid": s[5],
           "props": s[6], "allowed": s[7]}
    for s in SPORTS
}


# ───────────────────────── ESPN data layer (cached) ─────────────────────────
_cache = {}


def get_json(url, _ttl=CACHE_TTL, **params):
    key = url + json.dumps(params, sort_keys=True)
    hit = _cache.get(key)
    if hit and time.time() - hit[0] < _ttl:
        return hit[1]
    r = HTTP.get(url, params=params, timeout=12)
    r.raise_for_status()
    data = r.json()
    _cache[key] = (time.time(), data)
    return data


def normalize(name):
    name = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode()
    name = name.lower().replace(".", "").replace("'", "").replace("-", " ")
    return " ".join(p for p in name.split() if p not in ("jr", "sr", "ii", "iii", "iv"))


def search_players(sport, query, limit=6):
    items = get_json(f"{ESPN_COMMON}/search", query=query, limit=15, type="player").get("items", [])
    same_sport = [i for i in items if f"s:{sport['sid']}~" in i.get("uid", "") + "~"]
    if sport["lid"]:
        same_league = [i for i in same_sport if f"l:{sport['lid']}~" in i.get("uid", "")]
        same_sport = same_league + [i for i in same_sport if i not in same_league]
    target = normalize(query)
    same_sport.sort(key=lambda i: normalize(i.get("displayName", "")) != target)
    return [{"id": i["id"], "name": i.get("displayName", ""), "sub": i.get("subtitle", "") or i.get("description", "")}
            for i in same_sport[:limit]]


def game_log(sport, pid, season=None):
    s, l = sport["path"]
    params = {"season": season} if season else {}
    d = get_json(f"{ESPN_COMMON}/sports/{s}/{l}/athletes/{pid}/gamelog", **params)
    names, meta = d.get("names", []), d.get("events", {})
    games, seen = [], set()
    for st in d.get("seasonTypes", []):
        if re.search(r"\bpre-?\s?season\b", st.get("displayName", ""), re.I):
            continue
        for cat in st.get("categories", []):
            for ev in cat.get("events", []):
                eid = ev.get("eventId")
                if eid in seen:
                    continue
                seen.add(eid)
                m = meta.get(eid, {})
                opp = m.get("opponent", {}) or {}
                games.append({"date": m.get("gameDate", ""), "opp_id": str(opp.get("id", "")),
                              "opp": opp.get("abbreviation", ""), "at_vs": m.get("atVs", ""),
                              "row": dict(zip(names, ev.get("stats", [])))})
    games.sort(key=lambda g: g["date"], reverse=True)
    seasons = next((
        [str(o.get("value")) for o in f.get("options", [])]
        for f in d.get("filters", []) if f.get("name") == "season"), [])
    return games, seasons


def player_profile(sport, pid):
    s, l = sport["path"]
    try:
        a = get_json(f"{ESPN_COMMON}/sports/{s}/{l}/athletes/{pid}").get("athlete", {})
    except requests.RequestException:
        return {}
    team = a.get("team", {}) or {}
    return {"name": a.get("displayName", ""), "team_id": str(team.get("id", "")),
            "team": team.get("displayName", ""), "headshot": (a.get("headshot") or {}).get("href", ""),
            "position": (a.get("position") or {}).get("abbreviation", "")}


def parse_date(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def next_game(sport, team_id):
    if not team_id:
        return None
    s, l = sport["path"]
    # Most leagues list upcoming games in the schedule; soccer keeps them under fixture=true
    for params in ({}, {"fixture": "true"}):
        try:
            sch = get_json(f"{ESPN_SITE}/site/v2/sports/{s}/{l}/teams/{team_id}/schedule", **params)
        except requests.RequestException:
            continue
        found = _first_upcoming(sch, team_id)
        if found:
            return found
    return None


def _first_upcoming(sch, team_id):
    cutoff = datetime.now(timezone.utc) - timedelta(hours=4)
    for e in sorted(sch.get("events", []), key=lambda e: e.get("date", "")):
        try:
            if parse_date(e["date"]) < cutoff:
                continue
            comp = e["competitions"][0]
            if comp.get("status", {}).get("type", {}).get("completed"):
                continue
            opp = next(c for c in comp["competitors"] if str(c["team"]["id"]) != team_id)
            me = next(c for c in comp["competitors"] if str(c["team"]["id"]) == team_id)
        except (KeyError, IndexError, StopIteration, ValueError):
            continue
        return {"date": e["date"], "opp_id": str(opp["team"]["id"]),
                "opp": opp["team"].get("displayName", ""), "opp_abbr": opp["team"].get("abbreviation", ""),
                "home": me.get("homeAway") == "home"}
    return None


def team_table(sport):
    """{team_id: (allowed_per_game, scored_per_game)} from league standings."""
    s, l = sport["path"]
    st = get_json(f"{ESPN_SITE}/v2/sports/{s}/{l}/standings")

    def entries(node):
        out = list((node.get("standings") or {}).get("entries", []))
        for child in node.get("children", []):
            out += entries(child)
        return out

    table = {}
    for e in entries(st):
        stats = {}
        for x in e.get("stats", []):
            stats.setdefault(x.get("name"), x.get("value"))
        gp = stats.get("gamesPlayed") or sum(stats.get(k) or 0 for k in ("wins", "losses", "ties", "overtimeLosses", "otLosses"))
        allowed = stats.get("avgPointsAgainst") or ((stats.get("pointsAgainst") or 0) / gp if gp else None)
        scored = stats.get("avgPointsFor") or ((stats.get("pointsFor") or 0) / gp if gp else None)
        if allowed and scored and gp:
            table[str(e.get("team", {}).get("id", ""))] = (allowed, scored)
    return table


def matchup_rating(sport, opp_id, use_offense):
    try:
        table = team_table(sport)
    except (requests.RequestException, ValueError):
        return None
    if opp_id not in table:
        return None
    n = len(table)
    if use_offense:     # most runs/goals scored = toughest for a pitcher/goalie
        order = sorted(table, key=lambda t: -table[t][1])
        value, what = table[opp_id][1], f"{sport['allowed']} scored"
    else:               # fewest points allowed = toughest defense
        order = sorted(table, key=lambda t: table[t][0])
        value, what = table[opp_id][0], f"{sport['allowed']} allowed"
    rank = order.index(opp_id) + 1
    tier = "Tough" if rank <= n / 3 else "Soft" if rank > 2 * n / 3 else "Average"
    return {"tier": tier, "rank": rank, "of": n, "per_game": round(value, 1), "what": what,
            "basis": "offense" if use_offense else "defense"}


# ───────────────────────── Analysis ─────────────────────────
def window(values, line):
    n = len(values)
    over = sum(v > line for v in values)
    under = sum(v < line for v in values)
    return {"n": n, "over": over, "under": under, "push": n - over - under,
            "avg": round(sum(values) / n, 1) if n else None,
            "rate": over / (over + under) if over + under else None}


def analyze(sport_key, player_query, prop, line, player_id=None):
    sport = SPORT_BY_KEY[sport_key]
    if prop not in sport["props"]:
        raise ValueError(f"{prop} isn't a supported {sport['label']} prop.")
    calc = sport["props"][prop]

    if not player_id:
        matches = search_players(sport, player_query, limit=1)
        if not matches:
            raise ValueError(f"No {sport['label']} player found for \"{player_query}\".")
        player_id = matches[0]["id"]

    profile = player_profile(sport, player_id)
    games, seasons = game_log(sport, player_id)
    this_season = games
    notes = []
    older = []
    if len(this_season) < 10 and len(seasons) > 1:
        try:
            older, _ = game_log(sport, player_id, season=seasons[1])
        except requests.RequestException:
            older = []
        if older:
            notes.append("Fewer than 10 games this season, so last season's most recent games fill out the L5/L10 windows.")

    def values_of(gs):
        out = []
        for g in gs:
            try:
                out.append((g, calc(g["row"])))
            except (KeyError, ValueError, TypeError):
                pass
        return out

    season_pts = values_of(this_season)
    all_pts = season_pts + values_of(older)
    if not all_pts:
        raise ValueError(f"No {prop} stats in {profile.get('name') or player_query}'s game log. "
                         f"Check the prop fits their position and the sport is right.")

    vals = [v for _, v in all_pts]
    recent = {
        "l5": window(vals[:5], line),
        "l10": window(vals[:10], line),
        "season": window([v for _, v in season_pts], line) if season_pts else window(vals, line),
    }
    if not season_pts:
        notes.append("No games yet this season; 'Season' shows last season.")
    elif len(season_pts) < 5:
        notes.append(f"Only {len(season_pts)} game(s) this season, so treat the season numbers as a small sample.")

    # Next game, matchup and history vs that opponent
    nxt = next_game(sport, profile.get("team_id"))
    match = None
    if nxt:
        use_offense = prop in OFFENSE_MATCHUP_PROPS or (
            prop == "Strikeouts" and profile.get("position") in PITCHER_POSITIONS)
        match = matchup_rating(sport, nxt["opp_id"], use_offense)
        vs = [v for g, v in all_pts if g["opp_id"] == nxt["opp_id"]]
        recent["vs_opp"] = window(vs, line) if vs else None
        recent["vs_opp_abbr"] = nxt["opp_abbr"]

    # Verdict: weighted hit rate across windows that have decided games
    parts = [(WEIGHTS[k], recent[k]["rate"]) for k in WEIGHTS if recent[k]["rate"] is not None]
    if not parts:
        raise ValueError("Every recent game landed exactly on this line, so there's no lean to measure.")
    over_rate = sum(w * r for w, r in parts) / sum(w for w, _ in parts)
    side = "MORE" if over_rate >= 0.5 else "LESS"
    score = max(over_rate, 1 - over_rate)
    label = "Strong lean" if score >= 0.60 else "Lean" if score >= 0.55 else "Toss-up"

    def hits(w):
        return w["over"] if side == "MORE" else w["under"]

    reasons = []
    l10, ssn = recent["l10"], recent["season"]
    reasons.append(f"Went {side.lower()} {line:g} in {hits(l10)} of last {l10['n']} (avg {l10['avg']}).")
    if ssn["n"]:
        diff = ssn["avg"] - line
        reasons.append(f"Season average {ssn['avg']} ({'+' if diff >= 0 else ''}{diff:.1f} vs the line) over {ssn['n']} games.")
    if nxt and match:
        reasons.append(f"Next: {'vs' if nxt['home'] else '@'} {nxt['opp_abbr']}, a {match['tier'].lower()} matchup "
                       f"(#{match['rank']} of {match['of']} in {match['what']}, {match['per_game']}/game).")
    elif nxt:
        reasons.append(f"Next: {'vs' if nxt['home'] else '@'} {nxt['opp_abbr']} (no standings data for a matchup rating).")
    else:
        reasons.append("No upcoming game found on the schedule.")
    if recent.get("vs_opp"):
        vo = recent["vs_opp"]
        reasons.append(f"Vs {recent['vs_opp_abbr']} in fetched games: {side.lower()} {hits(vo)} of {vo['n']} (avg {vo['avg']}).")

    chart = [{"date": g["date"][:10], "opp": g["opp"], "at_vs": g["at_vs"], "value": v} for g, v in all_pts[:10]][::-1]

    return {
        "sport": sport_key, "sport_label": sport["label"], "group": sport["group"],
        "player": {"id": player_id, "name": profile.get("name") or player_query, "team": profile.get("team", ""),
                   "position": profile.get("position", ""), "headshot": profile.get("headshot", "")},
        "prop": prop, "line": line, "recent": recent, "chart": chart,
        "next_game": nxt, "matchup": match,
        "verdict": {"side": side, "score": round(score * 100), "label": label, "reasons": reasons},
        "notes": notes,
    }


# ───────────────────────── Daily master scan (The Odds API, once per day) ─────────────────────────
ODDS_API_KEY        = os.getenv("ODDS_API_KEY", "")
ODDS_URL            = "https://api.the-odds-api.com/v4"
DAILY_FILE          = APP_DIR / "today_best_pick.json"
DAILY_CREDIT_BUDGET = 15     # hard cap per daily scan (476 credits ≈ a month of scans)
SLATE_HOURS         = 30     # games starting within this window count as today's slate
DAILY_PICKS         = 6      # picks shown; the suggested entry uses the best 2 to 6 of them
MIN_ENTRY_EV        = 0.02   # sit the day out unless the best entry is estimated at +2% or better
ENTRY_SHRINK        = 0.70   # entry choice trims each estimate 30% toward 50/50 to allow for model error
MAX_POWER_LEGS      = 3      # 4- to 6-pick Power pays big but almost never hits; Flex covers those sizes
BOARD_ANALYZE_CAP   = 60     # lines per scan that get the ESPN check (all are graded later, for learning)
MAX_PER_GAME        = 2
MAX_SCAN_CALLS      = 80     # cap on odds calls per scan (empty markets are free but still take time)
SCAN_TIMES          = [(11, 0), (15, 0)]   # background scans; 3 PM only runs if 11 AM found too little
SCHEDULE_LABEL      = "com.prizepicks.dailyscan"
SCHEDULE_PLIST      = Path.home() / "Library" / "LaunchAgents" / f"{SCHEDULE_LABEL}.plist"
MARKET_WEIGHT       = 0.75   # de-vigged sportsbook odds lead...
HISTORY_WEIGHT      = 0.25   # ...ESPN hit rate adjusts
# Up to 10 bookmakers per request cost the same as one, so price against 9 books + PrizePicks.
REF_BOOKS           = ["pinnacle", "draftkings", "fanduel", "betmgm", "williamhill_us", "espnbet",
                       "betrivers", "fanatics", "bovada"]
FALLBACK_BOOKS      = ["draftkings", "fanduel"]   # used if the 10-book request ever costs extra
BOOK_WEIGHT         = {"pinnacle": 2.0}           # the sharpest book counts double
MAX_LINE_GAP        = (1.0, 0.12)                 # price a different book line up to max(1.0, 12% of the line) away
# Spread of each stat relative to its line, for pricing a PrizePicks line that differs from the books'
PROP_CV             = {"Points": 0.30, "Pts+Rebs+Asts": 0.25, "Pts+Rebs": 0.28, "Pts+Asts": 0.28,
                       "Pass Yards": 0.25, "Rush Yards": 0.45, "Receiving Yards": 0.50, "Rush+Rec Yards": 0.40,
                       "Pass Attempts": 0.18, "Completions": 0.20, "Pitching Outs": 0.20}
SAFE_INJURY_STATUS  = {"active", "probable"}
PP_BOOK             = "prizepicks"
BOOK_ABBR           = {"pinnacle": "PIN", "draftkings": "DK", "fanduel": "FD", "betmgm": "MGM",
                       "williamhill_us": "CZR", "espnbet": "ESPN", "betrivers": "BR", "fanatics": "FAN", "bovada": "BOV"}

BASKETBALL_MARKETS = [("player_points", "Points"), ("player_rebounds", "Rebounds"), ("player_assists", "Assists")]
FOOTBALL_MARKETS = [("player_pass_yds", "Pass Yards"), ("player_reception_yds", "Receiving Yards"),
                    ("player_rush_yds", "Rush Yards"), ("player_receptions", "Receptions")]
SOCCER_MARKETS = [("player_shots_on_target", "Shots on Target"), ("player_shots", "Shots")]
# Priority order: when the budget runs short, earlier sports get scanned first.
# Each game's first market is bought before any game's second market.
ODDS_SPORTS = [
    ("basketball_nba",            "NBA",    BASKETBALL_MARKETS),
    ("americanfootball_nfl",      "NFL",    FOOTBALL_MARKETS),
    ("basketball_ncaab",          "NCAAB",  BASKETBALL_MARKETS),
    ("americanfootball_ncaaf",    "NCAAF",  FOOTBALL_MARKETS),
    ("icehockey_nhl",             "NHL",    [("player_shots_on_goal", "Shots on Goal"), ("player_points", "Points")]),
    ("soccer_epl",                "EPL",    SOCCER_MARKETS),
    ("soccer_spain_la_liga",      "LALIGA", SOCCER_MARKETS),
    ("soccer_uefa_champs_league", "UCL",    SOCCER_MARKETS),
    ("soccer_usa_mls",            "MLS",    SOCCER_MARKETS),
    ("basketball_wnba",           "WNBA",   BASKETBALL_MARKETS),
    ("baseball_mlb",              "MLB",    [("pitcher_strikeouts", "Strikeouts"), ("batter_total_bases", "Total Bases"), ("batter_hits", "Hits")]),
]

_quota = {"remaining": None}
SCAN_LOCK = threading.Lock()


class ScanError(Exception):
    pass


def odds_get(path, **params):
    params["apiKey"] = ODDS_API_KEY
    r = HTTP.get(f"{ODDS_URL}{path}", params=params, timeout=20)
    if r.status_code == 401:
        raise ScanError("Your ODDS_API_KEY was rejected. Check the key in your .env file.")
    if r.status_code == 429:
        raise ScanError("Out of Odds API credits (or rate-limited). Try again later.")
    if r.status_code in (404, 422):
        return None
    r.raise_for_status()
    if r.headers.get("x-requests-remaining") is not None:
        _quota["remaining"] = int(float(r.headers["x-requests-remaining"]))
    return r.json()


def implied_prob(american):
    american = float(american)
    return -american / (-american + 100) if american < 0 else 100 / (american + 100)


def fair_over(over_odds, under_odds):
    p_over, p_under = implied_prob(over_odds), implied_prob(under_odds)
    return p_over / (p_over + p_under)          # strip the juice


def poisson_sf(k, lam):
    """P(X > k) for a Poisson count."""
    term = total = math.exp(-lam)
    for i in range(1, int(k) + 1):
        term *= lam / i
        total += term
    return max(0.0, 1.0 - total)


def prob_over(target, book_line, p_over, prop):
    """Chance of going over `target` given a book's fair over-chance at `book_line`."""
    if target == book_line:
        return p_over
    p_over = min(max(p_over, 0.02), 0.98)
    if max(target, book_line) < 10:                       # small counts: Poisson
        lo, hi = 1e-3, book_line * 3 + 10
        for _ in range(60):
            mid = (lo + hi) / 2
            if poisson_sf(math.floor(book_line), mid) < p_over:
                lo = mid
            else:
                hi = mid
        return poisson_sf(math.floor(target), (lo + hi) / 2)
    sigma = PROP_CV.get(prop, 0.35) * book_line            # bigger numbers: normal
    mu = book_line - sigma * NormalDist().inv_cdf(1 - p_over)
    return 1 - NormalDist(mu, sigma).cdf(target)


def lines_from_event(data, sport, prop_names):
    """Price every PrizePicks line against a weighted consensus of the books.
    Books hanging a different number (PrizePicks slow to move) are converted to the PrizePicks line."""
    game = f"{data.get('away_team', '?')} @ {data.get('home_team', '?')}"
    pp, quotes = {}, {}
    for bm in data.get("bookmakers", []):
        for mk in bm.get("markets", []):
            prop = prop_names.get(mk.get("key"))
            if not prop:
                continue
            for o in mk.get("outcomes", []):
                player, side, point = o.get("description"), o.get("name"), o.get("point")
                if not player or point is None or side not in ("Over", "Under"):
                    continue
                key = (player, prop)
                if bm["key"] == PP_BOOK:
                    pp.setdefault(key, set()).add(float(point))
                elif o.get("price") is not None:
                    quotes.setdefault(key, {}).setdefault(bm["key"], {}).setdefault(float(point), {})[side] = o["price"]

    if pp:   # one standard PrizePicks line per player/prop; several usually means goblin/demon lines, so skip
        targets = [(k, next(iter(ls))) for k, ls in pp.items() if len(ls) == 1]
    else:    # no PrizePicks feed: fall back to the books' most common line
        targets = [(k, median(sorted(l for b in books.values() for l in b))) for k, books in quotes.items()]

    out = []
    for key, target in targets:
        num = den = 0.0
        used = []
        for book, by_line in quotes.get(key, {}).items():
            two_sided = [l for l, q in by_line.items() if "Over" in q and "Under" in q]
            if not two_sided:
                continue
            line = min(two_sided, key=lambda l: abs(l - target))
            if abs(line - target) > max(MAX_LINE_GAP[0], MAX_LINE_GAP[1] * target):
                continue
            q = by_line[line]
            w = BOOK_WEIGHT.get(book, 1.0)
            num += w * prob_over(target, line, fair_over(q["Over"], q["Under"]), key[1])
            den += w
            used.append((book, line, q))
        if not den:
            continue
        p_over = num / den
        book_line = median(l for _, l, _ in used)
        used.sort(key=lambda u: -BOOK_WEIGHT.get(u[0], 1.0))
        shown = ", ".join(f"{BOOK_ABBR.get(b, b[:3].upper())} {l:g} O{int(round(float(q['Over']))):+d}/U{int(round(float(q['Under']))):+d}"
                          for b, l, q in used[:3])
        out.append({"sport": sport, "player": key[0], "prop": key[1], "line": target, "game": game,
                    "commence": data.get("commence_time"), "side": "MORE" if p_over >= 0.5 else "LESS",
                    "market_p": max(p_over, 1 - p_over), "n_books": len(used),
                    "books": shown + (f" +{len(used) - 3} more" if len(used) > 3 else ""),
                    "book_line": book_line, "line_gap": round(book_line - target, 1), "on_pp": key in pp})
    return out, bool(pp)


def injury_statuses(sport_key):
    """{espn_athlete_id: status} for one league from ESPN's injury report (free)."""
    s, l = SPORT_BY_KEY[sport_key]["path"]
    try:
        data = get_json(f"{ESPN_SITE}/site/v2/sports/{s}/{l}/injuries")
    except (requests.RequestException, ValueError):
        return {}
    out = {}
    for team in data.get("injuries", []):
        for i in team.get("injuries", []):
            a = i.get("athlete") or {}
            for link in a.get("links") or []:
                m = re.search(r"/id/(\d+)", link.get("href", ""))
                if m:
                    out[m.group(1)] = i.get("status", "")
                    break
            if a.get("displayName"):
                out["name:" + normalize(a["displayName"])] = i.get("status", "")
    return out


PAYOUT_TABLES = {
    "power": {2: {2: 3}, 3: {3: 5}, 4: {4: 10}, 5: {5: 20}, 6: {6: 37.5}},
    "flex": {3: {3: 3, 2: 1}, 4: {4: 6, 3: 1.5}, 5: {5: 10, 4: 2, 3: 0.4}, 6: {6: 25, 5: 2, 4: 0.4}},
}


def entry_ev(probs, kind):
    """Expected profit per $1 of a Power or Flex entry, legs treated as independent."""
    table = PAYOUT_TABLES[kind].get(len(probs))
    if not table:
        return None
    dist = [1.0]
    for p in probs:
        nxt = [0.0] * (len(dist) + 1)
        for i, v in enumerate(dist):
            nxt[i] += v * (1 - p)
            nxt[i + 1] += v * p
        dist = nxt
    return sum(dist[h] * m for h, m in table.items()) - 1


def best_entry(picks):
    """Highest-EV entry from the top 2 to 6 picks; sit out when nothing clears MIN_ENTRY_EV."""
    best = None
    for n in range(2, len(picks) + 1):
        legs = picks[:n]
        teams = {((p.get("report") or {}).get("player") or {}).get("team") or p["game"] + p["player"] for p in legs}
        if len(teams) < 2:
            continue                            # PrizePicks needs players from 2+ teams
        for kind in ("power", "flex"):
            if kind == "power" and n > MAX_POWER_LEGS:
                continue
            ev = entry_ev([0.5 + (p["final_p"] - 0.5) * ENTRY_SHRINK for p in legs], kind)
            if ev is not None and (best is None or ev > best["ev"]):
                best = {"kind": kind, "legs": n, "ev": round(ev, 4), "ids": [p["id"] for p in legs]}
    if not best:
        return {"kind": None, "legs": 0, "ev": None, "ids": [], "play": False}
    best["play"] = best["ev"] >= MIN_ENTRY_EV
    best["label"] = f"{best['legs']}-pick {'Power' if best['kind'] == 'power' else 'Flex'}"
    return best


def scan_daily():
    if not ODDS_API_KEY:
        raise ScanError("ODDS_API_KEY not found. Put it in the .env file next to sports_app.py.")

    # 1. Free: list every sport's games in the slate window
    now = datetime.now(timezone.utc)
    slate = []
    for prio, (odds_key, sport, markets) in enumerate(ODDS_SPORTS):
        try:
            events = odds_get(f"/sports/{odds_key}/events") or []
        except requests.RequestException:
            continue
        for e in events:
            try:
                start = parse_date(e["commence_time"])
            except (KeyError, ValueError):
                continue
            if now <= start <= now + timedelta(hours=SLATE_HOURS):
                slate.append((prio, start, odds_key, sport, markets, e))
    if not slate:
        raise ScanError(f"No games with player props in the next {SLATE_HOURS} hours.")
    slate.sort(key=lambda x: (x[0], x[1]))
    remaining_before = _quota["remaining"]
    games_by_sport = {}
    for _, _, _, sport, _, _ in slate:
        games_by_sport[sport] = games_by_sport.get(sport, 0) + 1

    # 2. Order purchases so every sport gets scanned: each sport's games take turns,
    #    main market on every game before any second market.
    queues = {sport: [] for sport in games_by_sport}
    for rank in range(max(len(item[4]) for item in slate)):
        for _, _, odds_key, sport, markets, e in slate:
            if rank < len(markets):
                queues[sport].append((odds_key, e, markets[rank]))
    order = []
    while any(queues.values()):
        for sport, q in queues.items():
            if q:
                order.append((sport,) + q.pop(0))

    # 3. Paid: one market per call. A market with no posted odds costs nothing,
    #    so the budget is checked against credits actually charged.
    lines, pp_seen, spent, calls = [], False, 0, 0
    sports_with_lines, games_with_lines = set(), set()
    books = REF_BOOKS
    for sport, odds_key, e, (market_key, prop) in order:
        if spent >= DAILY_CREDIT_BUDGET or calls >= MAX_SCAN_CALLS:
            break
        before = _quota["remaining"]
        data = odds_get(f"/sports/{odds_key}/events/{e['id']}/odds",
                        bookmakers=",".join(books + [PP_BOOK]),
                        markets=market_key, oddsFormat="american")
        calls += 1
        cost = (before - _quota["remaining"]) if before is not None and _quota["remaining"] is not None else 1
        spent += cost
        if cost > 1 and books is REF_BOOKS:
            books = FALLBACK_BOOKS          # 10 books cost extra after all: drop back to 2 for the rest
        if not data:
            continue
        got, has_pp = lines_from_event(data, sport, {market_key: prop})
        if got:
            sports_with_lines.add(sport)
            games_with_lines.add(e["id"])
        lines += got
        pp_seen = pp_seen or has_pp
    if pp_seen:
        lines = [l for l in lines if l["on_pp"]]

    # 4. Free: ESPN game-log check on the board, then blend using what the picker has learned
    lines.sort(key=lambda l: -l["market_p"])
    candidates = lines[:BOARD_ANALYZE_CAP]
    model = load_model()
    injuries = {k: injury_statuses(k) for k in {c["sport"] for c in candidates}}
    for c in candidates:
        try:
            rep = analyze(c["sport"], c["player"], c["prop"], c["line"])
        except (ValueError, KeyError, requests.RequestException):
            rep = None
        c["report"] = rep
        c["hist_p"], c["tier"] = None, None
        if rep:
            v = rep["verdict"]
            over_rate = v["score"] / 100 if v["side"] == "MORE" else 1 - v["score"] / 100
            c["hist_p"] = over_rate if c["side"] == "MORE" else 1 - over_rate
            c["tier"] = (rep.get("matchup") or {}).get("tier")
        pid = str(((rep or {}).get("player") or {}).get("id", ""))
        status = injuries[c["sport"]].get(pid) or injuries[c["sport"]].get("name:" + normalize(c["player"]))
        c["injury"] = status if status and status.lower() not in SAFE_INJURY_STATUS else None
        c["final_p"] = apply_model(c, model)
    board = [{
        "id": f"line|{c['sport']}|{c['player']}|{c['prop']}|{c['line']:g}".lower(),
        "sport": c["sport"], "player": c["player"], "prop": c["prop"], "line": c["line"], "side": c["side"],
        "market_p": c["market_p"], "hist_p": c["hist_p"], "final_p": c["final_p"], "tier": c["tier"],
        "commence": c.get("commence"), "game": c.get("game"), "injury": c["injury"],
        "book_line": c.get("book_line"), "n_books": c.get("n_books"),
        "espn_id": ((c.get("report") or {}).get("player") or {}).get("id"),
    } for c in candidates]

    # 5. Build the slip: best blended probability, 1 per player, max 2 per game
    candidates.sort(key=lambda c: -c["final_p"])
    picks, players, per_game = [], set(), {}
    for c in candidates:
        if c["final_p"] < 0.5:
            break                      # never fill the slip with a pick it expects to lose
        if c["injury"]:
            continue                   # listed on the injury report: skip
        if c["player"] in players or per_game.get(c["game"], 0) >= MAX_PER_GAME:
            continue
        picks.append(c)
        players.add(c["player"])
        per_game[c["game"]] = per_game.get(c["game"], 0) + 1
        if len(picks) == DAILY_PICKS:
            break
    for i, p in enumerate(picks, 1):
        p["rank"] = i
        p["id"] = f"daily|{p['sport']}|{p['player']}|{p['prop']}".lower()
    entry = best_entry(picks)

    used = (remaining_before - _quota["remaining"]) if remaining_before is not None and _quota["remaining"] is not None else spent
    return {
        "date": datetime.now().date().isoformat(),
        "scanned_at": datetime.now().isoformat(timespec="minutes"),
        "credits_used": used, "credits_remaining": _quota["remaining"], "budget": DAILY_CREDIT_BUDGET,
        "games_by_sport": games_by_sport, "sports": sorted(sports_with_lines),
        "games_scanned": len(games_with_lines), "lines_compared": len(lines),
        "pp_matched": pp_seen, "picks": picks, "locked": len(picks) >= 2,
        "board": board, "model": {"active": model["active"], "market_weight": model["market_weight"]},
        "entry": entry, "books_used": len(books), "injured_skipped": sum(1 for c in candidates if c["injury"]),
    }


def load_daily():
    try:
        d = json.loads(DAILY_FILE.read_text())
    except (OSError, ValueError):
        return None
    return d if d.get("date") == datetime.now().date().isoformat() else None


def save_daily(d):
    DAILY_FILE.write_text(json.dumps(d))
    archive_daily(d)


# ───────────────────────── Pick history & grading (ESPN results, free) ─────────────────────────
HISTORY_FILE  = APP_DIR / "pick_history.json"
RECORD_STAKE  = 10       # flat stake used for the hypothetical slip P/L
GRADE_AFTER_H = 3        # start checking a game this many hours after tip-off
VOID_AFTER_H  = 36       # no stat line this long after tip-off = didn't play
HISTORY_LOCK  = threading.Lock()


def load_history():
    try:
        return json.loads(HISTORY_FILE.read_text())
    except (OSError, ValueError):
        return {"days": {}}


def save_history(h):
    HISTORY_FILE.write_text(json.dumps(h, indent=1))


def archive_daily(d):
    """Copy a locked daily slip into the permanent history (keeps any grades already made)."""
    if not d or not d.get("locked"):
        return
    with HISTORY_LOCK:
        h = load_history()
        day = h["days"].get(d["date"], {"date": d["date"], "picks": []})
        graded = {p["id"]: p for p in day["picks"]}
        day["picks"] = []
        for p in d["picks"]:
            rep = p.get("report") or {}
            old = graded.get(p["id"], {})
            day["picks"].append({
                "id": p["id"], "sport": p["sport"], "player": p["player"], "prop": p["prop"], "line": p["line"],
                "side": p["side"], "final_p": p.get("final_p"), "market_p": p.get("market_p"),
                "commence": p.get("commence"), "game": p.get("game"),
                "espn_id": (rep.get("player") or {}).get("id"),
                "result": old.get("result"), "actual": old.get("actual"), "graded_at": old.get("graded_at"),
            })
        old_board = {b["id"]: b for b in day.get("board", [])}
        day["board"] = [{**b, **{k: old_board.get(b["id"], {}).get(k) for k in ("result", "actual", "graded_at")}}
                        for b in d.get("board", [])]
        day["entry"] = d.get("entry")
        h["days"][d["date"]] = day
        save_history(h)


def grade_pick(p, now):
    """Returns (result, actual) or None while still pending. result: hit / miss / push / void."""
    try:
        start = parse_date(p["commence"])
    except (KeyError, TypeError, ValueError):
        return None
    if now < start + timedelta(hours=GRADE_AFTER_H):
        return None
    sport = SPORT_BY_KEY.get(p["sport"])
    calc = sport and sport["props"].get(p["prop"])
    if not calc:
        return ("void", None)
    pid = p.get("espn_id")
    if not pid:
        found = search_players(sport, p["player"], limit=1)
        pid = found[0]["id"] if found else None
        p["espn_id"] = pid
    game = None
    if pid:
        games, _ = game_log(sport, pid)
        for g in games:
            try:
                if abs(parse_date(g["date"]) - start) < timedelta(hours=12):
                    game = g
                    break
            except ValueError:
                continue
    if game:
        try:
            actual = calc(game["row"])
        except (KeyError, ValueError, TypeError):
            return ("void", None)          # listed but no stats = did not play
        if actual == p["line"]:
            return ("push", actual)
        won = actual > p["line"] if p["side"] == "MORE" else actual < p["line"]
        return ("hit" if won else "miss", actual)
    if now > start + timedelta(hours=VOID_AFTER_H):
        return ("void", None)
    return None


def slip_result(picks, entry=None):
    """Outcome of the suggested entry at RECORD_STAKE. Voided legs drop out, as on PrizePicks.
    Older days without an entry are scored as one Flex of every pick."""
    if entry is not None and not entry.get("play"):
        return {"n": 0, "hits": 0, "type": "Sat out", "mult": 1, "pl": 0.0, "sat_out": True}
    legs = [p for p in picks if p["id"] in entry["ids"]] if entry else picks
    kind = entry["kind"] if entry else "flex"
    if any(p.get("result") is None for p in legs):
        return None
    live = [p for p in legs if p["result"] in ("hit", "miss")]
    hits = sum(p["result"] == "hit" for p in live)
    n = len(live)
    if n < 2:
        return {"n": n, "hits": hits, "type": "Refunded", "mult": 1, "pl": 0.0}
    if kind == "flex" and n >= 3:
        mult, label = PAYOUT_TABLES["flex"][n].get(hits, 0), f"{n}-pick Flex"
    else:
        mult, label = PAYOUT_TABLES["power"][n].get(hits, 0), f"{n}-pick Power"
    return {"n": n, "hits": hits, "type": label, "mult": mult, "pl": round(RECORD_STAKE * (mult - 1), 2)}


def grade_history():
    """Grade every pending pick whose game should be over. Returns newly graded day keys."""
    now = datetime.now(timezone.utc)
    newly_done = []
    with HISTORY_LOCK:
        h = load_history()
        changed = False
        for key, day in h["days"].items():
            was_done = all(p.get("result") for p in day["picks"])
            for p in day["picks"] + day.get("board", []):
                if p.get("result"):
                    continue
                try:
                    graded = grade_pick(p, now)
                except requests.RequestException:
                    graded = None
                if graded:
                    p["result"], p["actual"] = graded
                    p["graded_at"] = now.isoformat(timespec="minutes")
                    changed = True
            if not was_done and all(p.get("result") for p in day["picks"]):
                newly_done.append(key)
        if changed:
            save_history(h)
    return newly_done


# ───────────────────────── Learning from results ─────────────────────────
MODEL_FILE     = APP_DIR / "model.json"
LEARN_MIN      = 150     # graded lines before any adjustment (simulations: fewer can hurt more than help)
PRIOR_STRENGTH = 100     # how many lines of evidence the default 75/25 blend is worth
SEG_STRENGTH   = 50      # same, for sport / prop / side / matchup adjustments
SEG_MIN        = 15      # a group needs this many graded lines before it's adjusted
MAX_ADJ        = 0.03    # cap on any single adjustment (3 percentage points)
MAX_TOTAL_ADJ  = 0.05


def default_model():
    return {"active": False, "n": 0, "market_weight": MARKET_WEIGHT, "bias": 0.0, "segments": {}}


def load_model():
    try:
        return {**default_model(), **json.loads(MODEL_FILE.read_text())}
    except (OSError, ValueError):
        return default_model()


def segment_keys(c):
    return [f"sport:{c['sport']}", f"prop:{c['sport']}|{c['prop']}|{c['side']}", f"side:{c['side']}",
            f"tier:{c.get('tier') or 'none'}"]


def base_prob(c, w):
    return w * c["market_p"] + (1 - w) * c["hist_p"] if c.get("hist_p") is not None else c["market_p"]


def apply_model(c, model):
    p = base_prob(c, model["market_weight"])
    if model.get("active"):
        adj = model["bias"] + sum(model["segments"].get(k, 0) for k in segment_keys(c))
        p += max(-MAX_TOTAL_ADJ, min(MAX_TOTAL_ADJ, adj))
    return min(max(p, 0.01), 0.99)


def clamp(x):
    return max(-MAX_ADJ, min(MAX_ADJ, x))


def fit_model(h):
    """Learn from every graded line: blend weight, overall calibration, and group adjustments.
    Every estimate is shrunk toward 'no change' so small samples can't swing the picker."""
    seen, rows = set(), []
    for day in h["days"].values():
        for r in (day.get("board") or day["picks"]):           # older days have no board: use the picks
            if r.get("result") in ("hit", "miss") and r.get("market_p") is not None and r["id"] not in seen:
                seen.add(r["id"])
                rows.append(r)
    n = len(rows)
    y = {r["id"]: 1.0 if r["result"] == "hit" else 0.0 for r in rows}

    # 1. Market vs history weight: best Brier score on lines that have both, shrunk toward 75/25
    with_hist = [r for r in rows if r.get("hist_p") is not None]
    fit_w = MARKET_WEIGHT
    if len(with_hist) >= 20:
        grid = [x / 100 for x in range(50, 101, 5)]
        fit_w = min(grid, key=lambda w: sum((base_prob(r, w) - y[r["id"]]) ** 2 for r in with_hist))
    weight = (len(with_hist) * fit_w + PRIOR_STRENGTH * MARKET_WEIGHT) / (len(with_hist) + PRIOR_STRENGTH)

    # 2. Overall calibration: are the estimates too high or too low?
    pred = {r["id"]: base_prob(r, weight) for r in rows}
    bias = clamp(sum(y[i] - pred[i] for i in y) / (n + PRIOR_STRENGTH)) if n else 0.0

    # 3. Groups that keep beating or missing their estimates
    groups = {}
    for r in rows:
        for k in segment_keys(r):
            groups.setdefault(k, []).append(r)
    #    Fitted jointly (backfitting) so overlapping groups don't double-count the same misses.
    segments = {}
    for _ in range(8):
        for k, rs in groups.items():
            if len(rs) < SEG_MIN:
                continue
            resid = sum(y[r["id"]] - pred[r["id"]] - bias
                        - sum(segments.get(k2, 0) for k2 in segment_keys(r) if k2 != k) for r in rs)
            segments[k] = clamp(resid / (len(rs) + SEG_STRENGTH))
    segments = {k: round(v, 4) for k, v in segments.items() if abs(v) >= 0.005}
    report = sorted(({"key": k, "n": len(rs), "actual": sum(y[r["id"]] for r in rs) / len(rs),
                      "expected": sum(pred[r["id"]] for r in rs) / len(rs), "adj": segments.get(k, 0.0)}
                     for k, rs in groups.items()), key=lambda g: -g["n"])

    # 4. Calibration table for the Record page
    buckets = []
    for lo, hi in ((0.0, 0.53), (0.53, 0.56), (0.56, 0.60), (0.60, 1.0)):
        rs = [r for r in rows if lo <= pred[r["id"]] < hi]
        if rs:
            buckets.append({"range": [lo, hi], "n": len(rs), "expected": sum(pred[r["id"]] for r in rs) / len(rs),
                            "actual": sum(y[r["id"]] for r in rs) / len(rs)})

    active = n >= LEARN_MIN
    model = {
        "active": active, "n": n, "n_hist": len(with_hist), "learn_min": LEARN_MIN,
        "market_weight": round(weight, 3) if active else MARKET_WEIGHT, "fit_weight": fit_w,
        "bias": round(bias, 4) if active else 0.0, "segments": segments if active else {},
        "groups": report[:12], "calibration": buckets,
        "overall": {"expected": sum(pred.values()) / n, "actual": sum(y.values()) / n} if n else None,
        "updated": datetime.now().isoformat(timespec="minutes"),
    }
    MODEL_FILE.write_text(json.dumps(model, indent=1))
    return model


def history_summary(h):
    picks = [p for d in h["days"].values() for p in d["picks"]]
    count = lambda r, ps=picks: sum(p.get("result") == r for p in ps)
    by_sport = {}
    for p in picks:
        s = by_sport.setdefault(p["sport"], {"hit": 0, "miss": 0})
        if p.get("result") in s:
            s[p["result"]] += 1
    results = [slip_result(d["picks"], d.get("entry")) for d in h["days"].values()]
    slips = [s for s in results if s and not s.get("sat_out")]
    hits, misses = count("hit"), count("miss")
    return {
        "hit": hits, "miss": misses, "push": count("push"), "void": count("void"),
        "pending": sum(not p.get("result") for p in picks),
        "hit_rate": hits / (hits + misses) if hits + misses else None,
        "slips": len(slips), "slips_cashed": sum(s["mult"] > 1 for s in slips),
        "sat_out": sum(1 for s in results if s and s.get("sat_out")),
        "slip_pl": round(sum(s["pl"] for s in slips), 2), "stake": RECORD_STAKE, "by_sport": by_sport,
    }


def next_scan_time(locked_today):
    """Next scheduled scan as a local datetime (or None if the schedule isn't installed)."""
    if not SCHEDULE_PLIST.exists():
        return None
    now = datetime.now()
    for day in (0, 1):
        for h, m in SCAN_TIMES:
            t = (now + timedelta(days=day)).replace(hour=h, minute=m, second=0, microsecond=0)
            if t > now and not (day == 0 and locked_today):
                return t
    return None


def notify(title, message):
    """macOS banner notification (best effort)."""
    def q(s):
        return '"' + s.replace("\\", "").replace('"', "'") + '"'
    try:
        subprocess.run(["osascript", "-e", f"display notification {q(message)} with title {q(title)}"],
                       timeout=10, check=False)
    except (OSError, subprocess.SubprocessError):
        pass


def run_scheduled_scan():
    """Entry point for the background job: scan once if today isn't locked yet."""
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M")
    graded_days = grade_history()
    fit_model(load_history())
    for key in graded_days:
        day = load_history()["days"][key]
        res = slip_result(day["picks"], day.get("entry"))
        hits = sum(p["result"] == "hit" for p in day["picks"])
        graded = sum(p["result"] in ("hit", "miss") for p in day["picks"])
        msg = f"{hits} of {graded} picks hit"
        if res:
            msg += f" · ${RECORD_STAKE} {res['type']}: {'+' if res['pl'] >= 0 else '-'}${abs(res['pl']):.2f}"
        print(f"[{stamp}] Graded {key}: {msg}")
        notify("Results are in", msg)
    d = load_daily()
    archive_daily(d)
    if d and d.get("locked"):
        print(f"[{stamp}] Today's slip is already locked; 0 credits used.")
        return
    with SCAN_LOCK:
        try:
            d = scan_daily()
        except (ScanError, requests.RequestException) as e:
            print(f"[{stamp}] Scan failed: {e}")
            return
        save_daily(d)
    print(f"[{stamp}] {len(d['picks'])} picks, {d['credits_used']} credits used, {d['credits_remaining']} left.")
    if d["locked"]:
        top = d["picks"][0]
        notify("Daily slip ready", f"{len(d['picks'])} picks · #1 {top['side']} {top['player']} {top['prop']} {top['line']:g}")


def install_schedule():
    """Register a macOS LaunchAgent that runs the scan at SCAN_TIMES every day."""
    SCHEDULE_PLIST.parent.mkdir(parents=True, exist_ok=True)
    with open(SCHEDULE_PLIST, "wb") as f:
        plistlib.dump({
            "Label": SCHEDULE_LABEL,
            "ProgramArguments": [sys.executable, str(APP_DIR / "sports_app.py"), "--scan"],
            "StartCalendarInterval": [{"Hour": h, "Minute": m} for h, m in SCAN_TIMES],
            "WorkingDirectory": str(APP_DIR),
            "StandardOutPath": str(APP_DIR / "scan.log"),
            "StandardErrorPath": str(APP_DIR / "scan.log"),
        }, f)
    subprocess.run(["launchctl", "unload", str(SCHEDULE_PLIST)], capture_output=True)
    subprocess.run(["launchctl", "load", "-w", str(SCHEDULE_PLIST)], check=True)
    times = " and ".join(datetime(2000, 1, 1, h, m).strftime("%-I:%M %p") for h, m in SCAN_TIMES)
    print(f"Scheduled daily scans at {times}. Log: {APP_DIR / 'scan.log'}")


def rebuild_picks(d, reports=None):
    """Re-pick today's slip from the saved board (after a line moved or was pulled). Free: ESPN only."""
    reports = reports or {}
    existing = {(p["sport"], p["player"], p["prop"]): p for p in d.get("picks", [])}
    pool = sorted((b for b in d["board"] if not b.get("injury") and not b.get("pulled") and b["final_p"] >= 0.5),
                  key=lambda b: -b["final_p"])
    picks, players, per_game = [], set(), {}
    for b in pool:
        if b["player"] in players or per_game.get(b["game"], 0) >= MAX_PER_GAME:
            continue
        key = (b["sport"], b["player"], b["prop"])
        old = existing.get(key)
        rep = reports.get(key) or (old.get("report") if old and old["line"] == b["line"] else None)
        if rep is None:
            try:
                rep = analyze(b["sport"], b["player"], b["prop"], b["line"])
            except (ValueError, KeyError, requests.RequestException):
                rep = None
        pick = {**(old or {}), **{k: v for k, v in b.items() if k != "id"}, "report": rep}
        picks.append(pick)
        players.add(b["player"])
        per_game[b["game"]] = per_game.get(b["game"], 0) + 1
        if len(picks) == DAILY_PICKS:
            break
    for i, pk in enumerate(picks, 1):
        pk["rank"] = i
        pk["id"] = f"daily|{pk['sport']}|{pk['player']}|{pk['prop']}".lower()
    d["picks"] = picks
    d["entry"] = best_entry(picks)
    d["locked"] = True
    return d


def update_line(pick_id, new_line=None, pulled=False):
    """Apply a PrizePicks line move (or a pulled prop) to today's slip. Returns (daily, message)."""
    with SCAN_LOCK:
        d = load_daily()
        if not d or not d.get("board"):
            raise ValueError("Line updates work on slips from the new scan (tomorrow's onward).")
        pick = next((p for p in d["picks"] if p["id"] == pick_id), None)
        if not pick:
            raise ValueError("That pick isn't in today's slip anymore.")
        key = (pick["sport"], pick["player"], pick["prop"])
        b = next((x for x in d["board"] if (x["sport"], x["player"], x["prop"]) == key), None)
        if not b:
            raise ValueError("No saved odds for that pick.")
        reports = {}
        before = [p["player"] for p in d["picks"]]
        if pulled:
            b["pulled"] = True
        else:
            old_line = b.get("line_moved_from", b["line"])
            p_over = b["market_p"] if b["side"] == "MORE" else 1 - b["market_p"]
            p_new = prob_over(new_line, b["line"], p_over, b["prop"])
            b.update(line=new_line, side="MORE" if p_new >= 0.5 else "LESS", market_p=max(p_new, 1 - p_new),
                     line_moved_from=old_line, line_gap=round((b.get("book_line") or new_line) - new_line, 1),
                     id=f"line|{b['sport']}|{b['player']}|{b['prop']}|{new_line:g}".lower())
            try:
                rep = analyze(b["sport"], b["player"], b["prop"], new_line)
                v = rep["verdict"]
                over_rate = v["score"] / 100 if v["side"] == "MORE" else 1 - v["score"] / 100
                b["hist_p"] = over_rate if b["side"] == "MORE" else 1 - over_rate
                b["tier"] = (rep.get("matchup") or {}).get("tier")
                reports[key] = rep
            except (ValueError, KeyError, requests.RequestException):
                b["hist_p"] = None
            b["final_p"] = apply_model(b, load_model())
        rebuild_picks(d, reports)
        save_daily(d)

    after = [p["player"] for p in d["picks"]]
    still = next((p for p in d["picks"] if (p["sport"], p["player"], p["prop"]) == key), None)
    added = [x for x in after if x not in before]
    if pulled:
        msg = f"{pick['player']} removed."
    elif still and still["side"] != pick["side"]:
        msg = (f"At {new_line:g} {pick['player']} flips to {still['side']} (estimated {still['final_p'] * 100:.1f}%). "
               f"Your {pick['side']} edge is gone; take {still['side']} only if you like it.")
    elif still:
        msg = f"{pick['player']} at {new_line:g} is still a pick: {still['side']} at an estimated {still['final_p'] * 100:.1f}%."
    else:
        msg = f"At {new_line:g} the edge on {pick['player']} is gone ({b['side']} {b['final_p'] * 100:.1f}%), so it was dropped."
    if added:
        msg += f" Added {', '.join(added)}."
    e = d["entry"]
    msg += f" Suggested entry: {e['label']} (est. EV {e['ev'] * 100:+.1f}%)." if e.get("play") else " Best entry no longer clears the bar: sit out."
    return d, msg


# ───────── Phone access: private link on your Wi-Fi ─────────
APP_PORT     = 5001
TOKEN_FILE   = APP_DIR / ".phone_key"
SERVER_LABEL = "com.prizepicks.server"
SERVER_PLIST = Path.home() / "Library" / "LaunchAgents" / f"{SERVER_LABEL}.plist"


def phone_key():
    try:
        return TOKEN_FILE.read_text().strip()
    except OSError:
        key = secrets.token_urlsafe(12)
        TOKEN_FILE.write_text(key)
        TOKEN_FILE.chmod(0o600)
        return key


def phone_url():
    try:
        host = subprocess.run(["scutil", "--get", "LocalHostName"], capture_output=True, text=True, timeout=5).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        host = ""
    host = f"{host}.local" if host else socket.gethostbyname(socket.gethostname())
    return f"http://{host}:{APP_PORT}/?key={phone_key()}"


def install_server():
    """Keep the dashboard running in the background (starts at login, restarts if it stops)."""
    SERVER_PLIST.parent.mkdir(parents=True, exist_ok=True)
    with open(SERVER_PLIST, "wb") as f:
        plistlib.dump({
            "Label": SERVER_LABEL,
            "ProgramArguments": [sys.executable, str(APP_DIR / "sports_app.py"), "--serve"],
            "RunAtLoad": True, "KeepAlive": True, "WorkingDirectory": str(APP_DIR),
            "StandardOutPath": str(APP_DIR / "server.log"), "StandardErrorPath": str(APP_DIR / "server.log"),
        }, f)
    subprocess.run(["launchctl", "unload", str(SERVER_PLIST)], capture_output=True)
    subprocess.run(["launchctl", "load", "-w", str(SERVER_PLIST)], check=True)
    print(f"Dashboard now runs in the background on port {APP_PORT}.\nPhone link: {phone_url()}")


def uninstall_server():
    subprocess.run(["launchctl", "unload", str(SERVER_PLIST)], capture_output=True)
    SERVER_PLIST.unlink(missing_ok=True)
    print("Background dashboard removed.")


def uninstall_schedule():
    subprocess.run(["launchctl", "unload", str(SCHEDULE_PLIST)], capture_output=True)
    SCHEDULE_PLIST.unlink(missing_ok=True)
    print("Daily schedule removed.")


# ───────────────────────── Live in-game stats (ESPN box scores, free) ─────────────────────────
LIVE_TTL = 30            # seconds; box scores are re-fetched at most this often
# Game length for pace: (periods, minutes per period); the clock counts down
GAME_CLOCK = {"NBA": (4, 12), "WNBA": (4, 10), "NCAAB": (2, 20), "NFL": (4, 15), "NCAAF": (4, 15), "NHL": (3, 20)}
BOX_ALIASES = {"rebounds": "totalRebounds", "fullInnings.partInnings": "innings"}
SCOREBOARD_GROUPS = {"NCAAB": "50", "NCAAF": "80"}     # all of D1 / FBS, not just featured games


def find_event(sport_key, p):
    """The ESPN scoreboard event for a pick's game (matched by team and start time)."""
    sport = SPORT_BY_KEY[sport_key]
    s, l = sport["path"]
    start = parse_date(p["commence"])
    params = {"dates": (start - timedelta(hours=5)).strftime("%Y%m%d"), "limit": 400}   # ESPN days are US Eastern
    if sport_key in SCOREBOARD_GROUPS:
        params["groups"] = SCOREBOARD_GROUPS[sport_key]
    sb = get_json(f"{ESPN_SITE}/site/v2/sports/{s}/{l}/scoreboard", _ttl=LIVE_TTL, **params)
    team_id = player_profile(sport, p["espn_id"]).get("team_id") if p.get("espn_id") else ""
    for e in sb.get("events", []):
        try:
            if abs(parse_date(e["date"]) - start) > timedelta(hours=3):
                continue
            teams = e["competitions"][0]["competitors"]
        except (KeyError, IndexError, ValueError):
            continue
        ids = {str(c["team"]["id"]) for c in teams}
        names = {c["team"].get("displayName", "") for c in teams}
        if (team_id and team_id in ids) or all(n and n in (p.get("game") or "") for n in names):
            return e
    return None


def box_rows(sport_key, event_id):
    """{athlete_id: {stat_name: value}} from a game's box score, using game-log stat names."""
    s, l = SPORT_BY_KEY[sport_key]["path"]
    sm = get_json(f"{ESPN_SITE}/site/v2/sports/{s}/{l}/summary", _ttl=LIVE_TTL, event=event_id)
    rows = {}
    for team in sm.get("boxscore", {}).get("players", []):
        for grp in team.get("statistics", []):
            keys = grp.get("keys") or grp.get("names") or []
            for a in grp.get("athletes", []):
                aid = str((a.get("athlete") or {}).get("id", ""))
                if not aid or not a.get("stats"):
                    continue
                row = rows.setdefault(aid, {})
                for k, v in zip(keys, a["stats"]):
                    if k == "completions/passingAttempts":
                        row["completions"], _, row["passingAttempts"] = v.partition("/")
                    else:
                        row[BOX_ALIASES.get(k, k)] = v
    for team in sm.get("rosters", []):                   # soccer reports player stats here
        for r in team.get("roster", []):
            aid = str((r.get("athlete") or {}).get("id", ""))
            stats = {x.get("name"): x.get("value") for x in r.get("stats", []) if isinstance(x, dict)}
            if aid and stats:
                rows.setdefault(aid, {}).update({k: str(v) for k, v in stats.items() if v is not None})
    if SPORT_BY_KEY[sport_key]["group"] == "hockey":      # hockey box has no points column
        for row in rows.values():
            try:
                row.setdefault("points", str(float(row["goals"]) + float(row["assists"])))
            except (KeyError, ValueError):
                pass
    return rows


def elapsed_fraction(sport_key, status):
    """Share of regulation played, for pace. None when it can't be worked out."""
    period, clock = status.get("period") or 0, str(status.get("displayClock") or "")
    if SPORT_BY_KEY[sport_key]["group"] == "soccer":
        digits = re.match(r"\d+", clock)
        return min(int(digits.group()) / 90, 1) if digits else None
    if sport_key not in GAME_CLOCK or not period:
        return None
    periods, plen = GAME_CLOCK[sport_key]
    if period > periods:
        return 1.0
    try:
        m, _, sec = clock.partition(":")
        left = float(m) + float(sec or 0) / 60 if sec else float(m) / 60
    except ValueError:
        return None
    return min(max(((period - 1) * plen + (plen - left)) / (periods * plen), 0), 1)


def live_for_pick(p):
    sport = SPORT_BY_KEY.get(p["sport"])
    calc = sport and sport["props"].get(p["prop"])
    if not calc or not p.get("commence"):
        return None
    if not p.get("espn_id"):
        found = search_players(sport, p["player"], limit=1)
        p["espn_id"] = found[0]["id"] if found else None
    e = find_event(p["sport"], p)
    if not e:
        return {"state": "unknown"}
    status = e.get("status", {})
    out = {"state": status.get("type", {}).get("state", "pre"), "detail": status.get("type", {}).get("shortDetail", "")}
    if out["state"] == "pre":
        return out
    row = box_rows(p["sport"], e["id"]).get(str(p.get("espn_id")))
    if row is None:
        out["note"] = "Did not play" if out["state"] == "post" else "Hasn't checked in yet"
        return out
    try:
        out["value"] = calc(row)
    except (KeyError, ValueError, TypeError):
        out["note"] = "No live stat for this prop"
        return out
    frac = elapsed_fraction(p["sport"], status)
    if out["state"] == "in" and frac and 0.08 < frac < 1:
        out["pace"] = round(out["value"] / frac, 1)
    return out


def live_picks():
    """Picks worth tracking now: today's slip plus any ungraded pick whose game is near."""
    now = datetime.now(timezone.utc)
    picks = {}
    d = load_daily()
    for p in (d or {}).get("picks", []):
        picks[p["id"]] = {"id": p["id"], "sport": p["sport"], "player": p["player"], "prop": p["prop"],
                          "line": p["line"], "side": p["side"], "commence": p.get("commence"), "game": p.get("game"),
                          "espn_id": ((p.get("report") or {}).get("player") or {}).get("id")}
    for day in load_history()["days"].values():
        for p in day["picks"]:
            try:
                start = parse_date(p["commence"])
            except (KeyError, TypeError, ValueError):
                continue
            if not p.get("result") and now - timedelta(hours=8) < start < now + timedelta(hours=18):
                picks.setdefault(p["id"], dict(p))
    return list(picks.values())


# ───────────────────────── Web server ─────────────────────────
app = Flask(__name__, root_path=str(APP_DIR), instance_path=str(APP_DIR / "instance"))


LOCAL_ADDRS = {"127.0.0.1", "::1"}


@app.before_request
def require_key_off_this_mac():
    """Anything not on this Mac (your phone) needs the private key from the phone link once."""
    if request.remote_addr in LOCAL_ADDRS or request.path == "/api/ping":
        return None
    key = phone_key()
    if hmac.compare_digest(request.args.get("key", ""), key) or hmac.compare_digest(request.cookies.get("pp_key", ""), key):
        return None
    return Response("<!doctype html><meta name=viewport content='width=device-width'><body style='font:16px system-ui;"
                    "background:#0a0f1d;color:#e6e9ef;padding:32px'><h3>Private page</h3><p>Open the phone link from the "
                    "app on your Mac (the Phone button) to get access.</p>", status=401, mimetype="text/html")


@app.after_request
def remember_phone(resp):
    if request.args.get("key") and hmac.compare_digest(request.args.get("key", ""), phone_key()):
        resp.set_cookie("pp_key", phone_key(), max_age=10 * 365 * 24 * 3600, httponly=True, samesite="Lax")
    return resp


@app.get("/api/ping")
def api_ping():
    return jsonify({"app": "daily-slip"})


@app.get("/api/phone")
def api_phone():
    if request.remote_addr not in LOCAL_ADDRS:
        return jsonify({"error": "Only available on the Mac."}), 403
    url = phone_url()
    try:
        import segno
        svg = segno.make(url, error="m").svg_inline(scale=5, dark="#0a0f1d", light="#ffffff", border=2)
    except ImportError:
        svg = None
    return jsonify({"url": url, "qr": svg, "background": SERVER_PLIST.exists()})


@app.post("/api/line")
def api_line():
    body = request.get_json(force=True, silent=True) or {}
    try:
        if body.get("pulled"):
            d, msg = update_line(body.get("id"), pulled=True)
        else:
            d, msg = update_line(body.get("id"), new_line=float(body.get("line")))
    except (TypeError, ValueError) as e:
        return jsonify({"error": str(e) if str(e) and "float" not in str(e) else "Enter the new line, like 25.5."}), 400
    nxt = next_scan_time(True)
    return jsonify({"daily": {**d, "cached": True, "next_scan": nxt.isoformat(timespec="minutes") if nxt else None},
                    "message": msg})


@app.get("/api/daily")
def api_daily():
    """Today's locked slip from disk; scans (spending credits) only when asked and not yet locked."""
    def with_schedule(payload, locked):
        nxt = next_scan_time(locked)
        return jsonify({**payload, "next_scan": nxt.isoformat(timespec="minutes") if nxt else None})

    d = load_daily()
    if d and d.get("locked"):
        archive_daily(d)
        return with_schedule({**d, "cached": True}, True)
    if request.args.get("scan") != "1":
        return with_schedule({"needs_scan": True, "previous": d}, False)
    with SCAN_LOCK:
        d = load_daily()
        if d and d.get("locked"):
            return with_schedule({**d, "cached": True}, True)
        try:
            d = scan_daily()
        except ScanError as e:
            return jsonify({"error": str(e)}), 400
        except requests.RequestException:
            return jsonify({"error": "Couldn't reach The Odds API. Check your internet and try again."}), 502
        save_daily(d)
        return with_schedule({**d, "cached": False}, d["locked"])


@app.get("/api/live")
def api_live():
    out, finals = {}, {}
    for p in live_picks():
        try:
            live = live_for_pick(p)
        except (requests.RequestException, ValueError, KeyError):
            live = None
        if live:
            out[p["id"]] = live
            if live["state"] == "post" and live.get("value") is not None:
                v, line = live["value"], p["line"]
                finals[p["id"]] = ("push" if v == line else "hit" if (v > line) == (p["side"] == "MORE") else "miss", v)
            elif live["state"] == "post" and live.get("note") == "Did not play":
                finals[p["id"]] = ("void", None)
    if finals:
        with HISTORY_LOCK:
            h = load_history()
            stamp = datetime.now(timezone.utc).isoformat(timespec="minutes")
            for day in h["days"].values():
                for p in day["picks"]:
                    if p["id"] in finals and not p.get("result"):
                        p["result"], p["actual"] = finals[p["id"]]
                        p["graded_at"] = stamp
            save_history(h)
    return jsonify(out)


@app.get("/api/history")
def api_history():
    """Grades finished games (ESPN, free), then returns every saved slip plus the overall record."""
    grade_history()
    h = load_history()
    days = []
    for key in sorted(h["days"], reverse=True):
        day = h["days"][key]
        days.append({**day, "slip": slip_result(day["picks"], day.get("entry"))})
    return jsonify({"days": days, "summary": history_summary(h), "model": fit_model(h)})


@app.get("/")
def index():
    config = {
        "budget": DAILY_CREDIT_BUDGET, "min_ev": MIN_ENTRY_EV,
        "leagues": [{"key": s["key"], "label": s["label"], "group": s["group"], "props": list(s["props"])}
                    for s in SPORT_BY_KEY.values()],
    }
    return Response(PAGE.replace("__CONFIG__", json.dumps(config)), mimetype="text/html")


@app.get("/api/search")
def api_search():
    sport = SPORT_BY_KEY.get(request.args.get("sport", ""))
    q = request.args.get("q", "").strip()
    if not sport or len(q) < 3:
        return jsonify([])
    try:
        return jsonify(search_players(sport, q))
    except (requests.RequestException, ValueError):
        return jsonify([])


@app.post("/api/analyze")
def api_analyze():
    body = request.get_json(force=True, silent=True) or {}
    sport_key = body.get("sport", "")
    player = (body.get("player") or "").strip()
    prop = body.get("prop", "")
    try:
        line = float(body.get("line"))
    except (TypeError, ValueError):
        return jsonify({"error": "Enter a numeric PrizePicks line, like 24.5."}), 400
    if not player:
        return jsonify({"error": "Enter a player name."}), 400
    if sport_key not in SPORT_BY_KEY:
        return jsonify({"error": "Pick a league from the list."}), 400
    try:
        return jsonify(analyze(sport_key, player, prop, line, body.get("player_id")))
    except ValueError as e:
        return jsonify({"error": str(e)}), 400
    except requests.RequestException:
        return jsonify({"error": "Couldn't reach ESPN's stats right now. Check your internet and try again."}), 502


# ───────────────────────── Page (HTML/CSS/JS) ─────────────────────────
PAGE = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Daily Slip</title>
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Daily Slip">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="theme-color" content="#0a0f1d">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #0a0f1d;
    --surface: #0f1627;
    --surface-2: #141c30;
    --border: rgba(148, 163, 184, 0.12);
    --border-strong: rgba(148, 163, 184, 0.22);
    --text: #e6e9ef;
    --muted: #8b94a7;
    --faint: #5c6578;
    --accent: #8fb3ff;
    --pos: #3ecf8e;
    --neg: #f07178;
    --pos-bg: rgba(62, 207, 142, 0.10);
    --neg-bg: rgba(240, 113, 120, 0.10);
    --radius: 12px;
  }
  * { box-sizing: border-box; }
  html { color-scheme: dark; }
  body {
    margin: 0; background: var(--bg); color: var(--text);
    font: 14px/1.5 Inter, system-ui, -apple-system, sans-serif;
    font-feature-settings: "tnum" 1, "cv11" 1; -webkit-font-smoothing: antialiased;
  }
  button, input, select { font: inherit; color: inherit; }
  button { cursor: pointer; }
  .num { font-variant-numeric: tabular-nums; }

  /* Layout */
  .topbar { border-bottom: 1px solid var(--border); }
  .topbar-inner { max-width: 1440px; margin: 0 auto; padding: 14px 24px; display: flex; align-items: center; justify-content: space-between; gap: 16px; flex-wrap: wrap; }
  .brand { display: flex; align-items: baseline; gap: 10px; }
  .brand h1 { font-size: 16px; font-weight: 600; margin: 0; letter-spacing: -0.01em; }
  .brand span { color: var(--faint); font-size: 13px; }
  .status { color: var(--muted); font-size: 12.5px; display: flex; gap: 14px; flex-wrap: wrap; }
  .status b { color: var(--text); font-weight: 500; }
  .layout { max-width: 1440px; margin: 0 auto; padding: 24px; display: grid; gap: 24px; grid-template-columns: 180px minmax(0, 1fr) 320px; align-items: start; }
  @media (max-width: 1180px) { .layout { grid-template-columns: 160px minmax(0, 1fr); } .slip { grid-column: 2; } }
  @media (max-width: 760px) { .layout { grid-template-columns: minmax(0, 1fr); padding: 16px; gap: 16px; } .slip { grid-column: auto; } .topbar-inner { padding: 12px 16px; } }

  /* Sidebar */
  .side { position: sticky; top: 24px; }
  .side h3, .section-label { font-size: 11px; font-weight: 600; color: var(--faint); text-transform: uppercase; letter-spacing: 0.08em; margin: 0 0 8px; }
  .filters { display: flex; flex-direction: column; gap: 2px; }
  .filter { display: flex; justify-content: space-between; align-items: center; gap: 10px; padding: 7px 10px; border-radius: 8px; border: 0; background: none; color: var(--muted); text-align: left; }
  .filter:hover { background: var(--surface); color: var(--text); }
  .filter.active { background: var(--surface-2); color: var(--text); }
  .filter .count { color: var(--faint); font-size: 12px; }
  .side-note { margin-top: 20px; color: var(--faint); font-size: 12px; }
  .side-note a { color: var(--muted); }
  @media (max-width: 760px) { .side { position: static; } .filters { flex-direction: row; overflow-x: auto; } .filter { white-space: nowrap; } .side-note { display: none; } }

  /* Sections */
  .section-head { display: flex; justify-content: space-between; align-items: flex-end; gap: 12px; margin-bottom: 12px; flex-wrap: wrap; }
  .section-head h2 { font-size: 20px; font-weight: 600; margin: 0; letter-spacing: -0.015em; }
  .section-head p { margin: 2px 0 0; color: var(--muted); font-size: 13px; }
  .chip { display: inline-flex; align-items: center; gap: 6px; padding: 3px 9px; border: 1px solid var(--border); border-radius: 999px; color: var(--muted); font-size: 12px; }
  .chip.ok { color: var(--pos); border-color: rgba(62, 207, 142, 0.3); }
  .chip.warn { color: #e5c07b; border-color: rgba(229, 192, 123, 0.3); }
  .panel { background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); }

  /* Picks */
  .picks { display: flex; flex-direction: column; gap: 8px; }
  .pick { background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); padding: 14px 16px; cursor: pointer; transition: border-color .12s, background .12s; }
  .pick:hover { border-color: var(--border-strong); }
  .pick.is-selected { border-color: rgba(143, 179, 255, 0.45); background: var(--surface-2); }
  .pick:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
  .pick-top { display: grid; grid-template-columns: 22px minmax(0, 1fr) auto auto 20px; gap: 14px; align-items: center; }
  .rank { color: var(--faint); font-size: 13px; }
  .who .name { font-weight: 600; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .who .meta { color: var(--muted); font-size: 12.5px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .line { text-align: right; }
  .line .prop { color: var(--muted); font-size: 12px; }
  .line .val { font-size: 18px; font-weight: 600; }
  .side-badge { font-size: 12px; font-weight: 600; letter-spacing: 0.04em; padding: 4px 10px; border-radius: 6px; min-width: 56px; text-align: center; }
  .side-badge.more { color: var(--pos); background: var(--pos-bg); }
  .side-badge.less { color: var(--neg); background: var(--neg-bg); }
  .tick { width: 18px; height: 18px; border-radius: 5px; border: 1px solid var(--border-strong); display: grid; place-items: center; font-size: 12px; color: var(--bg); }
  .is-selected .tick { background: var(--accent); border-color: var(--accent); }
  .pick-bottom { display: grid; grid-template-columns: minmax(0, 1fr) 150px; gap: 16px; align-items: end; margin-top: 12px; padding-left: 36px; }
  .stats { display: grid; grid-template-columns: repeat(5, minmax(0, 1fr)); gap: 8px; margin: 0; }
  .stats dt { color: var(--faint); font-size: 11px; }
  .stats dd { margin: 0; font-size: 13px; font-weight: 500; }
  .why { color: var(--faint); font-size: 12px; margin: 8px 0 0 36px; }
  @media (max-width: 760px) {
    .pick-top { grid-template-columns: minmax(0, 1fr) auto auto; }
    .pick-top .rank, .pick-top .tick { display: none; }
    .pick-bottom { grid-template-columns: minmax(0, 1fr); padding-left: 0; }
    .stats { grid-template-columns: repeat(3, minmax(0, 1fr)); }
    .why { margin-left: 0; }
  }
  .pos { color: var(--pos); } .neg { color: var(--neg); }

  .empty { padding: 28px; text-align: center; color: var(--muted); }
  .empty strong { display: block; color: var(--text); font-weight: 600; margin-bottom: 4px; }
  .btn { border: 1px solid var(--border-strong); background: var(--surface-2); border-radius: 8px; padding: 8px 14px; font-weight: 500; }
  .btn:hover { border-color: var(--accent); }
  .btn-primary { background: var(--accent); border-color: var(--accent); color: #0a0f1d; font-weight: 600; }
  .btn-primary:hover { filter: brightness(1.08); }
  .btn:disabled { opacity: .5; cursor: default; }
  .spinner { width: 14px; height: 14px; border: 2px solid var(--border-strong); border-top-color: var(--accent); border-radius: 50%; display: inline-block; animation: spin .8s linear infinite; vertical-align: -2px; }
  @keyframes spin { to { transform: rotate(360deg); } }
  .footnote { color: var(--faint); font-size: 12px; margin-top: 12px; }

  /* Research */
  details.research { margin-top: 32px; }
  details.research > summary { list-style: none; cursor: pointer; display: flex; align-items: center; gap: 8px; color: var(--muted); font-weight: 500; }
  details.research > summary::-webkit-details-marker { display: none; }
  details.research > summary::before { content: "›"; display: inline-block; transition: transform .15s; font-size: 16px; }
  details.research[open] > summary::before { transform: rotate(90deg); }
  .form { display: grid; grid-template-columns: 150px minmax(0, 1fr) 170px 100px auto; gap: 10px; align-items: end; padding: 14px; margin-top: 12px; }
  @media (max-width: 1000px) { .form { grid-template-columns: 1fr 1fr; } }
  .field label { display: block; color: var(--faint); font-size: 11px; margin-bottom: 4px; }
  .field input, .field select { width: 100%; background: var(--bg); border: 1px solid var(--border-strong); border-radius: 8px; padding: 8px 10px; }
  .field input:focus, .field select:focus { outline: none; border-color: var(--accent); }
  .msg { color: var(--neg); font-size: 13px; margin-top: 8px; }
  .report { padding: 16px; margin-top: 10px; }
  .report-head { display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap; margin-bottom: 14px; }
  .report-head .name { font-size: 17px; font-weight: 600; }
  .report-grid { display: grid; grid-template-columns: repeat(5, minmax(0, 1fr)); gap: 10px; margin-bottom: 14px; }
  @media (max-width: 760px) { .report-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
  .stat-box { border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px; }
  .stat-box dt { color: var(--faint); font-size: 11px; }
  .stat-box dd { margin: 2px 0 0; font-weight: 600; }
  .stat-box small { color: var(--muted); font-weight: 400; font-size: 11.5px; display: block; }
  .reasons { margin: 12px 0 0; padding-left: 18px; color: var(--muted); font-size: 13px; }
  .actions { display: flex; gap: 8px; margin-top: 14px; flex-wrap: wrap; }

  /* Tabs, results, record */
  .tabs { display: flex; gap: 2px; background: var(--surface); border: 1px solid var(--border); border-radius: 8px; padding: 3px; }
  .tabs button { border: 0; background: none; color: var(--muted); padding: 5px 14px; border-radius: 6px; font-weight: 500; font-size: 13px; }
  .tabs button.on { background: var(--surface-2); color: var(--text); }
  .res { font-size: 11px; font-weight: 600; letter-spacing: 0.04em; padding: 3px 8px; border-radius: 6px; white-space: nowrap; }
  .res.hit { color: var(--pos); background: var(--pos-bg); }
  .res.miss { color: var(--neg); background: var(--neg-bg); }
  .res.push, .res.void, .res.pending { color: var(--muted); background: rgba(148, 163, 184, 0.10); }
  .summary { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 10px; margin: 0 0 20px; }
  @media (max-width: 760px) { .summary { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
  .summary .panel { padding: 14px 16px; }
  .summary dt { color: var(--faint); font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; }
  .summary dd { margin: 4px 0 0; font-size: 22px; font-weight: 600; }
  .summary small { display: block; color: var(--muted); font-size: 12px; font-weight: 400; margin-top: 2px; }
  .day { margin-bottom: 14px; overflow: hidden; }
  .day-head { display: flex; justify-content: space-between; align-items: baseline; gap: 12px; padding: 12px 16px; border-bottom: 1px solid var(--border); flex-wrap: wrap; }
  .day-head h3 { margin: 0; font-size: 14px; font-weight: 600; }
  .day-head span { color: var(--muted); font-size: 12.5px; }
  table.results { width: 100%; border-collapse: collapse; font-size: 13px; }
  table.results th { text-align: left; color: var(--faint); font-weight: 500; font-size: 11px; padding: 8px 16px; }
  table.results td { padding: 9px 16px; border-top: 1px solid var(--border); }
  table.results .r { text-align: right; }
  @media (max-width: 760px) { table.results .hide-sm { display: none; } table.results th, table.results td { padding-left: 10px; padding-right: 10px; } }

  /* Live tracking */
  .live { display: grid; grid-template-columns: auto minmax(0, 1fr) auto; gap: 14px; align-items: center; margin: 12px 0 0 36px; padding: 9px 12px; border: 1px solid var(--border); border-radius: 8px; background: var(--bg); font-size: 12.5px; }
  .live .clock { color: var(--muted); white-space: nowrap; display: flex; align-items: center; gap: 7px; }
  .live .dot { width: 7px; height: 7px; border-radius: 50%; background: var(--neg); animation: pulse 1.6s ease-in-out infinite; }
  .live.final .dot { display: none; }
  @keyframes pulse { 50% { opacity: .3; } }
  .live .bar { position: relative; height: 6px; border-radius: 3px; background: var(--surface-2); }
  .live .bar span { position: absolute; left: 0; top: 0; bottom: 0; border-radius: 3px; background: var(--accent); }
  .live .bar i { position: absolute; top: -4px; bottom: -4px; width: 2px; background: var(--muted); border-radius: 1px; }
  .live .now { white-space: nowrap; }
  .live .now b { font-size: 14px; font-weight: 600; }
  .live .now small { color: var(--muted); margin-left: 6px; }
  @media (max-width: 760px) { .live { margin-left: 0; grid-template-columns: minmax(0, 1fr) auto; } .live .bar { grid-column: 1 / -1; grid-row: 2; } }
  .live-chip { font-size: 11px; font-weight: 600; color: var(--neg); white-space: nowrap; }

  /* Learning panel */
  .learn { padding: 16px; margin-bottom: 20px; }
  .learn h3 { margin: 0 0 4px; font-size: 14px; font-weight: 600; }
  .learn p { margin: 0; color: var(--muted); font-size: 13px; }
  .progress { height: 6px; border-radius: 3px; background: var(--surface-2); margin: 12px 0 6px; overflow: hidden; }
  .progress span { display: block; height: 100%; background: var(--accent); border-radius: 3px; }
  .learn-grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 20px; margin-top: 14px; }
  @media (max-width: 760px) { .learn-grid { grid-template-columns: minmax(0, 1fr); } }
  .learn table { width: 100%; border-collapse: collapse; font-size: 12.5px; }
  .learn th { text-align: left; color: var(--faint); font-weight: 500; font-size: 11px; padding: 4px 0; }
  .learn td { padding: 5px 0; border-top: 1px solid var(--border); }
  .learn .r { text-align: right; }

  /* Line tools, phone panel */
  .line-tools { margin: 8px 0 0 36px; font-size: 12px; }
  @media (max-width: 760px) { .line-tools { margin-left: 0; } }
  .line-tools .link { color: var(--faint); text-decoration: underline; text-underline-offset: 2px; }
  .line-tools .link:hover { color: var(--text); }
  .line-form { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; margin-top: 6px; }
  .line-form input { width: 90px; background: var(--bg); border: 1px solid var(--border-strong); border-radius: 8px; padding: 6px 8px; }
  .line-form .btn { padding: 6px 12px; font-size: 12.5px; }
  .notice { padding: 10px 14px; margin-bottom: 10px; font-size: 13px; color: var(--text); border-color: rgba(143, 179, 255, 0.35); }
  .modal { position: fixed; inset: 0; background: rgba(5, 8, 16, 0.7); display: grid; place-items: center; z-index: 50; padding: 16px; }
  .modal .panel { max-width: 420px; width: 100%; padding: 20px; }
  .modal h3 { margin: 0 0 6px; font-size: 16px; }
  .modal p, .modal li { color: var(--muted); font-size: 13px; }
  .modal .qr { background: #fff; border-radius: 10px; padding: 8px; width: fit-content; margin: 12px auto; }
  .modal .qr svg { display: block; width: 200px; height: 200px; }
  .modal code { display: block; word-break: break-all; background: var(--bg); border: 1px solid var(--border); border-radius: 8px; padding: 8px; font-size: 12px; color: var(--text); }

  /* Slip */
  .slip { position: sticky; top: 24px; padding: 16px; }
  .slip-head { display: flex; justify-content: space-between; align-items: baseline; margin-bottom: 12px; }
  .slip-head h2 { font-size: 15px; font-weight: 600; margin: 0; }
  .seg { display: grid; grid-template-columns: 1fr 1fr; background: var(--bg); border: 1px solid var(--border); border-radius: 8px; padding: 3px; margin-bottom: 12px; }
  .seg button { border: 0; background: none; padding: 6px; border-radius: 6px; color: var(--muted); font-weight: 500; font-size: 13px; }
  .seg button.on { background: var(--surface-2); color: var(--text); }
  .legs { display: flex; flex-direction: column; gap: 6px; margin-bottom: 14px; }
  .leg { display: grid; grid-template-columns: minmax(0, 1fr) auto 18px; gap: 10px; align-items: center; padding: 8px 10px; border: 1px solid var(--border); border-radius: 8px; }
  .leg .name { font-weight: 500; font-size: 13px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .leg .meta { color: var(--muted); font-size: 11.5px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .leg .side-badge { min-width: 0; padding: 2px 7px; font-size: 11px; }
  .leg .x { border: 0; background: none; color: var(--faint); font-size: 16px; line-height: 1; padding: 0; }
  .leg .x:hover { color: var(--neg); }
  .stake { margin-bottom: 14px; }
  .stake-row { display: flex; justify-content: space-between; color: var(--muted); font-size: 12.5px; margin-bottom: 6px; }
  .stake-row b { color: var(--text); font-weight: 600; }
  input[type=range] { width: 100%; accent-color: var(--accent); }
  .payouts { border-top: 1px solid var(--border); padding-top: 12px; font-size: 13px; }
  .payouts .row { display: flex; justify-content: space-between; padding: 3px 0; color: var(--muted); }
  .payouts .row b { color: var(--text); font-weight: 500; }
  .payouts .max { display: flex; justify-content: space-between; align-items: baseline; margin-bottom: 6px; }
  .payouts .max span { color: var(--muted); font-size: 12px; }
  .payouts .max b { font-size: 22px; font-weight: 600; }
  .slip-warn { color: #e5c07b; font-size: 12px; margin-top: 10px; }
  .slip-foot { color: var(--faint); font-size: 11.5px; margin-top: 12px; }
  .link { background: none; border: 0; color: var(--muted); font-size: 12px; padding: 0; }
  .link:hover { color: var(--neg); }
</style>
</head>
<body>
<header class="topbar">
  <div class="topbar-inner">
    <div style="display:flex;align-items:center;gap:18px;flex-wrap:wrap">
      <div class="brand"><h1>Daily Slip</h1><span id="today"></span></div>
      <nav class="tabs" id="tabs"><button data-view="today">Today</button><button data-view="record">Record</button></nav>
      <button class="btn" id="phoneBtn" style="padding:5px 12px;font-size:13px" hidden>Phone</button>
    </div>
    <div class="status" id="status"></div>
  </div>
</header>

<div class="layout">
  <aside class="side">
    <h3>Leagues</h3>
    <div class="filters" id="filters"></div>
    <p class="side-note">Only leagues with picks today are listed. <a href="#research" id="jumpResearch">Research a player</a></p>
  </aside>

  <main>
    <section id="recordView" hidden></section>
    <div id="todayView">
    <section id="daily"></section>

    <details class="research" id="research">
      <summary>Research a player <span style="color:var(--faint);font-weight:400;font-size:12px">free · ESPN game logs · no credits</span></summary>
      <form class="form panel" id="researchForm" autocomplete="off">
        <div class="field"><label for="league">League</label><select id="league"></select></div>
        <div class="field"><label for="player">Player</label><input id="player" list="playerList" placeholder="Player name"><datalist id="playerList"></datalist></div>
        <div class="field"><label for="prop">Prop</label><select id="prop"></select></div>
        <div class="field"><label for="lineInput">Line</label><input id="lineInput" class="num" type="number" step="0.5" min="0" placeholder="24.5"></div>
        <button class="btn btn-primary" id="analyzeBtn" type="submit">Analyze</button>
      </form>
      <div id="formMsg" class="msg" hidden></div>
      <div id="report"></div>
    </details>
    </div>
  </main>

  <aside class="slip panel">
    <div class="slip-head"><h2>Slip</h2><span class="num" id="slipCount" style="color:var(--muted);font-size:12px"></span></div>
    <div class="seg"><button data-mode="power">Power</button><button data-mode="flex">Flex</button></div>
    <div class="legs" id="legs"></div>
    <div class="stake">
      <div class="stake-row"><span>Stake</span><b class="num" id="stakeVal"></b></div>
      <input id="stake" type="range" min="1" max="200" step="1">
    </div>
    <div class="payouts" id="payouts"></div>
    <div class="slip-warn" id="slipWarn"></div>
    <div style="display:flex;justify-content:space-between;align-items:center;margin-top:12px">
      <span class="slip-foot" style="margin:0">Preview only. Nothing is sent to PrizePicks.</span>
      <button class="link" id="clearSlip">Clear</button>
    </div>
  </aside>
</div>

<script>
const CONFIG = __CONFIG__;
const LEAGUE = Object.fromEntries(CONFIG.leagues.map(l => [l.key, l]));
const PAYOUTS = {
  power: { 2: 3, 3: 5, 4: 10, 5: 20, 6: 37.5 },
  flex: { 3: { 3: 3, 2: 1 }, 4: { 4: 6, 3: 1.5 }, 5: { 5: 10, 4: 2, 3: 0.4 }, 6: { 6: 25, 5: 2, 4: 0.4 } }
};
const MAX_LEGS = 6;

const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
};
const state = {
  daily: null, dailyError: null, loading: false,
  researched: store.get('ps_researched', []), slip: store.get('ps_slip', []),
  mode: store.get('ps_mode', 'flex'), stake: store.get('ps_stake', 10), filter: 'all',
  view: 'today', history: null, results: {}, live: {}, editing: null, lineMsg: null
};
function persist() {
  store.set('ps_researched', state.researched); store.set('ps_slip', state.slip);
  store.set('ps_mode', state.mode); store.set('ps_stake', state.stake);
}

const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const money = v => '$' + v.toFixed(2);
const pct = v => (v * 100).toFixed(1) + '%';
const dailyPicks = () => (state.daily && state.daily.picks) || [];
const leagueLabel = k => (LEAGUE[k] || {}).label || k;
const hitsFor = (w, side) => side === 'MORE' ? w.over : w.under;
const hitStr = (w, side) => w && w.n ? `${hitsFor(w, side)}/${w.n}` : '—';
const fmtTime = iso => new Date(iso).toLocaleString([], { weekday: 'short', hour: 'numeric', minute: '2-digit' });

/* ── Picks shared by slip ── */
function findPick(id) {
  const d = dailyPicks().find(p => p.id === id);
  if (d) return { id, player: d.player, league: d.sport, prop: d.prop, line: d.line, side: d.side, prob: d.final_p,
                  team: (d.report && d.report.player.team) || '' };
  return state.researched.find(p => p.id === id);
}
function togglePick(id) {
  const i = state.slip.indexOf(id);
  if (i >= 0) state.slip.splice(i, 1);
  else {
    const p = findPick(id);
    if (!p) return;
    if (state.slip.length >= MAX_LEGS) return flash(`A slip holds up to ${MAX_LEGS} picks.`);
    const clash = state.slip.map(findPick).find(x => x && x.player === p.player);
    if (clash) state.slip.splice(state.slip.indexOf(clash.id), 1);   // one pick per player
    state.slip.push(id);
  }
  render();
}
function flash(text) { $('#slipWarn').textContent = text; }

/* ── Status bar ── */
function renderStatus() {
  $('#today').textContent = new Date().toLocaleDateString([], { weekday: 'long', month: 'long', day: 'numeric' });
  const d = state.daily, bits = [];
  if (d && d.scanned_at) {
    bits.push(`Updated <b>${new Date(d.scanned_at).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' })}</b>`);
    if (d.credits_remaining != null) bits.push(`<b class="num">${d.credits_remaining}</b> credits left`);
  }
  if (state.nextScan) bits.push(`Next update <b>${fmtTime(state.nextScan)}</b>`);
  $('#status').innerHTML = bits.map(b => `<span>${b}</span>`).join('');
}

/* ── Sidebar: only leagues that have picks ── */
function renderFilters() {
  const counts = {};
  dailyPicks().forEach(p => { counts[p.sport] = (counts[p.sport] || 0) + 1; });
  if (state.filter !== 'all' && !counts[state.filter]) state.filter = 'all';
  const items = [['all', 'All', dailyPicks().length]].concat(Object.keys(counts).map(k => [k, leagueLabel(k), counts[k]]));
  $('#filters').innerHTML = items.map(([k, label, n]) =>
    `<button class="filter ${state.filter === k ? 'active' : ''}" data-filter="${k}"><span>${esc(label)}</span><span class="count num">${n}</span></button>`).join('');
}
$('#filters').addEventListener('click', e => { const b = e.target.closest('[data-filter]'); if (b) { state.filter = b.dataset.filter; render(); } });

/* ── Mini chart: last 10 results vs the line ── */
function spark(points, line, side, w = 150, h = 34) {
  if (!points || !points.length) return '';
  const max = Math.max(line, ...points.map(p => p.value)) * 1.1 || 1;
  const bw = w / points.length, y = v => h - (v / max) * h;
  const bars = points.map((p, i) => {
    const hit = side === 'MORE' ? p.value > line : p.value < line;
    const color = p.value === line ? 'var(--faint)' : hit ? 'var(--pos)' : 'var(--neg)';
    return `<rect x="${i * bw + 1.5}" y="${y(p.value)}" width="${Math.max(2, bw - 3)}" height="${Math.max(1, h - y(p.value))}" rx="1.5" fill="${color}" opacity="0.75"><title>${esc(p.date)} ${esc(p.opp)}: ${p.value}</title></rect>`;
  }).join('');
  return `<svg viewBox="0 0 ${w} ${h}" width="${w}" height="${h}" role="img" aria-label="Last ${points.length} games vs line ${line}">${bars}
    <line x1="0" x2="${w}" y1="${y(line)}" y2="${y(line)}" stroke="var(--muted)" stroke-width="1" stroke-dasharray="3 3"/></svg>`;
}

/* ── Today's picks ── */
function pickRow(p) {
  const r = p.report, sel = state.slip.includes(p.id), m = r && r.matchup, ng = r && r.next_game;
  const team = r && r.player.team;
  const meta = [leagueLabel(p.sport), team, p.commence ? fmtTime(p.commence) : null].filter(Boolean).join(' · ');
  const gap = p.line_gap ? `Books' line ${p.book_line} vs PrizePicks ${p.line}` : null;
  const why = [p.n_books ? `${p.n_books} book${p.n_books === 1 ? '' : 's'}: ${p.books}` : p.books, gap, ng ? `Next ${ng.home ? 'vs' : '@'} ${ng.opp_abbr}${m ? ` · #${m.rank} of ${m.of} in ${m.what}` : ''}` : null].filter(Boolean).join('  ·  ');
  return `
  <article class="pick ${sel ? 'is-selected' : ''}" data-pick="${esc(p.id)}" role="button" tabindex="0" aria-pressed="${sel}">
    <div class="pick-top">
      <span class="rank num">${p.rank}</span>
      <div class="who"><div class="name">${esc(p.player)}</div><div class="meta">${esc(meta)}${staleTag(p)}${entryTag(p)}</div></div>
      <div class="line"><div class="prop">${esc(p.prop)}</div><div class="val num">${p.line}</div></div>
      <span class="side-badge ${p.side === 'MORE' ? 'more' : 'less'}">${p.side}</span>
      ${resultTag(todaysResult(p.id)) || `<span class="tick">${sel ? '✓' : ''}</span>`}
    </div>
    <div class="pick-bottom">
      <dl class="stats num">
        <div><dt>Est. win</dt><dd>${pct(p.final_p)}</dd></div>
        <div><dt>Books</dt><dd>${pct(p.market_p)}</dd></div>
        <div><dt>Last 10</dt><dd>${r ? hitStr(r.recent.l10, p.side) : '—'}</dd></div>
        <div><dt>Season</dt><dd>${r ? hitStr(r.recent.season, p.side) : '—'}</dd></div>
        <div><dt>Matchup</dt><dd>${m ? m.tier : '—'}</dd></div>
      </dl>
      <div>${r ? spark(r.chart, p.line, p.side) : ''}</div>
    </div>
    ${liveStrip(p, state.live[p.id])}
    <p class="why">${esc(why)}</p>
    ${lineTools(p)}
  </article>`;
}

function renderDaily() {
  const el = $('#daily'), d = state.daily;
  const head = (title, sub, chips = '') => `<div class="section-head"><div><h2>${title}</h2>${sub ? `<p>${sub}</p>` : ''}</div><div style="display:flex;gap:6px;flex-wrap:wrap">${chips}</div></div>`;

  if (state.loading) {
    el.innerHTML = head("Today's picks") + `<div class="panel empty"><span class="spinner"></span>&nbsp; Scanning today's slate (max ${CONFIG.budget} credits). About a minute.</div>`;
    return;
  }
  if (state.dailyError) {
    el.innerHTML = head("Today's picks") + `<div class="panel empty"><strong>${esc(state.dailyErrorTitle || "Scan didn't finish")}</strong>${esc(state.dailyError)}${state.noRetry ? '' : '<div style="margin-top:12px"><button class="btn" data-scan>Try again</button></div>'}</div>`;
    return;
  }
  if (!d) { el.innerHTML = head("Today's picks"); return; }

  const picks = dailyPicks();
  if (picks.length < 2) {
    el.innerHTML = head("Today's picks") + `<div class="panel empty"><strong>Lines aren't posted yet</strong>
      The scan found ${picks.length} usable pick${picks.length === 1 ? '' : 's'}. Props usually go up a few hours before games.
      ${state.nextScan ? `It will check again at ${fmtTime(state.nextScan)}.` : ''}
      <div style="margin-top:12px"><button class="btn" data-scan>Scan now</button></div></div>`;
    return;
  }
  const shown = picks.filter(p => state.filter === 'all' || p.sport === state.filter);
  const sports = (d.sports || []).map(leagueLabel).join(', ');
  const e = d.entry;
  const evStr = v => (v >= 0 ? '+' : '-') + Math.abs(v * 100).toFixed(1) + '%';
  const entryText = !e ? (picks.length >= 3 ? `${picks.length}-pick Flex` : `${picks.length}-pick Power`)
    : e.play ? `Suggested: ${e.label} · est. EV ${evStr(e.ev)}` : 'Sit out today';
  const extras = [d.books_used ? `${d.books_used} books` : null, d.injured_skipped ? `${d.injured_skipped} injured skipped` : null].filter(Boolean).join(' · ');
  const sitOut = e && !e.play ? `<div class="panel" style="padding:12px 16px;margin-bottom:10px;color:var(--muted);font-size:13px">
      <b style="color:var(--text)">No slip worth playing today.</b> The best option (${esc(e.label || 'none')}${e.ev != null ? ', est. EV ' + evStr(e.ev) : ''}) doesn't clear the +${(CONFIG.min_ev * 100).toFixed(0)}% bar, so the record logs this day as sat out. The picks are still here to research.</div>` : '';
  el.innerHTML = head("Today's picks",
      `${entryText} · ${d.lines_compared} lines across ${d.games_scanned} games${sports ? ` (${esc(sports)})` : ''}${extras ? ' · ' + extras : ''}`,
      `<span class="chip ok">Locked for today</span>${d.pp_matched ? '' : '<span class="chip warn">Confirm lines in the app</span>'}`)
    + (state.lineMsg ? `<div class="panel notice">${esc(state.lineMsg)}</div>` : '') + sitOut + `<div class="picks">${shown.map(pickRow).join('')}</div>`
    + `<p class="footnote">Est. win blends a consensus of up to 9 sportsbooks (Pinnacle counts double) with the player's hit rate on this line. When PrizePicks' line differs from the books', the books' odds are converted to the PrizePicks number. Players on the injury report are skipped. The suggested entry is whichever Power or Flex size has the best estimated value.</p>`;
}
$('#daily').addEventListener('click', e => {
  if (e.target.closest('.line-tools')) return lineToolsClick(e);
  if (e.target.closest('[data-scan]')) return loadDaily(true);
  const c = e.target.closest('[data-pick]'); if (c) togglePick(c.dataset.pick);
});
$('#daily').addEventListener('keydown', e => {
  if ((e.key === 'Enter' || e.key === ' ') && e.target.matches('[data-pick]')) { e.preventDefault(); togglePick(e.target.dataset.pick); }
});

async function loadDaily(scan) {
  state.loading = scan; state.dailyError = null; render();
  try {
    const d = await fetch('/api/daily' + (scan ? '?scan=1' : '')).then(r => r.json());
    state.loading = false;
    if (d.error) {
      state.dailyError = d.error; state.dailyErrorTitle = d.error_title; state.noRetry = d.no_retry;
      if (d.next_scan) state.nextScan = d.next_scan;
      render(); return;
    }
    state.nextScan = d.next_scan;
    if (d.needs_scan) {
      if (!d.previous) return loadDaily(true);       // nothing scanned today yet
      state.daily = d.previous; render(); return;
    }
    state.daily = d;
    if (store.get('ps_slip_date', '') !== d.date && d.picks.length >= 2) {   // load today's slip once
      state.slip = d.entry ? (d.entry.play ? d.entry.ids.slice() : []) : d.picks.map(p => p.id);
      state.mode = d.entry && d.entry.kind ? d.entry.kind : (d.picks.length >= 3 ? 'flex' : 'power');
      store.set('ps_slip_date', d.date);
    }
    render();
  } catch (e) {
    state.loading = false; state.dailyError = 'Could not reach the app. Is sports_app.py still running?'; render();
  }
}

/* ── Research ── */
function fillLeagues() {
  $('#league').innerHTML = CONFIG.leagues.map(l => `<option value="${l.key}">${esc(l.label)}</option>`).join('');
  $('#league').value = store.get('ps_league', 'NBA');
  if (!LEAGUE[$('#league').value]) $('#league').value = 'NBA';
  fillProps();
}
function fillProps() {
  const l = LEAGUE[$('#league').value];
  $('#prop').innerHTML = l.props.map(p => `<option>${esc(p)}</option>`).join('');
  store.set('ps_league', l.key);
}
$('#league').addEventListener('change', () => { fillProps(); playerIds = {}; });
$('#jumpResearch').addEventListener('click', () => { $('#research').open = true; });

let playerIds = {}, searchTimer;
$('#player').addEventListener('input', () => {
  clearTimeout(searchTimer);
  const q = $('#player').value.trim(), league = $('#league').value;
  if (q.length < 3) return;
  searchTimer = setTimeout(async () => {
    try {
      const res = await fetch(`/api/search?sport=${encodeURIComponent(league)}&q=${encodeURIComponent(q)}`).then(r => r.json());
      res.forEach(p => { playerIds[p.name] = p.id; });
      $('#playerList').innerHTML = res.map(p => `<option value="${esc(p.name)}">${esc(p.sub || '')}</option>`).join('');
    } catch (e) {}
  }, 250);
});

function showMsg(text) { const m = $('#formMsg'); m.textContent = text || ''; m.hidden = !text; }
$('#researchForm').addEventListener('submit', async e => {
  e.preventDefault();
  const sport = $('#league').value, player = $('#player').value.trim(), prop = $('#prop').value, line = parseFloat($('#lineInput').value);
  if (!player) return showMsg('Enter a player name.');
  if (isNaN(line)) return showMsg('Enter the line, like 24.5.');
  showMsg('');
  const btn = $('#analyzeBtn'); btn.disabled = true; btn.innerHTML = '<span class="spinner"></span>';
  try {
    const r = await fetch('/api/analyze', { method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ sport, player, prop, line, player_id: playerIds[player] || null }) }).then(x => x.json());
    if (r.error) showMsg(r.error); else renderReport(r);
  } catch (err) { showMsg('Could not reach the app. Is sports_app.py still running?'); }
  finally { btn.disabled = false; btn.textContent = 'Analyze'; }
});

function renderReport(r) {
  const v = r.verdict, rc = r.recent, m = r.matchup, ng = r.next_game;
  const box = (label, w) => `<div class="stat-box"><dt>${label}</dt><dd class="num">${hitStr(w, v.side)}</dd><small>${w && w.n ? 'avg ' + w.avg : 'no games'}</small></div>`;
  $('#report').innerHTML = `
  <div class="panel report">
    <div class="report-head">
      <div><div class="name">${esc(r.player.name)}</div><div style="color:var(--muted);font-size:12.5px">${esc([r.player.team, r.player.position, r.sport_label].filter(Boolean).join(' · '))}</div></div>
      <div style="text-align:right"><div style="color:var(--muted);font-size:12px">${esc(r.prop)}</div><div class="num" style="font-size:20px;font-weight:600">${r.line}</div></div>
    </div>
    <dl class="report-grid" style="margin:0 0 14px">
      ${box('Last 5', rc.l5)}${box('Last 10', rc.l10)}${box('Season', rc.season)}${box(rc.vs_opp_abbr ? 'vs ' + esc(rc.vs_opp_abbr) : 'vs opponent', rc.vs_opp)}
      <div class="stat-box"><dt>Matchup</dt><dd>${m ? m.tier : '—'}</dd><small>${m ? `#${m.rank} of ${m.of} · ${m.per_game} ${esc(m.what)}` : ng ? 'no rating' : 'no game scheduled'}</small></div>
    </dl>
    <div>${spark(r.chart, r.line, v.side, 600, 70).replace('width="600"', 'width="100%"').replace('height="70"', 'height="70" preserveAspectRatio="none"')}</div>
    <p style="margin:12px 0 0">History leans <span class="${v.side === 'MORE' ? 'pos' : 'neg'}" style="font-weight:600">${v.side}</span>
      <span style="color:var(--muted)">· ${v.score}% weighted hit rate · ${esc(v.label.toLowerCase())}</span></p>
    <ul class="reasons">${v.reasons.map(x => `<li>${esc(x)}</li>`).join('')}${r.notes.map(n => `<li>${esc(n)}</li>`).join('')}</ul>
    <div class="actions">
      <button class="btn ${v.side === 'MORE' ? 'btn-primary' : ''}" data-add="MORE">Add MORE to slip</button>
      <button class="btn ${v.side === 'LESS' ? 'btn-primary' : ''}" data-add="LESS">Add LESS to slip</button>
    </div>
  </div>`;
  $('#report').querySelectorAll('[data-add]').forEach(b => b.addEventListener('click', () => {
    const id = `r|${r.sport}|${r.player.name}|${r.prop}`.toLowerCase();
    state.researched = state.researched.filter(p => p.id !== id).concat([{ id, player: r.player.name, league: r.sport, prop: r.prop,
      line: r.line, side: b.dataset.add, prob: null, team: r.player.team }]);
    if (!state.slip.includes(id)) togglePick(id); else render();
  }));
}

/* ── Slip ── */
function renderSlip() {
  const legs = state.slip.map(findPick).filter(Boolean);
  if (state.daily) state.slip = legs.map(l => l.id);   // drop stale legs once today's picks are known
  const n = legs.length;
  $('#slipCount').textContent = `${n} of ${MAX_LEGS}`;
  document.querySelectorAll('.seg button').forEach(b => b.classList.toggle('on', b.dataset.mode === state.mode));
  $('#stake').value = state.stake; $('#stakeVal').textContent = '$' + state.stake;
  $('#legs').innerHTML = n ? legs.map(l => `
    <div class="leg"><div style="min-width:0"><div class="name">${esc(l.player)}</div><div class="meta">${esc(leagueLabel(l.league))} · ${esc(l.prop)} ${l.line}${state.live[l.id] && state.live[l.id].value != null && state.live[l.id].state !== 'pre' ? ` · <span class="${legStatus(l, state.live[l.id])}">${state.live[l.id].state === 'in' ? 'live' : 'final'} ${state.live[l.id].value}</span>` : ''}</div></div>
      <span class="side-badge ${l.side === 'MORE' ? 'more' : 'less'}">${l.side}</span>
      <button class="x" data-unslip="${esc(l.id)}" aria-label="Remove ${esc(l.player)}">×</button></div>`).join('')
    : '<div style="color:var(--faint);font-size:13px;padding:8px 0">Select picks to build a slip.</div>';

  const table = state.mode === 'power' ? (PAYOUTS.power[n] ? { [n]: PAYOUTS.power[n] } : null) : PAYOUTS.flex[n] || null;
  let html = '';
  if (!table) {
    html = `<div style="color:var(--muted)">${state.mode === 'flex' ? 'Flex needs 3 to 6 picks.' : 'Power needs 2 to 6 picks.'}</div>`;
  } else {
    const tiers = Object.keys(table).map(Number).sort((a, b) => b - a), top = table[tiers[0]];
    html = `<div class="max"><span>To win</span><b class="num">${money(state.stake * top)}</b></div>`
      + tiers.map(h => `<div class="row num"><span>${h} of ${n} correct</span><b>${table[h]}× · ${money(state.stake * table[h])}</b></div>`).join('');
    if (legs.every(l => l.prob != null)) {
      let dist = [1];
      for (const l of legs) { const nx = new Array(dist.length + 1).fill(0); dist.forEach((v, i) => { nx[i] += v * (1 - l.prob); nx[i + 1] += v * l.prob; }); dist = nx; }
      const expMult = tiers.reduce((s, h) => s + dist[h] * table[h], 0), ev = state.stake * (expMult - 1);
      html += `<div class="row num" style="margin-top:8px;border-top:1px solid var(--border);padding-top:8px"><span>All ${n} hit (est.)</span><b>${pct(dist[n])}</b></div>
        <div class="row num"><span>Expected value (est.)</span><b class="${ev >= 0 ? 'pos' : 'neg'}">${ev >= 0 ? '+' : '−'}${money(Math.abs(ev))}</b></div>`;
    }
  }
  $('#payouts').innerHTML = html;
  const warn = [];
  if (n >= 2 && legs.every(l => l.team) && new Set(legs.map(l => l.team)).size === 1) warn.push('PrizePicks requires players from at least 2 teams.');
  $('#slipWarn').textContent = warn.join(' ');
}
$('#legs').addEventListener('click', e => { const b = e.target.closest('[data-unslip]'); if (b) { state.slip = state.slip.filter(id => id !== b.dataset.unslip); render(); } });
document.querySelectorAll('.seg button').forEach(b => b.addEventListener('click', () => { state.mode = b.dataset.mode; render(); }));
$('#stake').addEventListener('input', e => { state.stake = Number(e.target.value); renderSlip(); persist(); });
$('#clearSlip').addEventListener('click', () => { state.slip = []; render(); });

function staleTag(p) {
  if (!p.line_gap) return '';
  const good = (p.side === 'MORE') === (p.line_gap > 0);
  return ` <span class="${good ? 'pos' : 'neg'}" title="Books' line ${p.book_line} vs PrizePicks ${p.line}">· books ${p.line_gap > 0 ? '+' : ''}${p.line_gap}</span>`;
}
function entryTag(p) {
  const e = state.daily && state.daily.entry;
  return e && e.play && e.ids.includes(p.id) ? ' <span style="color:var(--accent)">· in suggested entry</span>' : '';
}

/* ── Line changed / pulled ── */
function lineTools(p) {
  if (!state.daily || !state.daily.board) return '';
  const lv = state.live[p.id];
  if (todaysResult(p.id) || (lv && (lv.state === 'in' || lv.state === 'post'))) return '';   // game already started
  if (state.editing !== p.id) {
    return `<div class="line-tools">${p.line_moved_from != null ? `<span style="color:var(--muted)">Line moved from ${p.line_moved_from} · </span>` : ''}<button class="link" data-edit="${esc(p.id)}">Line changed on PrizePicks?</button></div>`;
  }
  return `<div class="line-tools"><div class="line-form">
      <span style="color:var(--muted)">New line</span>
      <input class="num" type="number" step="0.5" min="0" value="${p.line}" data-newline="${esc(p.id)}">
      <button class="btn btn-primary" data-update="${esc(p.id)}">Update</button>
      <button class="btn" data-pulled="${esc(p.id)}">Line pulled</button>
      <button class="link" data-cancel>Cancel</button></div>
    <div style="color:var(--faint);margin-top:4px">Re-priced from this morning's saved odds. No credits used.</div></div>`;
}
async function lineToolsClick(e) {
  e.stopPropagation();
  const t = e.target;
  if (t.dataset.edit) { state.editing = t.dataset.edit; render(); return; }
  if (t.hasAttribute('data-cancel')) { state.editing = null; render(); return; }
  const id = t.dataset.update || t.dataset.pulled;
  if (!id) return;
  const body = t.dataset.pulled ? { id, pulled: true } : { id, line: document.querySelector(`[data-newline="${CSS.escape(id)}"]`).value };
  t.disabled = true; t.innerHTML = '<span class="spinner"></span>';
  try {
    const r = await fetch('/api/line', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) }).then(x => x.json());
    if (r.error) { state.lineMsg = r.error; }
    else {
      state.daily = r.daily; state.lineMsg = r.message; state.editing = null;
      const en = r.daily.entry;
      state.slip = en && en.play ? en.ids.slice() : [];
      if (en && en.kind) state.mode = en.kind;
    }
  } catch (err) { state.lineMsg = 'Could not reach the app.'; }
  render();
}

/* ── Phone access ── */
const onThisMac = ['127.0.0.1', 'localhost'].includes(location.hostname);
if (onThisMac) $('#phoneBtn').hidden = false;
$('#phoneBtn').addEventListener('click', async () => {
  const r = await fetch('/api/phone').then(x => x.json()).catch(() => null);
  if (!r || r.error) return;
  const m = document.createElement('div');
  m.className = 'modal';
  m.innerHTML = `<div class="panel">
    <h3>Open on your phone</h3>
    <p>Point your iPhone camera at this code, or open the link below. It's private to you: the key in the link is checked once, then remembered.</p>
    ${r.qr ? `<div class="qr">${r.qr}</div>` : ''}
    <code>${esc(r.url)}</code>
    <ul style="padding-left:18px;margin:12px 0 0">
      <li>Your phone must be on the same Wi-Fi as this Mac.</li>
      <li>This Mac must be awake. ${r.background ? 'The app runs in the background, so no window needs to stay open.' : ''}</li>
      <li>In Safari, tap Share, then <b>Add to Home Screen</b> for an app icon.</li>
    </ul>
    <div style="text-align:right;margin-top:14px"><button class="btn" data-close>Done</button></div></div>`;
  m.addEventListener('click', ev => { if (ev.target === m || ev.target.hasAttribute('data-close')) m.remove(); });
  document.body.appendChild(m);
});

/* ── Live in-game tracking ── */
function legStatus(p, lv) {
  if (!lv || lv.value == null) return '';
  return (p.side === 'MORE') === (lv.value > p.line) ? 'pos' : (lv.state === 'post' ? 'neg' : '');
}
function liveStrip(p, lv) {
  if (!lv || lv.state === 'pre' || lv.state === 'unknown') return '';
  const final = lv.state === 'post';
  const clock = `<span class="clock"><span class="dot"></span>${final ? 'Final' : 'Live · ' + esc(lv.detail)}</span>`;
  if (lv.value == null) return `<div class="live ${final ? 'final' : ''}">${clock}<span style="color:var(--muted)">${esc(lv.note || '')}</span><span></span></div>`;
  const v = lv.value, line = p.line, more = p.side === 'MORE';
  const scale = Math.max(line * 1.5, v, 1);
  const over = v > line;
  let msg, cls;
  if (more) {
    const need = Math.floor(line) + 1 - v;
    [msg, cls] = over ? ['Cleared', 'pos'] : [final ? 'Missed' : `Needs ${need} more`, final ? 'neg' : ''];
  } else {
    [msg, cls] = over ? [final ? 'Missed' : 'Over the line', 'neg'] : [final ? 'Stayed under' : `${(line - v).toFixed(1)} under`, final ? 'pos' : ''];
  }
  const barColor = over === more ? 'var(--pos)' : over ? 'var(--neg)' : 'var(--accent)';
  const pace = lv.pace != null && !final ? `<small>pace ${lv.pace}</small>` : '';
  return `<div class="live ${final ? 'final' : ''}">${clock}
    <div class="bar" title="${v} of ${line}"><span style="width:${Math.min(v / scale, 1) * 100}%;background:${barColor}"></span><i style="left:${line / scale * 100}%"></i></div>
    <span class="now num"><b>${v}</b><small>/ ${line}</small><small class="${cls}" style="font-weight:600">${msg}</small>${pace}</span></div>`;
}
let liveTimer;
async function loadLive() {
  clearTimeout(liveTimer);
  let next = 5 * 60 * 1000;
  try {
    state.live = await fetch('/api/live').then(r => r.json());
    const states = Object.values(state.live).map(l => l.state);
    if (states.includes('in')) next = 30 * 1000;                    // games on: refresh every 30s
    if (Object.values(state.live).some(l => l.state === 'post') && state.history) loadHistory();
    render();
  } catch (e) {}
  liveTimer = setTimeout(loadLive, next);
}

/* ── Record ── */
// Results are keyed by slip date: the same player and prop can appear on different days.
const todaysResult = id => state.daily && state.results[`${state.daily.date}|${id}`];
function resultTag(r) {
  if (!r || !r.result) return '';
  const label = { hit: 'HIT', miss: 'MISS', push: 'PUSH', void: 'VOID' }[r.result];
  const tip = r.result === 'void' ? ' title="No stat line: did not play"' : '';
  return `<span class="res ${r.result}"${tip}>${label}${r.actual != null ? ' ' + r.actual : ''}</span>`;
}
async function loadHistory() {
  try {
    const h = await fetch('/api/history').then(r => r.json());
    state.history = h;
    state.results = {};
    h.days.forEach(d => d.picks.forEach(p => { if (p.result) state.results[`${d.date}|${p.id}`] = p; }));
    render();
  } catch (e) {}
}
function renderRecord() {
  const el = $('#recordView'), h = state.history;
  if (!h) { el.innerHTML = '<div class="panel empty"><span class="spinner"></span>&nbsp; Checking results…</div>'; return; }
  const s = h.summary;
  const plStr = v => (v >= 0 ? '+' : '-') + money(Math.abs(v));
  const plCls = v => v > 0 ? 'pos' : v < 0 ? 'neg' : '';
  const leagues = Object.entries(s.by_sport).filter(([, v]) => v.hit + v.miss)
    .map(([k, v]) => `${leagueLabel(k)} ${v.hit}-${v.miss}`).join(' · ');
  const extras = [s.push ? `${s.push} push` : '', s.void ? `${s.void} void` : '', s.pending ? `${s.pending} pending` : '']
    .filter(Boolean).join(' · ');
  let html = `<div class="section-head"><div><h2>Record</h2><p>Every daily pick, graded from ESPN box scores once the game ends.</p></div></div>
    <dl class="summary num">
      <div class="panel"><dt>Picks</dt><dd>${s.hit}-${s.miss}</dd><small>${extras || 'wins - losses'}</small></div>
      <div class="panel"><dt>Hit rate</dt><dd>${s.hit_rate == null ? '—' : pct(s.hit_rate)}</dd><small>${esc(leagues) || 'no graded picks yet'}</small></div>
      <div class="panel"><dt>Slips</dt><dd>${s.slips_cashed} of ${s.slips}</dd><small>suggested slips that paid${s.sat_out ? ` · ${s.sat_out} day${s.sat_out === 1 ? '' : 's'} sat out` : ''}</small></div>
      <div class="panel"><dt>Slip P/L</dt><dd class="${plCls(s.slip_pl)}">${s.slips ? plStr(s.slip_pl) : '—'}</dd><small>at $${s.stake} per slip</small></div>
    </dl>`;
  html += learningPanel(h.model);
  if (!h.days.length) html += '<div class="panel empty"><strong>No slips saved yet</strong>Your first daily slip will show up here.</div>';
  html += h.days.map(d => {
    const graded = d.picks.filter(p => p.result).length;
    const hits = d.picks.filter(p => p.result === 'hit').length;
    const decided = d.picks.filter(p => p.result === 'hit' || p.result === 'miss').length;
    const label = new Date(d.date + 'T12:00').toLocaleDateString([], { weekday: 'short', month: 'short', day: 'numeric' });
    const status = d.slip && d.slip.sat_out
      ? `${hits} of ${decided} picks hit · <b>Sat out</b> (no +EV entry)`
      : d.slip
      ? `${hits} of ${decided} hit · ${d.slip.type} · <b class="${plCls(d.slip.pl)}">${plStr(d.slip.pl)}</b>`
      : `${hits} of ${decided} hit so far · ${d.picks.length - graded} pending`;
    const rows = d.picks.map(p => `<tr>
        <td>${esc(p.player)}<div class="hide-sm" style="color:var(--faint);font-size:11.5px">${esc(leagueLabel(p.sport))}${p.commence ? ' · ' + fmtTime(p.commence) : ''}</div></td>
        <td class="hide-sm">${esc(p.prop)}</td><td class="r">${p.line}</td>
        <td><span class="${p.side === 'MORE' ? 'pos' : 'neg'}" style="font-weight:600;font-size:12px">${p.side}</span></td>
        <td class="r">${p.actual ?? (state.live[p.id] && state.live[p.id].value != null ? state.live[p.id].value : '—')}</td>
        <td class="r">${p.result ? resultTag({ result: p.result })
          : state.live[p.id] && state.live[p.id].state === 'in' ? `<span class="live-chip">LIVE · ${esc(state.live[p.id].detail)}</span>`
          : '<span class="res pending">PENDING</span>'}</td></tr>`).join('');
    return `<div class="panel day">
      <div class="day-head"><h3>Slip from ${label}</h3><span class="num">${status}</span></div>
      <table class="results num"><thead><tr><th>Player</th><th class="hide-sm">Prop</th><th class="r">Line</th><th>Pick</th><th class="r">Actual</th><th class="r">Result</th></tr></thead>
      <tbody>${rows}</tbody></table></div>`;
  }).join('');
  html += `<p class="footnote">Slip P/L assumes you played each day's suggested entry at $${s.stake}, and $0 on days it said to sit out. A player with no stat line (did not play) is voided and drops out of the slip, as on PrizePicks. Results are checked whenever you open the app and each morning before the new scan.</p>`;
  el.innerHTML = html;
}
function groupLabel(key) {
  const [kind, val] = key.split(/:(.*)/s);
  if (kind === 'sport') return leagueLabel(val);
  if (kind === 'side') return `All ${val} picks`;
  if (kind === 'tier') return val === 'none' ? 'No matchup data' : `${val} matchups`;
  const [sport, prop, side] = val.split('|');
  return `${leagueLabel(sport)} ${prop} ${side}`;
}
function learningPanel(m) {
  if (!m) return '';
  const pp = v => (v >= 0 ? '+' : '-') + Math.abs(v * 100).toFixed(1) + ' pts';
  const head = m.active
    ? `<h3>What the picker has learned</h3><p>Learning from ${m.n} graded lines. Adjustments are capped and shrink toward the default when evidence is thin.</p>`
    : `<h3>Learning from results</h3>
       <p>${m.n} of ${m.learn_min} graded lines collected. The picker grades every line it scans (about 40 to 70 a day), not just your 5 picks. Until it has ${m.learn_min}, it keeps the default blend, because in testing, adjusting on fewer lines hurt about as often as it helped.</p>
       <div class="progress"><span style="width:${Math.min(m.n / m.learn_min, 1) * 100}%"></span></div>`;
  const changes = [];
  if (m.active) {
    changes.push(`<tr><td>Book odds vs. hit-rate blend</td><td class="r">${Math.round(m.market_weight * 100)} / ${Math.round((1 - m.market_weight) * 100)}</td><td class="r" style="color:var(--faint)">was 75 / 25</td></tr>`);
    if (m.bias) changes.push(`<tr><td>Overall calibration</td><td class="r ${m.bias > 0 ? 'pos' : 'neg'}">${pp(m.bias)}</td><td class="r" style="color:var(--faint)">${m.bias < 0 ? 'was overconfident' : 'was too cautious'}</td></tr>`);
    Object.entries(m.segments).sort((a, b) => Math.abs(b[1]) - Math.abs(a[1])).slice(0, 6).forEach(([k, v]) => {
      const g = m.groups.find(x => x.key === k);
      changes.push(`<tr><td>${esc(groupLabel(k))}</td><td class="r ${v > 0 ? 'pos' : 'neg'}">${pp(v)}</td><td class="r" style="color:var(--faint)">${g ? `${Math.round(g.actual * 100)}% hit vs ${Math.round(g.expected * 100)}% expected (${g.n})` : ''}</td></tr>`);
    });
  }
  const calib = (m.calibration || []).map(b => `<tr><td>${Math.round(b.range[0] * 100) || '<'}${b.range[0] ? '–' : ''}${Math.round(b.range[1] * 100)}%</td>
      <td class="r">${(b.expected * 100).toFixed(1)}%</td><td class="r ${b.actual >= b.expected ? 'pos' : 'neg'}">${(b.actual * 100).toFixed(1)}%</td><td class="r" style="color:var(--faint)">${b.n}</td></tr>`).join('');
  return `<div class="panel learn">${head}
    <div class="learn-grid">
      <div><table class="num"><thead><tr><th>Adjustment</th><th class="r">Now</th><th class="r"></th></tr></thead>
        <tbody>${changes.join('') || `<tr><td colspan="3" style="color:var(--faint)">${m.active ? 'No group has strayed far enough from its estimate to adjust.' : 'None yet. Using the default 75 / 25 blend.'}</td></tr>`}</tbody></table></div>
      <div><table class="num"><thead><tr><th>Estimated win</th><th class="r">Expected</th><th class="r">Actual</th><th class="r">Lines</th></tr></thead>
        <tbody>${calib || '<tr><td colspan="4" style="color:var(--faint)">No graded lines yet.</td></tr>'}</tbody></table></div>
    </div></div>`;
}
$('#tabs').addEventListener('click', e => {
  const b = e.target.closest('[data-view]'); if (!b) return;
  state.view = b.dataset.view; render();
  if (state.view === 'record') loadHistory();
});

function render() {
  const rec = state.view === 'record';
  document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.view === state.view));
  $('#todayView').hidden = rec; $('#recordView').hidden = !rec;
  document.querySelector('.side').style.visibility = rec ? 'hidden' : '';
  renderStatus(); renderFilters(); renderDaily(); renderSlip();
  if (rec) renderRecord();
  persist();
}
fillLeagues(); render(); loadDaily(false); loadHistory(); loadLive();
setInterval(loadHistory, 10 * 60 * 1000);   // pick up results while the page stays open
</script>
</body>
</html>
'''


# ───────────────────────── Launch ─────────────────────────
def pick_port():
    """5000 if free; macOS AirPlay Receiver often holds it, so fall back."""
    for port in (5000, 5001, 5050, 8050):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(0.3)
            if s.connect_ex(("127.0.0.1", port)) != 0:
                return port
    return 0


def already_running():
    try:
        return HTTP.get(f"http://127.0.0.1:{APP_PORT}/api/ping", timeout=1).json().get("app") == "daily-slip"
    except (requests.RequestException, ValueError):
        return False


if __name__ == "__main__":
    os.chdir(APP_DIR)   # works no matter which folder it was started from
    if "--install-phone" in sys.argv:
        install_server()
        sys.exit()
    if "--remove-phone" in sys.argv:
        uninstall_server()
        sys.exit()
    if "--scan" in sys.argv:
        run_scheduled_scan()
        sys.exit()
    if "--grade" in sys.argv:              # results + learning only, never spends credits
        grade_history()
        fit_model(load_history())
        print(f"[{datetime.now():%Y-%m-%d %H:%M}] Graded results; model updated.")
        sys.exit()
    if "--install-schedule" in sys.argv:
        install_schedule()
        sys.exit()
    if "--remove-schedule" in sys.argv:
        uninstall_schedule()
        sys.exit()
    url = f"http://127.0.0.1:{APP_PORT}"
    if already_running():                       # background copy is up: just open it
        if "--no-browser" not in sys.argv:
            webbrowser.open(url)
        print(f"Daily Slip is already running at {url}")
        sys.exit()
    print(f"\n  Daily Slip running at {url}")
    print(f"  Phone (same Wi-Fi): {phone_url()}")
    print("  Press Ctrl+C to stop.\n")
    if "--no-browser" not in sys.argv and "--serve" not in sys.argv:
        threading.Timer(1.2, lambda: webbrowser.open(url)).start()
    # 0.0.0.0 so your phone on the same Wi-Fi can reach it; off-Mac requests need the private key
    app.run(host="0.0.0.0", port=APP_PORT, debug=False, use_reloader=False, load_dotenv=False)
