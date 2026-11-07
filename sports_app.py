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
                games.append({"event_id": str(eid), "date": m.get("gameDate", ""), "opp_id": str(opp.get("id", "")),
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
                       "betrivers", "fanatics", "underdog"]
DFS_COMPARE         = {"underdog"}                # pick'em apps: compared line-for-line, never used as odds
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
                       "williamhill_us": "CZR", "espnbet": "ESPN", "betrivers": "BR", "fanatics": "FAN", "underdog": "UD"}

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
    for attempt in range(5):
        r = HTTP.get(f"{ODDS_URL}{path}", params=params, timeout=20)
        if r.status_code != 429:
            break
        if r.headers.get("x-requests-remaining") in ("0", "0.0"):
            raise ScanError("Out of Odds API credits for this month.")
        time.sleep(3 * (attempt + 1))         # rate-limited: back off and try again (free)
    else:
        raise ScanError("The Odds API kept rate-limiting requests. The next run will try again.")
    if r.status_code == 401:
        raise ScanError("Your ODDS_API_KEY was rejected. Check the key in your .env file.")
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
    """Strip the juice with the power method: find k so that p_over^k + p_under^k = 1.
    It handles lopsided prices (heavy favorites) more accurately than scaling both sides equally."""
    p_over, p_under = implied_prob(over_odds), implied_prob(under_odds)
    if p_over + p_under <= 1:
        return p_over / (p_over + p_under)
    lo, hi = 1.0, 3.0
    for _ in range(40):
        k = (lo + hi) / 2
        if p_over ** k + p_under ** k > 1:
            lo = k
        else:
            hi = k
    return p_over ** ((lo + hi) / 2)


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
    pp, quotes, ud = {}, {}, {}
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
                elif bm["key"] in DFS_COMPARE:
                    ud.setdefault(key, set()).add(float(point))
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
                    "book_line": book_line, "line_gap": round(book_line - target, 1), "on_pp": key in pp,
                    "ud_line": next(iter(ud[key])) if len(ud.get(key, ())) == 1 else None})
    return out, bool(pp)


def injury_statuses(sport_key):
    """{espn_athlete_id: status} for one league from ESPN's injury report (free)."""
    s, l = SPORT_BY_KEY[sport_key]["path"]
    try:
        data = get_json(f"{ESPN_SITE}/site/v2/sports/{s}/{l}/injuries")
    except (requests.RequestException, ValueError):
        return {}
    if not isinstance(data, dict):
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
    shrink = entry_shrink()
    # 6 legs magnifies any overconfidence; allow it only once entry sizing has been learned from results
    max_legs = 6 if (load_model().get("entry") or {}).get("active") else 5
    best = None
    for n in range(2, min(len(picks), max_legs) + 1):
        legs = picks[:n]
        teams = {((p.get("report") or {}).get("player") or {}).get("team") or p["game"] + p["player"] for p in legs}
        if len(teams) < 2:
            continue                            # PrizePicks needs players from 2+ teams
        for kind in ("power", "flex"):
            if kind == "power" and n > MAX_POWER_LEGS:
                continue
            ev = entry_ev([0.5 + (p["final_p"] - 0.5) * shrink for p in legs], kind)
            if ev is not None and (best is None or ev > best["ev"]):
                best = {"kind": kind, "legs": n, "ev": round(ev, 4), "ids": [p["id"] for p in legs]}
    if not best:
        return {"kind": None, "legs": 0, "ev": None, "ids": [], "play": False}
    best["play"] = best["ev"] >= MIN_ENTRY_EV
    best["label"] = f"{best['legs']}-pick {'Power' if best['kind'] == 'power' else 'Flex'}"
    return best


# Game context: starting guesses (MORE, LESS) in win-probability points until learning has enough data
CTX_DEFAULTS   = {"blowout": (-0.015, 0.010), "b2b": (-0.010, 0.005), "minutes_down": (-0.015, 0.010),
                  "minutes_up": (0.010, -0.010), "high_total": (0.005, -0.005), "low_total": (-0.005, 0.005),
                  "windy": (-0.020, 0.015), "returning": (-0.015, 0.010)}
CTX_CAP        = 0.03          # context can move an estimate at most 3 points
CTX_LABELS     = {"blowout": "blowout risk", "b2b": "2nd night of a back-to-back", "minutes_down": "minutes trending down",
                  "minutes_up": "minutes trending up", "high_total": "high-scoring game expected",
                  "low_total": "low-scoring game expected", "windy": "windy", "returning": "back from a long absence"}
BLOWOUT_SPREAD = {"NBA": 10, "WNBA": 10, "NCAAB": 15, "NFL": 10, "NCAAF": 17}
TOTAL_BANDS    = {"NBA": (215, 235), "WNBA": (155, 170), "NCAAB": (130, 155), "NFL": (40, 50), "NCAAF": (45, 60),
                  "NHL": (5.5, 6.5)}
WIND_PROPS     = {"Pass Yards", "Pass TDs", "Pass Attempts", "Completions", "Receiving Yards", "Receptions", "Rush+Rec Yards"}
WIND_MPH       = 15


def kickoff_weather(venue, commence):
    """Wind (mph) and rain (mm) at an outdoor stadium around kickoff, from Open-Meteo (free, no key)."""
    addr = venue.get("address") or {}
    if not addr.get("city"):
        return None
    try:
        geo = get_json("https://geocoding-api.open-meteo.com/v1/search", _ttl=86400, name=addr["city"], count=5, country="US")
        places = geo.get("results") or []
        place = next((x for x in places if addr.get("state") and addr["state"] in (x.get("admin1", ""), x.get("admin1_code", ""))), places[0] if places else None)
        if not place:
            return None
        wx = get_json("https://api.open-meteo.com/v1/forecast", _ttl=3600, latitude=place["latitude"], longitude=place["longitude"],
                      hourly="wind_speed_10m,precipitation", wind_speed_unit="mph", timezone="UTC", forecast_days=7)
        hours = wx["hourly"]["time"]
        target = parse_date(commence).strftime("%Y-%m-%dT%H:00")
        i = hours.index(target) if target in hours else None
        if i is None:
            return None
        return {"wind": round(wx["hourly"]["wind_speed_10m"][i]), "precip": wx["hourly"]["precipitation"][i]}
    except (requests.RequestException, KeyError, ValueError, IndexError, TypeError):
        return None


def minutes_values(games, group):
    out = []
    for g in games:
        try:
            if group == "basketball":
                out.append(float(g["row"]["minutes"]))
            elif group == "hockey":
                m, _, sec = g["row"]["timeOnIcePerGame"].partition(":")
                out.append(int(m) + int(sec or 0) / 60)
        except (KeyError, ValueError, TypeError, AttributeError):
            pass
    return out


def game_context(c, rep):
    """Spread, total, rest, minutes trend and (outdoor football) wind for one line. ESPN + Open-Meteo, free."""
    ctx = {"flags": []}
    key, sport = c["sport"], SPORT_BY_KEY[c["sport"]]
    pid = ((rep or {}).get("player") or {}).get("id")
    try:
        e = find_event(key, {"commence": c.get("commence"), "espn_id": pid, "game": c.get("game", "")})
    except (requests.RequestException, ValueError, KeyError):
        e = None
    if e:
        comp = e["competitions"][0]
        odds = (comp.get("odds") or [{}])[0]
        total, spread = odds.get("overUnder"), odds.get("spread")
        if total and key in TOTAL_BANDS:
            ctx["total"] = total
            lo, hi = TOTAL_BANDS[key]
            if total >= hi:
                ctx["flags"].append("high_total")
            elif total <= lo:
                ctx["flags"].append("low_total")
        if spread is not None and key in BLOWOUT_SPREAD:
            ctx["spread"] = abs(spread)
            if abs(spread) >= BLOWOUT_SPREAD[key]:
                ctx["flags"].append("blowout")
        venue = comp.get("venue") or {}
        if sport["group"] == "football" and venue.get("indoor") is False and c["prop"] in WIND_PROPS:
            w = kickoff_weather(venue, c["commence"])
            if w:
                ctx["wind"], ctx["precip"] = w["wind"], w["precip"]
                if w["wind"] >= WIND_MPH:
                    ctx["flags"].append("windy")
    if pid:
        try:
            games, _ = game_log(sport, pid)
        except (requests.RequestException, ValueError):
            games = []
        if games and c.get("commence"):
            try:
                rest = (parse_date(c["commence"]).astimezone().date() - parse_date(games[0]["date"]).astimezone().date()).days
                ctx["rest_days"] = rest
                if rest == 1 and sport["group"] in ("basketball", "hockey"):
                    ctx["flags"].append("b2b")
                elif rest >= 14 and sport["group"] != "football":    # returning players often have a minutes limit
                    ctx["flags"].append("returning")
            except ValueError:
                pass
        mins = minutes_values(games, sport["group"])
        if len(mins) >= 8:
            trend = (sum(mins[:5]) / 5) / (sum(mins) / len(mins))
            ctx["minutes_trend"] = round(trend, 2)
            if trend <= 0.85:
                ctx["flags"].append("minutes_down")
            elif trend >= 1.15:
                ctx["flags"].append("minutes_up")
    return ctx


def context_adjust(c, model):
    """Context nudge for a line: learned effects where there's enough data, starting guesses otherwise."""
    learned = (model or {}).get("ctx_learned", {}) if (model or {}).get("active") else {}
    total = 0.0
    for f in (c.get("ctx") or {}).get("flags", []):
        k = f"ctx:{f}|{c['side']}"
        total += learned[k] if k in learned else CTX_DEFAULTS.get(f, (0, 0))[0 if c["side"] == "MORE" else 1]
    return max(-CTX_CAP, min(CTX_CAP, total))


# ───────── 5. Where the picker wins: league / prop / side areas
COLD_MIN = 40        # graded lines before an area can be ruled out


def area_key(c):
    return f"{c['sport']}|{c['prop']}|{c['side']}"


def graded_rows(h):
    """Every graded line once per day (board when saved, else the picks)."""
    rows = []
    for dk, day in h["days"].items():
        for r in (day.get("board") or day["picks"]):
            if r.get("result") in ("hit", "miss") and r.get("final_p") is not None:
                rows.append({**r, "id": f"{dk}|{r['id']}"})
    return rows


def prop_key(c):
    return f"{c['sport']}|{c['prop']}|*"            # both sides of a prop together


def is_cold(c, cold):
    return area_key(c) in cold or prop_key(c) in cold


def areas_report(h):
    groups = {}
    for r in graded_rows(h):
        groups.setdefault(area_key(r), []).append(r)
        groups.setdefault(prop_key(r), []).append(r)
    out = []
    for k, rs in groups.items():
        sport, prop, side = k.split("|")
        rate = sum(r["result"] == "hit" for r in rs) / len(rs)
        exp = sum(r["final_p"] for r in rs) / len(rs)
        out.append({"key": k, "sport": sport, "prop": prop, "side": side, "n": len(rs), "hit_rate": rate, "expected": exp,
                    "cold": len(rs) >= COLD_MIN and rate < 0.5 and rate < exp - 0.05})
    return sorted(out, key=lambda a: -a["n"])


def cold_areas():
    return {a["key"] for a in areas_report(load_history()) if a["cold"]}


ODDS_CACHE_FILE = APP_DIR / "odds_cache.json"


def load_odds_cache():
    today = datetime.now().date().isoformat()
    try:
        c = json.loads(ODDS_CACHE_FILE.read_text())
    except (OSError, ValueError):
        c = {}
    return c if c.get("date") == today else {"date": today, "data": {}}


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
    cold = cold_areas()                      # don't spend credits on props it has stopped picking
    slate = [(prio, start, odds_key, sport, [m for m in markets if f"{sport}|{m[1]}|*" not in cold], e)
             for prio, start, odds_key, sport, markets, e in slate]
    slate = [item for item in slate if item[4]]
    for rank in range(max((len(item[4]) for item in slate), default=0)):
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
    paid = load_odds_cache()
    for sport, odds_key, e, (market_key, prop) in order:
        if spent >= DAILY_CREDIT_BUDGET or calls >= MAX_SCAN_CALLS:
            break
        cache_key = f"{e['id']}|{market_key}"
        if cache_key in paid["data"]:               # already bought today: reuse, 0 credits
            data, cost = paid["data"][cache_key], 0
        else:
            before = _quota["remaining"]
            data = odds_get(f"/sports/{odds_key}/events/{e['id']}/odds",
                            bookmakers=",".join(books + [PP_BOOK]),
                            markets=market_key, oddsFormat="american")
            calls += 1
            time.sleep(0.4)                          # stay well under the API's request-rate limit
            cost = (before - _quota["remaining"]) if before is not None and _quota["remaining"] is not None else 1
            if data:
                paid["data"][cache_key] = data
                ODDS_CACHE_FILE.write_text(json.dumps(paid))
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
    injuries = {}
    for k in {c["sport"] for c in candidates}:
        try:
            injuries[k] = injury_statuses(k)
        except Exception:
            injuries[k] = {}                         # no injury report today: don't block the scan
    for c in candidates:
        try:
            rep = analyze(c["sport"], c["player"], c["prop"], c["line"])
        except Exception as err:                     # one bad line must never sink the scan
            print(f"  skipped history for {c['player']} {c['prop']}: {type(err).__name__}")
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
        try:
            c["ctx"] = game_context(c, rep)
        except Exception:
            c["ctx"] = {"flags": []}
        c["final_p"] = apply_model(c, model)
    board = [{
        "id": f"line|{c['sport']}|{c['player']}|{c['prop']}|{c['line']:g}".lower(),
        "sport": c["sport"], "player": c["player"], "prop": c["prop"], "line": c["line"], "side": c["side"],
        "market_p": c["market_p"], "hist_p": c["hist_p"], "final_p": c["final_p"], "tier": c["tier"],
        "commence": c.get("commence"), "game": c.get("game"), "injury": c["injury"],
        "book_line": c.get("book_line"), "n_books": c.get("n_books"), "ctx": c.get("ctx"), "ud_line": c.get("ud_line"),
        "espn_id": ((c.get("report") or {}).get("player") or {}).get("id"),
    } for c in candidates]

    # 5. Build the slip: best blended probability, 1 per player, max 2 per game
    candidates.sort(key=lambda c: -c["final_p"])
    picks, players, per_game, game_cap = [], set(), {}, max_per_game()
    cold = cold_areas()
    for c in candidates:
        if c["final_p"] < 0.5:
            break                      # never fill the slip with a pick it expects to lose
        if c["injury"]:
            continue                   # listed on the injury report: skip
        if is_cold(c, cold):
            continue                   # an area with a proven losing record: skip
        if c["player"] in players or per_game.get(c["game"], 0) >= game_cap:
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
        "entry": entry, "books_used": len([b for b in books if b not in DFS_COMPARE]), "injured_skipped": sum(1 for c in candidates if c["injury"]),
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
    p += context_adjust(c, model)
    return min(max(p, 0.01), 0.99)


def clamp(x):
    return max(-MAX_ADJ, min(MAX_ADJ, x))


ENTRY_PRIOR_DAYS  = 30    # days of results the default entry caution is worth
ENTRY_MIN_DAYS    = 10    # graded days before entry caution is adjusted
ENTRY_RANGE       = (0.5, 0.9)   # never trim estimates less than 10% or more than 50%
SAME_GAME_MIN     = 40    # same-game pick pairs before the per-game limit can change


def payout_mult(kind, n, hits):
    if n < 2:
        return 1.0                                       # refunded
    if kind == "flex" and n >= 3:
        return PAYOUT_TABLES["flex"][n].get(hits, 0)
    return PAYOUT_TABLES["power"].get(n, {}).get(hits, 0)


def cash_prob(probs, kind):
    dist = [1.0]
    for q in probs:
        nxt = [0.0] * (len(dist) + 1)
        for i, v in enumerate(dist):
            nxt[i] += v * (1 - q)
            nxt[i + 1] += v * q
        dist = nxt
    return sum(v for h, v in enumerate(dist) if payout_mult(kind, len(probs), h) > 1)


def learn_entries(h):
    """Replay every entry size the picker could have suggested each day and compare how often it
    predicted the slip would cash with how often it actually did. If slips cash less than predicted,
    entry choice gets more cautious (and less cautious if they cash more)."""
    sims, days = [], 0
    for day in h["days"].values():
        legs = [p for p in day["picks"] if p.get("final_p") is not None]
        if len(legs) < 2 or any(not p.get("result") for p in legs):
            continue
        days += 1
        for n in range(2, min(len(legs), 6) + 1):
            for kind in ("power", "flex"):
                if (kind == "power" and n > MAX_POWER_LEGS) or (kind == "flex" and n < 3):
                    continue
                live = [p for p in legs[:n] if p["result"] in ("hit", "miss")]
                if len(live) < 2:
                    continue
                hits = sum(p["result"] == "hit" for p in live)
                sims.append(([p["final_p"] for p in live], kind, payout_mult(kind, len(live), hits) > 1))
    n = len(sims)

    def brier(shrink):
        return sum((cash_prob([0.5 + (q - 0.5) * shrink for q in probs], kind) - cashed) ** 2
                   for probs, kind, cashed in sims) / n

    fit = min((x / 100 for x in range(40, 101, 5)), key=brier) if n >= 10 else ENTRY_SHRINK
    # a day's replayed slips share the same picks, so evidence is counted in days, not slips
    shrink = (days * fit + ENTRY_PRIOR_DAYS * ENTRY_SHRINK) / (days + ENTRY_PRIOR_DAYS)
    shrink = min(max(shrink, ENTRY_RANGE[0]), ENTRY_RANGE[1])
    active = days >= ENTRY_MIN_DAYS
    used = shrink if active else ENTRY_SHRINK
    return {
        "active": active, "n": n, "days": days, "min_days": ENTRY_MIN_DAYS, "fit_shrink": fit,
        "shrink": round(used, 3),
        "predicted_cash": sum(cash_prob([0.5 + (q - 0.5) * used for q in pr], k) for pr, k, _ in sims) / n if n else None,
        "actual_cash": sum(c for _, _, c in sims) / n if n else None,
    }


def learn_same_game(h):
    """Do picks from the same game miss together more than chance? If so, allow only one per game."""
    pairs, expected, observed = 0, 0.0, 0
    for day in h["days"].values():
        rows = [r for r in (day.get("board") or day["picks"])
                if r.get("result") in ("hit", "miss") and r.get("final_p") is not None and r.get("game")]
        by_game = {}
        for r in rows:
            by_game.setdefault(r["game"], []).append(r)
        for rs in by_game.values():
            for i in range(len(rs)):
                for j in range(i + 1, len(rs)):
                    pairs += 1
                    expected += (1 - rs[i]["final_p"]) * (1 - rs[j]["final_p"])
                    observed += rs[i]["result"] == "miss" and rs[j]["result"] == "miss"
    active = pairs >= SAME_GAME_MIN
    excess = (observed - expected) / pairs if pairs else 0.0
    return {"active": active, "pairs": pairs, "min": SAME_GAME_MIN,
            "observed_both_miss": observed / pairs if pairs else None,
            "expected_both_miss": expected / pairs if pairs else None,
            "max_per_game": 1 if active and excess > 0.04 else MAX_PER_GAME}


def entry_shrink():
    e = load_model().get("entry") or {}
    return e.get("shrink", ENTRY_SHRINK) if e.get("active") else ENTRY_SHRINK


def max_per_game():
    g = load_model().get("same_game") or {}
    return g.get("max_per_game", MAX_PER_GAME) if g.get("active") else MAX_PER_GAME


def fit_model(h):
    """Learn from every graded line: blend weight, overall calibration, and group adjustments.
    Every estimate is shrunk toward 'no change' so small samples can't swing the picker."""
    rows = []
    for dk, day in h["days"].items():
        for r in (day.get("board") or day["picks"]):           # older days have no board: use the picks
            if r.get("result") in ("hit", "miss") and r.get("market_p") is not None:
                rows.append({**r, "id": f"{dk}|{r['id']}"})    # same player/prop on another day is a new result
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

    # Context effects (blowout, back-to-back, minutes, totals, wind): learned on what's left after the rest
    ctx_groups = {}
    for r in rows:
        for f in (r.get("ctx") or {}).get("flags", []):
            ctx_groups.setdefault(f"ctx:{f}|{r['side']}", []).append(r)
    ctx_learned, ctx_report = {}, []
    for k, rs in ctx_groups.items():
        resid = sum(y[r["id"]] - pred[r["id"]] - bias - sum(segments.get(k2, 0) for k2 in segment_keys(r)) for r in rs)
        adj = clamp(resid / (len(rs) + SEG_STRENGTH))
        if len(rs) >= SEG_MIN:
            ctx_learned[k] = round(adj, 4)
        ctx_report.append({"key": k, "n": len(rs), "actual": sum(y[r["id"]] for r in rs) / len(rs),
                           "expected": sum(pred[r["id"]] for r in rs) / len(rs), "adj": ctx_learned.get(k)})
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
        "entry": learn_entries(h), "same_game": learn_same_game(h),
        "ctx_learned": ctx_learned if active else {}, "ctx_groups": sorted(ctx_report, key=lambda g: -g["n"]),
        "updated": datetime.now().isoformat(timespec="minutes"),
    }
    MODEL_FILE.write_text(json.dumps(model, indent=1))
    return model


# ───────── How every suggestion did ─────────
SCORE_STAKE = 10     # replayed at $10 per slip


def entry_label(kind, n):
    return f"{n}-pick {'Power' if kind == 'power' else 'Flex'}"


def entry_return(legs, kind):
    """What one slip paid, as a multiple of its stake. Voids and pushes drop out, as on PrizePicks."""
    live = [p for p in legs if p.get("result") in ("hit", "miss")]
    return payout_mult(kind, len(live), sum(p["result"] == "hit" for p in live))


def payout_dist(probs, kind):
    dist = [1.0]
    for q in probs:
        nxt = [0.0] * (len(dist) + 1)
        for i, v in enumerate(dist):
            nxt[i] += v * (1 - q)
            nxt[i + 1] += v * q
        dist = nxt
    out = {}
    for h, v in enumerate(dist):
        m = payout_mult(kind, len(probs), h)
        out[m] = out.get(m, 0) + v
    return out


def split_plans(picks, shrink):
    """The split suggestions the Slip tab shows (same rules as the page): best of each shape, positive value only."""
    picks = picks[:6]
    m = len(picks)
    if m < 4:
        return []
    cautious = {p["id"]: 0.5 + (p["final_p"] - 0.5) * shrink for p in picks}

    def score(entries):
        total = {0.0: 1.0}
        for kind, legs in entries:
            d = payout_dist([cautious[p["id"]] for p in legs], kind)
            total = _combine(total, d)
        k = len(entries)
        ahead = sum(v for t, v in total.items() if t > k + 1e-9)
        ev = sum(t * v for t, v in total.items()) / k - 1
        return {"entries": entries, "ahead": ahead, "ev": ev,
                "label": " + ".join(entry_label(kind, len(legs)) for kind, legs in entries)}

    kinds_for = lambda n: ["power"] if n == 2 else ["power", "flex"] if n == 3 else ["flex"]
    plans = []
    for size in range(4, m + 1):
        for mask in range(1, (1 << size) - 1):
            if not mask & 1:
                continue
            a = [picks[i] for i in range(size) if mask >> i & 1]
            b = [picks[i] for i in range(size) if not mask >> i & 1]
            if len(a) < 2 or len(b) < 2:
                continue
            for ka in kinds_for(len(a)):
                for kb in kinds_for(len(b)):
                    plans.append(score([(ka, a), (kb, b)]))
    if m == 6:
        def pairings(rest):
            if not rest:
                return [[]]
            first, others = rest[0], rest[1:]
            return [[(first, o)] + tail for i, o in enumerate(others) for tail in pairings(others[:i] + others[i + 1:])]
        for groups in pairings(picks):
            plans.append(score([("power", list(g)) for g in groups]))
    plans = sorted((pl for pl in plans if pl["ev"] >= 0), key=lambda pl: (-pl["ahead"], -pl["ev"]))
    seen, out = set(), []
    for pl in plans:
        if pl["label"] not in seen:
            seen.add(pl["label"])
            out.append(pl)
    return out[:3]


def _combine(a, b):
    out = {}
    for x, px in a.items():
        for y, py in b.items():
            out[x + y] = out.get(x + y, 0) + px * py
    return out


def suggestions_report(h):
    """Replay every slip the app suggested each finished day, at $10 each, played or not."""
    shrink = entry_shrink()
    rows = {}

    def add(label, kind, mults):
        r = rows.setdefault(label, {"label": label, "type": kind, "days": 0, "cashed": 0, "staked": 0.0, "returned": 0.0, "sat_out": 0})
        r["days"] += 1
        r["staked"] += SCORE_STAKE * len(mults)
        r["returned"] += SCORE_STAKE * sum(mults)
        r["cashed"] += sum(mults) > len(mults)

    for dk in sorted(h["days"]):
        day = h["days"][dk]
        picks = [p for p in day["picks"] if p.get("final_p") is not None]
        if len(picks) < 2 or any(not p.get("result") for p in picks):
            continue
        for n in range(2, min(6, len(picks)) + 1):
            for kind in ("power", "flex"):
                if (kind == "power" and n > MAX_POWER_LEGS) or (kind == "flex" and n < 3):
                    continue
                add(entry_label(kind, n), "entry", [entry_return(picks[:n], kind)])
        for pl in split_plans(picks, shrink):
            add("Split: " + pl["label"], "split", [entry_return(legs, kind) for kind, legs in pl["entries"]])
        e = day.get("entry")
        if e and e.get("kind") and e.get("play"):
            add("Picker's daily suggestion", "suggested", [entry_return([p for p in day["picks"] if p["id"] in e["ids"]], e["kind"])])
        elif e is not None:
            rows.setdefault("Picker's daily suggestion", {"label": "Picker's daily suggestion", "type": "suggested", "days": 0,
                                                          "cashed": 0, "staked": 0.0, "returned": 0.0, "sat_out": 0})["sat_out"] += 1
    out = []
    for r in rows.values():
        r["pl"] = round(r["returned"] - r["staked"], 2)
        r["roi"] = r["pl"] / r["staked"] if r["staked"] else None
        out.append(r)
    order = {"suggested": 0, "entry": 1, "split": 2}
    return sorted(out, key=lambda r: (order[r["type"]], -r["pl"] if r["type"] == "split" else r["label"]))


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
    cold = cold_areas()
    pool = sorted((b for b in d["board"] if not b.get("injury") and not b.get("pulled") and b["final_p"] >= 0.5
                   and not is_cold(b, cold)), key=lambda b: -b["final_p"])
    picks, players, per_game, game_cap = [], set(), {}, max_per_game()
    for b in pool:
        if b["player"] in players or per_game.get(b["game"], 0) >= game_cap:
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


# ───────── Injury news watcher (ESPN, free) ─────────
ALERTS_FILE      = APP_DIR / "alerts.json"
INJURY_LEAGUES   = ["NBA", "WNBA", "NFL", "NHL"]       # leagues ESPN publishes injury reports for
OUT_STATUSES     = {"out", "doubtful"}
# A ruled-out player matters if he averages at least one of these this season
NOTABLE          = {"basketball": [("points", 12)], "hockey": [("points", 0.6), ("shotsTotal", 2.5)],
                    "football": [("passingYards", 150), ("rushingYards", 45), ("receivingYards", 40)]}
# Teammate stats compared with/without him, as (game-log stat, PrizePicks prop, minimum boost worth showing)
BOOST_STATS      = {"basketball": [("points", "Points", 1.5), ("totalRebounds", "Rebounds", 1.0), ("assists", "Assists", 1.0)],
                    "hockey": [("shotsTotal", "Shots on Goal", 0.4), ("points", "Points", 0.15)],
                    "football": [("receivingYards", "Receiving Yards", 8), ("receptions", "Receptions", 0.8),
                                 ("rushingYards", "Rush Yards", 10)]}
MIN_SPLIT_GAMES  = 3


def load_alerts():
    try:
        return json.loads(ALERTS_FILE.read_text())
    except (OSError, ValueError):
        return {"alerts": [], "seen": []}


def season_values(sport, pid, stat):
    """This season's values for one stat (newest first) and the event ids he played in."""
    try:
        games, _ = game_log(sport, pid)
    except (requests.RequestException, ValueError):
        return [], set()
    vals, events = [], set()
    for g in games:
        try:
            vals.append(float(g["row"][stat]))
            events.add(g["event_id"])
        except (KeyError, ValueError, TypeError):
            pass
    return vals, events


def is_notable(sport_key, pid):
    group = SPORT_BY_KEY[sport_key]["group"]
    for stat, threshold in NOTABLE.get(group, []):
        vals, _ = season_values(SPORT_BY_KEY[sport_key], pid, stat)
        if vals and sum(vals) / len(vals) >= threshold:
            return True
    return False


def teammate_boosts(sport_key, team_id, out_pid, skip_ids):
    """Teammates whose numbers go up in games the ruled-out player missed this season."""
    sport = SPORT_BY_KEY[sport_key]
    s_, l_ = sport["path"]
    stats = BOOST_STATS.get(sport["group"], [])
    try:
        roster = get_json(f"{ESPN_SITE}/site/v2/sports/{s_}/{l_}/teams/{team_id}/roster").get("athletes", [])
    except (requests.RequestException, ValueError):
        return [], []
    if roster and "items" in roster[0]:                 # football rosters come grouped by unit
        roster = [a for grp in roster for a in grp.get("items", [])]
    try:
        out_games, _ = game_log(sport, out_pid)
    except (requests.RequestException, ValueError):
        out_games = []
    out_events = {g["event_id"] for g in out_games}
    boosts, leaders = [], []
    for a in roster:
        aid = str(a.get("id", ""))
        if not aid or aid == out_pid or aid in skip_ids:
            continue
        try:
            games, _ = game_log(sport, aid)
        except (requests.RequestException, ValueError):
            continue
        if not games:
            continue
        for stat, prop, min_boost in stats:
            with_, without = [], []
            for g in games:
                try:
                    v = float(g["row"][stat])
                except (KeyError, ValueError, TypeError):
                    continue
                (with_ if g["event_id"] in out_events else without).append(v)
            if not with_ and not without:
                continue
            avg_all = sum(with_ + without) / len(with_ + without)
            leaders.append({"player": a.get("displayName", ""), "espn_id": aid, "prop": prop, "avg": round(avg_all, 1)})
            if len(with_) >= MIN_SPLIT_GAMES and len(without) >= MIN_SPLIT_GAMES:
                aw, ao = sum(with_) / len(with_), sum(without) / len(without)
                if ao - aw >= min_boost:
                    boosts.append({"player": a.get("displayName", ""), "espn_id": aid, "prop": prop,
                                   "with": round(aw, 1), "without": round(ao, 1), "games_without": len(without),
                                   "boost": round(ao - aw, 1)})
    boosts.sort(key=lambda b: -b["boost"] / max(b["with"], 1))
    first_prop = stats[0][1] if stats else None
    leaders = sorted((x for x in leaders if x["prop"] == first_prop), key=lambda x: -x["avg"])[:3]
    return boosts[:4], leaders


def todays_games(sport_key):
    """{team_id: {opp, start}} for games today (Eastern) that haven't started."""
    s_, l_ = SPORT_BY_KEY[sport_key]["path"]
    try:
        sb = get_json(f"{ESPN_SITE}/site/v2/sports/{s_}/{l_}/scoreboard", _ttl=300,
                      dates=datetime.now().strftime("%Y%m%d"))
    except (requests.RequestException, ValueError):
        return {}
    out = {}
    for e in sb.get("events", []):
        try:
            if e["status"]["type"]["state"] != "pre":
                continue
            teams = e["competitions"][0]["competitors"]
        except (KeyError, IndexError):
            continue
        for c in teams:
            other = next(o for o in teams if o is not c)
            out[str(c["team"]["id"])] = {"opp": other["team"].get("abbreviation", ""), "home": c.get("homeAway") == "home",
                                         "start": e.get("date")}
    return out


def check_injuries():
    """New 'Out'/'Doubtful' news today for notable players whose team still plays today -> alert with
    the teammates who gain the most without him. Uses ESPN only, so it never spends Odds API credits."""
    state = load_alerts()
    seen = set(state.get("seen", []))
    today = datetime.now().date().isoformat()
    daily = load_daily() or {}
    slip_players = {normalize(p["player"]) for p in daily.get("picks", [])}
    new = []
    for key in INJURY_LEAGUES:
        playing = todays_games(key)
        if not playing:
            continue
        s_, l_ = SPORT_BY_KEY[key]["path"]
        try:
            report = get_json(f"{ESPN_SITE}/site/v2/sports/{s_}/{l_}/injuries", _ttl=300)
        except (requests.RequestException, ValueError):
            continue
        out_ids = {}
        for team in report.get("injuries", []):
            for i in team.get("injuries", []):
                if (i.get("status") or "").lower() in OUT_STATUSES:
                    m = re.search(r"/id/(\d+)", ((i.get("athlete") or {}).get("links") or [{}])[0].get("href", ""))
                    if m:
                        out_ids[m.group(1)] = True
        for team in report.get("injuries", []):
            team_id = str(team.get("id", ""))
            if team_id not in playing:
                continue
            for i in team.get("injuries", []):
                status = (i.get("status") or "")
                if status.lower() not in OUT_STATUSES:
                    continue
                try:
                    updated = parse_date(i["date"]).astimezone().date().isoformat()
                except (KeyError, ValueError):
                    continue
                a = i.get("athlete") or {}
                m = re.search(r"/id/(\d+)", ((a.get("links") or [{}])[0]).get("href", ""))
                if updated != today or not m:
                    continue
                pid, tag = m.group(1), f"{today}|{m.group(1)}|{status}"
                if tag in seen:
                    continue
                seen.add(tag)
                if not is_notable(key, pid):
                    continue
                boosts, leaders = teammate_boosts(key, team_id, pid, set(out_ids))
                g = playing[team_id]
                new.append({
                    "id": tag, "date": today, "time": datetime.now().isoformat(timespec="minutes"), "league": key,
                    "player": a.get("displayName", ""), "team": (a.get("team") or {}).get("abbreviation", "") or team.get("displayName", ""),
                    "status": status, "note": i.get("shortComment", ""),
                    "game": f"{'vs' if g['home'] else '@'} {g['opp']}", "start": g["start"],
                    "in_slip": normalize(a.get("displayName", "")) in slip_players,
                    "teammates": boosts, "leaders": [] if boosts else leaders,
                })
    keep_from = (datetime.now() - timedelta(days=2)).date().isoformat()
    state["alerts"] = [x for x in new + state.get("alerts", []) if x["date"] >= keep_from]
    state["seen"] = sorted(t for t in seen if t[:10] >= keep_from)
    ALERTS_FILE.write_text(json.dumps(state))
    return new


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
        return jsonify({**payload, "next_scan": nxt.isoformat(timespec="minutes") if nxt else None,
                        "entry_shrink": entry_shrink(), "max_per_game": max_per_game()})

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


@app.post("/api/grade")
def api_grade():
    """Results so far for saved-slip legs: hit / miss / push / void once final, live numbers before."""
    legs = ((request.get_json(force=True, silent=True) or {}).get("legs") or [])[:40]
    out = {}
    for leg in legs:
        try:
            live = live_for_pick(dict(leg))
        except (requests.RequestException, ValueError, KeyError):
            live = None
        if not live:
            continue
        if live["state"] == "post" and live.get("value") is not None:
            v, line = live["value"], leg["line"]
            out[leg["id"]] = {"result": "push" if v == line else "hit" if (v > line) == (leg["side"] == "MORE") else "miss", "actual": v}
        elif live["state"] == "post" and live.get("note") == "Did not play":
            out[leg["id"]] = {"result": "void", "actual": None}
        else:
            out[leg["id"]] = {"state": live["state"], "value": live.get("value"), "detail": live.get("detail")}
    return jsonify(out)


@app.get("/api/alerts")
def api_alerts():
    today = datetime.now().date().isoformat()
    return jsonify({"alerts": [a for a in load_alerts().get("alerts", []) if a["date"] == today]})


@app.get("/api/history")
def api_history():
    """Grades finished games (ESPN, free), then returns every saved slip plus the overall record."""
    grade_history()
    h = load_history()
    days = []
    for key in sorted(h["days"], reverse=True):
        day = h["days"][key]
        days.append({**day, "slip": slip_result(day["picks"], day.get("entry"))})
    return jsonify({"days": days, "summary": history_summary(h), "model": fit_model(h), "areas": areas_report(h),
                    "suggestions": suggestions_report(h)})


@app.get("/")
def index():
    config = {
        "budget": DAILY_CREDIT_BUDGET, "min_ev": MIN_ENTRY_EV, "shrink": ENTRY_SHRINK, "max_power_legs": MAX_POWER_LEGS,
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
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Daily Slip</title>
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Daily Slip">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="theme-color" content="#0a0f1d">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #0a0f1d; --surface: #0f1627; --surface-2: #141c30; --surface-3: #1a2440;
    --border: rgba(148, 163, 184, 0.12); --border-strong: rgba(148, 163, 184, 0.22);
    --text: #e6e9ef; --muted: #8b94a7; --faint: #5c6578;
    --accent: #8fb3ff; --pos: #3ecf8e; --neg: #f07178; --warn: #e5c07b;
    --pos-bg: rgba(62, 207, 142, 0.12); --neg-bg: rgba(240, 113, 120, 0.12);
    --radius: 14px; --nav-h: 64px;
  }
  * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }
  html { color-scheme: dark; }
  body { margin: 0; background: var(--bg); color: var(--text); font: 14px/1.5 Inter, system-ui, -apple-system, sans-serif;
         font-feature-settings: "tnum" 1, "cv11" 1; -webkit-font-smoothing: antialiased; }
  body::before { content: ""; position: fixed; inset: 0 0 auto 0; height: 420px; pointer-events: none; z-index: 0;
    background: radial-gradient(600px 260px at 85% -60px, rgba(143, 179, 255, 0.16), transparent 70%),
                radial-gradient(500px 220px at 0% -40px, rgba(62, 207, 142, 0.08), transparent 70%); }
  button, input, select { font: inherit; color: inherit; }
  button { cursor: pointer; }
  .pos { color: var(--pos); } .neg { color: var(--neg); } .muted { color: var(--muted); } .faint { color: var(--faint); }

  /* Header & navigation */
  header.top { position: sticky; top: 0; z-index: 20; background: rgba(10, 15, 29, 0.82); backdrop-filter: blur(14px);
    -webkit-backdrop-filter: blur(14px); border-bottom: 1px solid var(--border); padding-top: env(safe-area-inset-top); }
  .top-inner { max-width: 880px; margin: 0 auto; padding: 12px 18px; display: flex; align-items: center; gap: 14px; }
  .brand { display: flex; align-items: center; gap: 10px; min-width: 0; }
  .brand svg { flex: none; border-radius: 9px; }
  .brand h1 { margin: 0; font-size: 16px; font-weight: 700; letter-spacing: -0.01em; }
  .brand .date { color: var(--faint); font-size: 12px; white-space: nowrap; }
  .top-right { margin-left: auto; display: flex; align-items: center; gap: 10px; }
  .status-pill { color: var(--muted); font-size: 12px; white-space: nowrap; }
  .status-pill b { color: var(--text); font-weight: 600; }
  nav.tabs { display: flex; gap: 2px; background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 3px; }
  nav.tabs button { border: 0; background: none; color: var(--muted); padding: 6px 14px; border-radius: 8px; font-weight: 500; font-size: 13px;
    display: flex; align-items: center; gap: 6px; }
  nav.tabs button.on { background: var(--surface-3); color: var(--text); }
  nav.tabs svg { width: 16px; height: 16px; }
  .badge { min-width: 18px; height: 18px; padding: 0 5px; border-radius: 9px; background: var(--accent); color: var(--bg);
    font-size: 11px; font-weight: 700; display: inline-grid; place-items: center; }
  .badge[hidden] { display: none; }
  .icon-btn { border: 1px solid var(--border-strong); background: var(--surface); border-radius: 9px; padding: 6px 10px; font-size: 12.5px; color: var(--muted); }
  @media (max-width: 720px) {
    /* a blurred header would trap the fixed tab bar inside it, so keep it solid on phones */
    header.top { backdrop-filter: none; -webkit-backdrop-filter: none; background: rgba(10, 15, 29, 0.96); }
    nav.tabs { position: fixed; left: 0; right: 0; bottom: 0; z-index: 30; border-radius: 0; border: 0; border-top: 1px solid var(--border);
      background: rgba(12, 18, 34, 0.92); backdrop-filter: blur(16px); -webkit-backdrop-filter: blur(16px);
      padding: 6px 8px calc(6px + env(safe-area-inset-bottom)); justify-content: space-around; }
    nav.tabs button { flex-direction: column; gap: 2px; font-size: 10.5px; padding: 6px 4px; flex: 1; position: relative; }
    nav.tabs button.on { background: none; color: var(--accent); }
    nav.tabs svg { width: 22px; height: 22px; }
    nav.tabs .badge { position: absolute; top: 2px; left: calc(50% + 6px); }
    .status-pill { display: none; }
    main { padding-bottom: calc(var(--nav-h) + env(safe-area-inset-bottom) + 20px) !important; }
  }
  main { position: relative; z-index: 1; max-width: 880px; margin: 0 auto; padding: 20px 18px 40px; }
  .view[hidden] { display: none; }

  /* Shared pieces */
  .card { background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); }
  .h2 { font-size: 20px; font-weight: 700; margin: 0 0 4px; letter-spacing: -0.015em; }
  .sub { color: var(--muted); font-size: 13px; margin: 0 0 14px; }
  .section-label { font-size: 11px; font-weight: 600; color: var(--faint); text-transform: uppercase; letter-spacing: 0.08em; margin: 22px 0 8px; }
  .chip { display: inline-flex; align-items: center; gap: 6px; padding: 4px 11px; border: 1px solid var(--border-strong); border-radius: 999px;
    color: var(--muted); font-size: 12.5px; background: none; }
  .chip.on { color: var(--bg); background: var(--text); border-color: var(--text); }
  .chips { display: flex; gap: 6px; overflow-x: auto; padding-bottom: 2px; scrollbar-width: none; }
  .chips::-webkit-scrollbar { display: none; }
  .side { font-size: 11.5px; font-weight: 700; letter-spacing: 0.05em; padding: 4px 9px; border-radius: 7px; white-space: nowrap; }
  .side.more { color: var(--pos); background: var(--pos-bg); }
  .side.less { color: var(--neg); background: var(--neg-bg); }
  .btn { border: 1px solid var(--border-strong); background: var(--surface-2); border-radius: 10px; padding: 9px 15px; font-weight: 600; font-size: 13.5px; }
  .btn:hover { border-color: var(--accent); }
  .btn-primary { background: var(--accent); border-color: var(--accent); color: var(--bg); }
  .btn-primary:hover { filter: brightness(1.07); }
  .btn:disabled { opacity: .5; cursor: default; }
  .link { background: none; border: 0; padding: 0; color: var(--muted); font-size: 12.5px; text-decoration: underline; text-underline-offset: 3px; }
  .spinner { width: 14px; height: 14px; border: 2px solid var(--border-strong); border-top-color: var(--accent); border-radius: 50%;
    display: inline-block; animation: spin .8s linear infinite; vertical-align: -2px; }
  @keyframes spin { to { transform: rotate(360deg); } }
  .empty { padding: 30px 20px; text-align: center; color: var(--muted); }
  .empty strong { display: block; color: var(--text); font-size: 15px; margin-bottom: 4px; }
  .notice { padding: 11px 14px; margin-bottom: 12px; font-size: 13px; border-color: rgba(143, 179, 255, 0.35); }
  .footnote { color: var(--faint); font-size: 12px; margin-top: 14px; }
  .res { font-size: 11px; font-weight: 700; letter-spacing: 0.05em; padding: 3px 8px; border-radius: 6px; white-space: nowrap; }
  .res.hit { color: var(--pos); background: var(--pos-bg); } .res.miss { color: var(--neg); background: var(--neg-bg); }
  .res.push, .res.void, .res.pending { color: var(--muted); background: rgba(148, 163, 184, 0.12); }

  /* Injury alerts */
  .alert { padding: 14px; margin-bottom: 12px; border-color: rgba(240, 113, 120, 0.35); }
  .alert-head { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
  .alert-head .out { color: var(--neg); background: var(--neg-bg); font-size: 11px; font-weight: 800; letter-spacing: 0.05em; padding: 3px 8px; border-radius: 6px; }
  .alert-head b { font-size: 15px; }
  .alert .note { color: var(--muted); font-size: 12.5px; margin: 6px 0 8px; }
  .alert-row { display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: 10px; align-items: center; padding: 8px 0; border-top: 1px solid var(--border); font-size: 13px; }
  .alert-row .who { font-weight: 600; } .alert-row .why { color: var(--muted); font-size: 12px; margin: 0; }
  .alert-row .btn { padding: 6px 11px; font-size: 12.5px; }

  /* Hero: today's best play */
  .hero { position: relative; padding: 18px; border-radius: 18px; overflow: hidden; margin-bottom: 18px;
    background: linear-gradient(160deg, #17213a, #0f1627 60%); border: 1px solid transparent;
    background-clip: padding-box; }
  .hero::before { content: ""; position: absolute; inset: 0; border-radius: 18px; padding: 1px; pointer-events: none;
    background: linear-gradient(135deg, rgba(143, 179, 255, 0.7), rgba(62, 207, 142, 0.6) 55%, rgba(143, 179, 255, 0.1));
    -webkit-mask: linear-gradient(#000 0 0) content-box, linear-gradient(#000 0 0); -webkit-mask-composite: xor; mask-composite: exclude; }
  .hero::after { content: ""; position: absolute; width: 260px; height: 260px; right: -80px; top: -120px; pointer-events: none;
    background: radial-gradient(circle, rgba(62, 207, 142, 0.25), transparent 65%); }
  .hero .eyebrow { font-size: 11px; font-weight: 700; letter-spacing: 0.14em; text-transform: uppercase; color: var(--accent); }
  .hero .title { font-size: 28px; font-weight: 800; letter-spacing: -0.02em; margin: 4px 0 2px; }
  .hero .title small { font-size: 15px; font-weight: 600; color: var(--muted); margin-left: 6px; }
  .hero-stats { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 10px; margin: 14px 0 16px; position: relative; z-index: 1; }
  .hero-stats div { background: rgba(10, 15, 29, 0.45); border: 1px solid var(--border); border-radius: 12px; padding: 10px 12px; }
  .hero-stats dt { color: var(--faint); font-size: 11px; }
  .hero-stats dd { margin: 2px 0 0; font-size: 19px; font-weight: 700; }
  .hero .actions { display: flex; gap: 8px; flex-wrap: wrap; position: relative; z-index: 1; }

  /* Pick rows */
  .picks { display: flex; flex-direction: column; gap: 8px; }
  .pick { padding: 0; overflow: hidden; transition: border-color .12s; }
  .pick.in-slip { border-color: rgba(143, 179, 255, 0.45); }
  .pick-row { display: grid; grid-template-columns: minmax(0, 1fr) auto auto 34px; gap: 12px; align-items: center; padding: 13px 14px; cursor: pointer; }
  .pick-row .name { font-weight: 600; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .pick-row .meta { color: var(--muted); font-size: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .pick-row .line { text-align: right; line-height: 1.2; }
  .pick-row .line .p { color: var(--muted); font-size: 11.5px; }
  .pick-row .line .v { font-size: 17px; font-weight: 700; }
  .pick-row .est { font-size: 11px; color: var(--faint); text-align: center; margin-top: 3px; }
  .add { width: 30px; height: 30px; border-radius: 50%; border: 1.5px solid var(--border-strong); background: none; display: grid; place-items: center;
    color: var(--muted); font-size: 17px; line-height: 1; padding: 0; }
  .in-slip .add { background: var(--accent); border-color: var(--accent); color: var(--bg); }
  .pick-live { padding: 0 14px 12px; }
  .details { border-top: 1px solid var(--border); padding: 12px 14px 14px; display: none; }
  .open .details { display: block; }
  .stats { display: grid; grid-template-columns: repeat(5, minmax(0, 1fr)); gap: 8px; margin: 0 0 10px; }
  .stats dt { color: var(--faint); font-size: 11px; }
  .stats dd { margin: 0; font-size: 13px; font-weight: 600; }
  .why { color: var(--muted); font-size: 12.5px; margin: 8px 0 0; }
  @media (max-width: 520px) { .stats { grid-template-columns: repeat(3, minmax(0, 1fr)); } .pick-row { gap: 10px; padding: 12px; } }

  /* Live strip */
  .live { display: grid; grid-template-columns: auto minmax(0, 1fr) auto; gap: 12px; align-items: center; padding: 8px 10px;
    border: 1px solid var(--border); border-radius: 10px; background: var(--bg); font-size: 12px; }
  .live .clock { color: var(--muted); white-space: nowrap; display: flex; align-items: center; gap: 6px; }
  .live .dot { width: 7px; height: 7px; border-radius: 50%; background: var(--neg); animation: pulse 1.6s ease-in-out infinite; }
  .live.final .dot { display: none; }
  @keyframes pulse { 50% { opacity: .3; } }
  .live .bar { position: relative; height: 6px; border-radius: 3px; background: var(--surface-3); }
  .live .bar span { position: absolute; left: 0; top: 0; bottom: 0; border-radius: 3px; }
  .live .bar i { position: absolute; top: -4px; bottom: -4px; width: 2px; background: var(--muted); border-radius: 1px; }
  .live .now { white-space: nowrap; } .live .now b { font-size: 13.5px; } .live .now small { color: var(--muted); margin-left: 5px; }
  @media (max-width: 520px) { .live { grid-template-columns: minmax(0, 1fr) auto; } .live .bar { grid-column: 1 / -1; grid-row: 2; } }

  /* Line tools */
  .line-tools { margin-top: 10px; font-size: 12.5px; }
  .line-form { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; margin-top: 6px; }
  .line-form input { width: 90px; background: var(--bg); border: 1px solid var(--border-strong); border-radius: 9px; padding: 7px 9px; }
  .line-form .btn { padding: 7px 12px; font-size: 12.5px; }

  /* Slip view */
  .options { display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 10px; padding-top: 8px; }
  .option { text-align: left; padding: 12px; border-radius: 14px; border: 1px solid var(--border); background: var(--surface); position: relative; }
  .option.on { border-color: var(--accent); background: var(--surface-2); box-shadow: 0 0 0 1px var(--accent) inset; }
  .option .lbl { font-weight: 700; font-size: 14px; }
  .option .best { position: absolute; top: -8px; right: 10px; background: linear-gradient(90deg, var(--accent), var(--pos)); color: var(--bg);
    font-size: 10px; font-weight: 800; letter-spacing: 0.06em; padding: 2px 7px; border-radius: 6px; }
  .option dl { margin: 8px 0 0; display: grid; gap: 3px; font-size: 12px; }
  .option dl div { display: flex; justify-content: space-between; gap: 8px; }
  .option dt { color: var(--faint); } .option dd { margin: 0; font-weight: 600; }
  .slip-grid { display: grid; grid-template-columns: minmax(0, 1fr) 300px; gap: 16px; align-items: start; }
  @media (max-width: 720px) { .slip-grid { grid-template-columns: minmax(0, 1fr); } }
  .legs { display: flex; flex-direction: column; gap: 6px; }
  .leg { display: grid; grid-template-columns: minmax(0, 1fr) auto 22px; gap: 10px; align-items: center; padding: 10px 12px; }
  .leg .name { font-weight: 600; font-size: 14px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .leg .meta { color: var(--muted); font-size: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .leg .x { border: 0; background: none; color: var(--faint); font-size: 18px; padding: 0; line-height: 1; }
  .payout-card { padding: 14px; }
  .seg { display: grid; grid-template-columns: 1fr 1fr; background: var(--bg); border: 1px solid var(--border); border-radius: 10px; padding: 3px; margin-bottom: 12px; }
  .seg button { border: 0; background: none; padding: 7px; border-radius: 8px; color: var(--muted); font-weight: 600; font-size: 13px; }
  .seg button.on { background: var(--surface-3); color: var(--text); }
  .stake-row { display: flex; justify-content: space-between; color: var(--muted); font-size: 12.5px; margin-bottom: 6px; }
  .stake-row b { color: var(--text); }
  input[type=range] { width: 100%; accent-color: var(--accent); }
  .payouts { border-top: 1px solid var(--border); margin-top: 12px; padding-top: 12px; font-size: 13px; }
  .payouts .row { display: flex; justify-content: space-between; padding: 3px 0; color: var(--muted); }
  .payouts .row b { color: var(--text); font-weight: 600; }
  .payouts .max { display: flex; justify-content: space-between; align-items: baseline; margin-bottom: 6px; }
  .payouts .max span { color: var(--muted); font-size: 12px; } .payouts .max b { font-size: 24px; font-weight: 800; }
  .slip-warn { color: var(--warn); font-size: 12px; margin-top: 8px; }

  /* Split suggestions */
  .splits { display: grid; grid-template-columns: repeat(auto-fill, minmax(240px, 1fr)); gap: 10px; padding-top: 8px; }
  .split { padding: 13px; position: relative; }
  .split .lbl { font-weight: 700; font-size: 14px; margin-bottom: 6px; }
  .split .grp { color: var(--muted); font-size: 12px; margin: 2px 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .split .grp b { color: var(--text); font-weight: 600; }
  .split dl { margin: 10px 0; display: grid; gap: 3px; font-size: 12px; }
  .split dl div { display: flex; justify-content: space-between; gap: 8px; }
  .split dt { color: var(--faint); } .split dd { margin: 0; font-weight: 600; }
  .split .best { position: absolute; top: -8px; right: 10px; background: linear-gradient(90deg, var(--accent), var(--pos)); color: var(--bg);
    font-size: 10px; font-weight: 800; letter-spacing: 0.06em; padding: 2px 7px; border-radius: 6px; }
  .split .btn { width: 100%; padding: 8px; font-size: 13px; }
  .seg.wide { max-width: 320px; margin-bottom: 14px; }

  /* Record */
  .summary { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 10px; margin: 0 0 14px; }
  @media (max-width: 720px) { .summary { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
  .summary > div { padding: 12px 14px; }
  .summary dt { color: var(--faint); font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; }
  .summary dd { margin: 3px 0 0; font-size: 22px; font-weight: 700; }
  .summary small { display: block; color: var(--muted); font-size: 12px; font-weight: 400; }
  details.fold { margin-bottom: 8px; }
  details.fold > summary { list-style: none; cursor: pointer; display: flex; justify-content: space-between; align-items: center; gap: 12px; padding: 13px 14px; }
  details.fold > summary::-webkit-details-marker { display: none; }
  details.fold > summary .chev { color: var(--faint); transition: transform .15s; }
  details.fold[open] > summary .chev { transform: rotate(90deg); }
  details.fold .fold-body { border-top: 1px solid var(--border); padding: 4px 0; }
  table.results { width: 100%; border-collapse: collapse; font-size: 13px; }
  table.results th { text-align: left; color: var(--faint); font-weight: 500; font-size: 11px; padding: 8px 14px; }
  table.results td { padding: 9px 14px; border-top: 1px solid var(--border); }
  table.results .r { text-align: right; }
  @media (max-width: 520px) { table.results .hide-sm { display: none; } table.results th, table.results td { padding-left: 10px; padding-right: 10px; } }
  .learn table { width: 100%; border-collapse: collapse; font-size: 12.5px; }
  .learn th { text-align: left; color: var(--faint); font-weight: 500; font-size: 11px; padding: 4px 0; }
  .learn td { padding: 5px 0; border-top: 1px solid var(--border); }
  .learn .r { text-align: right; }
  .learn-grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 18px; padding: 12px 14px 14px; }
  @media (max-width: 720px) { .learn-grid { grid-template-columns: minmax(0, 1fr); } }
  .progress { height: 6px; border-radius: 3px; background: var(--surface-3); overflow: hidden; margin: 8px 0 2px; }
  .progress span { display: block; height: 100%; background: linear-gradient(90deg, var(--accent), var(--pos)); border-radius: 3px; }

  /* Research */
  .form { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; padding: 14px; }
  @media (min-width: 721px) { .form { grid-template-columns: 140px minmax(0, 1fr) 160px 90px auto; align-items: end; } }
  .field label { display: block; color: var(--faint); font-size: 11px; margin-bottom: 4px; }
  .field input, .field select { width: 100%; background: var(--bg); border: 1px solid var(--border-strong); border-radius: 9px; padding: 9px 10px; }
  .field input:focus, .field select:focus { outline: none; border-color: var(--accent); }
  .msg { color: var(--neg); font-size: 13px; margin-top: 8px; }
  .report { padding: 16px; margin-top: 12px; }
  .report-grid { display: grid; grid-template-columns: repeat(5, minmax(0, 1fr)); gap: 8px; margin: 12px 0; }
  @media (max-width: 720px) { .report-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
  .stat-box { border: 1px solid var(--border); border-radius: 10px; padding: 8px 10px; }
  .stat-box dt { color: var(--faint); font-size: 11px; } .stat-box dd { margin: 2px 0 0; font-weight: 700; }
  .stat-box small { color: var(--muted); font-size: 11.5px; display: block; }
  .reasons { margin: 10px 0 0; padding-left: 18px; color: var(--muted); font-size: 13px; }

  /* Modals */
  .modal { position: fixed; inset: 0; background: rgba(5, 8, 16, 0.78); display: grid; place-items: center; z-index: 50; padding: 16px; }
  .modal .card { max-width: 440px; width: 100%; padding: 18px; max-height: 92vh; overflow: auto; }
  .modal h3 { margin: 0 0 6px; font-size: 16px; }
  .modal p, .modal li { color: var(--muted); font-size: 13px; }
  .modal img { width: 100%; border-radius: 12px; display: block; margin: 10px 0; }
  .modal .qr { background: #fff; border-radius: 10px; padding: 8px; width: fit-content; margin: 12px auto; }
  .modal .qr svg { display: block; width: 200px; height: 200px; }
  .modal code { display: block; word-break: break-all; background: var(--bg); border: 1px solid var(--border); border-radius: 8px; padding: 8px; font-size: 12px; color: var(--text); }
</style>
</head>
<body>
<header class="top">
  <div class="top-inner">
    <div class="brand">
      <svg width="34" height="34" viewBox="0 0 64 64" aria-hidden="true">
        <defs><linearGradient id="lg" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#18233e"/><stop offset="1" stop-color="#090d1b"/></linearGradient></defs>
        <rect width="64" height="64" rx="14" fill="url(#lg)"/>
        <rect x="11" y="34" width="8" height="14" rx="2" fill="#344670"/><rect x="22" y="28" width="8" height="20" rx="2" fill="#4e68a0"/>
        <rect x="33" y="31" width="8" height="17" rx="2" fill="#344670"/><rect x="44" y="18" width="8" height="30" rx="2" fill="#3ecf8e"/>
        <path d="M8 25.5H56" stroke="#8fb3ff" stroke-width="2.4" stroke-linecap="round" stroke-dasharray="3.5 3"/>
      </svg>
      <div><h1>Daily Slip</h1><div class="date" id="today"></div></div>
    </div>
    <div class="top-right">
      <span class="status-pill" id="status"></span>
      <nav class="tabs" id="tabs">
        <button data-view="today"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M4 20V10M10 20V4M16 20v-7M22 20H2"/></svg>Today</button>
        <button data-view="slip"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 3h14v18l-3-2-2 2-2-2-2 2-2-2-3 2z"/><path d="M9 8h6M9 12h6"/></svg>Slip<span class="badge" id="slipBadge" hidden></span></button>
        <button data-view="record"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 12l5 5L20 6"/></svg>Record</button>
        <button data-view="research"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="11" cy="11" r="7"/><path d="M20 20l-4-4"/></svg>Research</button>
      </nav>
      <button class="icon-btn" id="phoneBtn" hidden>Phone</button>
    </div>
  </div>
</header>

<main>
  <section class="view" id="view-today"></section>
  <section class="view" id="view-slip" hidden></section>
  <section class="view" id="view-record" hidden></section>
  <section class="view" id="view-research" hidden>
    <h2 class="h2">Research a player</h2>
    <p class="sub">Free ESPN game logs, no credits. Check any player and line, then add it to your slip.</p>
    <form class="form card" id="researchForm" autocomplete="off">
      <div class="field"><label for="league">League</label><select id="league"></select></div>
      <div class="field"><label for="player">Player</label><input id="player" list="playerList" placeholder="Player name"><datalist id="playerList"></datalist></div>
      <div class="field"><label for="prop">Prop</label><select id="prop"></select></div>
      <div class="field"><label for="lineInput">Line</label><input id="lineInput" type="number" step="0.5" min="0" inputmode="decimal" placeholder="24.5"></div>
      <button class="btn btn-primary" id="analyzeBtn" type="submit">Analyze</button>
    </form>
    <div id="formMsg" class="msg" hidden></div>
    <div id="report"></div>
  </section>
</main>

<script>
const CONFIG = __CONFIG__;
const LEAGUE = Object.fromEntries(CONFIG.leagues.map(l => [l.key, l]));
const PAYOUTS = {
  power: { 2: 3, 3: 5, 4: 10, 5: 20, 6: 37.5 },
  flex: { 3: { 3: 3, 2: 1 }, 4: { 4: 6, 3: 1.5 }, 5: { 5: 10, 4: 2, 3: 0.4 }, 6: { 6: 25, 5: 2, 4: 0.4 } }
};
const MAX_LEGS = 6;
const MAX_POWER = CONFIG.max_power_legs ?? 3;
// The picker trims estimates toward 50/50 to allow for error; how much is learned from past slips.
const shrinkNow = () => (state.daily && state.daily.entry_shrink) ?? CONFIG.shrink ?? 0.7;
const cautious = p => 0.5 + (p - 0.5) * shrinkNow();

const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
};
const state = {
  daily: null, dailyError: null, dailyErrorTitle: null, noRetry: false, loading: false, nextScan: null,
  researched: store.get('ps_researched', []), slip: store.get('ps_slip', []),
  mode: store.get('ps_mode', 'flex'), stake: store.get('ps_stake', 10), bankroll: store.get('ps_bankroll', 0), filter: 'all',
  view: 'today', history: null, results: {}, live: {}, editing: null, lineMsg: null, open: null,
  saved: store.get('ps_saved', []), savedLive: {}, recordTab: null, alerts: []
};
function persist() {
  store.set('ps_researched', state.researched); store.set('ps_slip', state.slip);
  store.set('ps_mode', state.mode); store.set('ps_stake', state.stake); store.set('ps_saved', state.saved);
  store.set('ps_bankroll', state.bankroll);
}

const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const money = v => '$' + v.toFixed(2);
const pct = v => (v * 100).toFixed(1) + '%';
const pct0 = v => Math.round(v * 100) + '%';
const evStr = v => (v >= 0 ? '+' : '-') + Math.abs(v * 100).toFixed(1) + '%';
const dailyPicks = () => (state.daily && state.daily.picks) || [];
const leagueLabel = k => (LEAGUE[k] || {}).label || k;
const hitsFor = (w, side) => side === 'MORE' ? w.over : w.under;
const hitStr = (w, side) => w && w.n ? `${hitsFor(w, side)}/${w.n}` : '—';
const fmtTime = iso => new Date(iso).toLocaleString([], { weekday: 'short', hour: 'numeric', minute: '2-digit' });
const todaysResult = id => state.daily && state.results[`${state.daily.date}|${id}`];

/* ───────── Picks and slip ───────── */
function findPick(id) {
  const d = dailyPicks().find(p => p.id === id);
  if (d) return { id, player: d.player, league: d.sport, prop: d.prop, line: d.line, side: d.side, prob: d.final_p,
                  team: (d.report && d.report.player.team) || '', commence: d.commence, game: d.game,
                  espn_id: ((d.report || {}).player || {}).id || null };
  return state.researched.find(p => p.id === id);
}
function togglePick(id) {
  const i = state.slip.indexOf(id);
  if (i >= 0) state.slip.splice(i, 1);
  else {
    const p = findPick(id);
    if (!p) return;
    if (state.slip.length >= MAX_LEGS) return toast(`A slip holds up to ${MAX_LEGS} picks.`);
    const clash = state.slip.map(findPick).find(x => x && x.player === p.player);
    if (clash) state.slip.splice(state.slip.indexOf(clash.id), 1);   // one pick per player
    state.slip.push(id);
  }
  render();
}
let toastTimer;
function toast(text) {
  let t = $('#toast');
  if (!t) { t = document.createElement('div'); t.id = 'toast';
    t.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:calc(84px + env(safe-area-inset-bottom));z-index:60;background:#1a2440;border:1px solid rgba(148,163,184,.25);border-radius:10px;padding:9px 14px;font-size:13px;box-shadow:0 8px 30px rgba(0,0,0,.4)';
    document.body.appendChild(t); }
  t.textContent = text; t.hidden = false;
  clearTimeout(toastTimer); toastTimer = setTimeout(() => { t.hidden = true; }, 2600);
}

/* ───────── Entry options: every size, side by side ───────── */
function distribution(probs) {
  let dist = [1];
  for (const p of probs) { const nx = new Array(dist.length + 1).fill(0); dist.forEach((v, i) => { nx[i] += v * (1 - p); nx[i + 1] += v * p; }); dist = nx; }
  return dist;
}
function payTable(kind, n) { return kind === 'power' ? (PAYOUTS.power[n] ? { [n]: PAYOUTS.power[n] } : null) : PAYOUTS.flex[n] || null; }
function entryOptions() {
  const picks = dailyPicks();
  const out = [];
  for (let n = 2; n <= Math.min(picks.length, MAX_LEGS); n++) {
    const legs = picks.slice(0, n);
    const teams = new Set(legs.map(p => ((p.report || {}).player || {}).team || p.game + p.player));
    if (teams.size < 2) continue;
    const probs = legs.map(p => cautious(p.final_p));
    const dist = distribution(probs);
    for (const kind of ['power', 'flex']) {
      if (kind === 'power' && n > MAX_POWER) continue;
      const table = payTable(kind, n);
      if (!table) continue;
      const tiers = Object.keys(table).map(Number);
      out.push({ kind, n, ids: legs.map(p => p.id), label: `${n}-pick ${kind === 'power' ? 'Power' : 'Flex'}`,
                 ev: tiers.reduce((s, h) => s + dist[h] * table[h], 0) - 1,
                 cash: tiers.filter(h => table[h] > 1).reduce((s, h) => s + dist[h], 0),
                 top: Math.max(...Object.values(table)) });
    }
  }
  return out.sort((a, b) => a.n - b.n || (a.kind === 'power' ? -1 : 1));
}
function bestOption(opts) {
  const e = state.daily && state.daily.entry;
  if (e && e.kind) return opts.find(o => o.kind === e.kind && o.n === e.legs) || null;
  return opts.slice().sort((a, b) => b.ev - a.ev)[0] || null;
}
function applyOption(o) {
  state.slip = o.ids.slice(); state.mode = o.kind; render();
  toast(`${o.label} loaded into your slip`);
}

/* ───────── Splitting the picks into several slips ───────── */
function payoutDist(probs, kind) {                 // [[multiplier, probability], ...] for one entry
  const table = payTable(kind, probs.length) || {}, out = new Map();
  distribution(probs).forEach((p, h) => { const m = table[h] || 0; out.set(m, (out.get(m) || 0) + p); });
  return [...out];
}
function combine(a, b) {
  const out = new Map();
  for (const [m1, p1] of a) for (const [m2, p2] of b) out.set(m1 + m2, (out.get(m1 + m2) || 0) + p1 * p2);
  return [...out];
}
function scorePlan(entries) {                       // entries: [{kind, legs: [pick, ...]}], same stake on each
  const dist = entries.map(e => payoutDist(e.legs.map(p => cautious(p.final_p)), e.kind)).reduce(combine);
  const k = entries.length;
  return { entries, k,
           ahead: dist.filter(([m]) => m > k + 1e-9).reduce((t, [, p]) => t + p, 0),
           bust: dist.filter(([m]) => m === 0).reduce((t, [, p]) => t + p, 0),
           ev: dist.reduce((t, [m, p]) => t + m * p, 0) / k - 1 };
}
const teamsOk = legs => new Set(legs.map(p => ((p.report || {}).player || {}).team || p.game + p.player)).size >= 2;
const entryLabel = e => `${e.legs.length}-pick ${e.kind === 'power' ? 'Power' : 'Flex'}`;
function splitPlans() {
  const picks = dailyPicks().slice(0, 6), m = picks.length;
  if (m < 4) return [];
  const kindsFor = n => n === 2 ? ['power'] : n === 3 ? ['power', 'flex'] : ['flex'];
  const plans = [];
  for (let size = 4; size <= m; size++) {
    for (let mask = 1; mask < (1 << size) - 1; mask++) {
      if (!(mask & 1)) continue;                    // the top pick always sits in the first slip: each split counted once
      const A = [], B = [];
      for (let i = 0; i < size; i++) (mask & (1 << i) ? A : B).push(picks[i]);
      if (A.length < 2 || B.length < 2 || !teamsOk(A) || !teamsOk(B)) continue;
      for (const ka of kindsFor(A.length)) for (const kb of kindsFor(B.length))
        plans.push(scorePlan([{ kind: ka, legs: A }, { kind: kb, legs: B }]));
    }
  }
  if (m === 6) {                                    // three 2-pick Powers
    const pair = (rest) => {
      if (!rest.length) return [[]];
      const [a, ...others] = rest, out = [];
      others.forEach((b, i) => { for (const tail of pair(others.filter((_, j) => j !== i))) out.push([[a, b], ...tail]); });
      return out;
    };
    for (const groups of pair(picks)) if (groups.every(teamsOk)) plans.push(scorePlan(groups.map(g => ({ kind: 'power', legs: g }))));
  }
  plans.sort((a, b) => b.ahead - a.ahead || b.ev - a.ev);
  const seen = new Set();                            // never suggest a split it expects to lose money on
  plans.splice(0, plans.length, ...plans.filter(pl => pl.ev >= 0));                            // best version of each shape only, for variety
  return plans.filter(pl => { const k = pl.entries.map(entryLabel).join('+'); return !seen.has(k) && seen.add(k); }).slice(0, 3);
}
function saveSlip(legs, kind, stake, note) {
  if (legs.length < 2) return;
  const date = (state.daily && state.daily.date) || new Date().toISOString().slice(0, 10);
  state.saved.unshift({ id: 's' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6), saved_at: new Date().toISOString(),
    date, kind, stake, note: note || '', results: {},
    legs: legs.map(l => ({ id: l.id, player: l.player, league: l.league || l.sport, sport: l.league || l.sport, prop: l.prop, line: l.line,
                           side: l.side, prob: l.prob ?? l.final_p ?? null, commence: l.commence || null, game: l.game || '',
                           espn_id: l.espn_id || (((l.report || {}).player || {}).id) || null })) });
  persist();
}

/* ───────── Header ───────── */
function renderHeader() {
  $('#today').textContent = new Date().toLocaleDateString([], { weekday: 'long', month: 'short', day: 'numeric' });
  const d = state.daily, bits = [];
  if (d && d.scanned_at) bits.push(`Updated <b>${new Date(d.scanned_at).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' })}</b>`);
  if (state.nextScan) bits.push(`next <b>${fmtTime(state.nextScan)}</b>`);
  $('#status').innerHTML = bits.join(' · ');
  document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.view === state.view));
  const n = state.slip.map(findPick).filter(Boolean).length;
  $('#slipBadge').hidden = !n; $('#slipBadge').textContent = n;
  ['today', 'slip', 'record', 'research'].forEach(v => { $('#view-' + v).hidden = state.view !== v; });
}
$('#view-record').addEventListener('click', e => {
  const t = e.target.closest('[data-rtab]');
  if (t) { state.recordTab = t.dataset.rtab; render(); if (state.recordTab === 'mine') gradeSaved(); return; }
  const del = e.target.closest('[data-delete-saved]');
  if (del && confirm('Delete this saved slip?')) { state.saved = state.saved.filter(s => s.id !== del.dataset.deleteSaved); persist(); render(); }
});
$('#tabs').addEventListener('click', e => {
  const b = e.target.closest('[data-view]'); if (!b) return;
  state.view = b.dataset.view; render(); window.scrollTo(0, 0);
  if (state.view === 'record') { loadHistory(); gradeSaved(); }
});

/* ───────── Mini chart: last 10 results vs the line ───────── */
function spark(points, line, side, w = 150, h = 34) {
  if (!points || !points.length) return '';
  const max = Math.max(line, ...points.map(p => p.value)) * 1.1 || 1;
  const bw = w / points.length, y = v => h - (v / max) * h;
  const bars = points.map((p, i) => {
    const hit = side === 'MORE' ? p.value > line : p.value < line;
    const color = p.value === line ? 'var(--faint)' : hit ? 'var(--pos)' : 'var(--neg)';
    return `<rect x="${i * bw + 1.5}" y="${y(p.value)}" width="${Math.max(2, bw - 3)}" height="${Math.max(1, h - y(p.value))}" rx="1.5" fill="${color}" opacity="0.8"><title>${esc(p.date)} ${esc(p.opp)}: ${p.value}</title></rect>`;
  }).join('');
  return `<svg viewBox="0 0 ${w} ${h}" width="100%" height="${h}" preserveAspectRatio="none" role="img" aria-label="Last ${points.length} games vs line ${line}">${bars}
    <line x1="0" x2="${w}" y1="${y(line)}" y2="${y(line)}" stroke="var(--muted)" stroke-width="1" stroke-dasharray="3 3" vector-effect="non-scaling-stroke"/></svg>`;
}

/* ───────── Today ───────── */
function heroCard() {
  const d = state.daily, e = d && d.entry, opts = entryOptions(), best = bestOption(opts);
  if (e && !e.play) {
    return `<div class="hero"><div class="eyebrow">Today's call</div><div class="title">Sit out today</div>
      <p class="muted" style="margin:6px 0 14px;position:relative;z-index:1">No entry size clears the +${Math.round((CONFIG.min_ev || 0.02) * 100)}% bar${best ? ` (best: ${esc(best.label)}, ${evStr(best.ev)})` : ''}. The picks are below if you want to research them.</p>
      <div class="actions"><button class="btn" data-goto="slip">Compare sizes</button></div></div>`;
  }
  if (!best) return '';
  const top = money(state.stake * best.top);
  return `<div class="hero"><div class="eyebrow">Today's best play</div>
    <div class="title">${esc(best.label)}<small>${best.n} legs</small></div>
    <dl class="hero-stats">
      <div><dt>Chance to cash</dt><dd>${pct0(best.cash)}</dd></div>
      <div><dt>Est. value</dt><dd class="${best.ev >= 0 ? 'pos' : 'neg'}">${evStr(best.ev)}</dd></div>
      <div><dt>$${state.stake} pays up to</dt><dd>${top}</dd></div>
    </dl>
    <div class="actions"><button class="btn btn-primary" data-load-best>Use this slip</button><button class="btn" data-goto="slip">Compare sizes</button></div></div>`;
}
const CTX_SHORT = { blowout: 'blowout risk', b2b: 'back-to-back', returning: 'returning', windy: 'windy', minutes_down: 'minutes down', minutes_up: 'minutes up' };
function contextText(p) {
  const c = p.ctx || {}, f = c.flags || [], bits = [];
  if (c.spread != null) bits.push(`spread ${c.spread}${f.includes('blowout') ? ' (blowout risk: starters may sit late)' : ''}`);
  if (c.total != null) bits.push(`total ${c.total}${f.includes('high_total') ? ' (high scoring)' : f.includes('low_total') ? ' (low scoring)' : ''}`);
  if (f.includes('b2b')) bits.push('2nd night of a back-to-back');
  if (f.includes('returning')) bits.push(`first game in ${c.rest_days} days`);
  if (c.minutes_trend != null && (f.includes('minutes_down') || f.includes('minutes_up')))
    bits.push(`minutes ${c.minutes_trend > 1 ? 'up' : 'down'} ${Math.round(Math.abs(c.minutes_trend - 1) * 100)}% lately`);
  if (c.wind != null) bits.push(`wind ${c.wind} mph${c.precip ? `, rain ${c.precip} mm` : ''}`);
  return bits.length ? 'Game context: ' + bits.join(' · ') : null;
}
function underdogText(p) {
  if (p.ud_line == null || p.ud_line === p.line) return p.ud_line != null ? `Underdog has the same line (${p.ud_line})` : null;
  const better = p.side === 'MORE' ? p.ud_line < p.line : p.ud_line > p.line;
  return `Underdog: ${p.ud_line} (${better ? `better for ${p.side} there` : `worse for ${p.side} there`})`;
}
function pickRow(p) {
  const r = p.report, inSlip = state.slip.includes(p.id), open = state.open === p.id;
  const m = r && r.matchup, ng = r && r.next_game, lv = state.live[p.id], res = todaysResult(p.id);
  const meta = [leagueLabel(p.sport), r && r.player.team, p.commence ? fmtTime(p.commence) : null].filter(Boolean).join(' · ');
  const flags = ((p.ctx || {}).flags || []).filter(f => CTX_SHORT[f]).map(f => CTX_SHORT[f]);
  const gap = p.line_gap ? ` · <span class="${(p.side === 'MORE') === (p.line_gap > 0) ? 'pos' : 'neg'}">books ${p.line_gap > 0 ? '+' : ''}${p.line_gap}</span>` : '';
  const why = [p.n_books ? `${p.n_books} book${p.n_books === 1 ? '' : 's'}: ${p.books}` : p.books,
               p.line_gap ? `Books' line ${p.book_line} vs PrizePicks ${p.line}` : null,
               ng ? `Next ${ng.home ? 'vs' : '@'} ${ng.opp_abbr}${m ? ` · #${m.rank} of ${m.of} in ${m.what}` : ''}` : null,
               contextText(p), underdogText(p)].filter(Boolean);
  const live = liveStrip(p, lv);
  return `
  <article class="card pick ${inSlip ? 'in-slip' : ''} ${open ? 'open' : ''}" data-pick="${esc(p.id)}">
    <div class="pick-row" data-toggle-open="${esc(p.id)}">
      <div style="min-width:0"><div class="name">${esc(p.player)}</div><div class="meta">${esc(meta)}${gap}${flags.length ? ` · <span class="faint">${esc(flags.join(', '))}</span>` : ''}</div></div>
      <div class="line"><div class="p">${esc(p.prop)}</div><div class="v">${p.line}</div></div>
      <div style="text-align:center">${res ? resultTag(res) : `<span class="side ${p.side === 'MORE' ? 'more' : 'less'}">${p.side}</span>`}<div class="est">${pct0(p.final_p)}</div></div>
      <button class="add" data-add-slip="${esc(p.id)}" aria-label="${inSlip ? 'Remove from' : 'Add to'} slip">${inSlip ? '✓' : '+'}</button>
    </div>
    ${live ? `<div class="pick-live">${live}</div>` : ''}
    <div class="details">
      <dl class="stats">
        <div><dt>Est. win</dt><dd>${pct(p.final_p)}</dd></div>
        <div><dt>Books</dt><dd>${pct(p.market_p)}</dd></div>
        <div><dt>Last 10</dt><dd>${r ? hitStr(r.recent.l10, p.side) : '—'}</dd></div>
        <div><dt>Season</dt><dd>${r ? hitStr(r.recent.season, p.side) : '—'}</dd></div>
        <div><dt>Matchup</dt><dd>${m ? m.tier : '—'}</dd></div>
      </dl>
      ${r ? spark(r.chart, p.line, p.side, 300, 40) : ''}
      ${why.map(w => `<p class="why">${esc(w)}</p>`).join('')}
      ${lineTools(p)}
    </div>
  </article>`;
}
/* ───────── Injury alerts ───────── */
async function loadAlerts() {
  try { state.alerts = (await fetch('/api/alerts').then(r => r.json())).alerts || []; render(); } catch (e) {}
}
function alertCards() {
  if (!state.alerts.length) return '';
  return `<div class="section-label" style="margin-top:0">Injury news · ${state.alerts.length}</div>` + state.alerts.map(a => {
    const when = new Date(a.time).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });
    const rows = (a.teammates || []).map(t => `<div class="alert-row"><div><div class="who">${esc(t.player)} · ${esc(t.prop)}</div>
        <p class="why">${t.without} without him vs ${t.with} with (${t.games_without} games)</p></div>
        <button class="btn" data-research='${esc(JSON.stringify({ league: a.league, player: t.player, prop: t.prop }))}'>Research</button></div>`).join('')
      || (a.leaders || []).map(t => `<div class="alert-row"><div><div class="who">${esc(t.player)} · ${esc(t.prop)}</div>
        <p class="why">Season avg ${t.avg}. No games without him yet to compare.</p></div>
        <button class="btn" data-research='${esc(JSON.stringify({ league: a.league, player: t.player, prop: t.prop }))}'>Research</button></div>`).join('');
    return `<div class="card alert">
      <div class="alert-head"><span class="out">${esc(a.status.toUpperCase())}</span><b>${esc(a.player)}</b>
        <span class="muted" style="font-size:12.5px">${esc(a.team)} · ${esc(a.game)}${a.start ? ' ' + new Date(a.start).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }) : ''} · news ${when}</span></div>
      ${a.note ? `<p class="note">${esc(a.note)}</p>` : ''}
      ${a.in_slip ? `<p class="note neg" style="font-weight:600">He's in today's picks; that leg will be voided if he sits.</p>` : ''}
      ${rows ? `<div class="faint" style="font-size:11.5px;margin-bottom:2px">Teammates to check on PrizePicks before their lines move:</div>${rows}` : ''}
    </div>`;
  }).join('');
}
function openResearch(league, player, prop) {
  state.view = 'research'; render(); window.scrollTo(0, 0);
  if (LEAGUE[league]) { $('#league').value = league; fillProps(); }
  $('#player').value = player; playerIds = {};
  if ([...$('#prop').options].some(o => o.value === prop)) $('#prop').value = prop;
  $('#lineInput').value = ''; $('#lineInput').focus();
  toast('Enter the PrizePicks line you see, then Analyze');
}

function renderToday() {
  const el = $('#view-today'), d = state.daily;
  if (state.loading) { el.innerHTML = `<div class="card empty"><span class="spinner"></span>&nbsp; Scanning today's slate…</div>`; return; }
  if (state.dailyError) {
    el.innerHTML = alertCards() + `<div class="card empty"><strong>${esc(state.dailyErrorTitle || "Scan didn't finish")}</strong>${esc(state.dailyError)}
      ${state.noRetry ? '' : '<div style="margin-top:12px"><button class="btn" data-scan>Try again</button></div>'}</div>`;
    return;
  }
  if (!d) {
    el.innerHTML = state.needsScan
      ? `<div class="card empty"><strong>No picks yet today</strong>Run today's scan to get your slip (uses up to ${CONFIG.budget} credits).<div style="margin-top:12px"><button class="btn btn-primary" data-scan>Scan now</button></div></div>`
      : `<div class="card empty"><span class="spinner"></span></div>`;
    return;
  }
  const picks = dailyPicks();
  if (picks.length < 2) {
    el.innerHTML = `<div class="card empty"><strong>Lines aren't posted yet</strong>The scan found ${picks.length} usable pick${picks.length === 1 ? '' : 's'}.
      ${state.nextScan ? `It checks again ${fmtTime(state.nextScan)}.` : ''}</div>`;
    return;
  }
  const leagues = [...new Set(picks.map(p => p.sport))];
  if (state.filter !== 'all' && !leagues.includes(state.filter)) state.filter = 'all';
  const shown = picks.filter(p => state.filter === 'all' || p.sport === state.filter);
  const extras = [`${d.lines_compared} lines`, `${d.games_scanned} games`, d.books_used ? `${d.books_used} books` : null,
                  d.injured_skipped ? `${d.injured_skipped} injured skipped` : null].filter(Boolean).join(' · ');
  el.innerHTML = alertCards() + heroCard()
    + (state.lineMsg ? `<div class="card notice">${esc(state.lineMsg)}</div>` : '')
    + `<div style="display:flex;justify-content:space-between;align-items:end;gap:10px;margin-bottom:10px">
         <div><h2 class="h2">Today's picks</h2><div class="faint" style="font-size:12px">${esc(extras)}${d.pp_matched ? '' : ' · confirm lines in the app'}</div></div>
         <span class="faint" style="font-size:12px;white-space:nowrap">Tap a pick for details</span></div>`
    + (leagues.length > 1 ? `<div class="chips" style="margin-bottom:10px">${['all'].concat(leagues).map(k =>
        `<button class="chip ${state.filter === k ? 'on' : ''}" data-filter="${k}">${k === 'all' ? 'All' : esc(leagueLabel(k))}</button>`).join('')}</div>` : '')
    + `<div class="picks">${shown.map(pickRow).join('')}</div>`
    + `<p class="footnote">Est. win blends up to 9 sportsbooks with the player's hit rate on this line. Injured players are skipped. Estimates, not guarantees; check each line in PrizePicks before entering.</p>`;
}
$('#view-today').addEventListener('click', e => {
  const rs = e.target.closest('[data-research]');
  if (rs) { const r = JSON.parse(rs.dataset.research); openResearch(r.league, r.player, r.prop); return; }
  if (e.target.closest('.line-tools')) return lineToolsClick(e);
  if (e.target.closest('[data-scan]')) return loadDaily(true);
  const go = e.target.closest('[data-goto]'); if (go) { state.view = go.dataset.goto; render(); window.scrollTo(0, 0); return; }
  if (e.target.closest('[data-load-best]')) { const b = bestOption(entryOptions()); if (b) { applyOption(b); state.view = 'slip'; render(); window.scrollTo(0, 0); } return; }
  const f = e.target.closest('[data-filter]'); if (f) { state.filter = f.dataset.filter; render(); return; }
  const add = e.target.closest('[data-add-slip]'); if (add) { togglePick(add.dataset.addSlip); return; }
  const row = e.target.closest('[data-toggle-open]');
  if (row) { state.open = state.open === row.dataset.toggleOpen ? null : row.dataset.toggleOpen; render(); }
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
    if (d.needs_scan) {                 // never scan on its own: the schedule does that
      state.needsScan = !d.previous; state.daily = d.previous || null; render(); return;
    }
    state.daily = d;
    if (store.get('ps_slip_date', '') !== d.date && d.picks.length >= 2) {   // load today's suggested entry once
      state.slip = d.entry ? (d.entry.play ? d.entry.ids.slice() : []) : d.picks.map(p => p.id);
      state.mode = d.entry && d.entry.kind ? d.entry.kind : (d.picks.length >= 3 ? 'flex' : 'power');
      store.set('ps_slip_date', d.date);
    }
    render();
  } catch (e) {
    state.loading = false; state.dailyError = 'Could not reach the app.'; render();
  }
}

/* ───────── Slip ───────── */
function renderSlipView() {
  const el = $('#view-slip');
  const legs = state.slip.map(findPick).filter(Boolean);
  if (state.daily) state.slip = legs.map(l => l.id);   // drop stale legs once today's picks are known
  const n = legs.length, opts = entryOptions(), best = bestOption(opts);
  const activeKey = `${state.mode}|${state.slip.slice().sort().join(',')}`;
  const optionCards = opts.length ? `<div class="section-label" style="margin-top:0">Choose your entry</div>
    <div class="options">${opts.map((o, i) => {
      const on = `${o.kind}|${o.ids.slice().sort().join(',')}` === activeKey;
      return `<button class="option ${on ? 'on' : ''}" data-option="${i}">
        ${best && o.kind === best.kind && o.n === best.n ? '<span class="best">BEST</span>' : ''}
        <div class="lbl">${esc(o.label)}</div>
        <dl><div><dt>Chance to cash</dt><dd>${pct0(o.cash)}</dd></div>
            <div><dt>Est. value</dt><dd class="${o.ev >= 0 ? 'pos' : 'neg'}">${evStr(o.ev)}</dd></div>
            <div><dt>Pays up to</dt><dd>${o.top}×</dd></div></dl></button>`;
    }).join('')}</div>
    <p class="faint" style="font-size:12px;margin:4px 0 0">Uses today's top picks in order. Smaller entries cash more often; bigger ones pay more.</p>` : '';
  const plans = splitPlans();
  const single = best ? scorePlan([{ kind: best.kind, legs: dailyPicks().filter(p => best.ids.includes(p.id)) }]) : null;
  const splitCards = plans.length ? `<div class="section-label">Or split it up</div>
    <div class="splits">${plans.map((pl, i) => `<div class="card split">
        ${i === 0 ? '<span class="best">SAFEST</span>' : ''}
        <div class="lbl">${pl.entries.map(entryLabel).join(' + ')}</div>
        ${pl.entries.map(e => `<div class="grp"><b>${esc(entryLabel(e))}:</b> ${esc(e.legs.map(p => p.player.split(' ').slice(-1)[0]).join(', '))}</div>`).join('')}
        <dl><div><dt>Chance to come out ahead</dt><dd>${pct0(pl.ahead)}</dd></div>
            <div><dt>Chance to lose it all</dt><dd>${pct0(pl.bust)}</dd></div>
            <div><dt>Est. value</dt><dd class="${pl.ev >= 0 ? 'pos' : 'neg'}">${evStr(pl.ev)}</dd></div>
            <div><dt>Total stake</dt><dd>$${state.stake * pl.k} ($${state.stake} each)</dd></div></dl>
        <button class="btn" data-save-plan="${i}">Save as ${pl.k} slips</button></div>`).join('')}</div>
    ${single ? `<p class="faint" style="font-size:12px;margin:6px 0 0">For comparison, one ${esc(best.label)}: ${pct0(single.ahead)} chance to come out ahead, ${pct0(single.bust)} chance to lose it all, ${evStr(single.ev)} est. value. Splitting usually cashes more often but pays less at the top.</p>` : ''}` : '';

  const table = payTable(state.mode, n);
  let pay = '';
  if (!table) pay = `<div class="muted">${state.mode === 'flex' ? 'Flex needs 3 to 6 picks.' : 'Power needs 2 to 6 picks.'}</div>`;
  else {
    const tiers = Object.keys(table).map(Number).sort((a, b) => b - a), top = table[tiers[0]];
    pay = `<div class="max"><span>To win</span><b>${money(state.stake * top)}</b></div>`
      + tiers.map(h => `<div class="row"><span>${h} of ${n} correct</span><b>${table[h]}× · ${money(state.stake * table[h])}</b></div>`).join('');
    if (legs.every(l => l.prob != null)) {
      const dist = distribution(legs.map(l => cautious(l.prob)));
      const ev = state.stake * (tiers.reduce((s, h) => s + dist[h] * table[h], 0) - 1);
      const cash = tiers.filter(h => table[h] > 1).reduce((s, h) => s + dist[h], 0);
      pay += `<div class="row" style="margin-top:8px;border-top:1px solid var(--border);padding-top:8px"><span>Chance to cash (est.)</span><b>${pct0(cash)}</b></div>
        <div class="row"><span>Expected value (est.)</span><b class="${ev >= 0 ? 'pos' : 'neg'}">${ev >= 0 ? '+' : '-'}${money(Math.abs(ev))}</b></div>`;
    }
  }
  const warn = n >= 2 && legs.every(l => l.team) && new Set(legs.map(l => l.team)).size === 1 ? 'PrizePicks requires players from at least 2 teams.' : '';
  el.innerHTML = `<h2 class="h2">Your slip</h2><p class="sub">Pick an entry size, adjust the legs, then share it.</p>`
    + optionCards + splitCards
    + `<div class="slip-grid" style="margin-top:18px">
        <div><div class="section-label" style="margin-top:0">Legs · ${n} of ${MAX_LEGS}</div>
          <div class="legs">${n ? legs.map(l => {
            const lv = state.live[l.id], res = todaysResult(l.id);
            const status = res ? resultTag(res) : `<span class="side ${l.side === 'MORE' ? 'more' : 'less'}">${l.side}</span>`;
            const liveTxt = lv && lv.value != null && lv.state !== 'pre' ? ` · <span class="${legStatus(l, lv)}">${lv.state === 'in' ? 'live' : 'final'} ${lv.value}</span>` : '';
            return `<div class="card leg"><div style="min-width:0"><div class="name">${esc(l.player)}</div>
              <div class="meta">${esc(leagueLabel(l.league))} · ${esc(l.prop)} ${l.line}${l.prob != null ? ` · ${pct0(l.prob)}` : ''}${liveTxt}</div></div>
              ${status}<button class="x" data-unslip="${esc(l.id)}" aria-label="Remove ${esc(l.player)}">×</button></div>`;
          }).join('') : `<div class="card empty" style="padding:20px"><strong>No legs yet</strong>Pick an entry above, or add picks from Today with +.</div>`}</div>
          ${n ? `<div style="display:flex;gap:8px;margin-top:12px;flex-wrap:wrap">
            <button class="btn btn-primary" id="saveBtn">Save to My Slips</button><button class="btn" id="shareBtn">Share image</button><button class="btn" id="clearSlip">Clear</button></div>
          <p class="faint" style="font-size:12px;margin:8px 0 0">Saving keeps this slip with your $${state.stake} stake on this device and grades it as games finish.</p>` : ''}
        </div>
        <div class="card payout-card">
          <div class="seg"><button data-mode="power" class="${state.mode === 'power' ? 'on' : ''}">Power</button><button data-mode="flex" class="${state.mode === 'flex' ? 'on' : ''}">Flex</button></div>
          <div class="stake-row"><span>Stake</span><b>$${state.stake}</b></div>
          <input id="stake" type="range" min="1" max="200" step="1" value="${state.stake}" aria-label="Stake">
          <div class="payouts">${pay}</div>
          ${n ? sizingHtml(legs) : ''}
          ${warn ? `<div class="slip-warn">${warn}</div>` : ''}
          <p class="faint" style="font-size:11.5px;margin:10px 0 0">Preview only. Nothing is sent to PrizePicks.</p>
        </div></div>`;
}
$('#view-slip').addEventListener('click', e => {
  const o = e.target.closest('[data-option]'); if (o) { applyOption(entryOptions()[+o.dataset.option]); return; }
  const u = e.target.closest('[data-unslip]'); if (u) { state.slip = state.slip.filter(id => id !== u.dataset.unslip); render(); return; }
  const m = e.target.closest('[data-mode]'); if (m) { state.mode = m.dataset.mode; render(); return; }
  const kb = e.target.closest('[data-use-kelly]'); if (kb) { state.stake = +kb.dataset.useKelly; persist(); render(); return; }
  if (e.target.closest('#clearSlip')) { state.slip = []; render(); return; }
  if (e.target.closest('#saveBtn')) {
    const legs = state.slip.map(findPick).filter(Boolean);
    if (!payTable(state.mode, legs.length)) return toast(state.mode === 'flex' ? 'Flex needs 3 to 6 picks.' : 'Power needs 2 to 6 picks.');
    saveSlip(legs, state.mode, state.stake); toast('Saved to My Slips (Record tab)'); return;
  }
  const sp = e.target.closest('[data-save-plan]');
  if (sp) {
    const pl = splitPlans()[+sp.dataset.savePlan];
    pl.entries.slice().reverse().forEach(en => saveSlip(en.legs.map(p => findPick(p.id)), en.kind, state.stake, pl.entries.map(entryLabel).join(' + ')));
    toast(`Saved ${pl.k} slips to My Slips (Record tab)`); return;
  }
  if (e.target.closest('#shareBtn')) shareSlip();
});
$('#view-slip').addEventListener('input', e => {        // live number while dragging...
  if (e.target.id !== 'stake') return;
  state.stake = Number(e.target.value);
  e.target.closest('.payout-card').querySelector('.stake-row b').textContent = '$' + state.stake;
});
$('#view-slip').addEventListener('change', e => {       // ...payouts when you let go
  if (e.target.id === 'stake') { persist(); renderSlipView(); }
  if (e.target.id === 'bankroll') { state.bankroll = Math.max(0, Number(e.target.value) || 0); persist(); renderSlipView(); }
});

/* ───────── Bet sizing: quarter-Kelly, capped ───────── */
function kellyStake(legs, kind) {
  const table = payTable(kind, legs.length);
  if (!table || !state.bankroll || legs.some(l => l.prob == null)) return null;
  const dist = distribution(legs.map(l => cautious(l.prob)));
  const outcomes = dist.map((p, h) => [p, (table[h] || 0) - 1]);          // net return per $1 staked
  let best = 0, bestG = 0;
  for (let f = 0.001; f <= 0.25; f += 0.001) {
    const g = outcomes.reduce((t, [p, r]) => t + p * Math.log(Math.max(1e-9, 1 + f * r)), 0);
    if (g > bestG) { bestG = g; best = f; }
  }
  const frac = Math.min(best / 4, 0.03);                                  // a quarter of full Kelly, never over 3%
  return { frac, stake: Math.round(state.bankroll * frac) };
}
function sizingHtml(legs) {
  const k = kellyStake(legs, state.mode);
  const field = `<div class="stake-row" style="margin-top:14px;align-items:center"><span>Bankroll</span>
    <input id="bankroll" type="number" min="0" step="10" inputmode="numeric" value="${state.bankroll || ''}" placeholder="e.g. 500"
      style="width:110px;background:var(--bg);border:1px solid var(--border-strong);border-radius:8px;padding:5px 8px;text-align:right"></div>`;
  if (!state.bankroll) return field + `<p class="faint" style="font-size:12px;margin:4px 0 0">Enter your bankroll to get a suggested stake.</p>`;
  if (!k) return field + `<p class="faint" style="font-size:12px;margin:4px 0 0">Suggested stakes need every leg's win estimate (today's picks have them; researched picks don't).</p>`;
  if (!k.stake) return field + `<p style="font-size:12.5px;margin:4px 0 0">Suggested stake: <b>$0</b> <span class="faint">(no edge on this slip)</span></p>`;
  return field + `<p style="font-size:12.5px;margin:4px 0 0">Suggested stake: <b>$${k.stake}</b> <span class="faint">(${(k.frac * 100).toFixed(1)}% of bankroll)</span>
    <button class="link" data-use-kelly="${Math.min(200, Math.max(1, k.stake))}" style="margin-left:6px">Use</button></p>
    <p class="faint" style="font-size:11.5px;margin:2px 0 0">Quarter-Kelly sizing, capped at 3% so a cold streak can't sink the bankroll.</p>`;
}

/* ───────── Share: the slip as a picture ───────── */
function rr(ctx, x, y, w, h, r) { ctx.beginPath(); ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r); ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath(); }
function fit(ctx, text, max) { let t = String(text); while (ctx.measureText(t).width > max && t.length > 3) t = t.slice(0, -2); return t === String(text) ? t : t.slice(0, -1) + '…'; }
async function drawSlipImage() {
  const legs = state.slip.map(findPick).filter(Boolean);
  const n = legs.length, table = payTable(state.mode, n);
  const W = 1080, rowH = 132, H = 230 + n * (rowH + 16) + 90;
  const c = document.createElement('canvas'); c.width = W; c.height = H;
  const ctx = c.getContext('2d');
  try { await document.fonts.ready; } catch (e) {}
  const F = (w, s) => `${w} ${s}px Inter, system-ui, -apple-system, sans-serif`;

  // background with glows
  const g = ctx.createLinearGradient(0, 0, 0, H); g.addColorStop(0, '#16203a'); g.addColorStop(1, '#090d1b');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
  const glow = (x, y, r, col) => { const rg = ctx.createRadialGradient(x, y, 0, x, y, r); rg.addColorStop(0, col); rg.addColorStop(1, 'rgba(0,0,0,0)'); ctx.fillStyle = rg; ctx.fillRect(0, 0, W, H); };
  glow(W - 80, 40, 520, 'rgba(143,179,255,0.22)'); glow(60, H - 60, 520, 'rgba(62,207,142,0.14)');

  // logo + wordmark
  const L = 92, lx = 72, ly = 70;
  rr(ctx, lx, ly, L, L, 22); ctx.fillStyle = '#0d1426'; ctx.fill(); ctx.strokeStyle = 'rgba(148,163,184,0.25)'; ctx.lineWidth = 2; ctx.stroke();
  [[16, 46, 20, '#344670'], [32, 38, 28, '#4e68a0'], [48, 42, 24, '#344670'], [64, 24, 42, '#3ecf8e']].forEach(([x, y, h, col]) => {
    rr(ctx, lx + x - 2, ly + y + 4, 12, h + 2, 3); ctx.fillStyle = col; ctx.fill(); });
  ctx.strokeStyle = '#8fb3ff'; ctx.lineWidth = 3; ctx.setLineDash([6, 5]); ctx.beginPath(); ctx.moveTo(lx + 10, ly + 36); ctx.lineTo(lx + L - 10, ly + 36); ctx.stroke(); ctx.setLineDash([]);
  ctx.fillStyle = '#e6e9ef'; ctx.font = F(800, 44); ctx.fillText('Daily Slip', lx + L + 26, ly + 48);
  ctx.fillStyle = '#8b94a7'; ctx.font = F(500, 28);
  ctx.fillText(new Date().toLocaleDateString([], { weekday: 'long', month: 'long', day: 'numeric' }), lx + L + 26, ly + 86);

  // legs
  let y = 230;
  for (const l of legs) {
    const res = todaysResult(l.id), lv = state.live[l.id];
    rr(ctx, 56, y, W - 112, rowH, 26); ctx.fillStyle = 'rgba(15,22,39,0.92)'; ctx.fill();
    ctx.strokeStyle = res && res.result === 'hit' ? 'rgba(62,207,142,0.6)' : res && res.result === 'miss' ? 'rgba(240,113,120,0.5)' : 'rgba(148,163,184,0.18)';
    ctx.lineWidth = 2; ctx.stroke();
    ctx.fillStyle = '#e6e9ef'; ctx.font = F(700, 40); ctx.fillText(fit(ctx, l.player, 520), 92, y + 58);
    ctx.fillStyle = '#8b94a7'; ctx.font = F(500, 27); ctx.fillText(fit(ctx, `${leagueLabel(l.league)} · ${l.prop}`, 520), 92, y + 100);
    // line value
    ctx.textAlign = 'right'; ctx.fillStyle = '#e6e9ef'; ctx.font = F(800, 52); ctx.fillText(String(l.line), W - 300, y + 82); ctx.textAlign = 'left';
    // side / result pill
    const more = l.side === 'MORE';
    let txt = l.side, fg = more ? '#3ecf8e' : '#f07178', bg = more ? 'rgba(62,207,142,0.16)' : 'rgba(240,113,120,0.16)';
    if (res && res.result) {
      txt = `${res.result.toUpperCase()}${res.actual != null ? ' ' + res.actual : ''}`;
      [fg, bg] = res.result === 'hit' ? ['#3ecf8e', 'rgba(62,207,142,0.18)'] : res.result === 'miss' ? ['#f07178', 'rgba(240,113,120,0.18)'] : ['#8b94a7', 'rgba(148,163,184,0.16)'];
    } else if (lv && lv.state === 'in' && lv.value != null) { txt = `${l.side} · ${lv.value}`; }
    ctx.font = F(800, 28); const sw = ctx.measureText(txt).width + 44;
    rr(ctx, W - 92 - sw, y + 38, sw, 56, 16); ctx.fillStyle = bg; ctx.fill();
    ctx.fillStyle = fg; ctx.fillText(txt, W - 92 - sw + 22, y + 76);
    y += rowH + 16;
  }

  ctx.fillStyle = '#5c6578'; ctx.font = F(500, 22);
  ctx.fillText('Made with Daily Slip', 72, H - 44);
  return c;
}
async function shareSlip() {
  const btn = $('#shareBtn'); if (btn) { btn.disabled = true; btn.innerHTML = '<span class="spinner"></span>'; }
  try {
    const canvas = await drawSlipImage();
    const blob = await new Promise(r => canvas.toBlob(r, 'image/png'));
    const file = new File([blob], `daily-slip-${new Date().toISOString().slice(0, 10)}.png`, { type: 'image/png' });
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      try { await navigator.share({ files: [file], title: 'My Daily Slip' }); return; } catch (e) { if (e.name === 'AbortError') return; }
    }
    const url = URL.createObjectURL(blob);
    const m = document.createElement('div'); m.className = 'modal';
    m.innerHTML = `<div class="card"><h3>Your slip image</h3><p>Press and hold the image to save or share it, or download it.</p>
      <img src="${url}" alt="Slip image"><div style="display:flex;gap:8px;justify-content:flex-end">
      <a class="btn btn-primary" href="${url}" download="${file.name}" style="text-decoration:none">Download</a><button class="btn" data-close>Done</button></div></div>`;
    m.addEventListener('click', ev => { if (ev.target === m || ev.target.hasAttribute('data-close')) { m.remove(); URL.revokeObjectURL(url); } });
    document.body.appendChild(m);
  } finally { if (btn) { btn.disabled = false; btn.textContent = 'Share image'; } }
}

/* ───────── Live in-game tracking ───────── */
function legStatus(p, lv) {
  if (!lv || lv.value == null) return '';
  return (p.side === 'MORE') === (lv.value > p.line) ? 'pos' : (lv.state === 'post' ? 'neg' : '');
}
function liveStrip(p, lv) {
  if (!lv || lv.state === 'pre' || lv.state === 'unknown') return '';
  const final = lv.state === 'post';
  const clock = `<span class="clock"><span class="dot"></span>${final ? 'Final' : 'Live · ' + esc(lv.detail)}</span>`;
  if (lv.value == null) return `<div class="live ${final ? 'final' : ''}">${clock}<span class="muted">${esc(lv.note || '')}</span><span></span></div>`;
  const v = lv.value, line = p.line, more = p.side === 'MORE', over = v > line;
  const scale = Math.max(line * 1.5, v, 1);
  let msg, cls;
  if (more) { const need = Math.floor(line) + 1 - v; [msg, cls] = over ? ['Cleared', 'pos'] : [final ? 'Missed' : `Needs ${need} more`, final ? 'neg' : '']; }
  else { [msg, cls] = over ? [final ? 'Missed' : 'Over the line', 'neg'] : [final ? 'Stayed under' : `${(line - v).toFixed(1)} under`, final ? 'pos' : '']; }
  const barColor = over === more ? 'var(--pos)' : over ? 'var(--neg)' : 'var(--accent)';
  const pace = lv.pace != null && !final ? `<small>pace ${lv.pace}</small>` : '';
  return `<div class="live ${final ? 'final' : ''}">${clock}
    <div class="bar"><span style="width:${Math.min(v / scale, 1) * 100}%;background:${barColor}"></span><i style="left:${line / scale * 100}%"></i></div>
    <span class="now"><b>${v}</b><small>/ ${line}</small><small class="${cls}" style="font-weight:600">${msg}</small>${pace}</span></div>`;
}
let liveTimer;
async function loadLive() {
  clearTimeout(liveTimer);
  let next = 5 * 60 * 1000;
  try {
    state.live = await fetch('/api/live').then(r => r.json());
    if (Object.values(state.live).some(l => l.state === 'in')) next = 30 * 1000;
    if (Object.values(state.live).some(l => l.state === 'post') && state.history) loadHistory();
    gradeSaved();
    loadAlerts();
    render();
  } catch (e) {}
  liveTimer = setTimeout(loadLive, next);
}

/* ───────── Line changed / pulled ───────── */
function lineTools(p) {
  if (!state.daily || !state.daily.board) return '';
  const lv = state.live[p.id];
  if (todaysResult(p.id) || (lv && (lv.state === 'in' || lv.state === 'post'))) return '';
  if (state.editing !== p.id) {
    return `<div class="line-tools">${p.line_moved_from != null ? `<span class="muted">Line moved from ${p.line_moved_from} · </span>` : ''}<button class="link" data-edit="${esc(p.id)}">Line changed on PrizePicks?</button></div>`;
  }
  return `<div class="line-tools"><div class="line-form">
      <span class="muted">New line</span>
      <input type="number" step="0.5" min="0" inputmode="decimal" value="${p.line}" data-newline="${esc(p.id)}">
      <button class="btn btn-primary" data-update="${esc(p.id)}">Update</button>
      <button class="btn" data-pulled="${esc(p.id)}">Line pulled</button>
      <button class="link" data-cancel>Cancel</button></div>
    <div class="faint" style="margin-top:4px">Re-priced from this morning's saved odds. No credits used.</div></div>`;
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
    if (r.error) state.lineMsg = r.error;
    else {
      state.daily = r.daily; state.lineMsg = r.message; state.editing = null;
      const en = r.daily.entry;
      state.slip = en && en.play ? en.ids.slice() : [];
      if (en && en.kind) state.mode = en.kind;
    }
  } catch (err) { state.lineMsg = 'Could not reach the app.'; }
  render();
}

/* ───────── Record ───────── */
function resultTag(r) {
  if (!r || !r.result) return '';
  const label = { hit: 'HIT', miss: 'MISS', push: 'PUSH', void: 'VOID' }[r.result];
  return `<span class="res ${r.result}"${r.result === 'void' ? ' title="Did not play"' : ''}>${label}${r.actual != null ? ' ' + r.actual : ''}</span>`;
}
async function loadHistory() {
  try {
    const h = await fetch('/api/history').then(r => r.json());
    state.history = h; state.results = {};
    h.days.forEach(d => d.picks.forEach(p => { if (p.result) state.results[`${d.date}|${p.id}`] = p; }));
    render();
  } catch (e) {}
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
  const summary = m.active ? `Learning from ${m.n} graded lines` : `Learning: ${m.n} of ${m.learn_min} graded lines`;
  const changes = [];
  if (m.active) {
    changes.push(`<tr><td>Book odds vs. hit-rate blend</td><td class="r">${Math.round(m.market_weight * 100)} / ${Math.round((1 - m.market_weight) * 100)}</td><td class="r faint">was 75 / 25</td></tr>`);
    if (m.bias) changes.push(`<tr><td>Overall calibration</td><td class="r ${m.bias > 0 ? 'pos' : 'neg'}">${pp(m.bias)}</td><td class="r faint">${m.bias < 0 ? 'was overconfident' : 'was too cautious'}</td></tr>`);
    Object.entries(m.segments).sort((a, b) => Math.abs(b[1]) - Math.abs(a[1])).slice(0, 6).forEach(([k, v]) => {
      const g = m.groups.find(x => x.key === k);
      changes.push(`<tr><td>${esc(groupLabel(k))}</td><td class="r ${v > 0 ? 'pos' : 'neg'}">${pp(v)}</td><td class="r faint">${g ? `${Math.round(g.actual * 100)}% vs ${Math.round(g.expected * 100)}% (${g.n})` : ''}</td></tr>`);
    });
  }
  const calib = (m.calibration || []).map(b => `<tr><td>${Math.round(b.range[0] * 100) || '<'}${b.range[0] ? '–' : ''}${Math.round(b.range[1] * 100)}%</td>
      <td class="r">${(b.expected * 100).toFixed(1)}%</td><td class="r ${b.actual >= b.expected ? 'pos' : 'neg'}">${(b.actual * 100).toFixed(1)}%</td><td class="r faint">${b.n}</td></tr>`).join('');
  const en = m.entry, sg = m.same_game;
  const slipRows = [];
  if (en) slipRows.push(`<tr><td>Entry sizing (${en.n} replayed slips, ${en.days} days)</td><td class="r">${en.actual_cash != null ? `${Math.round(en.actual_cash * 100)}% cashed vs ${Math.round(en.predicted_cash * 100)}% predicted` : '—'}</td>
      <td class="r faint">${en.active ? `trims ${Math.round((1 - en.shrink) * 100)}% toward 50/50` : `starts at ${en.min_days} days`}</td></tr>`);
  if (sg) slipRows.push(`<tr><td>Same-game picks (${sg.pairs} pairs)</td><td class="r">${sg.observed_both_miss != null ? `both missed ${Math.round(sg.observed_both_miss * 100)}% vs ${Math.round(sg.expected_both_miss * 100)}% chance` : '—'}</td>
      <td class="r faint">${sg.active ? `max ${sg.max_per_game} per game` : `starts at ${sg.min} pairs`}</td></tr>`);
  const slipTable = slipRows.length ? `<div style="padding:0 14px 14px"><div class="section-label" style="margin-top:0">Learning from slip results</div>
      <table><tbody>${slipRows.join('')}</tbody></table></div>` : '';
  return `<details class="card fold learn"><summary><div><b>${summary}</b>
      ${m.active ? '' : `<div class="progress" style="width:180px"><span style="width:${Math.min(m.n / m.learn_min, 1) * 100}%"></span></div>`}</div><span class="chev">›</span></summary>
    <div class="fold-body"><p class="muted" style="font-size:12.5px;margin:10px 14px 0">${m.active ? 'Adjustments are capped and shrink toward the default when evidence is thin.'
      : `The picker grades every line it scans, not just your picks. Until it has ${m.learn_min}, it keeps the default blend, because adjusting on fewer lines hurt about as often as it helped.`}</p>
    <div class="learn-grid">
      <table><thead><tr><th>Adjustment</th><th class="r">Now</th><th></th></tr></thead>
        <tbody>${changes.join('') || `<tr><td colspan="3" class="faint">${m.active ? 'Nothing has strayed far enough to adjust.' : 'None yet.'}</td></tr>`}</tbody></table>
      <table><thead><tr><th>Estimated win</th><th class="r">Expected</th><th class="r">Actual</th><th class="r">Lines</th></tr></thead>
        <tbody>${calib || '<tr><td colspan="4" class="faint">No graded lines yet.</td></tr>'}</tbody></table>
    </div>${slipTable}</div></details>`;
}
/* Plain-English slip outcomes */
function slipOutcome(legsWithResults, kind, stake) {
  if (legsWithResults.some(l => !l.result)) return null;
  const live = legsWithResults.filter(l => l.result === 'hit' || l.result === 'miss');
  const hits = live.filter(l => l.result === 'hit').length, n = live.length;
  if (n < 2) return { n, hits, mult: 1, pl: 0, type: 'Refunded' };
  const mult = kind === 'flex' && n >= 3 ? (PAYOUTS.flex[n][hits] || 0) : (hits === n ? PAYOUTS.power[n] : 0);
  return { n, hits, mult, pl: Math.round(stake * (mult - 1) * 100) / 100, type: `${n}-pick ${kind === 'flex' && n >= 3 ? 'Flex' : 'Power'}` };
}
function explainSlip(o) {
  if (!o) return '';
  const money2 = v => (v >= 0 ? '+' : '-') + money(Math.abs(v));
  if (o.sat_out) return 'Sat out (no bet)';
  if (o.type === 'Refunded') return 'Refunded (too many players sat out) · $0.00';
  const head = `${o.hits} of ${o.n} hit · ${o.type}`;
  if (o.mult > 1) return `${head} paid ${o.mult}× · ${money2(o.pl)}`;
  if (o.mult === 1) return `${head} paid back 1× · $0.00`;
  if (o.mult > 0) return `${head} paid ${o.mult}× · ${money2(o.pl)}`;
  return `${head} lost · ${money2(o.pl)}`;
}
function savedLegResult(slip, leg) {
  return slip.results[leg.id] || (state.results[`${slip.date}|${leg.id}`] || null);
}
let gradingSaved = false;
async function gradeSaved() {
  if (gradingSaved || !state.saved.length) return;
  gradingSaved = true;
  try {
    const now = Date.now(), todo = [];
    for (const slip of state.saved) for (const leg of slip.legs) {
      const known = savedLegResult(slip, leg);
      if (known && known.result) { slip.results[leg.id] = { result: known.result, actual: known.actual ?? null }; continue; }
      if (leg.commence && new Date(leg.commence).getTime() < now) todo.push(leg);
    }
    if (todo.length) {
      const res = await fetch('/api/grade', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ legs: todo }) }).then(r => r.json());
      for (const slip of state.saved) for (const leg of slip.legs) {
        const r = res[leg.id];
        if (!r) continue;
        if (r.result) slip.results[leg.id] = { result: r.result, actual: r.actual };
        else state.savedLive[leg.id] = r;
      }
    }
    persist();
  } catch (e) {} finally { gradingSaved = false; }
  if (state.view === 'record') render();
}
function renderMySlips() {
  if (!state.saved.length) return `<div class="card empty"><strong>No saved slips yet</strong>Build a slip on the Slip tab, set your stake to match your real entry, and tap <b>Save to My Slips</b>. It grades itself as games finish.</div>`;
  const plStr = v => (v >= 0 ? '+' : '-') + money(Math.abs(v));
  const outcomes = state.saved.map(sl => slipOutcome(sl.legs.map(l => ({ ...l, ...(savedLegResult(sl, l) || {}) })), sl.kind, sl.stake));
  const done = outcomes.filter(Boolean);
  const won = done.filter(o => o.pl > 0).length, net = done.reduce((t, o) => t + o.pl, 0);
  const staked = state.saved.reduce((t, sl, i) => t + (outcomes[i] ? sl.stake : 0), 0);
  let html = `<dl class="summary">
      <div class="card"><dt>Slips won</dt><dd>${won} of ${done.length}</dd><small>${state.saved.length - done.length} still playing</small></div>
      <div class="card"><dt>Net P/L</dt><dd class="${net > 0 ? 'pos' : net < 0 ? 'neg' : ''}">${done.length ? plStr(net) : '—'}</dd><small>simulated money</small></div>
      <div class="card"><dt>Staked</dt><dd>${money(staked)}</dd><small>on finished slips</small></div>
      <div class="card"><dt>Return</dt><dd>${staked ? Math.round((net / staked) * 100) + '%' : '—'}</dd><small>profit ÷ staked</small></div>
    </dl>`;
  html += state.saved.map((sl, i) => {
    const o = outcomes[i];
    const date = new Date(sl.date + 'T12:00').toLocaleDateString([], { weekday: 'short', month: 'short', day: 'numeric' });
    const label = `${sl.legs.length}-pick ${sl.kind === 'flex' ? 'Flex' : 'Power'} · $${sl.stake}`;
    const status = o ? `<b class="${o.pl > 0 ? 'pos' : o.pl < 0 ? 'neg' : ''}">${esc(explainSlip(o))}</b>`
      : `<span class="muted">${sl.legs.filter(l => (savedLegResult(sl, l) || {}).result === 'hit').length} hit so far · playing</span>`;
    const rows = sl.legs.map(l => {
      const r = savedLegResult(sl, l), lv = state.savedLive[l.id] || state.live[l.id];
      const actual = r && r.actual != null ? r.actual : lv && lv.value != null ? lv.value : '—';
      const tag = r && r.result ? resultTag({ result: r.result }) : lv && lv.state === 'in' ? '<span class="res pending" style="color:var(--neg)">LIVE</span>' : '<span class="res pending">PENDING</span>';
      return `<tr><td>${esc(l.player)}<div class="faint hide-sm" style="font-size:11.5px">${esc(leagueLabel(l.league))} · ${esc(l.prop)}</div></td>
        <td class="r">${l.line}</td><td><span class="${l.side === 'MORE' ? 'pos' : 'neg'}" style="font-weight:700;font-size:12px">${l.side}</span></td>
        <td class="r">${actual}</td><td class="r">${tag}</td></tr>`;
    }).join('');
    return `<details class="card fold" ${i === 0 ? 'open' : ''}><summary><div><b>${date}</b> <span class="faint" style="font-size:12px">${esc(label)}</span>
        <div style="font-size:12.5px;margin-top:2px">${status}</div></div><span class="chev">›</span></summary>
      <div class="fold-body"><table class="results"><thead><tr><th>Player</th><th class="r">Line</th><th>Pick</th><th class="r">Actual</th><th class="r">Result</th></tr></thead><tbody>${rows}</tbody></table>
        <div style="display:flex;justify-content:space-between;align-items:center;padding:8px 14px 10px">
          <span class="faint" style="font-size:11.5px">${sl.note ? esc(sl.note) + ' · ' : ''}saved on this device</span>
          <button class="link" data-delete-saved="${sl.id}">Delete</button></div></div></details>`;
  }).join('');
  return html + `<p class="footnote">Simulated money only, to mirror your real PrizePicks entries. Players who don't play drop out and the payout is recalculated, as on PrizePicks.</p>`;
}

function suggestionsPanel(rows) {
  if (!rows || !rows.length) return `<div class="card" style="padding:14px;margin-bottom:8px"><b>How every suggestion did</b>
    <p class="faint" style="font-size:12.5px;margin:4px 0 0">Fills in after the first full day of results.</p></div>`;
  const money2 = v => (v >= 0 ? '+' : '-') + money(Math.abs(v));
  const best = rows.filter(r => r.days >= 1).reduce((b, r) => (!b || r.pl > b.pl ? r : b), null);
  const line = r => `<tr>
      <td>${r.type === 'split' ? esc(r.label.replace('Split: ', '')) : `<b>${esc(r.label)}</b>`}${best && r === best && r.pl > 0 ? ' <span class="res hit">BEST</span>' : ''}</td>
      <td class="r">${r.cashed} of ${r.days}${r.sat_out ? `<div class="faint" style="font-size:11px">${r.sat_out} sat out</div>` : ''}</td>
      <td class="r ${r.pl > 0 ? 'pos' : r.pl < 0 ? 'neg' : ''}"><b>${money2(r.pl)}</b></td>
      <td class="r faint">${r.roi == null ? '—' : (r.roi >= 0 ? '+' : '') + Math.round(r.roi * 100) + '%'}</td></tr>`;
  const head = '<thead><tr><th>Slip</th><th class="r">Cashed</th><th class="r">P/L</th><th class="r">Return</th></tr></thead>';
  const singles = rows.filter(r => r.type !== 'split'), splits = rows.filter(r => r.type === 'split');
  return `<details class="card fold learn" open><summary><div><b>How every suggestion did</b>
      <div class="faint" style="font-size:12px">Every slip it suggested, replayed at $10 each, played or not</div></div><span class="chev">›</span></summary>
    <div class="fold-body" style="padding:10px 14px 14px">
      <table>${head}<tbody>${singles.map(line).join('')}</tbody></table>
      ${splits.length ? `<div class="section-label" style="margin:14px 0 4px">Split suggestions ($10 per slip in the split)</div><table>${head}<tbody>${splits.map(line).join('')}</tbody></table>` : ''}
      <p class="faint" style="font-size:12px;margin:10px 0 0">Entry sizes use the day's top picks in order, like the Slip tab. A few days of results is mostly luck; look for patterns over weeks.</p>
    </div></details>`;
}
function areasPanel(areas) {
  if (!areas || !areas.length) return '';
  const rows = areas.filter(a => a.n >= 3).slice(0, 14).map(a => `<tr>
      <td>${esc(leagueLabel(a.sport))} ${esc(a.prop)} ${a.side === '*' ? '<span class="faint" style="font-size:11px">both sides</span>'
        : `<span class="${a.side === 'MORE' ? 'pos' : 'neg'}" style="font-weight:700;font-size:11px">${a.side}</span>`}
        ${a.cold ? ' <span class="res miss">SKIPPED</span>' : ''}</td>
      <td class="r ${a.hit_rate >= a.expected ? 'pos' : 'neg'}">${Math.round(a.hit_rate * 100)}%</td>
      <td class="r faint">${Math.round(a.expected * 100)}%</td><td class="r faint">${a.n}</td></tr>`).join('');
  const cold = areas.filter(a => a.cold).length;
  return `<details class="card fold learn"><summary><div><b>Where it wins</b>
      <div class="faint" style="font-size:12px">${cold ? `${cold} losing area${cold === 1 ? '' : 's'} now skipped` : 'Every league, prop and side it has graded'}</div></div><span class="chev">›</span></summary>
    <div class="fold-body" style="padding:10px 14px 14px">
      <table><thead><tr><th>Area</th><th class="r">Hit</th><th class="r">Expected</th><th class="r">Lines</th></tr></thead>
      <tbody>${rows || '<tr><td colspan="4" class="faint">Not enough graded lines yet.</td></tr>'}</tbody></table>
      <p class="faint" style="font-size:12px;margin:10px 0 0">An area (one side, or both sides of a prop together) is skipped automatically once it has 40+ graded lines, hits under 50%, and runs 5+ points below what was expected.</p>
    </div></details>`;
}
function renderRecord() {
  const el = $('#view-record'), h = state.history;
  if (!state.recordTab) state.recordTab = state.saved.length ? 'mine' : 'daily';
  const tabs = `<div class="seg wide"><button data-rtab="mine" class="${state.recordTab === 'mine' ? 'on' : ''}">My slips</button><button data-rtab="daily" class="${state.recordTab === 'daily' ? 'on' : ''}">Daily picks</button></div>`;
  if (state.recordTab === 'mine') {
    el.innerHTML = `<h2 class="h2">Record</h2><p class="sub">Your saved slips, graded automatically.</p>` + tabs + renderMySlips();
    return;
  }
  if (!h) { el.innerHTML = '<div class="card empty"><span class="spinner"></span>&nbsp; Checking results…</div>'; return; }
  const s = h.summary;
  const plStr = v => (v >= 0 ? '+' : '-') + money(Math.abs(v));
  const plCls = v => v > 0 ? 'pos' : v < 0 ? 'neg' : '';
  const leagues = Object.entries(s.by_sport).filter(([, v]) => v.hit + v.miss).map(([k, v]) => `${leagueLabel(k)} ${v.hit}-${v.miss}`).join(' · ');
  const extras = [s.push ? `${s.push} push` : '', s.void ? `${s.void} void` : '', s.pending ? `${s.pending} pending` : ''].filter(Boolean).join(' · ');
  let html = `<h2 class="h2">Record</h2><p class="sub">Every daily pick, graded from ESPN box scores.</p>` + tabs + `
    <dl class="summary">
      <div class="card"><dt>Picks hit</dt><dd>${s.hit}-${s.miss}</dd><small>${extras || 'wins - losses'}</small></div>
      <div class="card"><dt>Hit rate</dt><dd>${s.hit_rate == null ? '—' : pct(s.hit_rate)}</dd><small>${esc(leagues) || 'no graded picks yet'}</small></div>
      <div class="card"><dt>Slips won</dt><dd>${s.slips_cashed} of ${s.slips}</dd><small>${s.sat_out ? `${s.sat_out} sat out` : 'suggested entries'}</small></div>
      <div class="card"><dt>Slip P/L</dt><dd class="${plCls(s.slip_pl)}">${s.slips ? plStr(s.slip_pl) : '—'}</dd><small>at $${s.stake} each</small></div>
    </dl>` + suggestionsPanel(h.suggestions) + learningPanel(h.model) + areasPanel(h.areas) + `<div class="section-label">Past slips</div>`;
  if (!h.days.length) html += '<div class="card empty"><strong>No slips yet</strong>Your first daily slip will show up here.</div>';
  html += h.days.map((d, i) => {
    const hits = d.picks.filter(p => p.result === 'hit').length;
    const decided = d.picks.filter(p => p.result === 'hit' || p.result === 'miss').length;
    const pending = d.picks.filter(p => !p.result).length;
    const label = new Date(d.date + 'T12:00').toLocaleDateString([], { weekday: 'short', month: 'short', day: 'numeric' });
    const right = d.slip ? `<b class="${plCls(d.slip.pl)}" style="font-size:12.5px">${esc(explainSlip(d.slip))}</b>`
      : `<span class="muted">${hits} of ${decided} hit · ${pending} playing</span>`;
    const rows = d.picks.map(p => {
      const lv = state.live[p.id];
      const actual = p.actual ?? (lv && lv.value != null ? lv.value : '—');
      const result = p.result ? resultTag({ result: p.result }) : lv && lv.state === 'in' ? `<span class="res pending" style="color:var(--neg)">LIVE</span>` : '<span class="res pending">PENDING</span>';
      return `<tr><td>${esc(p.player)}<div class="faint hide-sm" style="font-size:11.5px">${esc(leagueLabel(p.sport))} · ${esc(p.prop)}</div></td>
        <td class="r">${p.line}</td><td><span class="${p.side === 'MORE' ? 'pos' : 'neg'}" style="font-weight:700;font-size:12px">${p.side}</span></td>
        <td class="r">${actual}</td><td class="r">${result}</td></tr>`;
    }).join('');
    return `<details class="card fold" ${i === 0 ? 'open' : ''}><summary><div><b>${label}</b><div style="margin-top:2px">${right}</div></div>
      <span class="chev">›</span></summary>
      <div class="fold-body"><table class="results"><thead><tr><th>Player</th><th class="r">Line</th><th>Pick</th><th class="r">Actual</th><th class="r">Result</th></tr></thead><tbody>${rows}</tbody></table></div></details>`;
  }).join('');
  html += `<p class="footnote">Slip P/L assumes you played each day's suggested entry at $${s.stake}, and $0 on days it said to sit out. Players who don't play are voided and drop out, as on PrizePicks.</p>`;
  el.innerHTML = html;
}

/* ───────── Research ───────── */
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
  } catch (err) { showMsg('Could not reach the app.'); }
  finally { btn.disabled = false; btn.textContent = 'Analyze'; }
});
function renderReport(r) {
  const v = r.verdict, rc = r.recent, m = r.matchup, ng = r.next_game;
  const box = (label, w) => `<div class="stat-box"><dt>${label}</dt><dd>${hitStr(w, v.side)}</dd><small>${w && w.n ? 'avg ' + w.avg : 'no games'}</small></div>`;
  $('#report').innerHTML = `
  <div class="card report">
    <div style="display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap">
      <div><div style="font-size:17px;font-weight:700">${esc(r.player.name)}</div><div class="muted" style="font-size:12.5px">${esc([r.player.team, r.player.position, r.sport_label].filter(Boolean).join(' · '))}</div></div>
      <div style="text-align:right"><div class="muted" style="font-size:12px">${esc(r.prop)}</div><div style="font-size:20px;font-weight:700">${r.line}</div></div>
    </div>
    <dl class="report-grid">
      ${box('Last 5', rc.l5)}${box('Last 10', rc.l10)}${box('Season', rc.season)}${box(rc.vs_opp_abbr ? 'vs ' + esc(rc.vs_opp_abbr) : 'vs opponent', rc.vs_opp)}
      <div class="stat-box"><dt>Matchup</dt><dd>${m ? m.tier : '—'}</dd><small>${m ? `#${m.rank} of ${m.of}` : ng ? 'no rating' : 'no game'}</small></div>
    </dl>
    ${spark(r.chart, r.line, v.side, 600, 70)}
    <p style="margin:12px 0 0">History leans <b class="${v.side === 'MORE' ? 'pos' : 'neg'}">${v.side}</b> <span class="muted">· ${v.score}% weighted hit rate · ${esc(v.label.toLowerCase())}</span></p>
    <ul class="reasons">${v.reasons.map(x => `<li>${esc(x)}</li>`).join('')}${r.notes.map(n => `<li>${esc(n)}</li>`).join('')}</ul>
    <div style="display:flex;gap:8px;margin-top:14px;flex-wrap:wrap">
      <button class="btn ${v.side === 'MORE' ? 'btn-primary' : ''}" data-add="MORE">Add MORE to slip</button>
      <button class="btn ${v.side === 'LESS' ? 'btn-primary' : ''}" data-add="LESS">Add LESS to slip</button>
    </div>
  </div>`;
  $('#report').querySelectorAll('[data-add]').forEach(b => b.addEventListener('click', () => {
    const id = `r|${r.sport}|${r.player.name}|${r.prop}`.toLowerCase();
    state.researched = state.researched.filter(p => p.id !== id).concat([{ id, player: r.player.name, league: r.sport, prop: r.prop,
      line: r.line, side: b.dataset.add, prob: null, team: r.player.team, espn_id: r.player.id,
      commence: r.next_game ? r.next_game.date : null, game: '' }]);
    if (!state.slip.includes(id)) togglePick(id); else render();
    toast(`${r.player.name} ${b.dataset.add} ${r.line} added to your slip`);
  }));
}

/* ───────── Phone access (Mac version only) ───────── */
if (['127.0.0.1', 'localhost'].includes(location.hostname) && !window.CLOUD_META) $('#phoneBtn').hidden = false;
$('#phoneBtn').addEventListener('click', async () => {
  const r = await fetch('/api/phone').then(x => x.json()).catch(() => null);
  if (!r || r.error) return;
  const m = document.createElement('div'); m.className = 'modal';
  m.innerHTML = `<div class="card"><h3>Open on your phone</h3>
    <p>Point your iPhone camera at this code, or open the link. The key in the link is checked once, then remembered.</p>
    ${r.qr ? `<div class="qr">${r.qr}</div>` : ''}<code>${esc(r.url)}</code>
    <ul style="padding-left:18px;margin:12px 0 0"><li>Same Wi-Fi as this Mac, and the Mac must be awake.</li></ul>
    <div style="text-align:right;margin-top:14px"><button class="btn" data-close>Done</button></div></div>`;
  m.addEventListener('click', ev => { if (ev.target === m || ev.target.hasAttribute('data-close')) m.remove(); });
  document.body.appendChild(m);
});

function render() {
  renderHeader();
  if (state.view === 'today') renderToday();
  if (state.view === 'slip') renderSlipView();
  if (state.view === 'record') renderRecord();
  persist();
}
fillLeagues(); render(); loadDaily(false); loadHistory(); loadLive(); loadAlerts();
setInterval(loadHistory, 10 * 60 * 1000);
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
    if "--auto" in sys.argv:               # what the cloud job runs every 15 minutes
        hour = datetime.now().hour
        scan_hours = (11, 13) if 11 <= hour <= 13 else (15, 17) if 15 <= hour <= 17 else None
        d = load_daily()
        tried = d and d.get("scanned_at") and scan_hours and scan_hours[0] <= int(d["scanned_at"][11:13]) <= scan_hours[1]
        if scan_hours and not tried:
            run_scheduled_scan()            # at most one paid attempt per window; 0 credits once locked
        else:
            grade_history()
            fit_model(load_history())
        if hour >= 9 or hour <= 1:
            for a in check_injuries():
                print(f"[{datetime.now():%H:%M}] Injury alert: {a['player']} ({a['team']}) {a['status']}, {len(a['teammates'])} teammates to check")
        sys.exit()
    if "--watch" in sys.argv:              # injury news only (free)
        print(f"{len(check_injuries())} new injury alert(s)")
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
