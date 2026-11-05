/* cloud.js — lets the Daily Slip page run with no server behind it (GitHub Pages).
 *
 * The page asks for data with fetch('/api/...'), exactly as it does on the Mac.
 * This file answers those calls in the browser instead:
 *   - picks, record and learning data come from docs/data.enc, decrypted here with your passphrase
 *   - live stats, player research and "line changed" are worked out here from ESPN's free data
 * The analysis mirrors sports_app.py; settings come from window.CLOUD_META, which publish.py
 * fills from sports_app.py so the two stay in step.
 */
(() => {
  const META = window.CLOUD_META;
  const ESPN_COMMON = 'https://site.web.api.espn.com/apis/common/v3';
  const ESPN_SITE = 'https://site.api.espn.com/apis';
  const realFetch = window.fetch.bind(window);
  const store = {
    get(k, d) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} },
    del(k) { try { localStorage.removeItem(k); } catch (e) {} }
  };

  /* ───────── Unlock: passphrase → AES key → decrypted bundle ───────── */
  const b64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
  const toB64 = buf => btoa(String.fromCharCode(...new Uint8Array(buf)));
  let bundleMeta = null, aesKey = null, data = null, loadedAt = 0, resolveReady;
  const ready = new Promise(r => { resolveReady = r; });

  async function fetchBundle() {
    const r = await realFetch('data.enc?t=' + Date.now(), { cache: 'no-store' });
    if (!r.ok) throw new Error('missing');
    return r.json();
  }
  async function keyFromPassphrase(pw, salt, iter) {
    const base = await crypto.subtle.importKey('raw', new TextEncoder().encode(pw), 'PBKDF2', false, ['deriveKey']);
    return crypto.subtle.deriveKey({ name: 'PBKDF2', salt: b64(salt), iterations: iter, hash: 'SHA-256' },
      base, { name: 'AES-GCM', length: 256 }, true, ['decrypt']);
  }
  async function open(bundle, key) {
    const plain = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: b64(bundle.iv) }, key, b64(bundle.ct));
    return JSON.parse(new TextDecoder().decode(plain));
  }
  async function refresh(force) {
    if (!force && data && Date.now() - loadedAt < 5 * 60 * 1000) return data;
    const b = await fetchBundle();
    bundleMeta = b;
    data = await open(b, aesKey);
    loadedAt = Date.now();
    return data;
  }

  function showLock(message) {
    let el = document.getElementById('cloudLock');
    if (!el) {
      el = document.createElement('div');
      el.id = 'cloudLock';
      el.style.cssText = 'position:fixed;inset:0;z-index:100;background:#0a0f1d;display:grid;place-items:center;padding:24px';
      el.innerHTML = `<form style="width:100%;max-width:340px;font-family:Inter,system-ui,sans-serif;color:#e6e9ef">
          <div style="font-size:20px;font-weight:600;margin-bottom:4px">Daily Slip</div>
          <div style="color:#8b94a7;font-size:14px;margin-bottom:18px">Enter your passphrase to unlock your picks.</div>
          <input id="cloudPw" type="password" autocomplete="current-password" placeholder="Passphrase"
            style="width:100%;box-sizing:border-box;background:#0f1627;border:1px solid rgba(148,163,184,.25);border-radius:10px;padding:12px;color:#e6e9ef;font-size:16px">
          <label style="display:flex;gap:8px;align-items:center;color:#8b94a7;font-size:13px;margin:12px 0">
            <input id="cloudRemember" type="checkbox" checked> Remember on this device</label>
          <button style="width:100%;background:#8fb3ff;color:#0a0f1d;border:0;border-radius:10px;padding:12px;font-weight:600;font-size:15px">Unlock</button>
          <div id="cloudMsg" style="color:#f07178;font-size:13px;margin-top:10px;min-height:18px"></div></form>`;
      document.body.appendChild(el);
      el.querySelector('form').addEventListener('submit', async e => {
        e.preventDefault();
        const pw = el.querySelector('#cloudPw').value;
        const msg = el.querySelector('#cloudMsg');
        msg.style.color = '#8b94a7'; msg.textContent = 'Unlocking…';
        try {
          const b = bundleMeta || await fetchBundle();
          const key = await keyFromPassphrase(pw, b.salt, b.iter);
          data = await open(b, key);
          aesKey = key; bundleMeta = b; loadedAt = Date.now();
          if (el.querySelector('#cloudRemember').checked) {
            store.set('ps_unlock', { salt: b.salt, key: toB64(await crypto.subtle.exportKey('raw', key)) });
          }
          el.remove();
          resolveReady();
        } catch (err) {
          msg.style.color = '#f07178';
          msg.textContent = err.message === 'missing' ? 'No data published yet. Check back after the first scan.' : 'That passphrase doesn\'t match.';
        }
      });
    }
    if (message) el.querySelector('#cloudMsg').textContent = message;
    setTimeout(() => el.querySelector('#cloudPw').focus(), 50);
  }

  (async () => {
    try {
      bundleMeta = await fetchBundle();
    } catch (e) {
      showLock('No data published yet. Check back after the first scan.');
      return;
    }
    const saved = store.get('ps_unlock', null);
    if (saved && saved.salt === bundleMeta.salt) {
      try {
        aesKey = await crypto.subtle.importKey('raw', b64(saved.key), 'AES-GCM', true, ['decrypt']);
        data = await open(bundleMeta, aesKey);
        loadedAt = Date.now();
        resolveReady();
        return;
      } catch (e) { store.del('ps_unlock'); }
    }
    showLock();
  })();

  /* ───────── Small helpers ───────── */
  const cache = new Map();
  async function getJSON(url, params = {}, ttl = 600) {
    const q = new URLSearchParams(params).toString();
    const full = q ? `${url}?${q}` : url;
    const hit = cache.get(full);
    if (hit && Date.now() - hit.t < ttl * 1000) return hit.v;
    const r = await realFetch(full);
    if (!r.ok) throw new Error(`HTTP ${r.status}`);
    const v = await r.json();
    cache.set(full, { t: Date.now(), v });
    return v;
  }
  const parseDate = s => new Date(s);
  const fmtLine = v => String(+(+v).toFixed(2));
  function normalize(name) {
    return String(name).normalize('NFKD').replace(/[̀-ͯ]/g, '').toLowerCase()
      .replace(/[.']/g, '').replace(/-/g, ' ').split(/\s+/)
      .filter(p => p && !['jr', 'sr', 'ii', 'iii', 'iv'].includes(p)).join(' ');
  }
  const etParts = d => Object.fromEntries(new Intl.DateTimeFormat('en-CA', {
    timeZone: 'America/New_York', year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', hour12: false
  }).formatToParts(d).map(p => [p.type, p.value]));
  const todayET = () => { const p = etParts(new Date()); return `${p.year}-${p.month}-${p.day}`; };
  function etTime(dateStr, hour) {          // a given Eastern date + hour, as a real Date
    const [y, m, d] = dateStr.split('-').map(Number);
    for (const off of [4, 5]) {
      const t = new Date(Date.UTC(y, m - 1, d, hour + off));
      if (+etParts(t).hour % 24 === hour) return t;
    }
    return new Date(Date.UTC(y, m - 1, d, hour + 5));
  }

  /* ───────── Prop formulas (ESPN game-log stat names), as in sports_app.py ───────── */
  const num = (row, k) => { if (!(k in row)) throw 0; const v = parseFloat(row[k]); if (!isFinite(v) || /[-/]/.test(String(row[k]).slice(1))) throw 0; return v; };
  const stat = (...ks) => row => ks.reduce((s, k) => s + num(row, k), 0);
  const made = k => row => { if (!(k in row)) throw 0; const v = parseFloat(String(row[k]).split('-')[0]); if (!isFinite(v)) throw 0; return v; };
  const totalBases = r => num(r, 'hits') + num(r, 'doubles') + 2 * num(r, 'triples') + 3 * num(r, 'homeRuns');
  const pitchingOuts = r => { if (!('innings' in r)) throw 0; const [w, f] = String(r.innings).split('.'); const o = parseInt(w) * 3 + parseInt(f || 0); if (!isFinite(o)) throw 0; return o; };
  const PROPS = {
    basketball: { 'Points': stat('points'), 'Rebounds': stat('totalRebounds'), 'Assists': stat('assists'),
      'Pts+Rebs+Asts': stat('points', 'totalRebounds', 'assists'), 'Pts+Rebs': stat('points', 'totalRebounds'),
      'Pts+Asts': stat('points', 'assists'), 'Rebs+Asts': stat('totalRebounds', 'assists'),
      '3-PT Made': made('threePointFieldGoalsMade-threePointFieldGoalsAttempted'), 'Steals': stat('steals'),
      'Blocks': stat('blocks'), 'Blks+Stls': stat('blocks', 'steals'), 'Turnovers': stat('turnovers') },
    football: { 'Pass Yards': stat('passingYards'), 'Pass TDs': stat('passingTouchdowns'), 'Pass Attempts': stat('passingAttempts'),
      'Completions': stat('completions'), 'Interceptions': stat('interceptions'), 'Rush Yards': stat('rushingYards'),
      'Rush Attempts': stat('rushingAttempts'), 'Receptions': stat('receptions'), 'Receiving Yards': stat('receivingYards'),
      'Rush+Rec Yards': stat('rushingYards', 'receivingYards') },
    baseball: { 'Hits': stat('hits'), 'Runs': stat('runs'), 'RBIs': stat('RBIs'), 'Home Runs': stat('homeRuns'),
      'Total Bases': totalBases, 'Hits+Runs+RBIs': stat('hits', 'runs', 'RBIs'), 'Walks': stat('walks'),
      'Stolen Bases': stat('stolenBases'), 'Strikeouts': stat('strikeouts'), 'Pitching Outs': pitchingOuts,
      'Earned Runs Allowed': stat('earnedRuns'), 'Hits Allowed': stat('hits') },
    hockey: { 'Points': stat('points'), 'Goals': stat('goals'), 'Assists': stat('assists'),
      'Shots on Goal': stat('shotsTotal'), 'Goalie Saves': stat('saves') },
    soccer: { 'Goals': stat('totalGoals'), 'Assists': stat('goalAssists'), 'Goal+Assist': stat('totalGoals', 'goalAssists'),
      'Shots': stat('totalShots'), 'Shots on Target': stat('shotsOnTarget') }
  };
  const sportOf = key => META.sports[key];
  const calcFor = (key, prop) => (PROPS[(sportOf(key) || {}).group] || {})[prop];
  const tryCalc = (calc, row) => { try { return calc(row); } catch (e) { return null; } };

  /* ───────── ESPN data layer ───────── */
  async function searchPlayers(key, query, limit = 6) {
    const s = sportOf(key);
    const items = (await getJSON(`${ESPN_COMMON}/search`, { query, limit: 15, type: 'player' })).items || [];
    let same = items.filter(i => ((i.uid || '') + '~').includes(`s:${s.sid}~`));
    if (s.lid) {
      const lg = same.filter(i => (i.uid || '').includes(`l:${s.lid}~`));
      same = lg.concat(same.filter(i => !lg.includes(i)));
    }
    const target = normalize(query);
    same.sort((a, b) => (normalize(a.displayName || '') !== target) - (normalize(b.displayName || '') !== target));
    return same.slice(0, limit).map(i => ({ id: i.id, name: i.displayName || '', sub: i.subtitle || i.description || '' }));
  }
  async function gameLog(key, pid, season) {
    const [sp, lg] = sportOf(key).path;
    const d = await getJSON(`${ESPN_COMMON}/sports/${sp}/${lg}/athletes/${pid}/gamelog`, season ? { season } : {});
    const names = d.names || [], meta = d.events || {}, games = [], seen = new Set();
    for (const st of d.seasonTypes || []) {
      if (/\bpre-?\s?season\b/i.test(st.displayName || '')) continue;
      for (const cat of st.categories || []) for (const ev of cat.events || []) {
        if (seen.has(ev.eventId)) continue;
        seen.add(ev.eventId);
        const m = meta[ev.eventId] || {}, opp = m.opponent || {};
        const row = {}; names.forEach((n, i) => { row[n] = (ev.stats || [])[i]; });
        games.push({ date: m.gameDate || '', opp_id: String(opp.id || ''), opp: opp.abbreviation || '', at_vs: m.atVs || '', row });
      }
    }
    games.sort((a, b) => (a.date < b.date ? 1 : -1));
    const f = (d.filters || []).find(x => x.name === 'season');
    return { games, seasons: f ? (f.options || []).map(o => String(o.value)) : [] };
  }
  async function playerProfile(key, pid) {
    const [sp, lg] = sportOf(key).path;
    try {
      const a = (await getJSON(`${ESPN_COMMON}/sports/${sp}/${lg}/athletes/${pid}`)).athlete || {};
      const team = a.team || {};
      return { name: a.displayName || '', team_id: String(team.id || ''), team: team.displayName || '',
               headshot: (a.headshot || {}).href || '', position: (a.position || {}).abbreviation || '' };
    } catch (e) { return {}; }
  }
  async function nextGame(key, teamId) {
    if (!teamId) return null;
    const [sp, lg] = sportOf(key).path;
    const cutoff = Date.now() - 4 * 3600e3;
    for (const params of [{}, { fixture: 'true' }]) {
      let sch;
      try { sch = await getJSON(`${ESPN_SITE}/site/v2/sports/${sp}/${lg}/teams/${teamId}/schedule`, params); } catch (e) { continue; }
      const evs = (sch.events || []).slice().sort((a, b) => (a.date > b.date ? 1 : -1));
      for (const e of evs) {
        try {
          if (parseDate(e.date) < cutoff) continue;
          const comp = e.competitions[0];
          if (((comp.status || {}).type || {}).completed) continue;
          const opp = comp.competitors.find(c => String(c.team.id) !== teamId);
          const me = comp.competitors.find(c => String(c.team.id) === teamId);
          if (!opp || !me) continue;
          return { date: e.date, opp_id: String(opp.team.id), opp: opp.team.displayName || '', opp_abbr: opp.team.abbreviation || '', home: me.homeAway === 'home' };
        } catch (err) { continue; }
      }
    }
    return null;
  }
  async function teamTable(key) {
    const [sp, lg] = sportOf(key).path;
    const st = await getJSON(`${ESPN_SITE}/v2/sports/${sp}/${lg}/standings`);
    const entries = node => ((node.standings || {}).entries || []).concat(...(node.children || []).map(entries));
    const table = {};
    for (const e of entries(st)) {
      const s = {};
      for (const x of e.stats || []) if (!(x.name in s)) s[x.name] = x.value;
      const gp = s.gamesPlayed || ['wins', 'losses', 'ties', 'overtimeLosses', 'otLosses'].reduce((t, k) => t + (s[k] || 0), 0);
      const allowed = s.avgPointsAgainst || (gp ? (s.pointsAgainst || 0) / gp : null);
      const scored = s.avgPointsFor || (gp ? (s.pointsFor || 0) / gp : null);
      if (allowed && scored && gp) table[String((e.team || {}).id || '')] = [allowed, scored];
    }
    return table;
  }
  async function matchupRating(key, oppId, useOffense) {
    let table;
    try { table = await teamTable(key); } catch (e) { return null; }
    if (!(oppId in table)) return null;
    const ids = Object.keys(table), n = ids.length, allowed = sportOf(key).allowed;
    const order = useOffense ? ids.sort((a, b) => table[b][1] - table[a][1]) : ids.sort((a, b) => table[a][0] - table[b][0]);
    const rank = order.indexOf(oppId) + 1;
    const value = useOffense ? table[oppId][1] : table[oppId][0];
    return { tier: rank <= n / 3 ? 'Tough' : rank > 2 * n / 3 ? 'Soft' : 'Average', rank, of: n,
             per_game: Math.round(value * 10) / 10, what: `${allowed} ${useOffense ? 'scored' : 'allowed'}`,
             basis: useOffense ? 'offense' : 'defense' };
  }
  function windowStats(values, line) {
    const n = values.length, over = values.filter(v => v > line).length, under = values.filter(v => v < line).length;
    return { n, over, under, push: n - over - under, avg: n ? Math.round(values.reduce((a, b) => a + b, 0) / n * 10) / 10 : null,
             rate: over + under ? over / (over + under) : null };
  }

  async function analyze(key, playerQuery, prop, line, playerId) {
    const s = sportOf(key);
    const calc = calcFor(key, prop);
    if (!calc) throw new Error(`${prop} isn't a supported ${s.label} prop.`);
    if (!playerId) {
      const m = await searchPlayers(key, playerQuery, 1);
      if (!m.length) throw new Error(`No ${s.label} player found for "${playerQuery}".`);
      playerId = m[0].id;
    }
    const profile = await playerProfile(key, playerId);
    const { games, seasons } = await gameLog(key, playerId);
    const notes = [];
    let older = [];
    if (games.length < 10 && seasons.length > 1) {
      try { older = (await gameLog(key, playerId, seasons[1])).games; } catch (e) { older = []; }
      if (older.length) notes.push("Fewer than 10 games this season, so last season's most recent games fill out the L5/L10 windows.");
    }
    const pts = gs => gs.map(g => [g, tryCalc(calc, g.row)]).filter(([, v]) => v != null);
    const seasonPts = pts(games), allPts = seasonPts.concat(pts(older));
    if (!allPts.length) throw new Error(`No ${prop} stats in ${profile.name || playerQuery}'s game log. Check the prop fits their position and the sport is right.`);
    const vals = allPts.map(([, v]) => v);
    const recent = { l5: windowStats(vals.slice(0, 5), line), l10: windowStats(vals.slice(0, 10), line),
                     season: seasonPts.length ? windowStats(seasonPts.map(([, v]) => v), line) : windowStats(vals, line) };
    if (!seasonPts.length) notes.push("No games yet this season; 'Season' shows last season.");
    else if (seasonPts.length < 5) notes.push(`Only ${seasonPts.length} game(s) this season, so treat the season numbers as a small sample.`);

    const nxt = await nextGame(key, profile.team_id);
    let match = null;
    if (nxt) {
      const useOffense = META.offense_props.includes(prop) || (prop === 'Strikeouts' && META.pitcher_positions.includes(profile.position));
      match = await matchupRating(key, nxt.opp_id, useOffense);
      const vs = allPts.filter(([g]) => g.opp_id === nxt.opp_id).map(([, v]) => v);
      recent.vs_opp = vs.length ? windowStats(vs, line) : null;
      recent.vs_opp_abbr = nxt.opp_abbr;
    }
    const parts = Object.keys(META.weights).filter(k => recent[k].rate != null).map(k => [META.weights[k], recent[k].rate]);
    if (!parts.length) throw new Error("Every recent game landed exactly on this line, so there's no lean to measure.");
    const overRate = parts.reduce((t, [w, r]) => t + w * r, 0) / parts.reduce((t, [w]) => t + w, 0);
    const side = overRate >= 0.5 ? 'MORE' : 'LESS', score = Math.max(overRate, 1 - overRate);
    const label = score >= 0.6 ? 'Strong lean' : score >= 0.55 ? 'Lean' : 'Toss-up';
    const hits = w => (side === 'MORE' ? w.over : w.under);
    const reasons = [], l10 = recent.l10, ssn = recent.season;
    reasons.push(`Went ${side.toLowerCase()} ${fmtLine(line)} in ${hits(l10)} of last ${l10.n} (avg ${l10.avg}).`);
    if (ssn.n) { const diff = ssn.avg - line; reasons.push(`Season average ${ssn.avg} (${diff >= 0 ? '+' : ''}${diff.toFixed(1)} vs the line) over ${ssn.n} games.`); }
    if (nxt && match) reasons.push(`Next: ${nxt.home ? 'vs' : '@'} ${nxt.opp_abbr}, a ${match.tier.toLowerCase()} matchup (#${match.rank} of ${match.of} in ${match.what}, ${match.per_game}/game).`);
    else if (nxt) reasons.push(`Next: ${nxt.home ? 'vs' : '@'} ${nxt.opp_abbr} (no standings data for a matchup rating).`);
    else reasons.push('No upcoming game found on the schedule.');
    if (recent.vs_opp) { const vo = recent.vs_opp; reasons.push(`Vs ${recent.vs_opp_abbr} in fetched games: ${side.toLowerCase()} ${hits(vo)} of ${vo.n} (avg ${vo.avg}).`); }
    const chart = allPts.slice(0, 10).map(([g, v]) => ({ date: g.date.slice(0, 10), opp: g.opp, at_vs: g.at_vs, value: v })).reverse();
    return { sport: key, sport_label: s.label, group: s.group,
             player: { id: playerId, name: profile.name || playerQuery, team: profile.team || '', position: profile.position || '', headshot: profile.headshot || '' },
             prop, line, recent, chart, next_game: nxt, matchup: match,
             verdict: { side, score: Math.round(score * 100), label, reasons }, notes };
  }

  /* ───────── Live in-game stats ───────── */
  async function findEvent(key, p) {
    const [sp, lg] = sportOf(key).path;
    const start = parseDate(p.commence);
    const day = new Date(start.getTime() - 5 * 3600e3).toISOString().slice(0, 10).replace(/-/g, '');
    const params = { dates: day, limit: 400 };
    if (META.scoreboard_groups[key]) params.groups = META.scoreboard_groups[key];
    const sb = await getJSON(`${ESPN_SITE}/site/v2/sports/${sp}/${lg}/scoreboard`, params, 30);
    const teamId = p.espn_id ? (await playerProfile(key, p.espn_id)).team_id : '';
    for (const e of sb.events || []) {
      try {
        if (Math.abs(parseDate(e.date) - start) > 3 * 3600e3) continue;
        const teams = e.competitions[0].competitors;
        const ids = teams.map(c => String(c.team.id)), names = teams.map(c => c.team.displayName || '');
        if ((teamId && ids.includes(teamId)) || names.every(n => n && (p.game || '').includes(n))) return e;
      } catch (err) { continue; }
    }
    return null;
  }
  async function boxRows(key, eventId) {
    const [sp, lg] = sportOf(key).path;
    const sm = await getJSON(`${ESPN_SITE}/site/v2/sports/${sp}/${lg}/summary`, { event: eventId }, 30);
    const rows = {};
    for (const team of (sm.boxscore || {}).players || []) for (const grp of team.statistics || []) {
      const keys = grp.keys || grp.names || [];
      for (const a of grp.athletes || []) {
        const aid = String((a.athlete || {}).id || '');
        if (!aid || !(a.stats || []).length) continue;
        const row = rows[aid] = rows[aid] || {};
        keys.forEach((k, i) => {
          const v = a.stats[i];
          if (k === 'completions/passingAttempts') { const [c, att] = String(v).split('/'); row.completions = c; row.passingAttempts = att; }
          else row[META.box_aliases[k] || k] = v;
        });
      }
    }
    for (const team of sm.rosters || []) for (const r of team.roster || []) {
      const aid = String((r.athlete || {}).id || '');
      const st = {}; (r.stats || []).forEach(x => { if (x && x.name && x.value != null) st[x.name] = String(x.value); });
      if (aid && Object.keys(st).length) rows[aid] = Object.assign(rows[aid] || {}, st);
    }
    if (sportOf(key).group === 'hockey') for (const row of Object.values(rows)) {
      if (!('points' in row) && 'goals' in row && 'assists' in row) row.points = String(+row.goals + +row.assists);
    }
    return rows;
  }
  function elapsedFraction(key, status) {
    const period = status.period || 0, clock = String(status.displayClock || '');
    if (sportOf(key).group === 'soccer') { const m = clock.match(/\d+/); return m ? Math.min(+m[0] / 90, 1) : null; }
    const gc = META.game_clock[key];
    if (!gc || !period) return null;
    const [periods, plen] = gc;
    if (period > periods) return 1;
    const [m, sec] = clock.split(':');
    const left = sec !== undefined ? +m + +sec / 60 : +m / 60;
    if (!isFinite(left)) return null;
    return Math.min(Math.max(((period - 1) * plen + (plen - left)) / (periods * plen), 0), 1);
  }
  const liveFinals = {};
  async function liveForPick(p) {
    const calc = calcFor(p.sport, p.prop);
    if (!calc || !p.commence) return null;
    if (!p.espn_id) { const f = await searchPlayers(p.sport, p.player, 1); p.espn_id = f.length ? f[0].id : null; }
    const e = await findEvent(p.sport, p);
    if (!e) return { state: 'unknown' };
    const status = e.status || {}, type = status.type || {};
    const out = { state: type.state || 'pre', detail: type.shortDetail || '' };
    if (out.state === 'pre') return out;
    const row = (await boxRows(p.sport, e.id))[String(p.espn_id)];
    if (!row) { out.note = out.state === 'post' ? 'Did not play' : "Hasn't checked in yet"; return out; }
    const v = tryCalc(calc, row);
    if (v == null) { out.note = 'No live stat for this prop'; return out; }
    out.value = v;
    const frac = elapsedFraction(p.sport, status);
    if (out.state === 'in' && frac && frac > 0.08 && frac < 1) out.pace = Math.round(v / frac * 10) / 10;
    return out;
  }
  async function livePicks() {
    const now = Date.now(), picks = {};
    const d = currentDaily();
    for (const p of (d || {}).picks || []) {
      picks[p.id] = { id: p.id, sport: p.sport, player: p.player, prop: p.prop, line: p.line, side: p.side,
                      commence: p.commence, game: p.game, espn_id: ((p.report || {}).player || {}).id };
    }
    for (const day of data.view.days) for (const p of day.picks) {
      if (p.result || !p.commence) continue;
      const t = parseDate(p.commence).getTime();
      if (now - 8 * 3600e3 < t && t < now + 18 * 3600e3 && !picks[p.id]) picks[p.id] = { ...p };
    }
    const out = {};
    await Promise.all(Object.values(picks).map(async p => {
      try {
        const lv = await liveForPick(p);
        if (!lv) return;
        out[p.id] = lv;
        if (lv.state === 'post' && lv.value != null) {
          liveFinals[p.id] = { result: lv.value === p.line ? 'push' : (lv.value > p.line) === (p.side === 'MORE') ? 'hit' : 'miss', actual: lv.value };
        } else if (lv.state === 'post' && lv.note === 'Did not play') liveFinals[p.id] = { result: 'void', actual: null };
      } catch (e) {}
    }));
    return out;
  }

  /* ───────── Line changed / pulled: re-price on the phone ───────── */
  function normInv(p) {                           // inverse standard normal (Acklam)
    const a = [-39.69683028665376, 220.9460984245205, -275.9285104469687, 138.357751867269, -30.66479806614716, 2.506628277459239];
    const b = [-54.47609879822406, 161.5858368580409, -155.6989798598866, 66.80131188771972, -13.28068155288572];
    const c = [-0.007784894002430293, -0.3223964580411365, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
    const d = [0.007784695709041462, 0.3224671290700398, 2.445134137142996, 3.754408661907416];
    const q0 = Math.min(Math.max(p, 1e-10), 1 - 1e-10);
    if (q0 < 0.02425) { const q = Math.sqrt(-2 * Math.log(q0)); return (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
    if (q0 > 1 - 0.02425) { const q = Math.sqrt(-2 * Math.log(1 - q0)); return -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
    const q = q0 - 0.5, r = q * q;
    return (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
  }
  function normCdf(x) {                           // standard normal CDF
    const t = 1 / (1 + 0.2316419 * Math.abs(x));
    const y = 1 - 0.3989422804014327 * Math.exp(-x * x / 2) * t * (0.319381530 + t * (-0.356563782 + t * (1.781477937 + t * (-1.821255978 + t * 1.330274429))));
    return x >= 0 ? y : 1 - y;
  }
  function poissonSf(k, lam) {
    let term = Math.exp(-lam), total = term;
    for (let i = 1; i <= Math.floor(k); i++) { term *= lam / i; total += term; }
    return Math.max(0, 1 - total);
  }
  function probOver(target, bookLine, pOver, prop) {
    if (target === bookLine) return pOver;
    pOver = Math.min(Math.max(pOver, 0.02), 0.98);
    if (Math.max(target, bookLine) < 10) {
      let lo = 1e-3, hi = bookLine * 3 + 10;
      for (let i = 0; i < 60; i++) { const mid = (lo + hi) / 2; if (poissonSf(Math.floor(bookLine), mid) < pOver) lo = mid; else hi = mid; }
      return poissonSf(Math.floor(target), (lo + hi) / 2);
    }
    const sigma = (META.prop_cv[prop] || 0.35) * bookLine;
    const mu = bookLine - sigma * normInv(1 - pOver);
    return 1 - normCdf((target - mu) / sigma);
  }
  const segmentKeys = c => [`sport:${c.sport}`, `prop:${c.sport}|${c.prop}|${c.side}`, `side:${c.side}`, `tier:${c.tier || 'none'}`];
  function applyModel(c, model) {
    model = model || { market_weight: META.market_weight, active: false };
    const w = model.market_weight;
    let p = c.hist_p != null ? w * c.market_p + (1 - w) * c.hist_p : c.market_p;
    if (model.active) {
      const adj = (model.bias || 0) + segmentKeys(c).reduce((t, k) => t + ((model.segments || {})[k] || 0), 0);
      p += Math.max(-META.max_total_adj, Math.min(META.max_total_adj, adj));
    }
    return Math.min(Math.max(p, 0.01), 0.99);
  }
  function entryEv(probs, kind) {
    const table = (META.payouts[kind] || {})[probs.length];
    if (!table) return null;
    let dist = [1];
    for (const p of probs) { const nx = new Array(dist.length + 1).fill(0); dist.forEach((v, i) => { nx[i] += v * (1 - p); nx[i + 1] += v * p; }); dist = nx; }
    return Object.entries(table).reduce((t, [h, m]) => t + dist[+h] * m, 0) - 1;
  }
  function bestEntry(picks) {
    let best = null;
    for (let n = 2; n <= picks.length; n++) {
      const legs = picks.slice(0, n);
      const teams = new Set(legs.map(p => ((p.report || {}).player || {}).team || p.game + p.player));
      if (teams.size < 2) continue;
      for (const kind of ['power', 'flex']) {
        if (kind === 'power' && n > META.max_power_legs) continue;
        const ev = entryEv(legs.map(p => 0.5 + (p.final_p - 0.5) * META.entry_shrink), kind);
        if (ev != null && (!best || ev > best.ev)) best = { kind, legs: n, ev: Math.round(ev * 1e4) / 1e4, ids: legs.map(p => p.id) };
      }
    }
    if (!best) return { kind: null, legs: 0, ev: null, ids: [], play: false };
    best.play = best.ev >= META.min_entry_ev;
    best.label = `${best.legs}-pick ${best.kind === 'power' ? 'Power' : 'Flex'}`;
    return best;
  }
  async function rebuildPicks(d, reports) {
    const existing = {};
    for (const p of d.picks || []) existing[`${p.sport}|${p.player}|${p.prop}`] = p;
    const pool = d.board.filter(b => !b.injury && !b.pulled && b.final_p >= 0.5).sort((a, b) => b.final_p - a.final_p);
    const picks = [], players = new Set(), perGame = {};
    for (const b of pool) {
      if (players.has(b.player) || (perGame[b.game] || 0) >= META.max_per_game) continue;
      const k = `${b.sport}|${b.player}|${b.prop}`, old = existing[k];
      let rep = reports[k] || (old && old.line === b.line ? old.report : null);
      if (!rep) { try { rep = await analyze(b.sport, b.player, b.prop, b.line); } catch (e) { rep = null; } }
      const { id, ...rest } = b;
      picks.push({ ...(old || {}), ...rest, report: rep });
      players.add(b.player); perGame[b.game] = (perGame[b.game] || 0) + 1;
      if (picks.length === META.daily_picks) break;
    }
    picks.forEach((p, i) => { p.rank = i + 1; p.id = `daily|${p.sport}|${p.player}|${p.prop}`.toLowerCase(); });
    d.picks = picks; d.entry = bestEntry(picks); d.locked = true;
    return d;
  }
  async function updateLine(pickId, newLine, pulled) {
    const d = JSON.parse(JSON.stringify(currentDaily()));
    if (!d || !d.board) throw new Error("Line updates work on slips from the new scan (tomorrow's onward).");
    const pick = d.picks.find(p => p.id === pickId);
    if (!pick) throw new Error("That pick isn't in today's slip anymore.");
    const k = `${pick.sport}|${pick.player}|${pick.prop}`;
    const b = d.board.find(x => `${x.sport}|${x.player}|${x.prop}` === k);
    if (!b) throw new Error('No saved odds for that pick.');
    const before = d.picks.map(p => p.player), reports = {};
    if (pulled) b.pulled = true;
    else {
      const pOver = b.side === 'MORE' ? b.market_p : 1 - b.market_p;
      const pNew = probOver(newLine, b.line, pOver, b.prop);
      Object.assign(b, { line_moved_from: b.line_moved_from ?? b.line, line: newLine, side: pNew >= 0.5 ? 'MORE' : 'LESS',
                         market_p: Math.max(pNew, 1 - pNew), line_gap: Math.round(((b.book_line ?? newLine) - newLine) * 10) / 10 });
      try {
        const rep = await analyze(b.sport, b.player, b.prop, newLine);
        const v = rep.verdict, over = v.side === 'MORE' ? v.score / 100 : 1 - v.score / 100;
        b.hist_p = b.side === 'MORE' ? over : 1 - over;
        b.tier = (rep.matchup || {}).tier || null;
        reports[k] = rep;
      } catch (e) { b.hist_p = null; }
      b.final_p = applyModel(b, data.files['model.json']);
    }
    await rebuildPicks(d, reports);
    store.set('ps_override', { date: d.date, daily: d });
    const after = d.picks.map(p => p.player), added = after.filter(x => !before.includes(x));
    const still = d.picks.find(p => `${p.sport}|${p.player}|${p.prop}` === k);
    let msg;
    if (pulled) msg = `${pick.player} removed.`;
    else if (still && still.side !== pick.side) msg = `At ${fmtLine(newLine)} ${pick.player} flips to ${still.side} (estimated ${(still.final_p * 100).toFixed(1)}%). Your ${pick.side} edge is gone; take ${still.side} only if you like it.`;
    else if (still) msg = `${pick.player} at ${fmtLine(newLine)} is still a pick: ${still.side} at an estimated ${(still.final_p * 100).toFixed(1)}%.`;
    else msg = `At ${fmtLine(newLine)} the edge on ${pick.player} is gone (${b.side} ${(b.final_p * 100).toFixed(1)}%), so it was dropped.`;
    if (added.length) msg += ` Added ${added.join(', ')}.`;
    const e = d.entry;
    msg += e.play ? ` Suggested entry: ${e.label} (est. EV ${(e.ev * 100 >= 0 ? '+' : '')}${(e.ev * 100).toFixed(1)}%).` : ' Best entry no longer clears the bar: sit out.';
    msg += ' (Saved on this device.)';
    return { daily: withSchedule(d), message: msg };
  }

  /* ───────── The fake server: answers the page's /api calls ───────── */
  function currentDaily() {
    const base = data.files['today_best_pick.json'];
    const o = store.get('ps_override', null);
    if (o && base && o.date === base.date && (o.daily.scanned_at === base.scanned_at)) return o.daily;
    return base;
  }
  function nextScan(lockedToday) {
    const today = todayET(), now = new Date();
    for (const dayOffset of [0, 1]) {
      const day = dayOffset ? new Date(etTime(today, 12).getTime() + 24 * 3600e3) : etTime(today, 12);
      const p = etParts(day), ds = `${p.year}-${p.month}-${p.day}`;
      for (const [h] of META.scan_times) {
        const t = etTime(ds, h);
        if (t > now && !(dayOffset === 0 && lockedToday)) return t.toISOString();
      }
    }
    return null;
  }
  function withSchedule(d) { return { ...d, cached: true, next_scan: nextScan(d.date === todayET() && d.locked) }; }
  const json = (body, status = 200) => new Response(JSON.stringify(body), { status, headers: { 'Content-Type': 'application/json' } });

  async function api(path, opts) {
    const url = new URL(path, location.href);
    const route = url.pathname.replace(/^.*\/api\//, '');
    const body = opts && opts.body ? JSON.parse(opts.body) : {};
    await ready;
    if (route === 'daily' || route === 'history' || route === 'live') await refresh(false);
    switch (route) {
      case 'daily': {
        const d = currentDaily();
        if (!d || d.date !== todayET()) {
          return json({ error: "Today's picks arrive after the 11 AM Eastern scan. Last night's results are on the Record tab.",
                        error_title: "Today's picks aren't in yet", no_retry: true, next_scan: nextScan(false) });
        }
        if (!d.locked) return json({ error: 'The morning scan found too few posted lines. It checks again at 3 PM Eastern.',
                                     error_title: 'Lines aren\'t posted yet', no_retry: true, next_scan: nextScan(false) });
        return json(withSchedule(d));
      }
      case 'history': {
        const v = JSON.parse(JSON.stringify(data.view));
        v.days.forEach(day => day.picks.forEach(p => { if (!p.result && liveFinals[p.id]) Object.assign(p, liveFinals[p.id]); }));
        return json(v);
      }
      case 'live': return json(await livePicks());
      case 'search': {
        const q = url.searchParams.get('q') || '', sport = url.searchParams.get('sport');
        if (!sportOf(sport) || q.length < 3) return json([]);
        try { return json(await searchPlayers(sport, q)); } catch (e) { return json([]); }
      }
      case 'analyze': {
        const line = parseFloat(body.line);
        if (isNaN(line)) return json({ error: 'Enter a numeric PrizePicks line, like 24.5.' }, 400);
        if (!(body.player || '').trim()) return json({ error: 'Enter a player name.' }, 400);
        if (!sportOf(body.sport)) return json({ error: 'Pick a league from the list.' }, 400);
        try { return json(await analyze(body.sport, body.player.trim(), body.prop, line, body.player_id)); }
        catch (e) { return json({ error: e.message && !/^HTTP/.test(e.message) ? e.message : "Couldn't reach ESPN's stats right now." }, 400); }
      }
      case 'line': {
        try {
          if (body.pulled) return json(await updateLine(body.id, null, true));
          const line = parseFloat(body.line);
          if (isNaN(line)) return json({ error: 'Enter the new line, like 25.5.' }, 400);
          return json(await updateLine(body.id, line, false));
        } catch (e) { return json({ error: e.message }, 400); }
      }
      default: return json({ error: 'Not available on the phone version.' }, 404);
    }
  }
  window.fetch = (input, opts) => {
    const path = typeof input === 'string' ? input : input.url;
    return /^\/api\//.test(path) ? api(path, opts) : realFetch(input, opts);
  };
})();
