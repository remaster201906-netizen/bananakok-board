// 바나나콕 코트 보드 — GitHub Pages + Firebase Firestore build.
// Each room is one Firestore document (rooms/<6-digit code>); every viewer subscribes to it,
// and every change runs as a transaction on the latest server copy so simultaneous edits don't overwrite each other.
import { firebaseConfig } from "./firebase-config.js";

const FB = "https://www.gstatic.com/firebasejs/11.6.1/";
const $ = (s) => document.querySelector(s);
const $$ = (s) => [...document.querySelectorAll(s)];
const LEVELS = ["A","B","C","D","초심"];
const SCORE = {A:5,B:4,C:3,D:2,"초심":1};
const G = {M:"남",F:"여"}, SX = {M:"♂",F:"♀"};
const MODE_LABEL = {balance:"실력 밸런스",level:"비슷한 급수끼리",gender:"같은 성별끼리"};
const COURT_COLORS = ["#2f7fe0","#f0a500","#8b5cf6","#43a047","#e0508a","#0fa3b1","#ef6c00","#5c6bc0"];
const CONFIGURED = !!(firebaseConfig && firebaseConfig.apiKey && firebaseConfig.projectId && !firebaseConfig.apiKey.startsWith("여기에"));

let fb = null;               // firebase helpers once connected
let cur = null, R = null;    // current room code and its latest data
let unsub = null;
let sel = [], armed = {}, swapCtx = null;

// ---------- helpers ----------
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const P = (id) => R.players.find((p) => p.id === id) || null;
const uid = (p) => p + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const flat = (teams) => (teams ? teams[0].concat(teams[1]) : []);
const score = (id) => { const p = P(id); return p ? (SCORE[p.level] || 3) : 3; };
const sum = (pair) => pair.reduce((a, id) => a + score(id), 0);
const gOf = (p) => (p.gender === "F" ? "F" : "M");
const avIdx = (id) => { let h = 0; for (let i = 0; i < id.length; i++) h = (h * 31 + id.charCodeAt(i)) >>> 0; return h % 12; };
const fmt = (ms) => { const s = Math.max(0, Math.floor(ms / 1000)), m = Math.floor(s / 60); return String(m).padStart(2, "0") + ":" + String(s % 60).padStart(2, "0"); };
const hhmm = (t) => { const d = new Date(t); return String(d.getHours()).padStart(2, "0") + ":" + String(d.getMinutes()).padStart(2, "0"); };
function lsGet(k){ try{ return localStorage.getItem(k); }catch(e){ return null; } }
function lsSet(k,v){ try{ if(v==null) localStorage.removeItem(k); else localStorage.setItem(k,v); }catch(e){} }
function recentCodes(){ try{ return JSON.parse(lsGet("bb-recent") || "[]").filter((c) => /^[0-9]{6}$/.test(c)); }catch(e){ return []; } }
function addRecent(code){ lsSet("bb-recent", JSON.stringify([code, ...recentCodes().filter((c) => c !== code)].slice(0, 6))); }
function dropRecent(code){ lsSet("bb-recent", JSON.stringify(recentCodes().filter((c) => c !== code))); }
function toast(msg){
  const t = document.createElement("div"); t.className = "toast"; t.textContent = msg; document.body.appendChild(t);
  setTimeout(() => t.remove(), 3000);
}
function setStatus(s, text){ $$(".js-status").forEach((el) => { el.dataset.s = s; el.querySelector("span").textContent = text; }); }
function whereIs(id){
  for (let c = 0; c < R.courts.length; c++) if (flat(R.courts[c].teams).includes(id)) return {k:"court", i:c};
  for (let q = 0; q < R.queue.length; q++) if (flat(R.queue[q].teams).includes(id)) return {k:"queue", i:q};
  const p = P(id); if (p && p.rest) return {k:"rest"};
  return {k:"idle"};
}
const available = () => R.players.filter((p) => whereIs(p.id).k === "idle");

// ---------- rotation & team building ----------
const k2 = (a, b) => (a < b ? a + "|" + b : b + "|" + a);
// how often two people shared a game / were partners lately (recent games weigh double)
function togetherMap(){
  const m = {};
  R.history.slice(0, 40).forEach((h, idx) => {
    const w = idx < 8 ? 2 : 1, all = flat(h.t);
    for (let i = 0; i < all.length; i++) for (let j = i + 1; j < all.length; j++){ const k = k2(all[i], all[j]); (m[k] = m[k] || {g:0,p:0}).g += w; }
    h.t.forEach((pair) => { const k = k2(pair[0], pair[1]); (m[k] = m[k] || {g:0,p:0}).p += w; });
  });
  return m;
}
function byFairness(list){
  return list.map((p) => ({p, r:Math.random()}))
    .sort((x, y) => (x.p.games - y.p.games) || ((x.p.lastAt || 0) - (y.p.lastAt || 0)) || (x.r - y.r))
    .map((x) => x.p);
}
function bestSplit(four, tog = togetherMap()){
  const splits = [[[0,1],[2,3]],[[0,2],[1,3]],[[0,3],[1,2]]]; let best = null, bestCost = Infinity;
  splits.forEach((sp) => {
    const A = [four[sp[0][0]], four[sp[0][1]]], B = [four[sp[1][0]], four[sp[1][1]]];
    const pa = tog[k2(A[0], A[1])], pb = tog[k2(B[0], B[1])];
    const cost = Math.abs(sum(A) - sum(B)) * 10 + ((pa ? pa.p : 0) + (pb ? pb.p : 0)) * 7 + Math.random();
    if (cost < bestCost){ bestCost = cost; best = [A, B]; }
  });
  return best;
}
// choose 4 people: fewest games first, longest wait next, and avoid people who just played together
function pickFour(){
  const av = byFairness(available());
  if (av.length < 4) return null;
  const pool = av.slice(0, 12), minG = av[0].games, tog = togetherMap(), md = R.settings.mode, n = pool.length;
  let best = null, bc = Infinity;
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) for (let d = c + 1; d < n; d++){
    const f = [pool[a], pool[b], pool[c], pool[d]];
    if (md === "gender"){ const g0 = gOf(f[0]); if (!f.every((p) => gOf(p) === g0)) continue; }
    let cost = (a + b + c + d) * 1.5;
    f.forEach((p) => { cost += (p.games - minG) * 25; });
    for (let i = 0; i < 4; i++) for (let j = i + 1; j < 4; j++){ const t = tog[k2(f[i].id, f[j].id)]; if (t) cost += t.g * 6; }
    if (md === "level"){ const sc = f.map((p) => SCORE[p.level] || 3); cost += (Math.max(...sc) - Math.min(...sc)) * 8; }
    cost += Math.random() * 2;
    if (cost < bc){ bc = cost; best = f; }
  }
  return best ? best.map((p) => p.id) : null;
}
function replacementFor(id){
  const me = P(id); let av = byFairness(available());
  if (R.settings.mode === "gender" && me) av = av.filter((p) => gOf(p) === gOf(me));
  return av[0] || null;
}
function fillEmptyCourts(){
  if (!R.settings.auto) return;
  R.courts.forEach((c) => { if (!c.teams && R.queue.length){ c.teams = R.queue.shift().teams; c.startedAt = Date.now(); } });
}
function addOneMatch(){
  const four = pickFour(); if (!four) return false;
  R.queue.push({id:uid("q"), teams:bestSplit(four)});
  return true;
}
function endGame(ci){
  const c = R.courts[ci]; if (!c || !c.teams) return;
  const now = Date.now();
  flat(c.teams).forEach((id) => { const p = P(id); if (p){ p.games++; p.lastAt = now; } });
  R.history.unshift({t:c.teams, at:now, c:c.name, d:c.startedAt ? now - c.startedAt : 0});
  R.history = R.history.slice(0, 80);
  c.teams = null; c.startedAt = null;
  if (R.settings.auto && R.queue.length){ c.teams = R.queue.shift().teams; c.startedAt = now; }
}

// ---------- saving ----------
// fn mutates the global R. It runs once on the local copy (instant screen update) and again,
// inside a transaction, on the freshest server copy — so fn must look everything up by id.
async function mutate(fn){
  if (!fb || !R || !cur) return;
  fn(); R.updatedAt = Date.now(); render();
  setStatus("saving", "저장 중…");
  const ref = fb.doc(fb.db, "rooms", cur);
  try{
    await fb.runTransaction(fb.db, async (tx) => {
      const snap = await tx.get(ref);
      if (!snap.exists()) throw new Error("gone");
      const data = snap.data(), keep = R;
      R = data;
      try{ fn(); } finally { R = keep; }
      data.updatedAt = Date.now();
      tx.set(ref, data);
    });
  }catch(e){
    toast(e && e.message === "gone" ? "이 방은 삭제됐어요." : "저장하지 못했어요. 인터넷 연결을 확인하고 다시 눌러 주세요.");
    console.error(e);
  }
}

// ---------- rooms ----------
function newRoomData(code, club, n){
  const courts = []; for (let i = 0; i < n; i++) courts.push({name:(i + 1) + "코트", note:"", teams:null, startedAt:null});
  return {code, club, createdAt:Date.now(), updatedAt:Date.now(), settings:{mode:"balance", auto:true}, courts, queue:[], players:[], history:[]};
}
async function createRoom(club, n){
  for (let i = 0; i < 6; i++){
    const code = String(Math.floor(100000 + Math.random() * 900000));
    const ref = fb.doc(fb.db, "rooms", code);
    if ((await fb.getDoc(ref)).exists()) continue;
    await fb.setDoc(ref, newRoomData(code, club, n));
    return code;
  }
  throw new Error("no free code");
}
async function enterRoom(code, quiet){
  if (!fb) return false;
  const ref = fb.doc(fb.db, "rooms", code);
  const snap = await fb.getDoc(ref);
  if (!snap.exists()) return false;
  if (unsub) unsub();
  cur = code; R = snap.data(); sel = []; armed = {};
  lsSet("bb-room", code); addRecent(code);
  try{ history.replaceState(null, "", "#r" + code); }catch(e){}
  showView(); if (!quiet) window.scrollTo(0, 0);
  unsub = fb.onSnapshot(ref, {includeMetadataChanges:true}, (s) => {
    if (!s.exists()){ if (cur === code){ toast("방 " + code + " 이 삭제됐어요."); dropRecent(code); leaveRoom(); } return; }
    if (!s.metadata.hasPendingWrites) R = s.data();
    setStatus(s.metadata.fromCache ? "offline" : "live", s.metadata.fromCache ? "연결 끊김 · 다시 연결 중" : "실시간 공유 중");
    render();
  }, (err) => { console.error(err); setStatus("offline", "연결 오류"); });
  return true;
}
function leaveRoom(){
  if (unsub){ unsub(); unsub = null; }
  cur = null; R = null; sel = [];
  lsSet("bb-room", null);
  try{ history.replaceState(null, "", location.pathname + location.search); }catch(e){}
  showView(); window.scrollTo(0, 0);
}
function showView(){
  $("#view-home").hidden = !!R;
  $("#view-room").hidden = !R;
  if (!R) setStatus(fb ? "live" : (CONFIGURED ? "connecting" : "offline"), fb ? "연결됨" : (CONFIGURED ? "연결 중" : "설정 필요"));
  render();
}

// ---------- rendering ----------
const ava = (p) => '<span class="ava av' + avIdx(p.id) + '" aria-hidden="true"></span>';
const sx = (p) => { const g = gOf(p); return '<i class="sx ' + (g === "F" ? "f" : "m") + '" title="' + G[g] + '">' + SX[g] + "</i>"; };
const lvb = (p) => '<span class="lv" data-l="' + esc(p.level) + '">' + esc(p.level) + "</span>";
function pl(id){
  const p = P(id); if (!p) return '<span class="tag"><b>?</b></span>';
  return '<span class="pl">' + ava(p) + '<span class="tag"><b>' + esc(p.name) + "</b><small>" + sx(p) + " " + G[gOf(p)] + "·" + esc(p.level) + (p.guest ? "·G" : "") + (p.rest ? " · 끝나면 휴식" : "") + "</small></span></span>";
}
function mini(id, qid, kind){
  const p = P(id); if (!p) return "";
  const inner = ava(p) + '<span class="mn">' + esc(p.name) + '</span><span class="meta">' + sx(p) + " " + esc(p.level) + (kind ? " · " + p.games + "게임" : "") + "</span>";
  if (kind) return '<button class="mini" type="button" data-sw="' + kind + '" data-id="' + esc(p.id) + '">' + inner + "</button>";
  if (qid) return '<button class="mini" type="button" data-act="qswap" data-q="' + esc(qid) + '" data-id="' + esc(id) + '" title="' + esc(p.name) + ' 바꾸기">' + inner + "</button>";
  return '<span class="mini">' + inner + "</span>";
}
const COURT_SVG = '<svg viewBox="0 0 610 1340" preserveAspectRatio="none" aria-hidden="true"><g fill="none" stroke="#fff" stroke-width="7" opacity=".9">'
  + '<rect x="3.5" y="3.5" width="603" height="1333"/>'
  + '<line x1="46" y1="0" x2="46" y2="1340"/><line x1="564" y1="0" x2="564" y2="1340"/>'
  + '<line x1="0" y1="76" x2="610" y2="76"/><line x1="0" y1="1264" x2="610" y2="1264"/>'
  + '<line x1="0" y1="472" x2="610" y2="472"/><line x1="0" y1="868" x2="610" y2="868"/>'
  + '<line x1="305" y1="0" x2="305" y2="472"/><line x1="305" y1="868" x2="305" y2="1340"/></g>'
  + '<rect x="0" y="662" width="610" height="16" fill="#1a3d8f"/><line x1="0" y1="670" x2="610" y2="670" stroke="#fff" stroke-width="4" stroke-dasharray="10 6"/>'
  + '<rect x="0" y="640" width="14" height="60" rx="4" fill="#1a3d8f"/><rect x="596" y="640" width="14" height="60" rx="4" fill="#1a3d8f"/></svg>';

let homeToken = 0;
async function renderHome(){
  $("#setup-note").hidden = CONFIGURED;
  const codes = recentCodes(), token = ++homeToken;
  $("#recent-title").textContent = "최근 들어간 방";
  if (!fb || !codes.length){ $("#recent").hidden = true; return; }
  const rooms = await Promise.all(codes.map((c) => fb.getDoc(fb.doc(fb.db, "rooms", c)).then((s) => (s.exists() ? s.data() : null)).catch(() => null)));
  if (token !== homeToken || R) return;
  const list = rooms.filter(Boolean);
  $("#recent").hidden = !list.length;
  $("#room-list").innerHTML = list.map((r) => {
    const playing = r.courts.filter((x) => x.teams).length;
    return '<button type="button" class="room-item" data-enter="' + esc(r.code) + '"><span><b>' + esc(r.club) + '</b><br><span class="meta">참석 ' + r.players.length + "명 · 경기 중 " + playing + "코트 · 대기 " + r.queue.length + '경기</span></span><span class="code">' + esc(r.code) + "</span></button>";
  }).join("");
}
function renderCourts(){
  const firstQ = R.queue.length > 0, now = Date.now();
  $("#courts").innerHTML = R.courts.map((c, i) => {
    let body, foot;
    if (c.teams){
      body = '<div class="half top"><span class="side">A팀</span>' + pl(c.teams[0][0]) + pl(c.teams[0][1]) + "</div>"
           + '<div class="half bot"><span class="side">B팀</span>' + pl(c.teams[1][0]) + pl(c.teams[1][1]) + "</div>";
      foot = '<button class="g sm green" type="button" data-act="end" data-i="' + i + '">' + (armed[i] ? "한 번 더!" : "게임 종료") + "</button>"
           + '<button class="g sm" type="button" data-act="back" data-i="' + i + '" title="게임 수를 올리지 않고 대기 1번으로 되돌려요">배정 취소</button>';
    } else {
      body = '<div class="empty">빈 코트</div>';
      foot = '<button class="g sm yellow" type="button" data-act="load" data-i="' + i + '"' + (firstQ ? "" : " disabled") + ">대기 1번 올리기</button>";
    }
    const timer = c.teams && c.startedAt ? '<span class="timer" data-start="' + c.startedAt + '">' + fmt(now - c.startedAt) + "</span>" : "";
    const sc = c.teams ? '<div class="score">급수 합 A ' + sum(c.teams[0]) + " : " + sum(c.teams[1]) + " B</div>" : "";
    return '<article class="court-card"><div class="court-head"><span class="cname" style="--cc:' + COURT_COLORS[i % COURT_COLORS.length] + '">' + esc(c.name) + (c.note ? " <small>(" + esc(c.note) + ")</small>" : "") + "</span>" + timer + "</div>"
      + '<div class="court">' + COURT_SVG + body + "</div>" + sc
      + '<div class="court-foot edit-only">' + foot + "</div></article>";
  }).join("");
}
function renderQueue(){
  const hasEmpty = R.courts.some((c) => !c.teams);
  const rows = R.queue.map((q, i) => '<li class="qcard' + (i === 0 ? " next" : "") + '"><div class="qhead"><span class="qn">' + (i + 1) + "</span>" + (i === 0 ? "다음 경기 준비중" : "대기 중") + '<span class="bal">급수 ' + sum(q.teams[0]) + " : " + sum(q.teams[1]) + "</span></div>"
    + '<div class="qteams"><div class="team a">' + mini(q.teams[0][0], q.id) + mini(q.teams[0][1], q.id) + '</div><span class="vs">VS</span><div class="team b">' + mini(q.teams[1][0], q.id) + mini(q.teams[1][1], q.id) + "</div></div>"
    + '<div class="qacts edit-only">'
    + (hasEmpty ? '<button class="g sm yellow" type="button" data-act="qcourt" data-i="' + i + '">코트로</button>' : "")
    + '<button class="ib" type="button" data-act="qup" data-i="' + i + '"' + (i === 0 ? " disabled" : "") + ">▲ 위로</button>"
    + '<button class="ib" type="button" data-act="qmix" data-i="' + i + '">⇄ 팀 섞기</button>'
    + '<button class="ib del" type="button" data-act="qdel" data-i="' + i + '">✕ 삭제</button>'
    + "</div></li>");
  $("#queue").innerHTML = rows.length ? rows.join("") : '<li class="qempty">대기 경기가 없어요</li>';
  $("#q-count").textContent = R.queue.length;
  const avl = available(), av = avl.length; let ok;
  if (R.settings.mode === "gender"){
    const m = avl.filter((p) => gOf(p) === "M").length, f = av - m;
    ok = m >= 4 || f >= 4;
    $("#avail-hint").textContent = "편성 가능 남 " + m + "명 · 여 " + f + "명" + (ok ? "" : " (같은 성별 4명 필요)");
  } else {
    ok = av >= 4;
    $("#avail-hint").textContent = "편성 가능 " + av + "명" + (ok ? "" : " (4명 필요)");
  }
  $("#btn-one").disabled = !ok; $("#btn-auto").disabled = !ok;
}
function pcard(p){
  const w = whereIs(p.id); let st = "", stText = "";
  if (w.k === "court"){ st = "court"; stText = R.courts[w.i].name; }
  else if (w.k === "queue"){ st = "queue"; stText = "대기 " + (w.i + 1); }
  else if (w.k === "rest"){ st = "rest"; stText = "휴식"; }
  const pick = w.k === "idle", on = sel.includes(p.id);
  const after = p.rest && w.k === "court" ? '<span class="st after">끝나면 휴식</span>' : "";
  return '<div class="pcard' + (pick ? " pickable" : "") + (on ? " sel" : "") + '" data-st="' + st + '" data-id="' + esc(p.id) + '"' + (pick ? ' role="button" tabindex="0" aria-pressed="' + on + '"' : "") + ">"
    + ava(p) + '<span class="nm">' + esc(p.name) + "</span>"
    + '<span class="sub">' + sx(p) + " " + lvb(p) + (p.guest ? " 게스트" : "") + " · " + p.games + "게임" + (stText ? ' <span class="st">' + esc(stText) + "</span>" : "") + after + "</span>"
    + '<span class="pact edit-only">'
    + '<button class="ib rest" type="button" data-act="rest" data-id="' + esc(p.id) + '">' + (p.rest ? "▶ 복귀" : "☾ 휴식") + "</button>"
    + '<button class="ib del" type="button" data-act="pdel" data-id="' + esc(p.id) + '" aria-label="' + esc(p.name) + ' 명단에서 빼기">✕</button></span></div>';
}
const sorted = (list) => list.slice().sort((a, b) => (LEVELS.indexOf(a.level) - LEVELS.indexOf(b.level)) || a.name.localeCompare(b.name, "ko"));
function renderPlayers(){
  // someone still on court with a rest flag stays in their group until the game ends
  const resting = sorted(R.players.filter((p) => p.rest && whereIs(p.id).k === "rest"));
  const active = R.players.filter((p) => !resting.includes(p));
  const m = sorted(active.filter((p) => !p.guest)), g = sorted(active.filter((p) => p.guest));
  $("#roster").innerHTML = m.length ? m.map(pcard).join("") : '<span class="empty-note">아직 등록된 회원이 없어요.</span>';
  $("#guests").innerHTML = g.length ? g.map(pcard).join("") : '<span class="empty-note">없음</span>';
  $("#resting").innerHTML = resting.length ? resting.map(pcard).join("") : '<span class="empty-note">쉬는 사람이 없어요.</span>';
  $("#c-members").textContent = m.length; $("#c-guests").textContent = g.length; $("#c-rest").textContent = resting.length;
  sel = sel.filter((id) => P(id) && whereIs(id).k === "idle");
  $("#selbar").hidden = !sel.length;
  $("#sel-text").textContent = sel.length + "명 선택 · 4명을 고르세요";
  $("#sel-make").disabled = sel.length !== 4;
}
function renderHistory(){
  $("#hist-count").textContent = "(" + R.history.length + ")";
  $("#hist-list").innerHTML = R.history.length ? R.history.map((h) => {
    const names = (pair) => pair.map((id) => { const p = P(id); return p ? esc(p.name) : "(삭제됨)"; }).join("·");
    return '<li><span class="t">' + hhmm(h.at) + " " + esc(h.c) + (h.d ? " · " + Math.round(h.d / 60000) + "분" : "") + "</span>" + names(h.t[0]) + " vs " + names(h.t[1]) + "</li>";
  }).join("") : '<li class="empty-note" style="list-style:none;margin-left:-20px">아직 끝난 경기가 없어요.</li>';
}
function render(){
  if (!R){ renderHome(); return; }
  $("#club-name").textContent = R.club;
  $("#room-code").textContent = cur;
  $("#st-players").textContent = R.players.length + "명";
  $("#st-courts").textContent = R.courts.filter((c) => c.teams).length + "/" + R.courts.length + "코트";
  $("#st-queue").textContent = R.queue.length + "경기";
  $("#st-mode").textContent = (MODE_LABEL[R.settings.mode] || MODE_LABEL.balance) + " 편성";
  renderCourts(); renderQueue(); renderPlayers(); renderHistory();
}

// ---------- actions ----------
function toggleRest(id){
  const p = P(id); if (!p) return;
  const name = p.name;
  if (p.rest){ mutate(() => { const x = P(id); if (x) x.rest = false; }); toast(name + " 님이 복귀했어요."); return; }
  const w = whereIs(id);
  if (w.k === "queue"){
    const rep = replacementFor(id);
    if (!rep){ toast("대신 들어갈 사람이 없어요. 대기 경기를 지우거나 사람을 먼저 바꿔 주세요."); return; }
    mutate(() => {
      const x = P(id), ww = whereIs(id); if (!x) return;
      if (ww.k === "queue"){
        const r2 = replacementFor(id); if (!r2) return;
        const q = R.queue[ww.i];
        q.teams = q.teams.map((pair) => pair.map((y) => (y === id ? r2.id : y)));
      }
      x.rest = true;
    });
    toast(name + " 님은 휴식, 대기 " + (w.i + 1) + "번에는 " + rep.name + " 님이 들어가요.");
    return;
  }
  sel = sel.filter((x) => x !== id);
  mutate(() => { const x = P(id); if (x) x.rest = true; });
  toast(w.k === "court" ? name + " 님은 이번 경기가 끝나면 쉬어요." : name + " 님은 휴식 중이에요. 자동 편성에서 빠져요.");
}
function openSwap(qid, id){
  const q = R.queue.find((x) => x.id === qid), p = P(id); if (!q || !p) return;
  swapCtx = {q:qid, id};
  $("#sw-title").textContent = p.name + " 님 자리 바꾸기";
  $("#sw-inner").innerHTML = flat(q.teams).filter((x) => x !== id).map((x) => mini(x, null, "in")).join("");
  const idle = byFairness(available());
  $("#sw-outer").innerHTML = idle.length ? idle.map((o) => mini(o.id, null, "out")).join("") : '<span class="empty-note">지금 쉬고 있는 인원이 없어요.</span>';
  $("#dlg-swap").showModal();
}
function doSwap(kind, target){
  const ctx = swapCtx; swapCtx = null; $("#dlg-swap").close(); if (!ctx) return;
  mutate(() => {
    const q = R.queue.find((x) => x.id === ctx.q); if (!q || !flat(q.teams).includes(ctx.id)) return;
    if (kind === "out" && whereIs(target).k !== "idle") return;
    if (kind === "in" && !flat(q.teams).includes(target)) return;
    q.teams = q.teams.map((pair) => pair.map((x) => (x === ctx.id ? target : (kind === "in" && x === target ? ctx.id : x))));
  });
}
function togglePick(id){
  const k = sel.indexOf(id);
  if (k >= 0) sel.splice(k, 1);
  else { if (sel.length >= 4){ toast("한 경기는 4명이에요."); return; } sel.push(id); }
  renderPlayers();
}
function drawCourtRows(n){
  const host = $("#s-courts");
  const curRows = [...host.querySelectorAll("div")].map((r) => ({name:r.querySelector("[data-f=name]").value, note:r.querySelector("[data-f=note]").value}));
  let html = "";
  for (let i = 0; i < n; i++){
    const src = curRows[i] || R.courts[i] || {name:(i + 1) + "코트", note:""};
    html += '<div><input type="text" id="s-cn-' + i + '" data-f="name" maxlength="10" aria-label="' + (i + 1) + '번 코트 이름" value="' + esc(src.name) + '"><input type="text" id="s-ct-' + i + '" data-f="note" maxlength="10" aria-label="' + (i + 1) + '번 코트 메모" placeholder="메모 (예: 레슨용)" value="' + esc(src.note || "") + '"></div>';
  }
  host.innerHTML = html;
}
function openSettings(){
  $("#s-club").value = R.club;
  $("#s-count").value = String(R.courts.length);
  $("#s-courts").innerHTML = ""; drawCourtRows(R.courts.length);
  $$("input[name=s-mode]").forEach((r) => { r.checked = r.value === R.settings.mode; });
  $("#s-auto").checked = !!R.settings.auto;
  $("#dlg-settings").showModal();
}
function parseBatch(text){
  const rows = []; let skipped = 0;
  text.split(/\n/).forEach((raw) => {
    const line = raw.trim(); if (!line) return;
    // "게스트" counts only as its own word, so a nickname like 게스트1 stays intact
    let guest = false;
    const parts = line.split(/[\s,\/|\t]+/).filter(Boolean).filter((t, k) => { if (k > 0 && /^(게스트|\(G\)|G)$/i.test(t)){ guest = true; return false; } return true; });
    if (!parts.length) return;
    const name = parts[0].slice(0, 12); let lv = "C", gen = "M";
    parts.slice(1).forEach((t0) => {
      const t = t0.replace(/조$/, "").toUpperCase();
      if (/^(남|남자|M)$/.test(t)) gen = "M";
      else if (/^(여|여자|F|W)$/.test(t)) gen = "F";
      else if (/^[ABCD]$/.test(t)) lv = t;
      else if (/^(초심|입문|초보|E)$/.test(t)) lv = "초심";
    });
    if (R.players.some((p) => p.name === name) || rows.some((r) => r.name === name)){ skipped++; return; }
    rows.push({id:uid("p"), name, gender:gen, level:lv, guest, rest:false, games:0, lastAt:0});
  });
  return {rows, skipped};
}

// ---------- events ----------
function needFb(){
  if (fb) return true;
  toast(CONFIGURED ? "아직 연결 중이에요. 잠시 후 다시 눌러 주세요." : "Firebase 설정이 필요해요. README.md 를 봐 주세요.");
  return false;
}
function wire(){
  $("#app").addEventListener("click", (e) => {
    const en = e.target.closest("[data-enter]");
    if (en){ enterRoom(en.dataset.enter).then((ok) => { if (!ok){ toast("없는 방이에요."); dropRecent(en.dataset.enter); renderHome(); } }); return; }
    const sw = e.target.closest("[data-sw]"); if (sw){ doSwap(sw.dataset.sw, sw.dataset.id); return; }
    const b = e.target.closest("[data-act]");
    if (b){
      if (!R) return;
      const i = +b.dataset.i, id = b.dataset.id, act = b.dataset.act;
      if (act === "end"){
        if (!armed[i]){ armed[i] = true; renderCourts(); setTimeout(() => { if (armed[i]){ delete armed[i]; if (R) renderCourts(); } }, 3000); return; }
        delete armed[i]; mutate(() => endGame(i)); return;
      }
      if (act === "back") return mutate(() => { const c = R.courts[i]; if (!c || !c.teams) return; R.queue.unshift({id:uid("q"), teams:c.teams}); c.teams = null; c.startedAt = null; });
      if (act === "load") return mutate(() => { const c = R.courts[i]; if (c && !c.teams && R.queue.length){ c.teams = R.queue.shift().teams; c.startedAt = Date.now(); } });
      if (act === "qcourt"){ const qid = R.queue[i] && R.queue[i].id; return mutate(() => { const ci = R.courts.findIndex((c) => !c.teams), qi = R.queue.findIndex((q) => q.id === qid); if (ci < 0 || qi < 0) return; R.courts[ci].teams = R.queue.splice(qi, 1)[0].teams; R.courts[ci].startedAt = Date.now(); }); }
      if (act === "qup"){ const qid = R.queue[i] && R.queue[i].id; return mutate(() => { const qi = R.queue.findIndex((q) => q.id === qid); if (qi > 0){ const q = R.queue.splice(qi, 1)[0]; R.queue.splice(qi - 1, 0, q); } }); }
      if (act === "qmix"){ const qid = R.queue[i] && R.queue[i].id; return mutate(() => {
        const q = R.queue.find((x) => x.id === qid); if (!q) return;
        const f = flat(q.teams), before = JSON.stringify(q.teams); let next = bestSplit(f), tries = 0;
        while (JSON.stringify(next) === before && tries < 12){ f.sort(() => Math.random() - 0.5); next = [[f[0], f[1]], [f[2], f[3]]]; tries++; }
        q.teams = next;
      }); }
      if (act === "qdel"){ const qid = R.queue[i] && R.queue[i].id; return mutate(() => { R.queue = R.queue.filter((q) => q.id !== qid); }); }
      if (act === "qswap") return openSwap(b.dataset.q, id);
      if (act === "rest") return toggleRest(id);
      if (act === "pdel"){
        const w = whereIs(id);
        if (w.k === "court" || w.k === "queue"){ toast("경기 중이거나 대기 명단에 있는 사람은 뺄 수 없어요. 먼저 경기를 끝내거나 대기에서 지워 주세요."); return; }
        sel = sel.filter((x) => x !== id);
        return mutate(() => { const ww = whereIs(id); if (ww.k === "court" || ww.k === "queue") return; R.players = R.players.filter((p) => p.id !== id); });
      }
      return;
    }
    const c = e.target.closest(".pcard.pickable"); if (c) togglePick(c.dataset.id);
  });
  $("#app").addEventListener("keydown", (e) => {
    const c = e.target.closest && e.target.closest(".pcard.pickable");
    if (c && (e.key === "Enter" || e.key === " ") && e.target === c){ e.preventDefault(); togglePick(c.dataset.id); }
  });

  // home
  $("#btn-create").addEventListener("click", () => { if (!needFb()) return; $("#c-club").value = ""; $("#dlg-create").showModal(); });
  $("#dlg-create").addEventListener("close", async function(){
    if (this.returnValue !== "ok" || !needFb()) return;
    const club = ($("#c-club").value.trim() || "배드민턴 모임").slice(0, 24), n = +$("#c-count").value;
    try{ const code = await createRoom(club, n); await enterRoom(code); toast("방을 만들었어요. 코드 " + code + " 를 알려 주세요."); }
    catch(e){ console.error(e); toast("방을 만들지 못했어요. 인터넷 연결과 Firebase 설정을 확인해 주세요."); }
  });
  $("#j-code").addEventListener("input", function(){ this.value = this.value.replace(/[^0-9]/g, "").slice(0, 6); $("#join-err").hidden = true; });
  $("#join-form").addEventListener("submit", async (e) => {
    e.preventDefault(); if (!needFb()) return;
    const code = $("#j-code").value.trim(), err = $("#join-err");
    if (!/^[0-9]{6}$/.test(code)){ err.textContent = "방 코드 6자리를 넣어 주세요."; err.hidden = false; return; }
    if (!(await enterRoom(code))){ err.textContent = "없는 방 코드예요. 코드를 다시 확인해 주세요."; err.hidden = false; return; }
    $("#j-code").value = "";
  });

  // room
  $("#btn-leave").addEventListener("click", leaveRoom);
  $("#btn-copy").addEventListener("click", () => {
    const code = cur;
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(code).then(() => toast("방 코드 " + code + " 를 복사했어요."), () => toast("방 코드: " + code));
    else toast("방 코드: " + code);
  });
  $("#btn-one").addEventListener("click", () => {
    if (!pickFour()){ toast(R.settings.mode === "gender" ? "쉬지 않는 같은 성별 인원이 4명 이상이어야 경기를 만들 수 있어요." : "휴식 중이 아닌 대기 인원이 4명 이상이어야 경기를 만들 수 있어요."); return; }
    mutate(() => { if (addOneMatch()) fillEmptyCourts(); });
  });
  $("#btn-auto").addEventListener("click", () => {
    if (!pickFour()){ toast("편성할 수 있는 인원이 4명보다 적어요."); return; }
    mutate(() => { let n = 0; while (addOneMatch()) n++; if (n) fillEmptyCourts(); });
  });
  $("#sel-cancel").addEventListener("click", () => { sel = []; renderPlayers(); });
  $("#sel-make").addEventListener("click", () => {
    if (sel.length !== 4) return;
    const four = sel.slice(); sel = [];
    mutate(() => { if (!four.every((id) => P(id) && whereIs(id).k === "idle")) return; R.queue.push({id:uid("q"), teams:bestSplit(four)}); fillEmptyCourts(); });
  });
  $("#add-form").addEventListener("submit", (e) => {
    e.preventDefault();
    const name = $("#f-name").value.trim(); if (!name){ $("#f-name").focus(); return; }
    if (R.players.some((p) => p.name === name)){ toast("'" + name + "' 닉네임은 이미 명단에 있어요."); return; }
    const player = {id:uid("p"), name, gender:$("#f-gender").value, level:$("#f-level").value, guest:$("#f-guest").checked, rest:false, games:0, lastAt:0};
    $("#f-name").value = "";
    mutate(() => { if (!R.players.some((p) => p.name === name)) R.players.push({...player}); });
  });
  $("#btn-batch").addEventListener("click", () => { $("#batch-text").value = ""; $("#dlg-batch").showModal(); });
  $("#dlg-batch").addEventListener("close", function(){
    if (this.returnValue !== "ok" || !R) return;
    const {rows, skipped} = parseBatch($("#batch-text").value);
    if (!rows.length){ toast(skipped ? "모두 이미 명단에 있는 이름이에요." : "등록할 이름이 없어요."); return; }
    mutate(() => { rows.forEach((r) => { if (!R.players.some((p) => p.name === r.name)) R.players.push({...r}); }); });
    toast(rows.length + "명 등록했어요" + (skipped ? " (중복 " + skipped + "명 제외)" : ""));
  });
  $("#btn-settings").addEventListener("click", openSettings);
  $("#s-count").addEventListener("change", function(){ drawCourtRows(+this.value); });
  $("#dlg-settings").addEventListener("close", function(){
    if (this.returnValue !== "ok" || !R) return;
    const n = +$("#s-count").value;
    const rows = $$("#s-courts > div").map((r) => ({name:r.querySelector("[data-f=name]").value.trim(), note:r.querySelector("[data-f=note]").value.trim()}));
    if (R.courts.slice(n).some((c) => c.teams)){ toast("줄이려는 코트에서 경기가 진행 중이에요. 먼저 게임을 끝내 주세요."); return; }
    const club = ($("#s-club").value.trim() || "배드민턴 모임").slice(0, 24);
    const m = document.querySelector("input[name=s-mode]:checked"), md = m ? m.value : "balance", auto = $("#s-auto").checked;
    mutate(() => {
      if (R.courts.slice(n).some((c) => c.teams)) return;
      R.club = club;
      const next = [];
      for (let i = 0; i < n; i++){
        const old = R.courts[i] || {teams:null, startedAt:null}, r = rows[i] || {name:"", note:""};
        next.push({name:(r.name || (i + 1) + "코트").slice(0, 10), note:r.note.slice(0, 10), teams:old.teams, startedAt:old.startedAt});
      }
      R.courts = next; R.settings.mode = md; R.settings.auto = auto;
      fillEmptyCourts();
    });
  });
  $("#btn-reset").addEventListener("click", () => $("#dlg-reset").showModal());
  $("#dlg-reset").addEventListener("close", async function(){
    const v = this.returnValue; if (!R || !["soft","hard","delete"].includes(v)) return;
    if (v === "delete"){
      const code = cur;
      try{ await fb.deleteDoc(fb.doc(fb.db, "rooms", code)); dropRecent(code); leaveRoom(); toast("방 " + code + " 을 삭제했어요."); }
      catch(e){ console.error(e); toast("방을 삭제하지 못했어요."); }
      return;
    }
    sel = [];
    mutate(() => {
      R.courts.forEach((c) => { c.teams = null; c.startedAt = null; });
      R.queue = []; R.history = [];
      if (v === "hard") R.players = [];
      else R.players.forEach((p) => { p.games = 0; p.lastAt = 0; p.rest = false; });
    });
  });
  $("#dlg-swap").addEventListener("close", () => { swapCtx = null; });
  $("#sw-close").addEventListener("click", () => { swapCtx = null; $("#dlg-swap").close(); });
}

// ---------- boot ----------
async function connect(){
  if (!CONFIGURED){ document.body.dataset.mode = "setup"; showView(); return; }
  try{
    const [{initializeApp}, fs] = await Promise.all([import(FB + "firebase-app.js"), import(FB + "firebase-firestore.js")]);
    const app = initializeApp(firebaseConfig);
    fb = {db:fs.getFirestore(app), doc:fs.doc, getDoc:fs.getDoc, setDoc:fs.setDoc, deleteDoc:fs.deleteDoc, onSnapshot:fs.onSnapshot, runTransaction:fs.runTransaction};
    document.body.dataset.mode = "live";
  }catch(e){
    console.error(e);
    document.body.dataset.mode = "setup";
    setStatus("offline", "연결 실패");
    toast("Firebase에 연결하지 못했어요. 설정값을 확인해 주세요.");
    showView(); return;
  }
  const m = /^#r([0-9]{6})$/.exec(location.hash || ""), want = (m && m[1]) || lsGet("bb-room");
  if (!(want && (await enterRoom(want, true)))) showView();
}
wire();
showView();
setInterval(() => { const now = Date.now(); $$(".timer[data-start]").forEach((t) => { t.textContent = fmt(now - (+t.dataset.start)); }); }, 1000);
connect();
