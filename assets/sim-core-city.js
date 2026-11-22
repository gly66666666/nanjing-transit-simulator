/* ============================================================
   引擎层：线网图 / 最短路 / 列车运行 / 客流仿真
   ============================================================ */
'use strict';

const K = {
  TRANSFER: 3.2,        // 换乘步行 + 重新候车（分钟）
  DWELL: 0.55,          // 每站停站时间（分钟）
  BEND: 1.22,           // 线路弯曲修正系数
  WAIT_LIMIT: 28,       // 候车超时（分钟）判定放弃
  PLATFORM_CAP: 45,     // 站台容纳上限（按 1:100 抽样后的人数，对标高峰限流）
  SAMPLE: 0.01,         // 客流抽样比：1 名模拟乘客 ≈ 100 名真实乘客
  CAP_RATIO: 0.014,     // 列车抽样定员系数（真实 1200 人 → 17 名样本乘客）
  MAX_ACTIVE: 9000,     // 同时在途上限（性能保护）
  SIM_START: 420,       // 07:00
  ACCESS: 8,            // 两端接驳步行（分钟），计入门到门通勤
  DEMAND: 0.28,         // 每站每分钟基准生成率（按权重缩放）
  SAME_LINE: 0.62       // 同线直达出行占比（对标南京真实换乘系数 ≈1.4）
};

const App = {
  stations: new Map(),
  lines: [],
  mode: 'view',
  tool: 'station',
  selectedLine: null,
  editingLine: null,
  budget: START_BUDGET,
  spent: 0,
  newStations: 0,
  customStations: 0,
  sim: null,
  report: null,
  hover: null,
  cam: { x: 47, y: 52, s: 15 },
  world: null,
  graph: null,
  odTable: new Map(),
  odSame: new Map(),
  pathCache: new Map(),
  legCache: new Map(),
  totalWeight: 1,
  challenge: null,
  dirty: true,
  trackOff: {},
  toastTimer: null
};

/* ---------------- 基础数学 / 地理 ---------------- */
const R2D = Math.PI / 180;
function haversine(a, b) {
  const dLat = (b.lat - a.lat) * R2D, dLng = (b.lng - a.lng) * R2D;
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(a.lat * R2D) * Math.cos(b.lat * R2D) * Math.sin(dLng / 2) ** 2;
  return 12742 * Math.asin(Math.min(1, Math.sqrt(h)));
}

/* ---------------- 世界构建 ---------------- */
function buildWorld() {
  App.stations = new Map();
  App.lines = [];
  App.budget = START_BUDGET;
  App.spent = 0;
  App.newStations = 0;
  App.customStations = 0;
  App.trackOff = {};
  App.selectedLine = null;
  App.editingLine = null;
  App.challenge = null;

  for (const def of LINE_DEFS) {
    const ids = [];
    for (const name of def.stations) {
      let st = App.stations.get(name);
      if (!st) {
        const c = COORD[name] || [LNG0, LAT0];
        st = {
          id: name, name,
          lng: c[0], lat: c[1],
          x: (c[0] - LNG0) * KX, y: (LAT0 - c[1]) * KY,
          w: WEIGHT[name] || 0.45,
          lines: [], custom: false, boardings: 0, alightings: 0
        };
        App.stations.set(name, st);
      }
      if (!st.lines.includes(def.id)) st.lines.push(def.id);
      ids.push(name);
    }
    App.lines.push({
      id: def.id, name: def.name, short: def.short, color: def.color,
      headway: def.headway, speed: def.speed, cap: def.cap,
      bldHead: def.bldHead || 0, bldTail: def.bldTail || 0,
      stations: ids, enabled: true, custom: false, segs: null,
      pax: 0, peakLoad: 0, fleet: 0, ontime: 0, late: 0, depTimer: 0
    });
  }
  /* 分叉支线初始化 */
  for (const d0 of LINE_DEFS) {
    if (!d0.arms || !d0.arms.length) continue;
    const ln = App.lines.find(x => x.id === d0.id);
    if (!ln) continue;
    ln.arms = [{ stations: ln.stations.slice() }].concat(d0.arms.filter(a => a && a.stations && a.stations.length >= 2).map(a => ({ stations: a.stations.slice() })));
  }
  refreshSegs();
  rebuildGraph();
  App.odTable.clear();
  App.odSame.clear();
  App.pathCache.clear();
}

/* 线路 = 若干条运行臂（arm）：arms[0] 为主干，其余为分叉支线
   每条 arm 的 stations 独立有序，支线 arm 的第 0 站为主干线上的分叉点 */
function lineArms(line) {
  if (!line.arms || !line.arms.length) line.arms = [{ stations: line.stations }];
  line.arms[0].stations = line.stations;
  return line.arms;
}

/* 主干是否仍与原线定义完全一致：一致时仍可套用真实轨道折线，分叉支线单独画 */
function mainMatchesDef(line) {
  if (!line) return false;
  if (typeof LINE_DEFS === 'undefined' || typeof TRACK === 'undefined') return false;
  if (!TRACK[line.id]) return false;
  const def = LINE_DEFS.find(d => d.id === line.id);
  if (!def || !def.stations) return false;
  const main = lineArms(line)[0].stations;
  if (main.length !== def.stations.length) return false;
  for (let i = 0; i < main.length; i++) if (main[i] !== def.stations[i]) return false;
  return true;
}

function refreshSegs() {
  for (const line of App.lines) {
    const arms = lineArms(line);
    const definition = LINE_DEFS.find(def => def.id === line.id);
    let km = 0;
    for (const [index, arm] of arms.entries()) {
      arm.planned = MetroMap.isPlannedArm(arm.stations, definition, index);
      const segs = [];
      let total = 0;
      for (let i = 0; i < arm.stations.length - 1; i++) {
        const a = App.stations.get(arm.stations[i]);
        const b = App.stations.get(arm.stations[i + 1]);
        if (!a || !b) { segs.push({ dist: 0.8, t: 1.5 }); continue; }
        const d = Math.max(0.25, haversine(a, b) * K.BEND);
        const t = d / line.speed * 60 + K.DWELL;
        segs.push({ dist: d, t });
        total += t;
      }
      arm.segs = segs;
      arm.runTime = total;
      arm.km = segs.reduce((s, x) => s + x.dist, 0);
      km += arm.km;
    }
    line.segs = arms[0].segs;
    line.runTime = arms[0].runTime;
    line.km = km;
    // 分叉后各臂交替发车：单臂发车间隔 = 全线间隔 × 臂数
    let fleet = 0;
    for (const arm of arms) {
      if (arm.stations.length < 2) continue;
      const headH = (line.headway * arms.length) / 60;
      fleet += Math.ceil((2 * arm.runTime + 2 * 1.2) / headH);
    }
    line.fleet = Math.max(fleet, arms.length);
    line.depTimer = 0;
  }
}

/* ---------------- 线网图（站点-线路-臂 状态空间） ---------------- */
function rebuildGraph() {
  const nodes = [];
  const map = new Map();
  const byStation = new Map();
  for (const line of App.lines) {
    if (!line.enabled) continue;
    const arms = lineArms(line);
    arms.forEach((arm, ai) => {
      if (arm.stations.length < 2) return;
      for (let i = 0; i < arm.stations.length; i++) {
        const sid = arm.stations[i];
        const key = sid + '|' + line.id + '|' + ai;
        if (map.has(key)) continue;
        const idx = nodes.length;
        nodes.push({ s: sid, l: line.id, i, deg: 1, arm: ai });
        map.set(key, idx);
        if (!byStation.has(sid)) byStation.set(sid, []);
        byStation.get(sid).push(idx);
      }
    });
  }
  const adj = new Array(nodes.length);
  for (let i = 0; i < nodes.length; i++) adj[i] = [];
  const addEdge = (a, b, w, kind) => {
    if (a == null || b == null || a < 0 || b < 0) return;
    adj[a].push({ to: b, w, kind });
  };
  for (const line of App.lines) {
    if (!line.enabled) continue;
    const arms = lineArms(line);
    arms.forEach((arm, ai) => {
      for (let i = 0; i < arm.stations.length - 1; i++) {
        const a = map.get(arm.stations[i] + '|' + line.id + '|' + ai);
        const b = map.get(arm.stations[i + 1] + '|' + line.id + '|' + ai);
        if (a == null || b == null) continue;
        const w = arm.segs[i].t;
        addEdge(a, b, w, 1);
        addEdge(b, a, w, 1);
      }
    });
  }
  for (const [sid, list] of byStation) {
    if (list.length < 2) continue;
    for (const a of list) for (const b of list) {
      if (a === b) continue;
      const la = App.lines.find(l => l.id === nodes[a].l);
      const sameLine = nodes[a].l === nodes[b].l;
      // 同线不同臂 = 同站换乘，成本接近零；跨线按换乘时间计
      const w = sameLine ? 0.8 : K.TRANSFER + 0.5 * la.headway / 60;
      addEdge(a, b, w, 2);
    }
  }
  App.graph = { nodes, map, adj, byStation };
  App.pathCache.clear();
  App.legCache.clear();
  App.odTable.clear();
  App.totalWeight = 1;
}

/* ---------------- 最小堆 ---------------- */
class MinHeap {
  constructor() { this.a = []; }
  push(node, pri) { this.a.push({ node, pri }); this._up(this.a.length - 1); }
  pop() {
    const a = this.a; if (!a.length) return null;
    const top = a[0]; const last = a.pop();
    if (a.length) { a[0] = last; this._down(0); }
    return top;
  }
  _up(i) {
    const a = this.a;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p].pri <= a[i].pri) break;
      [a[p], a[i]] = [a[i], a[p]]; i = p;
    }
  }
  _down(i) {
    const a = this.a;
    for (;;) {
      const l = i * 2 + 1, r = l + 1; let m = i;
      if (l < a.length && a[l].pri < a[m].pri) m = l;
      if (r < a.length && a[r].pri < a[m].pri) m = r;
      if (m === i) break;
      [a[m], a[i]] = [a[i], a[m]]; i = m;
    }
  }
  get size() { return this.a.length; }
}

/* ---------------- Dijkstra（按起点缓存） ---------------- */
function dijkstra(origin) {
  if (App.pathCache.has(origin)) return App.pathCache.get(origin);
  const G = App.graph;
  const n = G.nodes.length;
  const dist = new Float64Array(n).fill(Infinity);
  const prev = new Int32Array(n).fill(-1);
  const ptype = new Uint8Array(n);
  const heap = new MinHeap();
  const startNodes = G.byStation.get(origin) || [];
  for (const idx of startNodes) {
    const line = App.lines.find(l => l.id === G.nodes[idx].l);
    const w = 0.5 * line.headway / 60;
    if (w < dist[idx]) { dist[idx] = w; ptype[idx] = 3; heap.push(idx, w); }
  }
  while (heap.size) {
    const { node, pri } = heap.pop();
    if (pri > dist[node]) continue;
    for (const e of G.adj[node]) {
      const nd = pri + e.w;
      if (nd < dist[e.to]) {
        dist[e.to] = nd; prev[e.to] = node; ptype[e.to] = e.kind;
        heap.push(e.to, nd);
      }
    }
  }
  const res = { dist, prev, ptype, nodes: G.nodes, t: performance.now() };
  App.pathCache.set(origin, res);
  if (App.pathCache.size > 320) App.pathCache.delete(App.pathCache.keys().next().value);
  return res;
}

/* 回溯出换乘腿 */
function legsFor(origin, dest, ds) {
  const G = App.graph;
  const destNodes = G.byStation.get(dest) || [];
  let best = -1, bd = Infinity;
  for (const idx of destNodes) if (ds.dist[idx] < bd) { bd = ds.dist[idx]; best = idx; }
  if (best < 0 || !isFinite(bd)) return null;
  if (bd > 360) return null;                     // 超过 6 小时视为不可达
  const seq = [];
  let cur = best;
  let guard = 0;
  while (cur !== -1 && guard++ < 900) { seq.push(cur); if (ds.ptype[cur] === 3) break; cur = ds.prev[cur]; }
  if (cur === -1 || ds.ptype[cur] !== 3) return null;
  seq.reverse();
  const nodes = ds.nodes;
  const legs = [];
  let leg = null;
  for (let k = 1; k < seq.length; k++) {
    const nd = nodes[seq[k]];
    const pv = nodes[seq[k - 1]];
    if (ds.ptype[seq[k]] === 2) {
      if (leg) { legs.push(leg); leg = null; }
      continue;
    }
    const dir = nd.i > pv.i ? 0 : 1;
    if (!leg) {
      leg = { line: nd.l, arm: nd.arm, dir, board: pv.s, alight: nd.s, bi: pv.i, ai: nd.i, stops: 1 };
    } else if (leg.line === nd.l && leg.dir === dir && leg.arm === nd.arm) {
      leg.alight = nd.s; leg.ai = nd.i; leg.stops++;
    } else {
      legs.push(leg);
      leg = { line: nd.l, arm: nd.arm, dir, board: pv.s, alight: nd.s, bi: pv.i, ai: nd.i, stops: 1 };
    }
  }
  if (leg) legs.push(leg);
  if (!legs.length) return null;
  for (const lg of legs) {
    const line = App.lines.find(l => l.id === lg.line);
    if (!line) { lg.t = 0; continue; }
    const arms = lineArms(line);
    const arm = arms[lg.arm] || arms[0];
    let t = 0;
    if (arm && typeof lg.bi === 'number' && typeof lg.ai === 'number' && arm.segs) {
      const a = Math.min(lg.bi, lg.ai), b = Math.max(lg.bi, lg.ai);
      for (let i = a; i < b; i++) if (arm.segs[i]) t += arm.segs[i].t;
    } else {
      const si = (arm ? arm.stations : []).indexOf(lg.board);
      const ei = (arm ? arm.stations : []).indexOf(lg.alight);
      if (si >= 0 && ei >= 0) {
        const a = Math.min(si, ei), b = Math.max(si, ei);
        for (let i = a; i < b; i++) if (arm.segs[i]) t += arm.segs[i].t;
      }
    }
    lg.t = t;
  }
  return { legs, cost: bd, transfers: legs.length - 1 };
}

/* ---------------- OD 抽样表 ---------------- */
function odFor(origin) {
  if (App.odTable.has(origin)) return App.odTable.get(origin);
  const items = [];
  const o = App.stations.get(origin);
  let total = 0;
  for (const [id, st] of App.stations) {
    if (id === origin) continue;
    const d = haversine(o, st) * 1.1;
    const w = st.w * Math.exp(-d / 13.5) + 0.02;
    total += w;
    items.push({ id, w, cum: total });
  }
  const table = { items, total };
  App.odTable.set(origin, table);
  return table;
}
function pickDest(origin) {
  let tb = null;
  if (Math.random() < K.SAME_LINE) {
    tb = sameLineOdFor(origin);
    if (!tb || !tb.items.length) tb = null;
  }
  if (!tb) tb = odFor(origin);
  const r = Math.random() * tb.total;
  let lo = 0, hi = tb.items.length - 1;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (tb.items[mid].cum < r) lo = mid + 1; else hi = mid;
  }
  return tb.items[lo].id;
}
/* 同一线路内的目的地表：还原“能直达就不换乘”的出行习惯 */
function sameLineOdFor(origin) {
  if (App.odSame.has(origin)) return App.odSame.get(origin);
  const o = App.stations.get(origin);
  const seen = new Set();
  const items = []; let total = 0;
  for (const lid of o.lines) {
    const ln = App.lines.find(l => l.id === lid && l.enabled);
    if (!ln) continue;
    for (const arm of lineArms(ln)) for (const id of arm.stations) {
      if (id === origin || seen.has(id)) continue;
      seen.add(id);
      const st = App.stations.get(id);
      const d = haversine(o, st) * 1.1;
      const w = st.w * Math.exp(-d / 13.5) + 0.02;
      total += w;
      items.push({ id, w, cum: total });
    }
  }
  const table = { items, total };
  App.odSame.set(origin, table);
  return table;
}
const weightPool = () => {
  const arr = []; let total = 0;
  for (const [id, st] of App.stations) { total += st.w; arr.push({ id, cum: total }); }
  App.totalWeight = total || 1;
  return { arr, total };
};
let ORIGIN_POOL = null;
function pickOrigin() {
  if (!ORIGIN_POOL) ORIGIN_POOL = weightPool();
  const r = Math.random() * ORIGIN_POOL.total;
  let lo = 0, hi = ORIGIN_POOL.arr.length - 1;
  while (lo < hi) { const mid = (lo + hi) >> 1; if (ORIGIN_POOL.arr[mid].cum < r) lo = mid + 1; else hi = mid; }
  return ORIGIN_POOL.arr[lo].id;
}
function invalidatePools() { ORIGIN_POOL = null; App.totalWeight = 0; App.odSame.clear(); }

/* 带缓存的 OD 路径 */
function getLegs(o, d) {
  const key = o + '|' + d;
 if (App.legCache.has(key)) return App.legCache.get(key);
  let ds = App.pathCache.get(o);
  if (!ds) ds = dijkstra(o);
  const legs = legsFor(o, d, ds);
  if (App.legCache.size > 15000) App.legCache.clear();
  App.legCache.set(key, legs);
  return legs;
}

/* ---------------- 仿真 ---------------- */
function startSim(opts) {
  opts = opts || {};
  const dur = opts.duration || 2;
  const demand = opts.demand || 1;
  const sim = {
    running: true, paused: false,
    t: K.SIM_START, t0: K.SIM_START, tEnd: K.SIM_START + dur * 60,
    speed: 30, dur, demand,
    pax: [], trains: [],
    waitQ: new Map(),
    stats: { gen: 0, done: 0, lost: 0, totalTime: 0, transfers: 0, waitSum: 0, rideSum: 0, samples: 0, boardings: 0, timedOut: 0, lostPlatform: 0, lostPath: 0, lostTimeout: 0, lostActive: 0 },
    lineStats: {},
    stationStats: new Map(),
    pid: 0, acc: 0, lastWall: 0, active: 0, odAgg: new Map(),
    events: [], hot: [], maxQueue: 0,
    odTimes: [],
    startWall: performance.now()
  };
  for (const line of App.lines) {
    sim.lineStats[line.id] = { boardings: 0, peak: 0, paxKm: 0 };
    line.pax = 0; line.peakLoad = 0; line.depTimer = 0;
    line.loadSum = 0; line.loadCount = 0; line.avgLoad = 0;
    line.capEff = Math.max(6, Math.round(line.cap * K.CAP_RATIO));
  }
  for (const [id, st] of App.stations) {
    sim.stationStats.set(id, { board: 0, alight: 0, queue: 0, transfer: 0 });
  }
  // 初始化列车：各运行臂按发车间隔铺车
  for (const line of App.lines) {
    if (!line.enabled) continue;
    initTrains(line, sim);
  }
  App.sim = sim;
  App.report = null;
  return sim;
}

function initTrains(line, sim) {
  const arms = lineArms(line);
  const nArms = Math.max(1, arms.filter(a => a.stations.length >= 2).length);
  let fleet = 0;
  arms.forEach((arm, ai) => {
    if (arm.stations.length < 2 || !arm.segs || !arm.segs.length) return;
    const head = (line.headway * nArms) / 60;      // 分叉后各臂交替发车
    const roundTrip = 2 * arm.runTime + 3.2;
    const perDir = Math.max(2, Math.round(roundTrip / head / 2));
    for (let k = 0; k < perDir; k++) {
      const offset = (k / perDir) * arm.runTime;
      addTrainAt(line, arm, ai, 0, offset, sim);
      addTrainAt(line, arm, ai, 1, offset, sim);
    }
    fleet += perDir * 2;
  });
  line.fleet = Math.max(fleet, nArms);
}
function addTrainAt(line, arm, ai, dir, offset, sim) {
  const segs = arm.segs;
  if (!segs || !segs.length) return;
  let rem = offset, i = 0;
  if (dir === 1) {
    for (let k = segs.length - 1; k >= 0; k--) {
      if (rem <= segs[k].t) { i = k; break; }
      rem -= segs[k].t;
    }
  } else {
    for (let k = 0; k < segs.length; k++) {
      if (rem <= segs[k].t) { i = k; break; }
      rem -= segs[k].t;
    }
  }
  sim.trains.push(makeTrain(line, ai, dir, i, rem / Math.max(0.1, segs[i].t)));
}
function makeTrain(line, arm, dir, i, prog) {
  return {
    id: line.id + dir + Math.random().toString(36).slice(2, 5),
    line: line.id, arm, dir, i, prog,
    load: 0, pax: [], dwell: 0, late: 0
  };
}
function spawnTrain(line, armIdx, dir, sim) {
  const arm = lineArms(line)[armIdx];
  if (!arm || arm.stations.length < 2) return;
  const n = arm.stations.length;
  const i = dir === 0 ? 0 : n - 2;
  const tr = makeTrain(line, armIdx, dir, i, 0);
  tr.dwell = K.DWELL;
  sim.trains.push(tr);
  boardPassengers(tr, arm.stations[dir === 0 ? 0 : n - 1], sim);
}

function peakFactor(t) {
  const h = t / 60;
  return 0.55 + 1.45 * Math.exp(-Math.pow((h - 8.0) / 0.78, 2));
}

function spawnDemand(sim, dt) {
  if (!App.totalWeight) weightPool();
  const pf = peakFactor(sim.t);
  const expected = App.totalWeight * K.DEMAND * pf * sim.demand * dt;
  sim.acc += expected;
  let n = Math.floor(sim.acc);
  sim.acc -= n;
  n = Math.min(n, 220);
  for (let k = 0; k < n; k++) createPax(sim);
}

function createPax(sim) {
  if (sim.active > K.MAX_ACTIVE) { sim.stats.lostActive++; sim.stats.lost++; return; }
  const o = pickOrigin();
  const d = pickDest(o);
  if (!d || d === o) return;
  const legs = getLegs(o, d);
  if (!legs) { sim.stats.lostPath++; sim.stats.lost++; return; }
  const ss = sim.stationStats.get(o);
  if (ss && ss.queue >= K.PLATFORM_CAP) { sim.stats.lostPlatform++; sim.stats.lost++; return; }
  const p = {
    id: ++sim.pid, o, d, legs: legs.legs, li: 0,
    tBirth: sim.t, tWait: sim.t, state: 'wait',
    transfers: 0, leg: legs.legs[0]
  };
  sim.pax.push(p);
  sim.active++;
  sim.stats.gen++;
  const key = queueKey(o, p.leg.line, p.leg.dir);
  let q = sim.waitQ.get(key);
  if (!q) { q = []; sim.waitQ.set(key, q); }
  q.push(p);
  if (ss) { ss.queue++; sim.maxQueue = Math.max(sim.maxQueue, ss.queue); }
}
function queueKey(st, line, dir) { return st + '|' + line + '|' + dir; }

/* 列车到站 → 下车 / 上车 */
function arrive(tr, stationId, sim) {
  const line = App.lines.find(l => l.id === tr.line);
  // 下车
  const stay = [];
  for (const p of tr.pax) {
    if (p.d === stationId) {
      // 到达终点
      finishPax(p, sim);
    } else if (p.leg && p.leg.alight === stationId) {
      // 换乘
      p.li++;
      p.transfers++;
      const ss = sim.stationStats.get(stationId);
      if (ss) { ss.alight++; ss.transfer++; }
      if (p.li < p.legs.length) {
        p.leg = p.legs[p.li];
        p.state = 'wait'; p.tWait = sim.t;
        const key = queueKey(stationId, p.leg.line, p.leg.dir);
        let q = sim.waitQ.get(key);
        if (!q) { q = []; sim.waitQ.set(key, q); }
        q.push(p);
        if (ss) ss.queue++;
      } else {
        finishPax(p, sim);
      }
    } else {
      stay.push(p);
    }
  }
  tr.pax = stay;
  tr.load = stay.length;
  // 上车
  boardPassengers(tr, stationId, sim);
  // 记录断面
  const ls = sim.lineStats[tr.line];
  if (ls) ls.peak = Math.max(ls.peak, tr.load);
  line.peakLoad = Math.max(line.peakLoad, tr.load);
  line.loadSum = (line.loadSum || 0) + tr.load;
  line.loadCount = (line.loadCount || 0) + 1;
}

function boardPassengers(tr, stationId, sim) {
  const line = App.lines.find(l => l.id === tr.line);
  const key = queueKey(stationId, tr.line, tr.dir);
  const q = sim.waitQ.get(key);
  if (!q || !q.length) return;
  const keep = [];
  for (const p of q) {
    if (tr.pax.length < line.capEff) {
      p.state = 'ride'; p.tBoard = sim.t;
      p.rideStart = sim.t;
      tr.pax.push(p);
      tr.load = tr.pax.length;
      const ss = sim.stationStats.get(stationId);
      if (ss) { ss.queue = Math.max(0, ss.queue - 1); ss.board++; }
      const ls = sim.lineStats[tr.line];
      if (ls) ls.boardings++;
      sim.stats.boardings++;
      sim.stats.waitSum += (sim.t - p.tWait);
    } else {
      keep.push(p);
    }
  }
  sim.waitQ.set(key, keep);
  if (keep.length > 8) {
    sim.events.push({ t: sim.t, msg: `${App.stations.get(stationId).name} 站台滞留 ${keep.length} 人，${line.name} 满载` });
  }
}

function finishPax(p, sim) {
  if (p.state === 'done' || p.state === 'lost') return;
  p.state = 'done';
  sim.active = Math.max(0, sim.active - 1);
  const tt = sim.t - p.tBirth;
  sim.stats.done++;
  sim.stats.totalTime += tt;
  sim.stats.transfers += p.transfers;
  sim.stats.samples++;
  const ss = sim.stationStats.get(p.d);
  if (ss) ss.alight++;
  const key = p.o + '|' + p.d;
  let ag = sim.odAgg.get(key);
  if (!ag) { ag = { n: 0, sum: 0 }; sim.odAgg.set(key, ag); }
  ag.n++; ag.sum += tt;
  if (p.transfers > 0) {
    // 记录换乘衔接时间
  }
}

/* 单步推进 */
function stepSim(sim, dt) {
  if (dt <= 0) return;
  dt = Math.min(dt, 6);
  sim.t += dt;
  if (!sim.draining && sim.t >= sim.tEnd) {
    sim.t = sim.tEnd;
    sim.draining = true;
    sim.drainEnd = sim.tEnd + 42;
  }

  // 列车运行（车队数量固定，端点折返）
  const dead = [];
  for (const tr of sim.trains) {
    const line = App.lines.find(l => l.id === tr.line);
    if (!line || !line.enabled) { dead.push(tr); continue; }
    const arms = lineArms(line);
    const arm = arms[tr.arm] || arms[0];
    if (!arm || arm.stations.length < 2) { dead.push(tr); continue; }
    let move = dt, guard = 0;
    while (move > 0.0001 && guard++ < 60) {
      if (tr.dwell > 0) {
        const use = Math.min(move, tr.dwell);
        tr.dwell -= use; move -= use;
        continue;
      }
      const seg = arm.segs[tr.i];
      if (!seg) { dead.push(tr); break; }
      const need = (1 - tr.prog) * seg.t;
      if (move < need) { tr.prog += move / seg.t; move = 0; break; }
      move -= need;
      const n = arm.stations.length;
      const stationId = tr.dir === 0 ? arm.stations[tr.i + 1] : arm.stations[tr.i];
      tr.prog = 1;
      arrive(tr, stationId, sim);
      tr.dwell = K.DWELL;
      if (tr.dir === 0) {
        if (tr.i >= n - 2) {
          tr.dir = 1; tr.i = n - 2; tr.prog = 0; tr.dwell = 1.6;
          boardPassengers(tr, arm.stations[n - 1], sim);
        } else { tr.i++; tr.prog = 0; }
      } else {
        if (tr.i <= 0) {
          tr.dir = 0; tr.i = 0; tr.prog = 0; tr.dwell = 1.6;
          boardPassengers(tr, arm.stations[0], sim);
        } else { tr.i--; tr.prog = 0; }
      }
    }
  }
  if (dead.length) sim.trains = sim.trains.filter(t => !dead.includes(t));

  // 需求（清客阶段停止生成）
  if (!sim.draining) spawnDemand(sim, dt);

  // 候车超时清理
  if (Math.floor(sim.t * 2) !== Math.floor((sim.t - dt) * 2)) {
    for (const [key, q] of sim.waitQ) {
      if (!q.length) continue;
      const bad = [];
      for (const p of q) if (sim.t - p.tWait > K.WAIT_LIMIT) bad.push(p);
      if (bad.length) {
        for (const p of bad) {
          const i = q.indexOf(p);
          if (i >= 0) q.splice(i, 1);
          p.state = 'lost';
          sim.active = Math.max(0, sim.active - 1);
          sim.stats.lost++;
          sim.stats.lostTimeout++;
          const ss = sim.stationStats.get(p.o);
          if (ss) ss.queue = Math.max(0, ss.queue - bad.length);
        }
      }
    }
    // 移除已放弃/完成乘客
    if (sim.pax.length > 400) {
      sim.pax = sim.pax.filter(p => p.state !== 'done' && p.state !== 'lost');
      sim.active = sim.pax.length;
    }
  }

  // 事件裁剪
  if (sim.events.length > 40) sim.events.splice(0, sim.events.length - 40);
  if (sim.draining && (sim.active <= 18 || sim.t >= sim.drainEnd)) finishSim(sim);
}

function finishSim(sim) {
  sim = sim || App.sim;
  if (!sim || !sim.running) return;
  sim.running = false;
  sim.ended = true;
  const st = sim.stats;
  const avg = st.samples ? st.totalTime / st.samples + K.ACCESS : 0;
  const trRate = st.samples ? st.transfers / st.samples : 0;
  const lostRate = st.gen ? st.lost / st.gen : 0;
  const wait = st.boardings ? st.waitSum / st.boardings : 0;
  const lines = App.lines.filter(l => l.enabled).map(l => {
    const capEff = l.capEff || Math.max(6, Math.round(l.cap * K.CAP_RATIO));
    const avgLoad = l.loadCount ? l.loadSum / l.loadCount : 0;
    l.avgLoad = avgLoad;
    return {
      id: l.id, name: l.name, color: l.color, headway: l.headway,
      peak: Math.round(l.peakLoad / K.SAMPLE), cap: l.cap,
      boardings: sim.lineStats[l.id].boardings,
      loadRate: avgLoad / Math.max(1, capEff),
      peakRate: l.peakLoad / Math.max(1, capEff)
    };
  }).sort((a, b) => b.loadRate - a.loadRate);
  const hot = [];
  for (const [id, ss] of sim.stationStats) {
    if (ss.queue > 0 || ss.board > 0) hot.push({ id, name: App.stations.get(id).name, queue: ss.queue, board: ss.board });
  }
  hot.sort((a, b) => b.board - a.board || b.queue - a.queue);
  const grade = calcGrade({ avg, trRate, lostRate, lines });
  App.report = {
    avg, trRate, lostRate, wait, lines, hot: hot.slice(0, 6), grade,
    done: st.done, lost: st.lost, gen: st.gen,
    duration: sim.tEnd - sim.t0, finishAt: sim.t, challenge: App.challenge
  };
  return App.report;
}

function calcGrade(m) {
  let score = 100;
  score -= Math.max(0, m.avg - 32) * 2.6;
  score -= Math.max(0, m.trRate - 0.6) * 26;
  score -= m.lostRate * 500;
  const worst = m.lines[0] ? m.lines[0].loadRate : 0;
  score -= Math.max(0, worst - 0.9) * 120;
  score = Math.max(0, Math.min(100, score));
  const g = score >= 94 ? 'S' : score >= 86 ? 'A' : score >= 74 ? 'B' : score >= 58 ? 'C' : 'D';
  return { score: Math.round(score), grade: g, avg: m.avg, trRate: m.trRate, lostRate: m.lostRate };
}

/* ---------------- 编辑操作 ---------------- */
function getLine(id) { return App.lines.find(l => l.id === id); }

/* ---------------- 线路中段拆分（类广州 2/8 号线拆分） ----------------
   TRACK_OV：轨道折线覆盖表。拆分时把原线轨道在断点处裁成两段写进来，
   不动原始 TRACK 常量，撤销 / 存档只需带走这张小表。 */
const TRACK_OV = {};
function trackOf(id) {
  if (TRACK_OV[id]) return TRACK_OV[id];
  return (typeof TRACK !== 'undefined') ? TRACK[id] : null;
}
function trackResetAll() { for (const k in TRACK_OV) delete TRACK_OV[k]; }

function havPtLL(a, b) {   // a:[lng,lat]  b:{lng,lat}
  return Math.hypot((a[0] - b.lng) * KX, (a[1] - b.lat) * KY);
}

/* 把 fromId 的轨道折线在 head / tail 交界处切开，前段归 fromId，后段归 toId */
function trackCut(fromId, toId, head, tail) {
  const pts = trackOf(fromId);
  if (!pts || pts.length < 4) return false;
  const S = App.stations;
  const st0 = S.get(head[0]), stN = S.get(tail[tail.length - 1]);
  const sA = S.get(head[head.length - 1]), sB = S.get(tail[0]);
  if (!st0 || !stN || !sA || !sB) return false;
  const rev = havPtLL(pts[pts.length - 1], st0) < havPtLL(pts[0], st0);
  const path = rev ? pts.slice().reverse() : pts;
  const xy = path.map(p => [(p[0] - LNG0) * KX, (LAT0 - p[1]) * KY]);
  const cum = [0];
  for (let i = 1; i < xy.length; i++) {
    cum.push(cum[i - 1] + Math.hypot(xy[i][0] - xy[i - 1][0], xy[i][1] - xy[i - 1][1]));
  }
  const proj = st => {
    const p = [(st.lng - LNG0) * KX, (LAT0 - st.lat) * KY];
    let best = { d: 1e9, s: 0 };
    for (let i = 0; i < xy.length - 1; i++) {
      const a = xy[i], b = xy[i + 1];
      const dx = b[0] - a[0], dy = b[1] - a[1];
      const L2 = dx * dx + dy * dy || 1e-9;
      let t = ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L2;
      t = t < 0 ? 0 : t > 1 ? 1 : t;
      const qx = a[0] + t * dx, qy = a[1] + t * dy;
      const d = Math.hypot(p[0] - qx, p[1] - qy);
      if (d < best.d) best = { d, s: cum[i] + t * Math.hypot(dx, dy) };
    }
    return best;
  };
  const pA = proj(sA), pB = proj(sB);
  if (pA.d > 1.3 || pB.d > 1.3) return false;      // 断点站偏离轨道太远，放弃裁切
  if (Math.abs(pB.s - pA.s) > 3.5) return false;   // 两站不在轨道上相邻
  const sCut = (pA.s + pB.s) / 2;
  let i = 0;
  while (i < cum.length - 2 && cum[i + 1] <= sCut) i++;
  const a = xy[i], b = xy[i + 1];
  const L = (cum[i + 1] - cum[i]) || 1e-9;
  let t = (sCut - cum[i]) / L;
  t = t < 0 ? 0 : t > 1 ? 1 : t;
  const cut = [a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])];
  const toLL = arr => arr.map(q => [q[0] / KX + LNG0, LAT0 - q[1] / KY]);
  TRACK_OV[fromId] = toLL(xy.slice(0, i + 1).concat([cut]));
  TRACK_OV[toId] = toLL([cut].concat(xy.slice(i + 1)));
  return true;
}

/* 在主干上 cutIdx 处断开：head = [0, cutIdx)，tail = [cutIdx, n) */
function splitLine(lineId, cutIdx, opts) {
  opts = opts || {};
  const line = getLine(lineId);
  if (!line) return { ok: false, reason: '找不到这条线路' };
  const arms = lineArms(line);
  const main = arms[0];
  const n = main.stations.length;
  if (cutIdx < 2 || cutIdx > n - 2) return { ok: false, reason: '断点太靠端，两段都要至少 2 站' };
  if (typeof pushUndo === 'function') pushUndo();

  const head = main.stations.slice(0, cutIdx);
  const tail = main.stations.slice(cutIdx);
  const stay = [], move = [];
  for (let k = 1; k < arms.length; k++) {
    (tail.indexOf(arms[k].stations[0]) >= 0 ? move : stay).push(arms[k]);
  }

  const nl = createLine(opts.name || (line.name + '·新段'), opts.color || '#8AB4F8');
  nl.short = opts.short || (line.short + 'b');
  nl.headway = line.headway; nl.speed = line.speed; nl.cap = line.cap; nl.enabled = line.enabled;
  nl.custom = true;

  line.stations = head;
  line.arms = [{ stations: line.stations }].concat(stay.map(a => ({ stations: a.stations.slice() })));
  nl.stations = tail;
  nl.arms = [{ stations: nl.stations }].concat(move.map(a => ({ stations: a.stations.slice() })));

  for (const sid of tail) {
    const st = App.stations.get(sid);
    if (!st) continue;
    st.lines = st.lines.filter(x => x !== line.id);
    if (!st.lines.includes(nl.id)) st.lines.push(nl.id);
  }

  App.trackOff[line.id] = 0;
  App.trackOff[nl.id] = 0;
  if (line.arms.length > 1) App.trackOff[line.id] = 1;
  else if (!trackCut(line.id, nl.id, head, tail)) App.trackOff[line.id] = 1;
  if (nl.arms.length > 1 || !trackOf(nl.id)) App.trackOff[nl.id] = 1;

  refreshSegs(); rebuildGraph();
  App.selectedLine = nl.id; App.editingLine = nl.id;
  return { ok: true, id: nl.id, line: nl, head: head.length, tail: tail.length };
}

function addStation(name, lng, lat) {
  if (!name) return null;
  name = name.trim();
  if (!name) return null;
  let st = App.stations.get(name);
  if (st) return st;
  st = {
    id: name, name, lng, lat,
    x: (lng - LNG0) * KX, y: (LAT0 - lat) * KY,
    w: 0.5, lines: [], custom: true, boardings: 0, alightings: 0
  };
  App.stations.set(name, st);
  App.customStations++;
  return st;
}

function createLine(name, color) {
  const id = 'C' + (App.lines.length + 1) + '_' + Date.now().toString(36).slice(-3);
  const line = {
    id, name, short: '新', color,
    headway: 240, speed: 34, cap: 1000, stations: [], enabled: true, custom: true,
    segs: null, pax: 0, peakLoad: 0, fleet: 0, depTimer: 0
  };
  App.lines.push(line);
  App.selectedLine = id;
  return line;
}

/* 在任意锚点处接入车站：
   - 锚点是某臂的首站 → 向前延长
   - 锚点是某臂的末站 → 向后延长
   - 锚点在臂中间   → 从该站分出一条新的支线（Y 型） */
function lineAttach(line, anchorSid, stationId) {
  const st = App.stations.get(stationId);
  if (!st) return null;
  const arms = lineArms(line);
  const allStations = new Set();
  for (const arm of arms) for (const s of arm.stations) allStations.add(s);
  if (allStations.has(stationId)) return { ok: false, reason: 'dup' };

  let anchorArm = -1, anchorIdx = -1;
  if (anchorSid) {
    for (let ai = 0; ai < arms.length; ai++) {
      const i = arms[ai].stations.indexOf(anchorSid);
      if (i >= 0) { anchorArm = ai; anchorIdx = i; break; }
    }
  }
  if (!st.lines.includes(line.id)) st.lines.push(line.id);

  let mode = 'append';
  if (anchorArm < 0) {
    // 没有锚点：接到主干的任一端（优先末端）
    const main = arms[0];
    if (!main.stations.length) { main.stations.push(stationId); mode = 'new'; }
    else { main.stations.push(stationId); mode = 'append'; }
    anchorArm = 0;
  } else {
    const arm = arms[anchorArm];
    if (anchorIdx === arm.stations.length - 1) {
      arm.stations.push(stationId); mode = 'append';
    } else if (anchorIdx === 0) {
      arm.stations.unshift(stationId); mode = 'prepend';
    } else {
      const branch = { stations: [anchorSid, stationId] };
      arms.push(branch); mode = 'branch';
    }
  }
  // 主干被改动（插站/换端）时才放弃真实轨道折线；纯分叉不影响主干几何
  if (!mainMatchesDef(line)) App.trackOff[line.id] = 1;
  refreshSegs();
  rebuildGraph();
  return { ok: true, mode, arm: mode === 'branch' ? arms.length - 1 : anchorArm };
}

/* 兼容旧接口：追加到主干末端 */
function lineAppend(line, stationId) {
  return !!lineAttach(line, line.stations[line.stations.length - 1] || null, stationId);
}

/* 从指定运行臂上摘除某一站（主干至少保留 2 站；支线摘到只剩分叉点则整条支线移除） */
function removeStationFromArm(line, ai, sid) {
  const arms = lineArms(line);
  const arm = arms[ai];
  if (!arm) return false;
  const i = arm.stations.indexOf(sid);
  if (i < 0) return false;
  if (ai === 0) {
    if (arm.stations.length <= 2) return false;
    for (let k = arms.length - 1; k >= 1; k--) if (arms[k].stations[0] === sid) arms.splice(k, 1);
    arm.stations.splice(i, 1);
  } else {
    if (arm.stations.length <= 1) return false;
    arm.stations.splice(i, 1);
    if (arm.stations.length < 2) arms.splice(ai, 1);
  }
  revokeStationLine(sid, line.id);
  syncLineOwnership(line);
  refreshSegs();
  rebuildGraph();
  return true;
}

function removeStationFromLine(line, stationId) {
  if (!line) return false;
  const arms = lineArms(line);
  let removed = false;
  for (let ai = arms.length - 1; ai >= 0; ai--) {
    const arm = arms[ai];
    const i = arm.stations.indexOf(stationId);
    if (i < 0) continue;
    if (arm.stations.length <= 1) continue;
    if (ai === 0) for (let k = arms.length - 1; k >= 1; k--) if (arms[k].stations[0] === stationId) arms.splice(k, 1);
    arm.stations.splice(i, 1);
    removed = true;
    // 支线被摘到只剩 1 站（分叉点）时整臂移除，避免退化
    if (ai > 0 && arm.stations.length < 2) arms.splice(ai, 1);
  }
  // 主干不足 2 站：拒绝删除（调用方已前置校验，这里兜底）
  if (arms[0] && arms[0].stations.length < 2) {
    arms[0].stations = arms[0].stations.length ? arms[0].stations : [];
  }
  if (!removed) return false;
  // 跳过该站后列车仍沿原轨道行驶，不置 trackOff，保留真实几何
  revokeStationLine(stationId, line.id);
  syncLineOwnership(line);
  refreshSegs();
  rebuildGraph();
  return true;
}
/* 按线路当前所有运行臂重建"站→线路"归属，清掉因分支/整臂移除而残留的引用 */
function syncLineOwnership(line) {
  if (!line) return;
  const keep = new Set();
  for (const arm of lineArms(line)) for (const s of arm.stations) keep.add(s);
  for (const st of App.stations.values()) {
    if (keep.has(st.id)) { if (!st.lines.includes(line.id)) st.lines.push(line.id); }
    else if (st.lines.includes(line.id)) st.lines = st.lines.filter(x => x !== line.id);
  }
}

function revokeStationLine(sid, lineId) {
  const st = App.stations.get(sid);
  if (!st) return;
  const line = App.lines.find(l => l.id === lineId);
  const still = line && lineArms(line).some(a => a.stations.includes(sid));
  if (!still) st.lines = st.lines.filter(x => x !== lineId);
}

function deleteLine(id) {
  const line = getLine(id);
  if (!line) return;
  for (const arm of lineArms(line)) {
    for (const sid of arm.stations) {
      const st = App.stations.get(sid);
      if (st) st.lines = st.lines.filter(x => x !== id);
    }
  }
  App.lines = App.lines.filter(l => l.id !== id);
  if (App.selectedLine === id) App.selectedLine = null;
  if (App.editingLine === id) App.editingLine = null;
  refreshSegs();
  rebuildGraph();
}

function moveStation(sid, lng, lat) {
  const st = App.stations.get(sid);
  if (!st) return;
  st.lng = lng; st.lat = lat;
  st.x = (lng - LNG0) * KX; st.y = (LAT0 - lat) * KY;
  refreshSegs();
  rebuildGraph();
}

function removeStationEverywhere(sid) {
  const st = App.stations.get(sid);
  for (const line of App.lines) {
    const arms = lineArms(line);
    for (let ai = arms.length - 1; ai >= 0; ai--) {
      const arm = arms[ai];
      const i = arm.stations.indexOf(sid);
      if (i >= 0) {
        if (ai === 0) for (let k = arms.length - 1; k >= 1; k--) if (arms[k].stations[0] === sid) arms.splice(k, 1);
        arm.stations.splice(i, 1);
      }
      if (ai > 0 && arm.stations.length < 2) arms.splice(ai, 1);
    }
  }
  App.stations.delete(sid);
  if (st && st.custom) {
    App.customStations = Math.max(0, App.customStations - 1);
    App.newStations = Math.max(0, App.newStations - 1);
  }
  for (const line of App.lines) syncLineOwnership(line);
  App.hover = null;
  App.dragStation = null;
  invalidatePools();
  refreshSegs();
  rebuildGraph();
}

/* ---------------- 指标工具 ---------------- */
function networkStats() {
  const active = App.lines.filter(l => l.enabled && lineArms(l).some(a => a.stations.length >= 2));
  const km = active.reduce((s, l) => s + (l.km || 0), 0);
  const stations = new Set();
  for (const l of active) for (const arm of lineArms(l)) for (const s of arm.stations) stations.add(s);
  return { lines: active.length, stations: stations.size, km };
}
function fmtClock(min) {
  const h = Math.floor(min / 60) % 24, m = Math.floor(min % 60);
  return String(h).padStart(2, '0') + ':' + String(m).padStart(2, '0');
}


/* ============================================================
   渲染层：Canvas 地图 / 线网 / 列车 / 热力
   ============================================================ */
'use strict';

const canvas = document.getElementById('map');
const ctx = canvas.getContext('2d');
let W = 0, H = 0, DPR = 1;
let lastFrame = performance.now();
const mouse = { x: 0, y: 0, inside: false, world: { x: 48, y: 62 }, down: false, dragging: false, sx: 0, sy: 0, moved: false };

function resizeCanvas() {
  const wrap = canvas.parentElement;
  DPR = Math.min(2, window.devicePixelRatio || 1);
  W = wrap.clientWidth; H = wrap.clientHeight;
  canvas.width = Math.round(W * DPR);
  canvas.height = Math.round(H * DPR);
  canvas.style.width = W + 'px';
  canvas.style.height = H + 'px';
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  App.dirty = true;
}

function w2s(x, y) {
  return { x: (x - App.cam.x) * App.cam.s + W / 2, y: (y - App.cam.y) * App.cam.s + H / 2 };
}
function s2w(sx, sy) {
  return { x: (sx - W / 2) / App.cam.s + App.cam.x, y: (sy - H / 2) / App.cam.s + App.cam.y };
}
function lngLatToWorld(lng, lat) { return { x: (lng - LNG0) * KX, y: (LAT0 - lat) * KY }; }
function worldToLngLat(x, y) { return { lng: x / KX + LNG0, lat: LAT0 - y / KY }; }

/* ---------- 平滑折线 ---------- */
function smoothPath(pts) {
  ctx.beginPath();
  if (pts.length < 2) return;
  ctx.moveTo(pts[0].x, pts[0].y);
  if (pts.length === 2) { ctx.lineTo(pts[1].x, pts[1].y); return; }
  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)], p1 = pts[i];
    const p2 = pts[i + 1], p3 = pts[Math.min(pts.length - 1, i + 2)];
    const c1x = p1.x + (p2.x - p0.x) / 6, c1y = p1.y + (p2.y - p0.y) / 6;
    const c2x = p2.x - (p3.x - p1.x) / 6, c2y = p2.y - (p3.y - p1.y) / 6;
    ctx.bezierCurveTo(c1x, c1y, c2x, c2y, p2.x, p2.y);
  }
}

/* 站点折线（无真实轨道几何时）：直线段 + 小圆角，避免样条过冲造成的虚假弯弧 */
function cornerPath(pts, rMax) {
  ctx.beginPath();
  if (pts.length < 2) return;
  ctx.moveTo(pts[0].x, pts[0].y);
  if (pts.length === 2) { ctx.lineTo(pts[1].x, pts[1].y); return; }
  for (let i = 1; i < pts.length - 1; i++) {
    const p0 = pts[i - 1], p1 = pts[i], p2 = pts[i + 1];
    const d1 = Math.hypot(p1.x - p0.x, p1.y - p0.y);
    const d2 = Math.hypot(p2.x - p1.x, p2.y - p1.y);
    if (d1 < 0.01 || d2 < 0.01) { ctx.lineTo(p1.x, p1.y); continue; }
    const r = Math.min(rMax, d1 * 0.42, d2 * 0.42);
    if (r < 0.8) { ctx.lineTo(p1.x, p1.y); continue; }
    const ax = p1.x + (p0.x - p1.x) / d1 * r, ay = p1.y + (p0.y - p1.y) / d1 * r;
    const bx = p1.x + (p2.x - p1.x) / d2 * r, by = p1.y + (p2.y - p1.y) / d2 * r;
    ctx.lineTo(ax, ay);
    ctx.quadraticCurveTo(p1.x, p1.y, bx, by);
  }
  const last = pts[pts.length - 1];
  ctx.lineTo(last.x, last.y);
}

/* ---------- 背景 ---------- */
function drawBackground() {
  const colors = MetroMap.palette();
  const g = ctx.createLinearGradient(0, 0, 0, H);
  g.addColorStop(0, colors.ground[0]);
  g.addColorStop(0.55, colors.ground[1]);
  g.addColorStop(1, colors.ground[2]);
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, W, H);

  // 网格（5km）
  const step = 5;
  ctx.lineWidth = 1;
  ctx.strokeStyle = colors.grid;
  const x0 = Math.floor((App.cam.x - W / 2 / App.cam.s) / step) * step;
  const x1 = App.cam.x + W / 2 / App.cam.s;
  const y0 = Math.floor((App.cam.y - H / 2 / App.cam.s) / step) * step;
  const y1 = App.cam.y + H / 2 / App.cam.s;
  ctx.beginPath();
  for (let x = x0; x <= x1; x += step) {
    const s = w2s(x, 0);
    ctx.moveTo(Math.round(s.x) + .5, 0); ctx.lineTo(Math.round(s.x) + .5, H);
  }
  for (let y = y0; y <= y1; y += step) {
    const s = w2s(0, y);
    ctx.moveTo(0, Math.round(s.y) + .5); ctx.lineTo(W, Math.round(s.y) + .5);
  }
  ctx.stroke();

  // 区域名称（弱化，作为地理参照）
  if (App.cam.s > 6) {
    const regions = GEO.regions || [
      ['河 西', 118.735, 32.020], ['仙 林', 118.905, 32.098], ['江 宁', 118.850, 31.945],
      ['江北新区', 118.700, 32.120], ['紫金山', 118.850, 32.060], ['老 山', 118.600, 32.100],
      ['主 城', 118.788, 32.045], ['江 宁 大 学 城', 118.830, 31.900]
    ];
    for (const [name, lng, lat] of regions) {
      const p = w2s((lng - LNG0) * KX, (LAT0 - lat) * KY);
      if (p.x < 20 || p.x > W - 20 || p.y < 20 || p.y > H - 20) continue;
      ctx.font = '600 13px "Microsoft YaHei","Segoe UI"';
      ctx.textAlign = 'center';
      ctx.fillStyle = colors.region;
      ctx.fillText(name, p.x, p.y);
    }
    ctx.textAlign = 'left';
  }


  // 线路名标签（官方线网示意图风格：深蓝底白字路线牌）
  if (GEO.lineLabels && App.cam.s > 4.5) {
    ctx.font = '700 10.5px "Microsoft YaHei","Segoe UI"';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    for (const [name, lng, lat] of GEO.lineLabels) {
      const p = w2s((lng - LNG0) * KX, (LAT0 - lat) * KY);
      if (p.x < 44 || p.x > W - 44 || p.y < 22 || p.y > H - 22) continue;
      const tw = ctx.measureText(name).width;
      const bw = tw + 13, bh = 17;
      ctx.fillStyle = 'rgba(42,89,167,0.96)';
      ctx.beginPath();
      ctx.rect(p.x - bw / 2, p.y - bh / 2, bw, bh);
      ctx.fill();
      ctx.strokeStyle = 'rgba(180,208,245,0.5)';
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.fillStyle = '#f2f8ff';
      ctx.fillText(name, p.x, p.y + 0.5);
    }
    ctx.textAlign = 'left';
    ctx.textBaseline = 'middle';
  }

  // 山体
  for (const hh of GEO.hills) {
    const c = w2s((hh.x - LNG0) * KX, (LAT0 - hh.y) * KY);
    const rx = hh.rx * KX * App.cam.s, ry = hh.ry * KY * App.cam.s;
    if (c.x + rx < 0 || c.x - rx > W || c.y + ry < 0 || c.y - ry > H) continue;
    const rg = ctx.createRadialGradient(c.x, c.y, 0, c.x, c.y, Math.max(rx, ry));
    rg.addColorStop(0, colors.hill);
    rg.addColorStop(1, colors.hillEnd);
    ctx.fillStyle = rg;
    ctx.save(); ctx.translate(c.x, c.y); ctx.scale(rx / Math.max(rx, ry), ry / Math.max(rx, ry));
    ctx.beginPath(); ctx.arc(0, 0, Math.max(rx, ry), 0, Math.PI * 2); ctx.fill();
    ctx.restore();
  }

  // 湖泊
  for (const lk of GEO.lakes) {
    const c = w2s((lk.x - LNG0) * KX, (LAT0 - lk.y) * KY);
    const rx = lk.rx * KX * App.cam.s, ry = lk.ry * KY * App.cam.s;
    ctx.fillStyle = colors.lake;
    ctx.strokeStyle = colors.lakeEdge;
    ctx.lineWidth = 1;
    ctx.beginPath(); ctx.ellipse(c.x, c.y, rx, ry, 0, 0, Math.PI * 2);
    ctx.fill(); ctx.stroke();
  }

  // 长江
  const pts = GEO.river.map(p => w2s((p[0] - LNG0) * KX, (LAT0 - p[1]) * KY));
  const rw = Math.max(5, GEO.riverW * App.cam.s);
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  ctx.strokeStyle = colors.riverBank; ctx.lineWidth = rw + Math.max(3, rw * 0.3);
  smoothPath(pts); ctx.stroke();
  ctx.strokeStyle = colors.river; ctx.lineWidth = rw;
  smoothPath(pts); ctx.stroke();
  ctx.strokeStyle = colors.riverCenter; ctx.lineWidth = Math.max(2, rw * 0.3);
  smoothPath(pts); ctx.stroke();

  // 大河字样（默认南京长江，可用 GEO.riverLabel 覆写）
  const rl = GEO.riverLabel || { lng: 118.900, lat: 32.176, rot: -0.48, text: '长   江' };
  if (App.cam.s > 8) {
    const p = w2s((rl.lng - LNG0) * KX, (LAT0 - rl.lat) * KY);
    ctx.save();
    ctx.translate(p.x, p.y); ctx.rotate(rl.rot);
    ctx.font = '600 14px "Microsoft YaHei","Segoe UI"';
    ctx.fillStyle = colors.riverName;
    ctx.fillText(rl.text, 0, 0);
    ctx.restore();
  }
}

/* ---------- 线路 ---------- */
function drawLines() {
  const colors = MetroMap.palette();
  const lw = Math.max(3.0, Math.min(8.6, App.cam.s * 0.215));
  for (const line of App.lines) {
    const arms = lineArms(line);
    if (!arms.some(a => a.stations.length >= 2)) continue;
    const off = App.trackOff && App.trackOff[line.id];
    const tk = off ? null : trackOf(line.id);
    const paths = [];
    const useTrack = !!tk && mainMatchesDef(line);
    if (useTrack) {
      const segs = (typeof TRACK_SEG !== 'undefined' && TRACK_SEG[line.id]) ? TRACK_SEG[line.id] : [tk];
      for (const seg of segs) paths.push({ pts: seg.map(p => w2s((p[0] - LNG0) * KX, (LAT0 - p[1]) * KY)), tk: true });
    }
    for (let ai = useTrack ? 1 : 0; ai < arms.length; ai++) {
      const arm = arms[ai];
      if (arm.stations.length < 2) continue;
      const pts = arm.stations.map(id => {
        const st = App.stations.get(id);
        return st ? w2s(st.x, st.y) : null;
      }).filter(Boolean);
      if (pts.length >= 2) paths.push({ pts, planned: arm.planned });
    }
    const rMax = Math.max(2.5, Math.min(13, lw * 3.4));
    const paint = ({ pts, tk, planned }) => {
      if (tk) smoothPath(pts);
      else if (planned) MetroMap.tracePlannedPath(ctx, pts);
      else cornerPath(pts, rMax);
    };
    const sel = line.id === App.selectedLine || line.id === App.editingLine;
    const on = line.enabled;
    // 在建线路画虚线，与运营线（含同为橙色系的 S4/S8）区分开
    const bld = typeof BUILDING_IDS !== 'undefined' && BUILDING_IDS.indexOf(line.id) >= 0;
    const dash = bld ? [lw * 2.4, lw * 1.8] : null;
    // 延伸段（如苏州 2 号线北延）在建：用同色虚线覆盖该段
    const bldSegs = [];
    if (line.bldHead || line.bldTail) {
      const points = line.stations.map(id => App.stations.get(id)).filter(Boolean).map(st => w2s(st.x, st.y));
      if (line.bldHead) bldSegs.push([points, 0, Math.min(line.bldHead, points.length - 1)]);
      if (line.bldTail) bldSegs.push([points, Math.max(0, points.length - line.bldTail - 1), points.length - 1]);
    }
    const paintBuilt = ([points, first, last]) => {
      if (arms[0].planned) MetroMap.tracePlannedPath(ctx, points, first, last);
      else cornerPath(points.slice(first, last + 1), rMax);
    };
    const luma = (hex) => {
      const h = hex.replace('#', '');
      const r = parseInt(h.slice(0, 2), 16) / 255, g = parseInt(h.slice(2, 4), 16) / 255, b = parseInt(h.slice(4, 6), 16) / 255;
      return 0.299 * r + 0.587 * g + 0.114 * b;
    };
    const lightLine = luma(line.color) > 0.62;

    // 外描边（暗色线用浅边、浅色线用深边，保证深底可读）
    ctx.lineCap = 'butt'; ctx.lineJoin = 'round';
    ctx.strokeStyle = lightLine ? colors.lightLineEdge : colors.darkLineEdge;
    ctx.lineWidth = lightLine ? lw + 3.8 : lw + 3.2;
    if (dash) ctx.setLineDash(dash);
    for (const o of paths) { paint(o); ctx.stroke(); }
    ctx.setLineDash([]);

    if (!on) {
      ctx.setLineDash([6, 7]);
      ctx.strokeStyle = 'rgba(120,140,165,0.55)';
      ctx.lineWidth = Math.max(1.8, lw * 0.55);
      for (const o of paths) { paint(o); ctx.stroke(); }
      ctx.setLineDash([]);
      continue;
    }

    ctx.lineCap = 'butt';
    if (dash) ctx.setLineDash(dash);
    if (sel) {
      ctx.save();
      ctx.shadowColor = line.color;
      ctx.shadowBlur = 18;
      ctx.strokeStyle = line.color;
      ctx.lineWidth = lw;
      for (const o of paths) { paint(o); ctx.stroke(); }
      ctx.restore();
    }
    ctx.strokeStyle = line.color;
    ctx.lineWidth = lw;
    for (const o of paths) { paint(o); ctx.stroke(); }

    // 高光
    if (App.cam.s > 9) {
      ctx.strokeStyle = sel ? 'rgba(255,255,255,0.42)' : 'rgba(255,255,255,0.13)';
      ctx.lineWidth = Math.max(1, lw * (sel ? 0.34 : 0.28));
      for (const o of paths) { paint(o); ctx.stroke(); }
    }
    ctx.setLineDash([]);

    // 在建延伸段：先把该段清出地盘，再画同色虚线，断口才能露出底色
    if (bldSegs.length) {
      ctx.lineCap = 'butt';
      ctx.setLineDash([]);
      ctx.strokeStyle = colors.constructionGap;
      ctx.lineWidth = lw + 4.6;
      for (const segment of bldSegs) { paintBuilt(segment); ctx.stroke(); }
      const d2 = [lw * 2.2, lw * 1.7];
      ctx.setLineDash(d2);
      ctx.strokeStyle = lightLine ? colors.lightLineEdge : colors.darkLineEdge;
      ctx.lineWidth = lw + 3.2;
      for (const segment of bldSegs) { paintBuilt(segment); ctx.stroke(); }
      ctx.strokeStyle = line.color;
      ctx.lineWidth = lw;
      for (const segment of bldSegs) { paintBuilt(segment); ctx.stroke(); }
      ctx.setLineDash([]);
    }
    ctx.lineCap = 'round';
  }
}

/* ---------- 底图上的换乘/普通站 ---------- */
function drawStations() {
  const colors = MetroMap.palette();
  const sim = App.sim;
  const s = App.cam.s;
  const termSet = terminalSet();
  const transitR = Math.max(4.0, Math.min(7.8, s * 0.31));
  const tinyR = Math.max(2.1, Math.min(4.7, s * 0.2));

  for (const [id, st] of App.stations) {
    const p = w2s(st.x, st.y);
    if (p.x < -20 || p.x > W + 20 || p.y < -20 || p.y > H + 20) continue;
    const isTrans = st.lines.length > 1;
    const isSelLine = App.selectedLine && st.lines.includes(App.selectedLine);
    const r = isTrans ? transitR : (isSelLine ? tinyR * 1.15 : tinyR);

    // 拥挤光晕
    if (sim) {
      const ss = sim.stationStats.get(id);
      if (ss && ss.queue > 18) {
        const ratio = Math.min(1, ss.queue / K.PLATFORM_CAP);
        const col = ratio > 0.72 ? '255,95,116' : ratio > 0.4 ? '255,181,69' : '58,217,155';
        const rg = ctx.createRadialGradient(p.x, p.y, r, p.x, p.y, r * 4.2);
        rg.addColorStop(0, `rgba(${col},0.55)`);
        rg.addColorStop(1, `rgba(${col},0)`);
        ctx.fillStyle = rg;
        ctx.beginPath(); ctx.arc(p.x, p.y, r * 4.2, 0, Math.PI * 2); ctx.fill();
      }
    }

    ctx.beginPath();
    ctx.arc(p.x, p.y, r, 0, Math.PI * 2);
    if (st.lines.length === 0) {
      // 站网里的孤立车站：空心环，表示尚未被任何线路使用
      ctx.fillStyle = colors.orphan;
      ctx.fill();
      ctx.strokeStyle = colors.orphanEdge;
      ctx.lineWidth = 1.4;
      ctx.stroke();
    } else if (isTrans) {
      const xf = (typeof XFER !== 'undefined') ? XFER[st.name] : undefined;
      const xcol = (xf && typeof XFER_TYPES !== 'undefined' && XFER_TYPES[xf.t]) ? XFER_TYPES[xf.t].color : '#8aa6c4';
      ctx.fillStyle = colors.transferRing;
      ctx.fill();
      ctx.beginPath();
      ctx.arc(p.x, p.y, r * 0.46, 0, Math.PI * 2);
      ctx.fillStyle = colors.transferCenter;
      ctx.fill();
      // 换乘方式标记环：外圈按方式着色（虚拟换乘用虚线）
      ctx.save();
      ctx.strokeStyle = xcol;
      ctx.lineWidth = Math.max(1, Math.min(1.9, r * 0.24));
      if (xf && xf.t === 'virtual') { ctx.setLineDash([r * 0.55, r * 0.5]); }
      ctx.beginPath(); ctx.arc(p.x, p.y, r + 1.3, 0, Math.PI * 2); ctx.stroke();
      if (xf && xf.t === 'same' && xf.b !== 1) {
        // 同台换乘：环外加两枚对向小箭头刻度
        ctx.setLineDash([]);
        ctx.beginPath(); ctx.moveTo(p.x - r - 4.2, p.y); ctx.lineTo(p.x - r - 1.4, p.y - 2.6); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(p.x - r - 4.2, p.y); ctx.lineTo(p.x - r - 1.4, p.y + 2.6); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(p.x + r + 4.2, p.y); ctx.lineTo(p.x + r + 1.4, p.y - 2.6); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(p.x + r + 4.2, p.y); ctx.lineTo(p.x + r + 1.4, p.y + 2.6); ctx.stroke();
      }
      ctx.restore();
      ctx.strokeStyle = colors.transferEdge;
      ctx.lineWidth = 1;
      ctx.beginPath(); ctx.arc(p.x, p.y, r, 0, Math.PI * 2); ctx.stroke();
    } else {
      MetroMap.fillOrdinaryStation(ctx, colors, r);
    }

    if (st.custom) {
      ctx.strokeStyle = colors.editAccent; ctx.lineWidth = 1.4;
      ctx.beginPath(); ctx.arc(p.x, p.y, r + 2.5, 0, Math.PI * 2); ctx.stroke();
    }
    // 线路端点（首站 / 末站）：外加一圈白色细环，与中途站区分
    if (termSet.has(id) && st.lines.length > 0) {
      ctx.strokeStyle = colors.terminalRing;
      ctx.lineWidth = 1.2;
      ctx.beginPath(); ctx.arc(p.x, p.y, r + 2.6, 0, Math.PI * 2); ctx.stroke();
    }
  }

  // hover
  if (App.hover) {
    const st = App.stations.get(App.hover);
    if (st) {
      const p = w2s(st.x, st.y);
      const isTrans = st.lines.length > 1;
      ctx.strokeStyle = '#4da3ff'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(p.x, p.y, (isTrans ? transitR : tinyR) + 5, 0, Math.PI * 2); ctx.stroke();
    }
  }
}

/* ---------- 列车 ---------- */
function drawTrains() {
  const sim = App.sim;
  if (!sim || !sim.running) return;
  const s = App.cam.s;
  const size = Math.max(3, Math.min(9, s * 0.38));
  for (const tr of sim.trains) {
    const line = App.lines.find(l => l.id === tr.line);
    if (!line) continue;
    const arms = lineArms(line);
    const arm = arms[tr.arm] || arms[0];
    if (!arm || arm.stations.length < 2) continue;
    const sts = arm.stations;
    const n = sts.length;
    const i = Math.max(0, Math.min(n - 2, tr.i));
    const aId = sts[i], bId = sts[i + 1];
    const A = App.stations.get(aId), B = App.stations.get(bId);
    if (!A || !B) continue;
    const from = tr.dir === 0 ? A : B, to = tr.dir === 0 ? B : A;
    const prog = Math.max(0, Math.min(1, tr.prog));
    const pose = arm.planned ? MetroMap.trainPose(App.stations, sts, i, prog, tr.dir !== 0) : {
      x: from.x + (to.x - from.x) * prog,
      y: from.y + (to.y - from.y) * prog,
      angle: Math.atan2(to.y - from.y, to.x - from.x),
    };
    const p = w2s(pose.x, pose.y);
    if (p.x < -30 || p.x > W + 30 || p.y < -30 || p.y > H + 30) continue;
    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(pose.angle);
    const loadRate = line.capEff ? tr.load / line.capEff : 0;
    const col = loadRate > 0.95 ? '#ff6b7f' : loadRate > 0.7 ? '#ffc061' : '#ffffff';
    ctx.fillStyle = col;
    ctx.strokeStyle = line.color;
    ctx.lineWidth = 1.2;
    ctx.shadowColor = line.color; ctx.shadowBlur = 8;
    ctx.fillRect(-size * 0.7, -size * 0.34, size * 1.4, size * 0.68);
    ctx.shadowBlur = 0;
    ctx.strokeRect(-size * 0.7, -size * 0.34, size * 1.4, size * 0.68);
    ctx.restore();
  }
}

/* ---------- 站名 ---------- */
const labelBoxes = [];
function placeLabel(x, y, w, h, maxHit) {
  let hit = 0;
  for (const r of labelBoxes) {
    if (!(x > r.x + r.w || x + w < r.x || y > r.y + r.h || y + h < r.y)) {
      if (++hit > (maxHit || 0)) return false;
    }
  }
  labelBoxes.push({ x, y, w, h });
  return true;
}
/* 每条运营线（含支线）的首末站：这些站必须始终标出站名 */
function terminalSet() {
  const T = new Set();
  for (const l of App.lines) {
    for (const arm of lineArms(l)) {
      const st = arm.stations;
      if (!st || st.length === 0) continue;
      T.add(st[0]);
      T.add(st[st.length - 1]);
    }
  }
  return T;
}

function drawLabels() {
  const colors = MetroMap.palette();
  labelBoxes.length = 0;
  const s = App.cam.s;
  if (s < 4.2) return;
  const font = s > 22 ? 11.5 : s > 15 ? 10.5 : 10;
  ctx.font = `500 ${font}px "Segoe UI","Microsoft YaHei"`;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'middle';

  const TERM = terminalSet();
  const priority = [];
  for (const [id, st] of App.stations) {
    const trans = st.lines.length > 1;
    const sel = App.selectedLine && st.lines.includes(App.selectedLine);
    const term = TERM.has(id) && st.lines.length > 0;
    if (!trans && !sel && !term) {
      if (s < 11) continue;
      if (s < 26 && st.w < 0.62) continue;
    }
    priority.push({ st, trans, sel, term });
  }
  priority.sort((a, b) => (b.trans - a.trans) || (b.term - a.term) || (b.sel - a.sel) || (b.st.w - a.st.w));
  if (priority.length > 200) {
    // 端点与换乘站不截断
    const keep = priority.filter(p => p.term || p.trans);
    const rest = priority.filter(p => !p.term && !p.trans).slice(0, Math.max(0, 200 - keep.length));
    priority.length = 0;
    priority.push(...keep, ...rest);
  }

  for (const { st, trans, term } of priority) {
    const p = w2s(st.x, st.y);
    if (p.x < -8 || p.x > W + 8 || p.y < -8 || p.y > H + 8) continue;
    ctx.font = `${term ? 700 : 500} ${term ? font + 0.5 : font}px "Segoe UI","Microsoft YaHei"`;
    const tw = ctx.measureText(st.name).width;
    // 端点靠边时优先朝画面内侧排字
    const edge = [];
    if (p.x > W - 130) edge.push([-9, -10, 'right'], [-9, 12, 'right']);
    else if (p.x < 130) edge.push([9, -10, 'left'], [9, 12, 'left']);
    if (p.y < 60) edge.push([0, 20, 'center'], [9, 16, 'left'], [-9, 16, 'right']);
    else if (p.y > H - 60) edge.push([0, -18, 'center'], [9, -16, 'left'], [-9, -16, 'right']);
    const base = trans
      ? [[9, -10, 'left'], [-9, -10, 'right'], [9, 12, 'left'], [-9, 12, 'right'], [0, -17, 'center']]
      : [[7, -10, 'left'], [-7, -10, 'right'], [7, 12, 'left'], [-7, 12, 'right']];
    const cands = edge.concat(base);
    for (const [dx, dy, al] of cands) {
      ctx.textAlign = al;
      const tx = p.x + dx, ty = p.y + dy;
      const x0 = al === 'left' ? tx : al === 'right' ? tx - tw : tx - tw / 2;
      if (!placeLabel(x0 - 4, ty - font * 0.8, tw + 8, font * 1.62, term ? 1 : 0)) continue;
      ctx.lineWidth = 3;
      ctx.strokeStyle = colors.labelHalo;
      ctx.strokeText(st.name, tx, ty);
      ctx.fillStyle = term ? colors.labelTerminal : trans ? colors.labelTransfer : colors.label;
      ctx.fillText(st.name, tx, ty);
      break;
    }
  }
  ctx.textAlign = 'left';
}

/* ---------- 编辑层 ---------- */
function drawEditOverlay() {
  const colors = MetroMap.palette();
  if (App.mode !== 'edit') return;
  const el = App.editingLine ? getLine(App.editingLine) : null;
  let anchorSid = App.drawAnchor && App.drawAnchor.sid != null ? App.drawAnchor.sid : null;
  if (anchorSid == null && el) {
    const arms = lineArms(el);
    for (let k = arms.length - 1; k >= 0; k--) {
      if (arms[k].stations.length) { anchorSid = arms[k].stations[arms[k].stations.length - 1]; break; }
    }
  }
  const anchorSt = anchorSid != null ? App.stations.get(anchorSid) : null;
  if (anchorSt && App.tool === 'draw') {
    const p = w2s(anchorSt.x, anchorSt.y);
    const r0 = 8 + Math.sin((App.tick || 0) * 0.9) * 2;
    ctx.save();
    ctx.beginPath(); ctx.arc(p.x, p.y, r0, 0, Math.PI * 2);
    ctx.strokeStyle = colors.editAccent; ctx.lineWidth = 2.4; ctx.stroke();
    ctx.beginPath(); ctx.arc(p.x, p.y, r0 + 6, 0, Math.PI * 2);
    ctx.strokeStyle = colors.editHalo; ctx.lineWidth = 1.4; ctx.stroke();
    ctx.restore();
    if (mouse.inside) {
      const mp = { x: mouse.x, y: mouse.y };
      ctx.save();
      ctx.setLineDash([7, 6]);
      ctx.strokeStyle = (el ? el.color : colors.editAccent) + 'cc';
      ctx.lineWidth = 2.2;
      const route = el && lineArms(el).find(arm => arm.stations.includes(anchorSid))?.stations;
      const previous = route?.[0] === anchorSid ? route[1] : route?.at(-1) === anchorSid ? route.at(-2) : null;
      const st = previous && App.stations.get(previous);
      if (st) MetroMap.tracePlannedPath(ctx, [w2s(st.x, st.y), p, mp], 1);
      else MetroMap.tracePlannedPath(ctx, [p, mp]);
      ctx.stroke();
      ctx.restore();
      // 幽灵站点
      ctx.beginPath();
      ctx.arc(mp.x, mp.y, 5, 0, Math.PI * 2);
      ctx.strokeStyle = colors.editAccent; ctx.lineWidth = 1.6; ctx.stroke();
    }
  }
  if (App.tool === 'drag' && App.dragStation) {
    const st = App.stations.get(App.dragStation);
    if (st) {
      const p = w2s(st.x, st.y);
      ctx.beginPath(); ctx.arc(p.x, p.y, 9, 0, Math.PI * 2);
      ctx.strokeStyle = colors.editAccent; ctx.lineWidth = 2; ctx.stroke();
    }
  }
}

/* ---------- 主绘制 ---------- */
function draw() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, W, H);
  App.tick = (App.tick || 0) + 1;
  if (App.mode === 'chart') { drawChart(); return; }
  drawBackground();
  drawLines();
  drawStations();
  drawTrains();
  drawLabels();
  drawEditOverlay();

  // 仿真时段结束的暗角
  if (App.sim && !App.sim.running) {
    const vg = ctx.createRadialGradient(W / 2, H / 2, Math.min(W, H) * 0.42, W / 2, H / 2, Math.max(W, H) * 0.72);
    vg.addColorStop(0, 'rgba(0,0,0,0)');
    vg.addColorStop(1, MetroMap.palette().finishedShade);
    ctx.fillStyle = vg;
    ctx.fillRect(0, 0, W, H);
  }
}

/* ---------- 相机 ---------- */
function fitView(padding = 34) {
  const pts = [];
  for (const [, st] of App.stations) pts.push(st);
  if (!pts.length) return;
  let minX = 1e9, maxX = -1e9, minY = 1e9, maxY = -1e9;
  for (const st of pts) {
    minX = Math.min(minX, st.x); maxX = Math.max(maxX, st.x);
    minY = Math.min(minY, st.y); maxY = Math.max(maxY, st.y);
  }
  const sx = (W - padding * 2) / Math.max(1, maxX - minX);
  const sy = (H - padding * 2) / Math.max(1, maxY - minY);
  App.cam.s = Math.max(2.5, Math.min(sx, sy));
  App.cam.x = (minX + maxX) / 2;
  App.cam.y = (minY + maxY) / 2;
  App.dirty = true;
}

function fitCity() {
  const hasView = (typeof GEO !== 'undefined' && GEO.cityView);
  if (!hasView) { fitView(48); return; }
  const v = GEO.cityView;
  App.cam.x = v.x; App.cam.y = v.y; App.cam.s = v.s;
  App.dirty = true;
  if (App.stations.size === 0) return;
  // 端点（首末站）若被裁到画外：小幅平移视野把首末站捞回画面，不改变缩放
  const terms = [];
  for (const id of terminalSet()) { const st = App.stations.get(id); if (st) terms.push(st); }
  if (!terms.length) return;
  let sx0 = 1e9, sx1 = -1e9, sy0 = 1e9, sy1 = -1e9;
  for (const st of terms) {
    const px = (st.x - App.cam.x) * v.s + W / 2;
    const py = (st.y - App.cam.y) * v.s + H / 2;
    if (px < sx0) sx0 = px; if (px > sx1) sx1 = px;
    if (py < sy0) sy0 = py; if (py > sy1) sy1 = py;
  }
  const padL = 330, padR = 40, padT = 46, padB = 70;
  let dX = 0, dY = 0;
  if (sx0 < padL && sx1 < W - padR) dX = Math.min(padL - sx0, (W - padR) - sx1);
  else if (sx1 > W - padR && sx0 > padL) dX = -Math.min(sx1 - (W - padR), sx0 - padL);
  else if (sx0 < padL) dX = Math.min((W - padR) - sx1 > 0 ? (W - padR - sx1) / 2 : 0, padL - sx0);
  if (sy0 < padT && sy1 < H - padB) dY = Math.min(padT - sy0, (H - padB) - sy1);
  else if (sy1 > H - padB && sy0 > padT) dY = -Math.min(sy1 - (H - padB), sy0 - padT);
  dX = Math.max(-220, Math.min(220, dX));
  dY = Math.max(-180, Math.min(180, dY));
  if (dX || dY) {
    App.cam.x -= dX / v.s;
    App.cam.y -= dY / v.s;
    App.dirty = true;
  }
}

function zoomAt(sx, sy, factor) {
  const before = s2w(sx, sy);
  App.cam.s = Math.max(3, Math.min(App.mode === 'chart' ? 140 : 58, App.cam.s * factor));
  const after = s2w(sx, sy);
  App.cam.x += before.x - after.x;
  App.cam.y += before.y - after.y;
  App.dirty = true;
}

/* ---------- 循环 ---------- */
function loop(now) {
  requestAnimationFrame(loop);
  const dtWall = Math.min(0.1, (now - lastFrame) / 1000);
  lastFrame = now;
  const sim = App.sim;
  if (sim && sim.running && !sim.paused) {
    stepSim(sim, dtWall * sim.speed / 60);
  }
  draw();
  if (now - lastUI > 200) { lastUI = now; syncUI(); }
}
let lastUI = 0;


/* ============================================================
   拓扑挂图：从真实几何自动生成八方向示意图（metro map style）
   - 站点吸附到整数格网，任意相邻站必须落在 0°/45°/90° 方向
   - 格距均匀化，整体形状仍由真实经纬度牵引（保形）
   - 转弯惩罚 → 长直段、少锯齿，接近官方挂图观感
   - 渲染：浅底、粗线、白描边过线桥、站名八向避让
   ============================================================ */
'use strict';

const Chart = {
  ready: false,
  sig: '',
  cell: 1.6,
  pos: new Map(),
  viol: 0,
  edges: 0,
  ms: 0
};

const CHART_FONT = '"Microsoft YaHei","Segoe UI",sans-serif';
const OCT8 = [[1, 0], [1, 1], [0, 1], [-1, 1], [-1, 0], [-1, -1], [0, -1], [1, -1]];

function octDir(dx, dy) {
  if (!dx && !dy) return [0, 0];
  let k = Math.round(Math.atan2(dy, dx) / (Math.PI / 4));
  k = ((k % 8) + 8) % 8;
  return OCT8[k];
}

/* 真实站距 → 目标格数：城区 1 格，郊区按对数压缩，最多 4 格 */
function chartHopTarget(km) {
  const v = Math.round(Math.log2(Math.max(0.6, km) / 2.2));
  return 1 + Math.min(3, Math.max(0, v));
}

/* ---------------- 1. 图结构 ---------------- */
function chartGraph() {
  const nodes = [];
  const idx = new Map();
  for (const st of App.stations.values()) {
    idx.set(st.id, nodes.length);
    nodes.push({ id: st.id, st, links: [], turns: [], deg: 0 });
  }
  const edges = [];
  const seen = new Map();
  const pushTurn = (i, p, n) => {
    if (i == null || p == null || n == null) return;
    nodes[i].turns.push({ p, n });
  };
  const linkTo = (a, b, t) => {
    let lk = nodes[a].links.find(x => x.m === b);
    if (lk) { lk.t = Math.min(lk.t, t); return; }
    nodes[a].links.push({ m: b, t });
  };
  for (const line of App.lines) {
    for (const arm of lineArms(line)) {
      const seq = arm.stations;
      const ii = seq.map(id => (idx.has(id) ? idx.get(id) : null));
      for (let k = 0; k < seq.length - 1; k++) {
        const a = ii[k], b = ii[k + 1];
        if (a == null || b == null || a === b) continue;
        const A = nodes[a].st, B = nodes[b].st;
        const t = chartHopTarget(Math.hypot(B.x - A.x, B.y - A.y));
        const key = a < b ? a + '_' + b : b + '_' + a;
        edges.push({ a, b, key, line: line.id, t });
        if (!seen.has(key)) {
          seen.set(key, { t });
          linkTo(a, b, t); linkTo(b, a, t);
          nodes[a].deg++; nodes[b].deg++;
        } else {
          const old = seen.get(key);
          if (t < old.t) { old.t = t; linkTo(a, b, t); linkTo(b, a, t); }
        }
      }
      for (let k = 1; k < ii.length - 1; k++) pushTurn(ii[k], ii[k - 1], ii[k + 1]);
    }
  }
  return { nodes, edges };
}

function chartCellOf(nodes, edges) {
  const ds = [];
  for (const e of edges) {
    const A = nodes[e.a], B = nodes[e.b];
    const d = Math.hypot(B.sx - A.sx, B.sy - A.sy);
    if (d > 0.08) ds.push(d);
  }
  if (!ds.length) return 1.6;
  ds.sort((a, b) => a - b);
  const med = ds[Math.floor(ds.length * 0.42)];
  return Math.max(0.6, Math.min(2.6, med));
}

/* ---------------- 2. 八方向格网求解（ICM + 逐步收紧） ---------------- */
const OCT_LEGAL = (dx, dy) => {
  const ax = Math.abs(dx), ay = Math.abs(dy);
  if (!ax && !ay) return false;
  return ax === 0 || ay === 0 || ax === ay;
};

function chartSolve(nodes, seed) {
  const N = nodes.length;
  const link = nodes.map(n => n.links);
  const turns = nodes.map(n => n.turns);
  const QX = new Float64Array(N), QY = new Float64Array(N);
  nodes.forEach((n, i) => { QX[i] = n.qx; QY[i] = n.qy; });

  let ix = new Int32Array(N), iy = new Int32Array(N);
  for (let i = 0; i < N; i++) { ix[i] = Math.round(QX[i]); iy[i] = Math.round(QY[i]); }

  const keyOf = (i, j) => i * 7919 + j;
  let occ = new Map();
  {
    // 初始占位：以真实坐标为锚，在附近螺旋找最近的空格，避免挤成一排
    const used = new Map();
    for (let i = 0; i < N; i++) {
      const gi = Math.round(QX[i]), gj = Math.round(QY[i]);
      let done = false;
      for (let rad = 0; rad <= 8 && !done; rad++) {
        for (let dx = -rad; dx <= rad && !done; dx++) {
          for (let dy = -rad; dy <= rad && !done; dy++) {
            if (Math.max(Math.abs(dx), Math.abs(dy)) !== rad) continue;
            const kk = keyOf(gi + dx, gj + dy);
            if (!used.has(kk)) {
              used.set(kk, i); ix[i] = gi + dx; iy[i] = gj + dy; done = true;
            }
          }
        }
      }
    }
    for (let i = 0; i < N; i++) occ.set(keyOf(ix[i], iy[i]), i);
  }

  function nodeCost(i, ci, cj, P) {
    let c = P.wf * ((ci - QX[i]) * (ci - QX[i]) + (cj - QY[i]) * (cj - QY[i]));
    const o = occ.get(keyOf(ci, cj));
    if (o !== undefined && o !== i) c += P.col;

    const L = link[i];
    for (let t = 0; t < L.length; t++) {
      const m = L[t].m, tg = L[t].t;
      const dx = ix[m] - ci, dy = iy[m] - cj;
      if (!OCT_LEGAL(dx, dy)) c += P.ill;
      else {
        const len = Math.max(Math.abs(dx), Math.abs(dy));
        const d = len - tg;
        c += P.wl * d * d;
      }
    }

    if (P.turn) {
      const T = turns[i];
      for (let t = 0; t < T.length; t++) {
        const a = T[t].p, b = T[t].n;
        const d1 = octDir(ci - ix[a], cj - iy[a]);
        const d2 = octDir(ix[b] - ci, iy[b] - cj);
        const cos = d1[0] * d2[0] + d1[1] * d2[1];
        if (cos < 1) c += P.turn * (1 - cos) + (cos < -0.55 ? P.turn * 1.6 : 0);
      }
    }
    return c;
  }

  function measure(P) {
    let cost = 0, viol = 0, col = 0, bend = 0;
    for (let i = 0; i < N; i++) {
      cost += P.wf * ((ix[i] - QX[i]) * (ix[i] - QX[i]) + (iy[i] - QY[i]) * (iy[i] - QY[i]));
      const L = link[i];
      for (let t = 0; t < L.length; t++) {
        const m = L[t].m;
        if (m <= i) continue;
        const dx = ix[m] - ix[i], dy = iy[m] - iy[i];
        if (!OCT_LEGAL(dx, dy)) { cost += P.ill; viol++; }
        else {
          const d = Math.max(Math.abs(dx), Math.abs(dy)) - L[t].t;
          cost += P.wl * d * d;
        }
      }
      if (P.turn) {
        const T = turns[i];
        for (let t = 0; t < T.length; t++) {
          const d1 = octDir(ix[i] - ix[T[t].p], iy[i] - iy[T[t].p]);
          const d2 = octDir(ix[T[t].n] - ix[i], iy[T[t].n] - iy[i]);
          const cos = d1[0] * d2[0] + d1[1] * d2[1];
          if (cos < 1) { cost += P.turn * (1 - cos); bend++; }
        }
      }
    }
    const cells = new Set();
    for (let i = 0; i < N; i++) {
      const kk = keyOf(ix[i], iy[i]);
      if (cells.has(kk)) col++; else cells.add(kk);
    }
    return { cost: cost + col * P.col, viol, col, bend };
  }

  const order = [];
  for (let i = 0; i < N; i++) order.push(i);
  let s0 = seed || 1;
  const rnd = () => { s0 = (s0 * 1103515245 + 12345) & 0x7fffffff; return s0 / 0x7fffffff; };
  const shuffle = () => {
    for (let i = N - 1; i > 0; i--) {
      const j = (rnd() * (i + 1)) | 0;
      const t = order[i]; order[i] = order[j]; order[j] = t;
    }
  };

  function sweep(P, radius) {
    for (let oi = 0; oi < N; oi++) {
      const i = order[oi];
      let bc = nodeCost(i, ix[i], iy[i], P);
      let bi = ix[i], bj = iy[i];
      for (let dx = -radius; dx <= radius; dx++) {
        for (let dy = -radius; dy <= radius; dy++) {
          if (!dx && !dy) continue;
          const c2 = nodeCost(i, ix[i] + dx, iy[i] + dy, P);
          if (c2 < bc - 1e-9) { bc = c2; bi = ix[i] + dx; bj = iy[i] + dy; }
        }
      }
      if (bi !== ix[i] || bj !== iy[i]) {
        const ok = keyOf(ix[i], iy[i]);
        if (occ.get(ok) === i) occ.delete(ok);
        ix[i] = bi; iy[i] = bj;
        occ.set(keyOf(bi, bj), i);
      }
    }
  }

  /* 阶段：先松后紧，越往后越看重“像地铁图” */
  const phases = [
    { P: { wf: 0.10, ill: 8, col: 2, turn: 0, wl: 0.9 }, r: 3, n: 22 },
    { P: { wf: 0.14, ill: 11, col: 10, turn: 1.0, wl: 1.1 }, r: 3, n: 20 },
    { P: { wf: 0.20, ill: 15, col: 26, turn: 1.8, wl: 1.3 }, r: 2, n: 18 },
    { P: { wf: 0.26, ill: 20, col: 40, turn: 2.3, wl: 1.4 }, r: 2, n: 14 },
    { P: { wf: 0.32, ill: 26, col: 52, turn: 2.7, wl: 1.5 }, r: 1, n: 10 }
  ];

  let best = null;
  for (const ph of phases) {
    shuffle();
    for (let t = 0; t < ph.n; t++) sweep(ph.P, ph.r);
    const m = measure(ph.P);
    const score = m.viol * 10 + m.col * 10 + m.cost;
    if (!best || score < best.score) {
      best = { viol: m.viol, col: m.col, bend: m.bend, cost: m.cost, score,
        ix: Array.from(ix), iy: Array.from(iy) };
    }
  }
  return best;
}

/* ---------------- 3. 生成布局 ---------------- */
function chartSignature() {
  let sig = App.lines.length + '|' + App.stations.size;
  for (const l of App.lines) sig += '#' + l.id + (l.enabled ? '1' : '0') + ':' + lineArms(l).map(a => a.stations.join(',')).join('|');
  for (const st of App.stations.values()) sig += '@' + Math.round(st.x * 40) + ',' + Math.round(st.y * 40);
  return sig;
}

function computeChart(force) {
  const sig = chartSignature();
  if (!force && Chart.ready && Chart.sig === sig) return false;
  const t0 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();

  const G = chartGraph();
  const N = G.nodes.length;
  Chart.pos = new Map();
  Chart.edges = G.edges.length;
  Chart.viol = 0;
  if (N < 2) { Chart.ready = false; return false; }

  /* 径向压缩：把远处郊区按幂函数拉近，主城相对放大（官方挂图的做法）。
     先把真实 km 压成“示意 km”，再标定格距。 */
  let cx = 0, cy = 0;
  for (const n of G.nodes) { cx += n.st.x; cy += n.st.y; }
  cx /= N; cy /= N;
  let R = 0;
  for (const n of G.nodes) R = Math.max(R, Math.hypot(n.st.x - cx, n.st.y - cy));
  const POW = 0.62;
  for (const n of G.nodes) {
    const dx = n.st.x - cx, dy = n.st.y - cy;
    const r = Math.hypot(dx, dy);
    const f = r > 0.05 ? (R * Math.pow(r / R, POW)) / r : 1;
    n.sx = dx * f; n.sy = dy * f;
  }

  Chart.cell = chartCellOf(G.nodes, G.edges);
  let mx = 0, my = 0;
  for (const n of G.nodes) { mx += n.sx / Chart.cell; my += n.sy / Chart.cell; }
  mx /= N; my /= N;
  for (const n of G.nodes) {
    n.qx = n.sx / Chart.cell - mx;
    n.qy = n.sy / Chart.cell - my;
  }

  let best = null;
  for (let rep = 0; rep < 2; rep++) {
    const r = chartSolve(G.nodes, 20261121 + rep * 7717);
    if (!best || r.score < best.score) best = r;
    if (best.viol === 0 && best.col === 0) break;
  }

  for (let i = 0; i < N; i++) {
    Chart.pos.set(G.nodes[i].id, {
      x: best.ix[i] * Chart.cell,
      y: best.iy[i] * Chart.cell,
      i: best.ix[i], j: best.iy[i]
    });
  }
  Chart.viol = best.viol;
  Chart.bends = best.bend;
  Chart.ready = true;
  Chart.sig = sig;
  Chart.ms = Math.round(((typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now()) - t0);
  return true;
}

/* ---------------- 4. 版面与相机 ---------------- */
function chartBandSpec(vw) {
  const nLine = App.lines.filter(l => lineArms(l).some(a => a.stations.length > 1)).length || 1;
  const cols = Math.max(3, Math.min(8, Math.floor((vw - 208) / 98)));
  const rows = Math.max(1, Math.ceil(nLine / cols));
  return { headerH: 92, legendBand: 26 + rows * 21, cols, rows };
}

function fitChart() {
  let minX = 1e9, maxX = -1e9, minY = 1e9, maxY = -1e9;
  for (const p of Chart.pos.values()) {
    minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x);
    minY = Math.min(minY, p.y); maxY = Math.max(maxY, p.y);
  }
  if (!isFinite(minX)) return;
  const spec = chartBandSpec(W);
  const side = 44;
  const bw = Math.max(1, maxX - minX), bh = Math.max(1, maxY - minY);
  const cw = Math.max(140, W - side * 2 - 24);
  const chh = Math.max(140, H - spec.headerH - spec.legendBand - 46);
  const s = Math.max(4, Math.min(160, Math.min(cw / bw, chh / bh)));
  App.cam.s = s;
  const boxCx = W / 2, boxCy = spec.headerH + 12 + chh / 2;
  App.cam.x = (minX + maxX) / 2 + (W / 2 - boxCx) / s;
  App.cam.y = (minY + maxY) / 2 + (H / 2 - boxCy) / s;
  App.dirty = true;
}

/* ---------------- 5. 绘制 ---------------- */
function roundRectPath(g, x, y, w, h, r) {
  const rr = Math.min(r, w / 2, h / 2);
  g.beginPath();
  g.moveTo(x + rr, y);
  g.lineTo(x + w - rr, y); g.quadraticCurveTo(x + w, y, x + w, y + rr);
  g.lineTo(x + w, y + h - rr); g.quadraticCurveTo(x + w, y + h, x + w - rr, y + h);
  g.lineTo(x + rr, y + h); g.quadraticCurveTo(x, y + h, x, y + h - rr);
  g.lineTo(x, y + rr); g.quadraticCurveTo(x, y, x + rr, y);
  g.closePath();
}

function drawChartTo(g, vw, vh, cam, k, uiInset) {
  const colors = MetroMap.palette();
  const s = cam.s;
  const px = (wx, wy) => ({ x: (wx - cam.x) * s + vw / 2, y: (wy - cam.y) * s + vh / 2 });
  const boxes = [];
  const claim = (x, y, w, h) => { boxes.push({ x, y, w, h }); return true; };
  const free = (x, y, w, h) => {
    for (const b of boxes) {
      if (!(x > b.x + b.w || x + w < b.x || y > b.y + b.h || y + h < b.y)) return false;
    }
    return true;
  };
  const labelBox = (x, y, w, h) => (free(x, y, w, h) ? claim(x, y, w, h) : false);
  const inset = uiInset == null ? 0 : uiInset;

  /* --- 版面：一张“挂图”海报贴在深色底板上 --- */
  let cX0 = 1e9, cY0 = 1e9, cX1 = -1e9, cY1 = -1e9;
  for (const p of Chart.pos.values()) {
    const q = px(p.x, p.y);
    if (q.x < cX0) cX0 = q.x;
    if (q.x > cX1) cX1 = q.x;
    if (q.y < cY0) cY0 = q.y;
    if (q.y > cY1) cY1 = q.y;
  }
  if (!isFinite(cX0)) { cX0 = vw * 0.45; cX1 = vw * 0.55; cY0 = vh * 0.45; cY1 = vh * 0.55; }

  const sidePad = 44 * k;
  const headerH = 92 * k;
  const nLine = App.lines.filter(l => lineArms(l).some(a => a.stations.length > 1)).length || 1;
  const sheetW = Math.max(cX1 - cX0 + sidePad * 2, 840 * k);
  const legendCols = Math.max(3, Math.min(8, Math.floor((sheetW - sidePad * 2 - 120 * k) / (98 * k))));
  const legendRows = Math.max(1, Math.ceil(nLine / legendCols));
  const legendBand = (26 + legendRows * 21) * k;
  const sheetH = (cY1 - cY0) + headerH + legendBand + 24 * k;
  const sx0 = (cX0 + cX1) / 2 - sheetW / 2;
  const sy0 = cY0 - headerH - 12 * k;
  const sx1 = sx0 + sheetW;
  const sy1 = sy0 + sheetH;
  const area = { x0: sx0 + sidePad, y0: sy0 + headerH, x1: sx1 - sidePad, y1: sy1 - legendBand };
  const ch = { top: area.y0, legendH: legendBand + 22 * k, cols: legendCols, rows: legendRows };
  Chart.sheetRect = { x: sx0, y: sy0, w: sheetW, h: sheetH };

  /* 深色底板 */
  const bg = g.createLinearGradient(0, 0, vw, vh);
  bg.addColorStop(0, colors.chartGround[0]);
  bg.addColorStop(0.55, colors.chartGround[1]);
  bg.addColorStop(1, colors.chartGround[2]);
  g.fillStyle = bg;
  g.fillRect(0, 0, vw, vh);

  /* 纸张 + 投影 */
  g.save();
  g.shadowColor = 'rgba(0,0,0,0.5)';
  g.shadowBlur = 24 * k;
  g.shadowOffsetY = 7 * k;
  g.fillStyle = '#fdfdfa';
  roundRectPath(g, sx0, sy0, sheetW, sheetH, 3 * k);
  g.fill();
  g.restore();

  /* 纸面（之后所有图元都裁在纸内） */
  g.save();
  roundRectPath(g, sx0, sy0, sheetW, sheetH, 3 * k);
  g.clip();
  const pg = g.createLinearGradient(0, sy0, 0, sy1);
  pg.addColorStop(0, '#ffffff');
  pg.addColorStop(0.6, '#fcfcf7');
  pg.addColorStop(1, '#f5f6f0');
  g.fillStyle = pg;
  g.fillRect(sx0, sy0, sheetW, sheetH);

  /* --- 格网点阵 --- */
  const cellPx = Chart.cell * s;
  if (cellPx > 9 * k && cellPx < 90 * k) {
    g.fillStyle = 'rgba(52,86,120,0.055)';
    const o = px(0, 0);
    const i0 = Math.floor((sx0 - o.x) / cellPx) - 1, i1 = Math.ceil((sx1 - o.x) / cellPx) + 1;
    const j0 = Math.floor((sy0 - o.y) / cellPx) - 1, j1 = Math.ceil((sy1 - o.y) / cellPx) + 1;
    for (let i = i0; i <= i1; i++) {
      for (let j = j0; j <= j1; j++) {
        g.fillRect(o.x + i * cellPx, o.y + j * cellPx, 1.4 * k, 1.4 * k);
      }
    }
  }

  const lw = Math.max(2.4, Math.min(14, cellPx * 0.46));
  const visible = p => p.x > -70 && p.x < vw + 70 && p.y > -70 && p.y < vh + 70;

  /* --- 线路 --- */
  const drawOrder = [...App.lines].filter(l => lineArms(l).some(a => a.stations.length > 1))
    .sort((a, b) => b.stations.length - a.stations.length);

  const strokePath = (pts) => {
    g.beginPath();
    g.moveTo(pts[0].x, pts[0].y);
    for (let i = 1; i < pts.length; i++) g.lineTo(pts[i].x, pts[i].y);
    g.stroke();
  };

  /* 线网占位格：站名只落在空白处，不压线 */
  const inkStep = 5 * k;
  const inkSet = new Set();
  const inkKey = (i, j) => i * 100003 + j;
  const markInk = (pts, halfW) => {
    for (let i = 0; i < pts.length - 1; i++) {
      const a = pts[i], b = pts[i + 1];
      const d = Math.hypot(b.x - a.x, b.y - a.y);
      const steps = Math.max(1, Math.ceil(d / (inkStep * 0.5)));
      for (let t = 0; t <= steps; t++) {
        const x = a.x + (b.x - a.x) * (t / steps);
        const y = a.y + (b.y - a.y) * (t / steps);
        const ci = Math.floor(x / inkStep), cj = Math.floor(y / inkStep);
        inkSet.add(inkKey(ci, cj));
        if (halfW > inkStep * 0.9) {
          inkSet.add(inkKey(ci + 1, cj));
          inkSet.add(inkKey(ci, cj + 1));
        }
      }
    }
  };

  const inkFree = (x, y, w, h) => {
    const i0 = Math.floor(x / inkStep), i1 = Math.floor((x + w) / inkStep);
    const j0 = Math.floor(y / inkStep), j1 = Math.floor((y + h) / inkStep);
    for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++) {
      if (inkSet.has(inkKey(i, j))) return false;
    }
    return true;
  };

  for (const line of drawOrder) {
    for (const arm of lineArms(line)) {
      const pts = [];
      for (const id of arm.stations) {
        const p = Chart.pos.get(id);
        if (p) pts.push(px(p.x, p.y));
      }
      if (pts.length < 2) continue;
      if (!pts.some(visible)) continue;
      markInk(pts, lw / 2);
      g.lineCap = 'round';
      g.lineJoin = 'round';

      if (!line.enabled) {
        g.setLineDash([7 * k, 7 * k]);
        g.strokeStyle = 'rgba(95,110,128,0.5)';
        g.lineWidth = Math.max(1.6, lw * 0.45);
        strokePath(pts);
        g.setLineDash([]);
        continue;
      }

      // 白色描边（交叉处形成过线桥）
      if (lw > 3) {
        g.strokeStyle = 'rgba(255,255,255,0.95)';
        g.lineWidth = lw + 1.9 * k;
        strokePath(pts);
      }
      g.strokeStyle = line.color;
      g.lineWidth = lw;
      strokePath(pts);
    }
  }

  /* --- 车站符号 --- */
  const rNorm = Math.max(1.6, lw * 0.34);
  for (const st of App.stations.values()) {
    const cp = Chart.pos.get(st.id);
    if (!cp) continue;
    const p = px(cp.x, cp.y);
    if (!visible(p)) continue;
    const trans = st.lines.length > 1;
    const r = trans ? rNorm * 1.9 : rNorm;
    g.beginPath();
    g.arc(p.x, p.y, r, 0, Math.PI * 2);
    g.fillStyle = '#ffffff';
    g.fill();
    g.strokeStyle = '#182231';
    g.lineWidth = (trans ? 1.85 : 1.0) * k;
    g.stroke();
    if (st.custom) {
      g.beginPath();
      g.arc(p.x, p.y, r + 3 * k, 0, Math.PI * 2);
      g.strokeStyle = 'rgba(15,138,138,0.7)';
      g.lineWidth = 1.1 * k;
      g.stroke();
    }
  }

  /* --- 端头线号牌 --- */
  if (cellPx > 12) {
    const badge = (line, stId, otherId) => {
      const a = Chart.pos.get(stId), b = Chart.pos.get(otherId);
      if (!a || !b) return;
      const pa = px(a.x, a.y), pb = px(b.x, b.y);
      const dx = pa.x - pb.x, dy = pa.y - pb.y;
      const d = Math.hypot(dx, dy) || 1;
      const bw = 19 * k, bh = 15 * k;
      const cx = pa.x + dx / d * (rNorm + 15 * k), cy = pa.y + dy / d * (rNorm + 15 * k);
      const x = cx - bw / 2, y = cy - bh / 2;
      if (!labelBox(x - 2 * k, y - 2 * k, bw + 4 * k, bh + 4 * k)) return;
      const rr = 4 * k;
      g.beginPath();
      g.moveTo(x + rr, y);
      g.lineTo(x + bw - rr, y); g.quadraticCurveTo(x + bw, y, x + bw, y + rr);
      g.lineTo(x + bw, y + bh - rr); g.quadraticCurveTo(x + bw, y + bh, x + bw - rr, y + bh);
      g.lineTo(x + rr, y + bh); g.quadraticCurveTo(x, y + bh, x, y + bh - rr);
      g.lineTo(x, y + rr); g.quadraticCurveTo(x, y, x + rr, y);
      g.closePath();
      g.fillStyle = line.color;
      g.fill();
      g.strokeStyle = 'rgba(255,255,255,0.5)';
      g.lineWidth = 0.8 * k;
      g.stroke();
      g.fillStyle = '#ffffff';
      g.font = `700 ${Math.round(10 * k)}px ${CHART_FONT}`;
      g.textAlign = 'center';
      g.textBaseline = 'middle';
      g.fillText(line.short, x + bw / 2, y + bh / 2 + 0.5 * k);
    };
    for (const line of drawOrder) {
      for (const arm of lineArms(line)) {
        const s = arm.stations;
        if (s.length < 2) continue;
        badge(line, s[0], s[1]);
        badge(line, s[s.length - 1], s[s.length - 2]);
      }
    }
  }

  /* --- 站名 --- */
  const fs = cellPx > 34 ? 13.5 : cellPx > 17 ? 12 : cellPx > 11 ? 10.5 : 9;
  const items = [];
  const terminals = new Set();
  for (const line of App.lines) {
    for (const arm of lineArms(line)) {
      if (arm.stations.length < 2) continue;
      terminals.add(arm.stations[0]);
      terminals.add(arm.stations[arm.stations.length - 1]);
    }
  }
  const showAll = cellPx > 13;
  for (const st of App.stations.values()) {
    const cp = Chart.pos.get(st.id);
    if (!cp) continue;
    const trans = st.lines.length > 1;
    if (!trans && !terminals.has(st.id) && !showAll) continue;
    items.push({ st, cp, trans, term: terminals.has(st.id) });
  }
  items.sort((a, b) => (b.trans - a.trans) || (b.term - a.term) || (b.st.w - a.st.w));

  const cands = [
    [1, 0, 'left', 'middle'], [-1, 0, 'right', 'middle'],
    [0, -1, 'center', 'bottom'], [0, 1, 'center', 'top'],
    [1, -1, 'left', 'bottom'], [1, 1, 'left', 'top'],
    [-1, -1, 'right', 'bottom'], [-1, 1, 'right', 'top']
  ];
  const halo = cellPx > 14;

  for (const it of items) {
    const p = px(it.cp.x, it.cp.y);
    if (!visible(p)) continue;
    g.font = it.trans ? `700 ${Math.round((fs + 0.9) * k)}px ${CHART_FONT}`
      : `500 ${Math.round(fs * k)}px ${CHART_FONT}`;
    const tw = g.measureText(it.st.name).width;
    const th = (fs + 1) * k;
    const rr = (it.trans ? rNorm * 1.9 : rNorm) + 4 * k;
    // 顺着线路走向的方向容易压到线，放到最后再考虑
    const along = new Set();
    for (const lid of it.st.lines) {
      const ln = getLine(lid);
      if (!ln) continue;
      for (const arm of lineArms(ln)) {
        const at = arm.stations.indexOf(it.st.id);
        if (at < 0) continue;
        for (const nb of [at - 1, at + 1]) {
          if (nb < 0 || nb >= arm.stations.length) continue;
          const q = Chart.pos.get(arm.stations[nb]);
          if (!q) continue;
          along.add(Math.sign(q.i - it.cp.i) + ',' + Math.sign(q.j - it.cp.j));
        }
      }
    }
    const ordered = cands.filter(c => !along.has(c[0] + ',' + c[1]))
      .concat(cands.filter(c => along.has(c[0] + ',' + c[1])));

    // 先在空白处找位置；重点站（换乘/终点）找不到时允许压线（带白色描边）
    const passes = it.trans || it.term ? [false, true] : [false];
    let done = false;
    for (const allowInk of passes) {
      if (done) break;
      for (const [dx, dy, align, base] of ordered) {
        const x = align === 'left' ? p.x + rr : align === 'right' ? p.x - rr - tw : p.x - tw / 2;
        const y = base === 'top' ? p.y + rr : base === 'bottom' ? p.y - rr - th : p.y - th / 2;
        if (y < area.y0 + 4 * k || y + th > area.y1 - 4 * k) continue;
        if (x < area.x0 - 2 * k || x + tw > area.x1 + 2 * k) continue;
        if (!allowInk && !inkFree(x - 1.2 * k, y - 0.8 * k, tw + 2.4 * k, th + 1.6 * k)) continue;
        if (!labelBox(x - 1.5 * k, y - 1 * k, tw + 3 * k, th + 2 * k)) continue;
        g.textAlign = align === 'left' ? 'left' : align === 'right' ? 'right' : 'center';
        g.textBaseline = base === 'top' ? 'top' : base === 'bottom' ? 'bottom' : 'middle';
        const tx = align === 'left' ? x : align === 'right' ? x + tw : x + tw / 2;
        const ty = base === 'top' ? y : base === 'bottom' ? y + th : y + th / 2;
        if (halo || allowInk) {
          g.lineWidth = (allowInk ? 3.4 : 2.4) * k;
          g.strokeStyle = 'rgba(255,255,255,0.96)';
          g.strokeText(it.st.name, tx, ty);
        }
        g.fillStyle = it.trans ? '#0d1626' : it.term ? '#1c2734' : '#404d5f';
        g.fillText(it.st.name, tx, ty);
        done = true;
        break;
      }
    }
  }

  /* --- 页眉（纸面上方） --- */
  g.restore();                 // 结束纸内裁剪
  g.strokeStyle = 'rgba(28,46,66,0.18)';
  g.lineWidth = 1 * k;
  g.beginPath();
  g.moveTo(sx0 + 14 * k, area.y0 - 10 * k);
  g.lineTo(sx1 - 14 * k, area.y0 - 10 * k);
  g.stroke();

  g.textAlign = 'left';
  g.textBaseline = 'alphabetic';
  g.fillStyle = '#0d1624';
  g.font = `700 ${Math.round(24 * k)}px ${CHART_FONT}`;
  g.fillText((document.title.split('·')[0] || '线网').trim() + '线网图', sx0 + 34 * k, sy0 + 44 * k);
  g.fillStyle = '#7d8999';
  g.font = `600 ${Math.round(9 * k)}px ${CHART_FONT}`;
  g.fillText((GEO.meta || 'N A N J I N G   M E T R O   N E T W O R K   M A P').replace(/_/g, ' '), sx0 + 35 * k, sy0 + 64 * k);

  let nSt = 0;
  for (const st of App.stations.values()) if (st.lines.length) nSt++;
  const alignPct = Chart.edges ? ((Chart.edges - Chart.viol) / Chart.edges * 100).toFixed(1) : '—';
  const rx = sx1 - (34 + inset) * k;
  g.textAlign = 'right';
  g.fillStyle = '#55637a';
  g.font = `600 ${Math.round(10.5 * k)}px ${CHART_FONT}`;
  g.fillText(`2026.11 · ${drawOrder.length} 条线 · ${nSt} 座车站`, rx, sy0 + 38 * k);
  g.fillStyle = '#95a0b2';
  g.font = `500 ${Math.round(9 * k)}px ${CHART_FONT}`;
  g.fillText(`按真实几何自动压缩 · 八方向格网 · 对齐 ${alignPct}%`, rx, sy0 + 56 * k);

  /* --- 页脚图例 --- */
  const ly = sy1 - legendBand;
  g.strokeStyle = 'rgba(28,46,66,0.18)';
  g.lineWidth = 1 * k;
  g.beginPath(); g.moveTo(sx0 + 14 * k, ly); g.lineTo(sx1 - 14 * k, ly); g.stroke();

  g.textAlign = 'left';
  g.textBaseline = 'middle';
  g.font = `600 ${Math.round(9.5 * k)}px ${CHART_FONT}`;
  g.fillStyle = '#8a95a5';
  g.fillText('图例 / LEGEND', sx0 + 34 * k, ly + 13 * k);

  const startX = sx0 + 34 * k, startY = ly + 30 * k;
  const colW = (sheetW - 68 * k - 120 * k) / ch.cols;
  let ci = 0;
  for (const line of App.lines) {
    if (!lineArms(line).some(a => a.stations.length > 1)) continue;
    const col = ci % ch.cols, row = Math.floor(ci / ch.cols);
    const x = startX + col * colW, y = startY + row * 21 * k;
    g.fillStyle = line.color;
    g.fillRect(x, y - 5 * k, 11 * k, 10 * k);
    g.strokeStyle = 'rgba(20,30,46,0.25)';
    g.lineWidth = 0.8 * k;
    g.strokeRect(x, y - 5 * k, 11 * k, 10 * k);
    g.fillStyle = line.enabled ? '#26313f' : '#98a2b1';
    g.font = `500 ${Math.round(10 * k)}px ${CHART_FONT}`;
    g.fillText(line.name, x + 16 * k, y);
    ci++;
  }

  g.textAlign = 'right';
  g.textBaseline = 'middle';
  g.fillStyle = '#9aa5b5';
  g.font = `500 ${Math.round(9 * k)}px ${CHART_FONT}`;
  g.fillText('滚轮缩放 · 拖拽平移 · 灰色虚线为停运线路', sx1 - 32 * k, ly + 13 * k);

  /* --- 纸边与四角刻度 --- */
  g.strokeStyle = 'rgba(28,46,66,0.22)';
  g.lineWidth = 1 * k;
  roundRectPath(g, sx0, sy0, sheetW, sheetH, 3 * k);
  g.stroke();
  g.fillStyle = 'rgba(28,46,66,0.28)';
  const t1 = 1.3 * k, t2 = 16 * k;
  const bx = sx0 + 9 * k, by = sy0 + 9 * k, ex = sx1 - 9 * k, ey = sy1 - 9 * k;
  g.fillRect(bx, by, t2, t1); g.fillRect(bx, by, t1, t2);
  g.fillRect(ex - t2, by, t2, t1); g.fillRect(ex - t1, by, t1, t2);
  g.fillRect(bx, ey - t1, t2, t1); g.fillRect(bx, ey - t2, t1, t2);
  g.fillRect(ex - t2, ey - t1, t2, t1);
  g.fillRect(ex - t1, ey - t2, t1, t2);
}

function drawChart() {
  drawChartTo(ctx, W, H, App.cam, 1, 268);
}

/* ---------------- 6. 交互与导出 ---------------- */
function chartExport() {
  const k = 2;
  const vw = Math.round(W * k), vh = Math.round(H * k);
  const c2 = document.createElement('canvas');
  c2.width = vw; c2.height = vh;
  const g2 = c2.getContext('2d');
  drawChartTo(g2, vw, vh, { x: App.cam.x, y: App.cam.y, s: App.cam.s * k }, k, 0);
  // 只导出那张“图”，不要深色底板
  const r = Chart.sheetRect || { x: 0, y: 0, w: vw, h: vh };
  const x = Math.max(0, Math.round(r.x)), y = Math.max(0, Math.round(r.y));
  const w = Math.min(vw - x, Math.round(r.w) + 4), h = Math.min(vh - y, Math.round(r.h) + 4);
  const c3 = document.createElement('canvas');
  c3.width = w; c3.height = h;
  const g3 = c3.getContext('2d');
  g3.fillStyle = '#ffffff';
  g3.fillRect(0, 0, w, h);
  g3.drawImage(c2, x, y, w, h, 0, 0, w, h);
  const a = document.createElement('a');
  a.download = (document.title.split('·')[0] || '线网').trim() + '线网图.png';
  a.href = c3.toDataURL('image/png');
  a.click();
}

(function bindChartUI() {
  const bind = (id, fn) => { const b = document.getElementById(id); if (b) b.addEventListener('click', fn); };
  bind('btnChartRegen', () => {
    computeChart(true);
    fitChart();
    const st = Chart.edges ? ((Chart.edges - Chart.viol) / Chart.edges * 100).toFixed(1) : '—';
    toast(`拓扑图已重算 · ${Chart.edges} 段 · 八方向对齐 ${st}%`);
  });
  bind('btnChartFit', () => fitChart());
  bind('btnChartPng', () => { chartExport(); toast('线网图已导出为 PNG'); });
})();


/* ============================================================
   交互层：模式切换 / 线网列表 / 线路编辑 / 地图操作
   ============================================================ */
'use strict';

const $ = id => document.getElementById(id);

const el = {
  tabs: $('tabs'), lineList: $('lineList'), netBadge: $('netBadge'),
  detail: $('lineDetail'), dtChip: $('dtChip'), dtName: $('dtName'), dtSub: $('dtSub'),
  dtHeadway: $('dtHeadway'), dtSpeed: $('dtSpeed'), dtCap: $('dtCap'),
  dtHeadwayVal: $('dtHeadwayVal'), dtSpeedVal: $('dtSpeedVal'), dtCapVal: $('dtCapVal'),
  dtKm: $('dtKm'), dtFleet: $('dtFleet'), dtMaxLoad: $('dtMaxLoad'), dtPax: $('dtPax'),
  editorPanel: $('editorPanel'), simPanel: $('simPanel'), livePanel: $('livePanel'),
  editHint: $('editHint'), editLineSel: $('editLineSel'),
  editSpent: $('editSpent'), editBudget: $('editBudget'),
  hudClock: $('hudClock'), hudFlow: $('hudFlow'), hudAvg: $('hudAvg'), hudBudget: $('hudBudget'),
  modePill: $('modePill'), modePillText: $('modePillText'), netPill: $('netPill'),
  tooltip: $('tooltip'), eventLog: $('eventLog'),
  tlFill: $('tlFill'), tlMark: $('tlMark'), footPlay: $('footPlay'), tlRange: $('tlRange'),
  challengeList: $('challengeList'), modal: $('modal'), toast: $('toast'),
  xfStats: $('xfStats'), xfList: $('xfList'), xfBadge: $('xfBadge')
};

/* ---------------- 模式 ---------------- */
function setMode(mode) {
  const prevMode = App.mode;
  App.mode = mode;
  for (const b of el.tabs.querySelectorAll('button')) b.classList.toggle('active', b.dataset.mode === mode);
  el.editorPanel.classList.toggle('show', mode === 'edit');
  document.body.classList.toggle('mode-edit', mode === 'edit');
  el.simPanel.classList.toggle('show', mode === 'sim');
  el.livePanel.classList.toggle('show', mode === 'sim');
  document.body.classList.toggle('mode-chart', mode === 'chart');
  canvas.classList.toggle('picking', mode === 'edit' && App.tool !== 'drag');
  const txt = { view: '观察模式', edit: '规划模式', sim: '仿真模式', chart: '拓扑挂图' }[mode] || '';
  el.modePillText.textContent = txt;
  el.modePill.classList.toggle('warn', mode !== 'view');
  if (mode === 'edit' && !App.editSnapshot) pushUndo();
  if (mode === 'edit') {
    renderEditSelect();
    if (!App.editingLine && App.selectedLine) App.editingLine = App.selectedLine;
  }
  if (mode !== 'sim' && App.sim && App.sim.running) { /* 保持运行 */ }

  // 拓扑挂图：进入时按当前线网自动生成，离开时恢复原来的地图视角
  if (mode === 'chart') {
    if (!App.camBackup) App.camBackup = { x: App.cam.x, y: App.cam.y, s: App.cam.s };
    const fresh = computeChart(false);
    fitChart();
    if (fresh) toast('拓扑图已按当前线网生成');
  } else if (prevMode === 'chart' && App.camBackup) {
    App.cam.x = App.camBackup.x; App.cam.y = App.camBackup.y; App.cam.s = App.camBackup.s;
    App.camBackup = null;
  }

  App.dirty = true;
  syncBudget();
}
el.tabs.addEventListener('click', e => {
  const b = e.target.closest('button');
  if (b) setMode(b.dataset.mode);
});

/* ---------------- 线网列表 ---------------- */
function renderLineList() {
  const frag = document.createDocumentFragment();
  const cmp = (a, b) => (b.enabled - a.enabled) || (rankOf(a) - rankOf(b));
  const makeItem = (line) => {
    const item = document.createElement('div');
    item.className = 'lineItem' + (line.id === App.selectedLine ? ' active' : '') + (!line.enabled ? ' off' : '');
    item.dataset.id = line.id;
    const capEff = line.capEff || Math.max(6, Math.round(line.cap * K.CAP_RATIO));
    const avgLoad = line.loadCount ? line.loadSum / line.loadCount : 0;
    const peak = App.sim && App.sim.lineStats[line.id] ? Math.round(avgLoad / capEff * 100) : null;
    const bldMark = BUILDING_IDS.indexOf(line.id) >= 0 ? '<i class="bld">在建</i>'
      : (line.bldHead || line.bldTail) ? '<i class="bld">延伸在建</i>' : '';
    item.innerHTML = `
      <span class="lineChip" style="background:${line.color}">${line.short}</span>
      <span class="nm">${line.name}${bldMark}</span>
      <span class="ct">${uniqueCount(line)}站${lineArms(line).length > 1 ? '·' + lineArms(line).length + '支' : ''}${peak !== null ? ' · ' + peak + '%' : ''}</span>
      <span class="dot"></span>`;
    item.addEventListener('click', () => selectLine(line.id));
    item.addEventListener('dblclick', () => { App.editingLine = line.id; setMode('edit'); renderEditSelect(); });
    frag.appendChild(item);
  };
  const head = (txt) => {
    const d = document.createElement('div');
    d.className = 'grpHead';
    d.textContent = txt;
    frag.appendChild(d);
  };
  const blds = App.lines.filter(l => BUILDING_IDS.indexOf(l.id) >= 0).sort(cmp);
  const ops = App.lines.filter(l => BUILDING_IDS.indexOf(l.id) < 0).sort(cmp);
  if (blds.length) {
    head(`在建 · CONSTRUCTING ${blds.length}`);
    blds.forEach(makeItem);
    head(`运营 · IN SERVICE ${ops.length}`);
  }
  ops.forEach(makeItem);
  el.lineList.innerHTML = '';
  el.lineList.appendChild(frag);
  const ns = networkStats();
  el.netBadge.textContent = `${ns.lines} 线 / ${ns.stations} 站`;
  el.netPill.textContent = `${ns.lines} 条线 · ${ns.stations} 站 · ${Math.round(ns.km)} km`;
  updateNetStat();
  if (typeof renderXfers === 'function') { try { renderXfers(); } catch (e) {} }
}
function rankOf(l) {
  const order = ['L1','L2','L3','L4','L5','L6','L7','L9','L10','L11','S1','S2','S3','S4','S5','S6','S7','S8','S9'];
  const i = order.indexOf(l.id);
  return i < 0 ? 99 : i;
}

function selectLine(id) {
  App.selectedLine = id;
  App.editingLine = id;
  renderLineList();
  renderDetail();
  renderEditSelect();
  App.dirty = true;
}

function renderDetail() {
  const line = App.selectedLine ? getLine(App.selectedLine) : null;
  if (!line) { el.detail.classList.remove('show'); return; }
  el.detail.classList.add('show');
  el.dtChip.textContent = line.short;
  el.dtChip.style.background = line.color;
  el.dtName.textContent = line.name;
  const arm0 = lineArms(line)[0] || { stations: [] };
  const firstSt = arm0.stations[0] || '', lastSt = arm0.stations[arm0.stations.length - 1] || '';
  el.dtSub.textContent = (firstSt && lastSt ? `${firstSt} ⇄ ${lastSt} · ` : '')
    + `${uniqueCount(line)} 站` + (lineArms(line).length > 1 ? ` · ${lineArms(line).length} 臂` : '');
  el.dtHeadway.value = line.headway;
  el.dtSpeed.value = line.speed;
  el.dtCap.value = line.cap;
  el.dtHeadwayVal.textContent = line.headway + 's';
  el.dtSpeedVal.textContent = line.speed + 'km/h';
  el.dtCapVal.textContent = line.cap + '人';
  el.dtKm.textContent = (line.km || 0).toFixed(1) + 'km';
  el.dtFleet.textContent = (line.fleet || 0) + '列';
  const capEff = line.capEff || Math.max(6, Math.round(line.cap * K.CAP_RATIO));
  const avgLoad = line.loadCount ? line.loadSum / line.loadCount : 0;
  const load = Math.round(avgLoad / capEff * 100);
  el.dtMaxLoad.textContent = load + '%';
  el.dtMaxLoad.className = 'v ' + (load > 95 ? 'bad' : load > 70 ? 'warn' : '');
  const ls = App.sim ? App.sim.lineStats[line.id] : null;
  el.dtPax.textContent = ls ? Math.round(ls.boardings).toLocaleString() : '0';
  renderSeq(line);
  $('btnToggleLine').textContent = line.enabled ? '停运' : '启用';
  $('btnDelLine').disabled = uniqueCount(line) === 0 && line.custom === false;
}

/* 站点序列：主干 + 各支线分组显示，可逐站移出本线 */
function uniqueCount(line) {
  const s = new Set();
  for (const a of lineArms(line)) for (const x of a.stations) s.add(x);
  return s.size;
}

function buildSeq(box, hint, line) {
  if (!box) return;
  box.innerHTML = '';
  const arms = lineArms(line);
  const multi = arms.length > 1;
  const frag = document.createDocumentFragment();
  arms.forEach((arm, ai) => {
    if (multi) {
      const head = document.createElement('div');
      head.className = 'seqBranch';
      const fx = App.stations.get(arm.stations[0]);
      head.textContent = ai === 0
        ? `主干 · ${arm.stations.length} 站`
        : `支线 ${ai} · 分叉点 ${fx ? fx.name : '?'} · ${arm.stations.length} 站`;
      frag.appendChild(head);
    }
    const canDetach = ai === 0 ? arm.stations.length > 2 : arm.stations.length > 1;
    arm.stations.forEach((sid, i) => {
      const st = App.stations.get(sid);
      if (!st) return;
      const row = document.createElement('div');
      row.className = 'seqRow' + (canDetach ? '' : ' locked');
      row.innerHTML = `<span class="idx">${i + 1}</span><span class="nm">${st.name}</span>` +
        (st.lines.length > 1 ? '<span class="tr">换乘</span>' : '') +
        (canDetach ? `<span class="x" title="从本线移出该站">✕</span>` : '');
      row.addEventListener('click', () => focusStation(sid));
      const x = row.querySelector('.x');
      if (x) x.addEventListener('click', e => { e.stopPropagation(); detachStation(line.id, sid, ai); });
      frag.appendChild(row);
      if (ai === 0 && i >= 1 && i <= arm.stations.length - 3) {
        const sp = document.createElement('div');
        sp.className = 'seqSplit';
        sp.innerHTML = '<span>✂ 在此断开</span>';
        sp.title = '把这条线从此处拆成两条独立线路';
        sp.addEventListener('click', e => { e.stopPropagation(); openSplitDialog(line.id, i + 1); });
        frag.appendChild(sp);
      }
    });
  });
  box.appendChild(frag);
  if (hint) hint.textContent = multi
    ? `${uniqueCount(line)} 站 · ${arms.length} 条运行臂`
    : `${line.stations.length} 站 · 可移出`;
}

function renderSeq(line) {
  buildSeq($('dtSeq'), $('dtSeqHint'), line);
  if ($('edSeq') && App.editingLine === line.id) buildSeq($('edSeq'), $('edSeqHint'), line);
}

/* 把某站从一条线路的某个运行臂上摘掉（车站本身保留） */
function detachStation(lineId, sid, armIdx) {
  const line = getLine(lineId), st = App.stations.get(sid);
  if (!line || !st) return false;
  const arms = lineArms(line);
  let ai = typeof armIdx === 'number' ? armIdx : -1;
  if (ai < 0) {
    for (let k = 0; k < arms.length; k++) {
      const ok = k === 0 ? arms[k].stations.length > 2 : arms[k].stations.length > 1;
      if (ok && arms[k].stations.includes(sid)) { ai = k; break; }
    }
  }
  if (ai < 0) { toast('该站不能从这条线移出（每条运行段至少要保留 2 站）'); return false; }
  pushUndo();
  if (!removeStationFromArm(line, ai, sid)) { toast('移出失败'); return false; }
  renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); updateNetStat(); App.dirty = true;
  toast(`已从 ${line.name} 移出 ${st.name}（剩 ${uniqueCount(line)} 站）`);
  return true;
}

function focusStation(sid) {
  const st = App.stations.get(sid);
  if (!st) return;
  App.cam.s = Math.max(App.cam.s, 30);
  App.cam.x = st.x; App.cam.y = st.y;
  App.dirty = true;
}

el.dtHeadway.addEventListener('input', () => {
  const line = getLine(App.selectedLine); if (!line) return;
  line.headway = +el.dtHeadway.value;
  el.dtHeadwayVal.textContent = line.headway + 's';
  refreshSegs(); rebuildGraph(); renderDetail(); App.dirty = true;
});
el.dtSpeed.addEventListener('input', () => {
  const line = getLine(App.selectedLine); if (!line) return;
  line.speed = +el.dtSpeed.value;
  el.dtSpeedVal.textContent = line.speed + 'km/h';
  refreshSegs(); rebuildGraph(); renderDetail(); App.dirty = true;
});
el.dtCap.addEventListener('input', () => {
  const line = getLine(App.selectedLine); if (!line) return;
  line.cap = +el.dtCap.value;
  el.dtCapVal.textContent = line.cap + '人';
  renderDetail();
});
$('btnToggleLine').addEventListener('click', () => {
  const line = getLine(App.selectedLine); if (!line) return;
  line.enabled = !line.enabled;
  refreshSegs(); rebuildGraph(); renderLineList(); renderDetail(); toast(`${line.name} 已${line.enabled ? '恢复运营' : '停运'}`);
});
$('btnDelLine').addEventListener('click', () => {
  const line = getLine(App.selectedLine); if (!line) return;
  confirmDialog('拆除线路', `确定拆除 <b>${line.name}</b> ？该线 ${line.km ? line.km.toFixed(1) + ' km' : uniqueCount(line) + ' 站'} 将停运，返还 30% 建设费用。`, () => {
    pushUndo();
    const refund = line.custom ? COST_LINE_OPEN * 0.3 : 0;
    App.spent = Math.max(0, App.spent - refund);
    deleteLine(line.id);
    renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); toast(`${line.name} 已拆除`);
  });
});

/* ---------------- 预算 ---------------- */
function spend(n) {
  const left = App.budget - App.spent;
  if (left < n) { toast('预算不足，无法建设'); return false; }
  App.spent += n;
  syncBudget();
  return true;
}
function syncBudget() {
  const left = Math.max(0, App.budget - App.spent);
  el.hudBudget.innerHTML = `${left.toFixed(0)}<small>亿</small>`;
  el.editSpent.textContent = App.spent.toFixed(1) + ' 亿';
  el.editBudget.textContent = left.toFixed(1) + ' 亿';
  el.editBudget.className = 'v ' + (left < 60 ? 'bad' : left < 150 ? 'warn' : 'good');
}

/* ---------------- 撤销 ---------------- */
function snapshot() {
  return {
    stations: [...App.stations.values()].map(s => ({ id: s.id, name: s.name, lng: s.lng, lat: s.lat, w: s.w, lines: [...s.lines], custom: s.custom })),
    lines: App.lines.map(l => ({
      id: l.id, name: l.name, short: l.short, color: l.color, headway: l.headway, speed: l.speed, cap: l.cap,
      stations: [...l.stations],
      arms: lineArms(l).map(a => ({ stations: [...a.stations] })),
      enabled: l.enabled, custom: l.custom
    })),
    spent: App.spent, newStations: App.newStations, customStations: App.customStations,
    trackOff: { ...(App.trackOff || {}) },
    trackOV: { ...TRACK_OV },
    selected: App.selectedLine, editing: App.editingLine, drawAnchor: App.drawAnchor ? { ...App.drawAnchor } : null
  };
}
function restore(snap) {
  App.stations = new Map();
  for (const s of snap.stations) {
    const st = { ...s, x: (s.lng - LNG0) * KX, y: (LAT0 - s.lat) * KY, boardings: 0, alightings: 0 };
    App.stations.set(st.id, st);
  }
  App.lines = snap.lines.map(l => {
    const obj = { ...l, stations: [...l.stations], segs: null, pax: 0, peakLoad: 0, fleet: 0, depTimer: 0 };
    obj.arms = (l.arms && l.arms.length ? l.arms : [{ stations: l.stations }]).map(a => ({ stations: [...a.stations] }));
    obj.arms[0].stations = obj.stations;   // 主干与 line.stations 共用同一数组
    return obj;
  });
  App.spent = snap.spent; App.newStations = snap.newStations; App.customStations = snap.customStations;
  App.trackOff = { ...(snap.trackOff || {}) };
  trackResetAll();
  Object.assign(TRACK_OV, snap.trackOV || {});
  App.drawAnchor = snap.drawAnchor ? { ...snap.drawAnchor } : null;
  App.selectedLine = snap.selected; App.editingLine = snap.editing;
  invalidatePools(); refreshSegs(); rebuildGraph();
}
function pushUndo() {
  if (!App.undoStack) App.undoStack = [];
  App.undoStack.push(snapshot());
  if (App.undoStack.length > 24) App.undoStack.shift();
}
$('btnUndo').addEventListener('click', () => {
  if (!App.undoStack || !App.undoStack.length) { toast('没有可撤销的操作'); return; }
  const snap = App.undoStack.pop();
  const sim = App.sim;
  if (sim && sim.running) { sim.running = false; }
  restore(snap);
  renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); App.dirty = true;
  toast('已撤销');
});

/* ---------------- 编辑选择器 ---------------- */
function renderEditSelect() {
  const keep = App.editingLine;
  el.editLineSel.innerHTML = '';
  const opt0 = document.createElement('option');
  opt0.value = ''; opt0.textContent = '— 选择线路 —';
  el.editLineSel.appendChild(opt0);
  for (const l of App.lines) {
    const o = document.createElement('option');
    o.value = l.id; o.textContent = `${l.name}（${uniqueCount(l)}站）`;
    el.editLineSel.appendChild(o);
  }
  el.editLineSel.value = keep && getLine(keep) ? keep : '';
  const box = $('edSeq'), hint = $('edSeqHint');
  if (box) {
    const ln = keep && getLine(keep);
    if (ln) buildSeq(box, hint, ln);
    else { box.innerHTML = ''; if (hint) hint.textContent = '未选择线路'; }
  }
  updateNetStat();
}
el.editLineSel.addEventListener('change', () => {
  App.editingLine = el.editLineSel.value || null;
  App.selectedLine = App.editingLine;
  App.drawAnchor = null;
  renderLineList(); renderDetail(); renderEditSelect(); App.dirty = true;
});

$('btnToolStation').addEventListener('click', () => setTool('station'));
$('btnToolSplit').addEventListener('click', () => openSplitPick());
$('btnToolDraw').addEventListener('click', () => setTool('draw'));
$('btnToolDrag').addEventListener('click', () => setTool('drag'));
$('btnToolErase').addEventListener('click', () => setTool('erase'));
function setTool(t) {
  App.tool = t;
  if (t !== 'draw') App.drawAnchor = null;
  $('btnToolStation').classList.toggle('primary', t === 'station');
  $('btnToolDraw').classList.toggle('primary', t === 'draw');
  $('btnToolDrag').classList.toggle('primary', t === 'drag');
  $('btnToolErase').classList.toggle('primary', t === 'erase');
  el.editHint.innerHTML = {
    station: '<b>建站</b>：点空白处新建车站。车站先进入站网、不隶属任何线路。',
    draw: '<b>画线</b>：先点线路上任一站作为接续点（出现青绿脉冲环），再点其他车站即可从该处向前/向后延伸；<b>点在两站之间会分叉出支线</b>。空白处不会自动建站。',
    drag: '<b>拖动</b>：按住车站拖动，站网与所连线路同步跟随。',
    erase: '<b>删站</b>：点车站可整站删除，或仅把该站从当前线路移出。'
  }[t];
  canvas.classList.toggle('picking', t !== 'drag');
}
function updateNetStat() {
  const box = $('editNetStat');
  if (!box) return;
  let orphan = 0, total = 0;
  for (const st of App.stations.values()) { total++; if (!st.lines.length) orphan++; }
  box.innerHTML = `站网 <b>${total}</b> 站<span class="sep">/</span>未接入 <b>${orphan}</b><span class="sep">/</span>新建 <b>${App.newStations || 0}</b>`;
}
$('btnFinishLine').addEventListener('click', () => {
  if (!App.editingLine) { toast('没有正在编辑的线路'); return; }
  const line = getLine(App.editingLine);
  if (line && uniqueCount(line) < 2) { toast('线路至少需要 2 个车站'); return; }
  if (line) { pushUndo(); toast(`${line.name} 已保存，共 ${uniqueCount(line)} 站`); }
  renderLineList(); renderDetail(); App.dirty = true;
});

/* ---------------- 恢复真实线网 ---------------- */
$('btnReset').addEventListener('click', () => {
  const bldNames = App.lines.filter(l => BUILDING_IDS.indexOf(l.id) >= 0).map(l => l.name);
  const extNames = App.lines.filter(l => l.bldHead || l.bldTail).map(l => l.name);
  const bldTxt = bldNames.length
    ? ` + ${bldNames.length} 条在建线路（${bldNames.join('、')}）`
    : (extNames.length ? `（${extNames.join('、')}另有延伸段在建）` : '');
  const nsAll = networkStats();
  openDialog(`
    <h3>恢复真实线网</h3>
    <p>将丢弃全部规划改动，回到 2026 年 11 月的真实线网：${App.lines.length - bldNames.length} 条运营线路${bldTxt}，共 ${nsAll.stations} 座车站。预算同步重置。</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn primary" data-act="ok">确认恢复</button>
    </div>`, root => {
    root.querySelector('[data-act=ok]').addEventListener('click', () => {
      App.editingLine = null; App.selectedLine = null; App.sim = null; App.report = null;
      App.reportShown = true; App.undoStack = []; App.challenge = null;
      buildWorld(); syncBudget(); fitCity();
      renderLineList(); renderDetail(); renderEditSelect(); renderChallenges();
      $('simIdle').style.display = 'block'; $('simRunning').style.display = 'none';
      $('livePanel').classList.remove('show');
      setMode('view'); App.dirty = true;
      clearSave();
      closeDialog(); toast('已恢复 2026 年 11 月真实线网，旧存档已清空');
    });
  });
});

/* ---------------- 新建线路 / 新建车站 ---------------- */
const PALETTE = ['#ff6b6b', '#ffa43d', '#ffd93d', '#6bcB77', '#4dabf7', '#9775fa', '#f783ac', '#38d9a9', '#ff922b', '#748ffc'];

$('btnAddLine').addEventListener('click', () => {
  openDialog(`
    <h3>新建线路</h3>
    <p>选择线路颜色与名称，随后在地图上依次点击车站进行铺设。开通费用 ${COST_LINE_OPEN} 亿元。</p>
    <div class="field"><label>线路名称</label><input id="dlgLineName" value="新线" maxlength="10"></div>
    <div class="field"><label>线路色</label><div class="swatches" id="dlgSwatches">
      ${PALETTE.map((c, i) => `<div class="swatch ${i === 0 ? 'active' : ''}" data-color="${c}" style="background:${c}"></div>`).join('')}
    </div></div>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn primary" data-act="ok">创建并画线</button>
    </div>`, root => {
    let color = PALETTE[0];
    root.querySelectorAll('.swatch').forEach(sw => sw.addEventListener('click', () => {
      root.querySelectorAll('.swatch').forEach(x => x.classList.remove('active'));
      sw.classList.add('active'); color = sw.dataset.color;
    }));
    root.querySelector('[data-act=ok]').addEventListener('click', () => {
      const name = root.querySelector('#dlgLineName').value.trim() || '新线';
      if (!spend(COST_LINE_OPEN)) return;
      pushUndo();
      const line = createLine(name, color);
      App.editingLine = line.id; App.selectedLine = line.id; App.drawAnchor = null;
      closeDialog(); setMode('edit'); setTool('draw');
      renderLineList(); renderDetail(); renderEditSelect(); syncBudget();
      toast('线路已创建，请在地图上点击车站');
    });
  });
});

function blankNewStation(lng, lat) {
  openDialog(`
    <h3>新建车站</h3>
    <p>坐标 ${lng.toFixed(4)}, ${lat.toFixed(4)} · 造价 ${COST_STATION} 亿元</p>
    <div class="field"><label>车站名称</label><input id="dlgStName" placeholder="例如：所街" maxlength="16"></div>
    <p style="font-size:11px;color:var(--dim);margin:-4px 0 12px">新建的车站先进入站网、暂不隶属任何线路；之后用「画线」把它按顺序接入线路。</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn primary" data-act="ok">建站</button>
    </div>`, root => {
    const input = root.querySelector('#dlgStName');
    setTimeout(() => input.focus(), 60);
    root.querySelector('[data-act=ok]').addEventListener('click', () => {
      const name = input.value.trim();
      if (!name) { toast('请输入车站名称'); return; }
      if (App.stations.has(name)) { toast('该站名已存在，请直接用画线工具接入'); return; }
      if (!spend(COST_STATION)) return;
      pushUndo();
      addStation(name, lng, lat);
      App.newStations++;
      closeDialog();
      renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); App.dirty = true;
      toast(`${name} 已建成，进入站网${App.editingLine ? '（用画线接入线路）' : ''}`);
    });
    input.addEventListener('keydown', e => { if (e.key === 'Enter') root.querySelector('[data-act=ok]').click(); });
  });
}


/* ---------------- 线路拆分弹窗 ---------------- */
function openSplitDialog(lineId, cutIdx) {
  const line = getLine(lineId);
  if (!line) return;
  const main = lineArms(line)[0];
  if (cutIdx < 2 || cutIdx > main.stations.length - 2) {
    toast('断点太靠端：两段都要至少 2 站');
    return;
  }
  const a = App.stations.get(main.stations[cutIdx - 1]);
  const b = App.stations.get(main.stations[cutIdx]);
  const headN = cutIdx, tailN = main.stations.length - cutIdx;
  const palette = [line.color, '#8AB4F8', '#EF426F', '#FA4616', '#009ACE', '#FF8000', '#4A7729', '#7D55C7'];
  openDialog(`<h3>拆分线路 · ${line.name}</h3>
    <p>在 <b>${a ? a.name : '?'}</b> 与 <b>${b ? b.name : '?'}</b> 之间断开。
    前半段 <b>${headN}</b> 站仍叫「${line.name}」，后半段 <b>${tailN}</b> 站独立成新线。</p>
    <div style="display:flex;align-items:center;gap:8px;margin:12px 0 10px">
      <span style="font-size:11.5px;color:var(--muted);flex:0 0 52px">新线名称</span>
      <input id="spName" value="${line.name}·新段" style="flex:1;min-width:0;background:var(--player-control);
        border:1px solid rgba(120,180,255,.3);border-radius:6px;color:var(--text);padding:6px 8px;font-size:12px" />
    </div>
    <div style="display:flex;align-items:center;gap:8px;margin:10px 0">
      <span style="font-size:11.5px;color:var(--muted);flex:0 0 52px">新线颜色</span>
      <div id="spSw" style="display:flex;gap:6px;flex-wrap:wrap"></div>
    </div>
    <p style="color:var(--muted);font-size:11.5px;margin-top:10px">拆分属于运营调整，不产生建设费用。
    断点处真实轨道几何会被裁成两段，两段各自沿原位延伸。</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn" data-act="ok">确认拆分</button>
    </div>`, root => {
    let color = '#8AB4F8';
    const sw = root.querySelector('#spSw');
    palette.forEach((c, i) => {
      const d = document.createElement('div');
      d.style.cssText = 'width:22px;height:22px;border-radius:6px;background:' + c +
        ';cursor:pointer;border:2px solid ' + (i === 1 ? '#dce8f7' : 'transparent') + ';box-sizing:border-box';
      if (i === 1) color = c;
      d.title = c;
      d.addEventListener('click', () => {
        color = c;
        Array.from(sw.children).forEach(x => { x.style.borderColor = 'transparent'; });
        d.style.borderColor = '#dce8f7';
      });
      sw.appendChild(d);
    });
    root.querySelector('[data-act=ok]').addEventListener('click', () => {
      const nm = (root.querySelector('#spName').value || '').trim() || (line.name + '·新段');
      const r = splitLine(lineId, cutIdx, { name: nm, color });
      closeDialog();
      if (!r.ok) { toast('拆分失败：' + r.reason); return; }
      renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); updateNetStat();
      App.dirty = true;
      toast(`已拆分：${line.name} ${r.head} 站 + ${r.line.name} ${r.tail} 站`);
    });
  });
}


/* 「✂ 拆分线路」：先选线路与断点，再进入拆分确认 */
function openSplitPick() {
  const usable = App.lines.filter(l => lineArms(l)[0].stations.length >= 4);
  if (!usable.length) { toast('没有可拆分的线路（至少要 4 站）'); return; }
  const curId = (App.editingLine && usable.some(l => l.id === App.editingLine)) ? App.editingLine : usable[0].id;
  const opts = usable.map(l => `<option value="${l.id}"${l.id === curId ? ' selected' : ''}>${l.name}（${l.stations.length} 站）</option>`).join('');
  const cutHtml = lid => {
    const line = getLine(lid);
    if (!line) return '';
    const main = lineArms(line)[0], n = main.stations.length;
    let out = '';
    for (let i = 2; i <= n - 2; i++) {
      const a = App.stations.get(main.stations[i - 1]), b = App.stations.get(main.stations[i]);
      out += `<option value="${i}">${a ? a.name : '?'} → ${b ? b.name : '?'}（前 ${i} 站 / 后 ${n - i} 站）</option>`;
    }
    return out;
  };
  openDialog(`<h3>拆分线路</h3>
    <p>选一条线和断点，把它拆成两条独立运营的线路，类似广州 2 号线 / 8 号线拆分。</p>
    <div style="display:flex;align-items:center;gap:8px;margin:10px 0">
      <span style="font-size:11.5px;color:var(--muted);flex:0 0 52px">线路</span>
      <select id="spLine" style="flex:1;min-width:0;background:var(--player-control);border:1px solid rgba(120,180,255,.3);
        border-radius:6px;color:var(--text);padding:6px 8px;font-size:12px">${opts}</select>
    </div>
    <div style="display:flex;align-items:center;gap:8px;margin:10px 0">
      <span style="font-size:11.5px;color:var(--muted);flex:0 0 52px">断点</span>
      <select id="spCut" style="flex:1;min-width:0;background:var(--player-control);border:1px solid rgba(120,180,255,.3);
        border-radius:6px;color:var(--text);padding:6px 8px;font-size:12px">${cutHtml(curId)}</select>
    </div>
    <p style="color:var(--muted);font-size:11.5px">拆分不产生建设费用，断点处的轨道几何按两段裁切。</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn" data-act="next">下一步</button>
    </div>`, root => {
    root.querySelector('#spLine').addEventListener('change', e => {
      root.querySelector('#spCut').innerHTML = cutHtml(e.target.value);
    });
    root.querySelector('[data-act=next]').addEventListener('click', () => {
      const lid = root.querySelector('#spLine').value;
      const cut = +root.querySelector('#spCut').value;
      closeDialog();
      openSplitDialog(lid, cut);
    });
  });
}


/* ============================================================
   UI 层：地图交互 / 弹窗 / 仿真控制 / 成绩单
   ============================================================ */

/* ---------------- 弹窗 ---------------- */
function openDialog(html, mount) {
  el.modal.innerHTML = `<div class="dialog">${html}</div>`;
  el.modal.classList.add('show');
  const root = el.modal.firstElementChild;
  root.querySelectorAll('[data-act=cancel]').forEach(b => b.addEventListener('click', closeDialog));
  el.modal.onclick = e => { if (e.target === el.modal) closeDialog(); };
  if (mount) mount(root);
  return root;
}
function closeDialog() {
  el.modal.classList.remove('show');
  el.modal.innerHTML = '';
  el.modal.onclick = null;
}
function confirmDialog(title, text, onOk) {
  openDialog(`<h3>${title}</h3><p>${text}</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      <button class="btn danger" data-act="ok">确认</button>
    </div>`, root => {
    root.querySelector('[data-act=ok]').addEventListener('click', () => { closeDialog(); onOk(); });
  });
}
function toast(msg) {
  el.toast.textContent = msg;
  el.toast.classList.add('show');
  clearTimeout(App.toastTimer);
  App.toastTimer = setTimeout(() => el.toast.classList.remove('show'), 2300);
}

/* ---------------- 地图拾取 ---------------- */
function pickStation(sx, sy, radius = 13) {
  let best = null, bd = radius * radius;
  for (const [id, st] of App.stations) {
    const p = w2s(st.x, st.y);
    const d = (p.x - sx) ** 2 + (p.y - sy) ** 2;
    if (d < bd) { bd = d; best = id; }
  }
  return best;
}

function updateHover(x, y) {
  if (App.mode === 'chart') { App.hover = null; el.tooltip.classList.remove('show'); return; }
  const hit = App.mode === 'edit' && App.tool === 'erase' ? pickStation(x, y, 15) : pickStation(x, y, 13);
  App.hover = hit;
  if (!hit) { el.tooltip.classList.remove('show'); return; }
  const st = App.stations.get(hit);
  const sim = App.sim;
  const ss = sim ? sim.stationStats.get(hit) : null;
  const linesHtml = st.lines.map(id => {
    const l = getLine(id);
    return l ? `<span style="color:${l.color};font-weight:600">${l.name}</span>` : '';
  }).filter(Boolean).join('、') || '<span style="color:var(--dim)">未接入任何线路</span>';
  let rows = `<div class="tr"><span>车站权重</span><b>${(st.w * 100).toFixed(0)}</b></div>`;
  const XFDB = (typeof XFER !== 'undefined') ? XFER : null;
  const XFTY = (typeof XFER_TYPES !== 'undefined') ? XFER_TYPES : null;
  const xf = XFDB ? XFDB[st.name] : undefined;
  let xferHtml = '';
  if (xf && XFTY && XFTY[xf.t]) {
    const ty = XFTY[xf.t];
    xferHtml = `<div class="tr xfRow"><span>换乘方式</span><b style="color:${ty.color}">${ty.name}${xf.b ? '<i class="xfB">在建</i>' : ''}</b></div>
      <div class="tr"><span>换乘线路</span><b>${xf.l}</b></div>
      <div class="xfD">${xf.d}${xf.m ? '<br>' + xf.m.join('<br>') : ''}</div>`;
  }
  if (sim) {
    rows += `<div class="tr"><span>站台等待</span><b style="color:${ss && ss.queue > 300 ? '#ff5f74' : '#e9f1ff'}">${ss ? ss.queue : 0} 人</b></div>
             <div class="tr"><span>今日上车</span><b>${ss ? ss.board : 0}</b></div>`;
  }
  el.tooltip.innerHTML = `
    <div class="tt"><i style="background:${st.lines.length ? getLine(st.lines[0]).color : '#5d738f'}"></i>${st.name}</div>
    <div class="tl">${linesHtml}</div>
    ${xferHtml}
    ${rows}
    ${st.custom ? '<div class="tr" style="margin-top:4px;color:#28d7c0"><span>规划新建车站</span></div>' : ''}`;
  el.tooltip.classList.add('show');
  const tw = el.tooltip.offsetWidth || 190, th = el.tooltip.offsetHeight || 90;
  let left = x + 18, top = y + 16;
  if (left + tw > W - 8) left = x - tw - 16;
  if (top + th > H - 8) top = y - th - 14;
  el.tooltip.style.left = Math.max(6, left) + 'px';
  el.tooltip.style.top = Math.max(6, top) + 'px';
}

/* ---------------- 点击处理 ---------------- */
function handleClick(x, y) {
  if (App.mode === 'chart') return;   // 挂图为只读视图
  const hit = pickStation(x, y, 14);
  if (App.mode === 'edit') {
    if (App.tool === 'erase') {
      if (hit) askDeleteStation(hit);
      return;
    }
    if (App.tool === 'station') {
      if (hit) {
        toast(`这里已有车站「${App.stations.get(hit).name}」，用画线把它接入线路即可`);
        return;
      }
      const w = s2w(x, y);
      const ll = worldToLngLat(w.x, w.y);
      blankNewStation(ll.lng, ll.lat);
      return;
    }
    if (App.tool === 'draw') {
      if (!App.editingLine) { toast('请先新建线路或从下拉框选择线路'); return; }
      const line = getLine(App.editingLine);
      if (!line) { toast('线路不存在'); return; }
      if (!hit) {
        toast('此处没有车站：画线只连接已有车站，请先用「建站」工具新建');
        return;
      }
      const name = App.stations.get(hit).name;
      const arms = lineArms(line);
      let inLine = -1;
      for (let k = 0; k < arms.length; k++) if (arms[k].stations.includes(hit)) { inLine = k; break; }
      if (inLine >= 0) {
        App.drawAnchor = { sid: hit, arm: inLine };
        toast(`接续点已设为 ${name}：继续点其他车站，可从这站向前/向后延伸，或在中间生出支线`);
        App.dirty = true;
        return;
      }
      const anchor = App.drawAnchor && App.drawAnchor.sid != null ? App.drawAnchor : null;
      const anchorName = anchor ? (App.stations.get(anchor.sid) || {}).name : null;
      const wasOff = !!(App.trackOff && App.trackOff[line.id]);
      if (anchor) {
        pushUndo();
        const r = lineAttach(line, anchor.sid, hit);
        if (!r || !r.ok) { toast('接入失败'); return; }
        App.drawAnchor = { sid: hit, arm: r.arm };
        const note = (!wasOff && App.trackOff[line.id]) ? '；主干起终点已外扩，该线改用车站连线绘制' : '';
        toast(r.mode === 'branch'
          ? `已从「${anchorName}」分叉出新支线，接入「${name}」（${line.name} 现 ${uniqueCount(line)} 站 / ${lineArms(line).length} 臂）`
          : `已接入「${name}」（${line.name} 现 ${uniqueCount(line)} 站）${note}`);
      } else {
        pushUndo();
        const main = arms[0].stations;
        const r = lineAttach(line, main.length ? main[main.length - 1] : null, hit);
        if (!r || !r.ok) { toast('接入失败'); return; }
        App.drawAnchor = { sid: hit, arm: r.arm };
        toast(`已接入「${name}」，它现在是接续点`);
      }
      renderDetail(); renderLineList(); renderEditSelect(); updateNetStat();
      App.dirty = true;
      return;
    }
    return;
  }
  if (hit) showStationCard(hit);
}

function askDeleteStation(id) {
  const st = App.stations.get(id);
  if (!st) return;
  const cur = App.selectedLine && st.lines.includes(App.selectedLine) ? getLine(App.selectedLine) : null;
  const used = st.lines.length;
  const names = st.lines.map(lid => (getLine(lid) || {}).name).filter(Boolean).join('、') || '—';
  openDialog(`<h3>删除车站</h3>
    <p>${st.name} 被 <b>${used}</b> 条线路经过（${names}）。</p>
    <p style="color:var(--muted);font-size:11.5px">「仅移出本线」只让当前选中的线路跳过这一站，其他线路照常停靠；「整站删除」会把车站从图上移除，所有线路都会出现断口。</p>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="cancel">取消</button>
      ${cur ? `<button class="btn" data-act="detach">仅移出 ${cur.name}</button>` : ''}
      <button class="btn danger" data-act="ok">整站删除</button>
    </div>`, root => {
    root.querySelector('[data-act=ok]').addEventListener('click', () => { closeDialog(); doDeleteStation(id); });
    const d = root.querySelector('[data-act=detach]');
    if (d) d.addEventListener('click', () => { closeDialog(); detachStation(cur.id, id); });
  });
}

function doDeleteStation(id) {
  const st = App.stations.get(id);
  if (!st) return;
  pushUndo();
  removeStationEverywhere(id);
  renderLineList(); renderDetail(); renderEditSelect(); syncBudget(); App.dirty = true;
  el.tooltip.classList.remove('show');
  toast(`${st.name} 已删除`);
}

function showStationCard(id) {
  const st = App.stations.get(id);
  const sim = App.sim;
  const ss = sim ? sim.stationStats.get(id) : null;
  const lines = st.lines.map(l => {
    const ln = getLine(l);
    return `<span style="display:inline-flex;align-items:center;gap:5px;margin-right:10px">
      <i style="width:8px;height:8px;border-radius:2px;background:${ln.color};display:inline-block"></i>${ln.name}</span>`;
  }).join('');
  const detachBtns = st.lines.map(lid => {
    const ln = getLine(lid);
    if (!ln || uniqueCount(ln) <= 2) return '';
    return `<button class="btn ghost mini" data-detach="${lid}" style="margin:0 6px 6px 0">从 ${ln.name} 移出</button>`;
  }).join('');
  openDialog(`
    <h3>${st.name}</h3>
    <p>${st.lines.length > 1 ? '换乘车站' : '普通车站'} · 权重 ${(st.w * 100).toFixed(0)} · ${st.lng.toFixed(4)}, ${st.lat.toFixed(4)}</p>
    <div style="margin-bottom:14px;font-size:12px;color:#8ba3c4">${lines || '尚未接入线路'}</div>
    ${detachBtns ? `<div style="margin:-4px 0 12px">${detachBtns}</div>
      <div style="font-size:11px;color:var(--dim);margin-bottom:12px">移出后列车经过此处不再停车，车站本身保留在图上。</div>` : ''}
    <div class="metricGrid" style="grid-template-columns:repeat(3,1fr)">
      <div class="statCard"><div class="k">今日上车</div><div class="v">${ss ? ss.board : 0}</div></div>
      <div class="statCard"><div class="k">今日下车</div><div class="v">${ss ? ss.alight : 0}</div></div>
      <div class="statCard"><div class="k">站台等待</div><div class="v ${ss && ss.queue > 300 ? 'bad' : ss && ss.queue > 120 ? 'warn' : ''}">${ss ? ss.queue : 0}</div></div>
    </div>
    <div class="dialogFoot"><button class="btn ghost" data-act="cancel">关闭</button></div>`, root => {
    root.querySelectorAll('[data-detach]').forEach(b => b.addEventListener('click', () => {
      closeDialog();
      detachStation(b.dataset.detach, id);
    }));
  });
}

/* ---------------- 地图事件 ---------------- */
let dragStart = null;
function bindMap() {
  canvas.addEventListener('pointerdown', e => {
    if (!e.isPrimary || e.button !== 0) return;
    if (e.pointerType !== 'mouse') canvas.setPointerCapture(e.pointerId);
    mouse.down = true; mouse.moved = false;
    mouse.sx = e.offsetX; mouse.sy = e.offsetY;
    mouse.x = e.offsetX; mouse.y = e.offsetY;
    dragStart = { camx: App.cam.x, camy: App.cam.y };
    if (App.mode === 'edit' && App.tool === 'drag') {
      const hit = pickStation(e.offsetX, e.offsetY, 14);
      if (hit) { App.dragStation = hit; canvas.classList.add('dragging'); return; }
    }
    canvas.classList.add('dragging');
  });

  canvas.addEventListener('pointerenter', () => { mouse.inside = true; });
  canvas.addEventListener('pointerleave', () => { mouse.inside = false; });
  window.addEventListener('pointermove', e => {
    if (!e.isPrimary || (e.pointerType !== 'mouse' && !mouse.down)) return;
    const rect = canvas.getBoundingClientRect();
    const x = Math.max(-40, Math.min(W + 40, e.clientX - rect.left));
    const y = Math.max(-40, Math.min(H + 40, e.clientY - rect.top));
    mouse.x = x; mouse.y = y; mouse.world = s2w(x, y);
    if (mouse.down) {
      const dx = x - mouse.sx, dy = y - mouse.sy;
      if (Math.abs(dx) + Math.abs(dy) > 5) mouse.moved = true;
      if (mouse.moved) {
        if (App.dragStation) {
          const w = s2w(x, y);
          const st = App.stations.get(App.dragStation);
          const lng = w.x / KX + LNG0, lat = LAT0 - w.y / KY;
          st.lng = lng; st.lat = lat;
          st.x = (lng - LNG0) * KX; st.y = (LAT0 - lat) * KY;
          for (const lid of (st.lines || [])) App.trackOff[lid] = 1;
          App.dirty = true;
        } else {
          App.cam.x = dragStart.camx - dx / App.cam.s;
          App.cam.y = dragStart.camy - dy / App.cam.s;
          App.dirty = true;
          el.tooltip.classList.remove('show');
        }
      }
    } else if (App.mode !== 'sim' || true) {
      updateHover(x, y);
    }
  });

  function finishPointer(e) {
    if (!e.isPrimary || !mouse.down) return;
    mouse.down = false;
    canvas.classList.remove('dragging');
    if (App.dragStation) {
      const sid = App.dragStation;
      App.dragStation = null;
      refreshSegs(); rebuildGraph();
      toast(`${App.stations.get(sid).name} 位置已更新`);
      renderDetail();
      return;
    }
    if (e.type !== 'pointercancel' && !mouse.moved) {
      const rect = canvas.getBoundingClientRect();
      handleClick(e.clientX - rect.left, e.clientY - rect.top);
    }
  }
  window.addEventListener('pointerup', finishPointer);
  window.addEventListener('pointercancel', finishPointer);

  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    zoomAt(e.offsetX, e.offsetY, e.deltaY > 0 ? 0.87 : 1.15);
  }, { passive: false });

  canvas.addEventListener('pointerleave', () => {
    App.hover = null;
    el.tooltip.classList.remove('show');
  });

  $('zoomIn').addEventListener('click', () => zoomAt(W / 2, H / 2, 1.22));
  $('zoomOut').addEventListener('click', () => zoomAt(W / 2, H / 2, 0.82));
  $('zoomFit').addEventListener('click', () => (App.mode === 'chart' ? fitChart() : fitView()));
}

/* ---------------- 挑战 ---------------- */
function renderChallenges() {
  el.challengeList.innerHTML = '';
  for (const c of CHALLENGES) {
    const d = document.createElement('div');
    d.className = 'lineItem' + (App.challenge === c.id ? ' active' : '');
    d.dataset.id = c.id;
    d.innerHTML = `<span class="lineChip" style="background:#2b5f9e;font-size:9px">${c.name.slice(0, 1)}</span>
      <span class="nm" style="flex:1">${c.name}<span style="display:block;font-size:10px;color:var(--dim);font-weight:400;margin-top:2px">${c.desc}</span></span>`;
    d.addEventListener('click', () => selectChallenge(c));
    el.challengeList.appendChild(d);
  }
}
function selectChallenge(c) {
  App.challenge = c.id;
  renderChallenges();
  $('simDur').value = c.dur;
  $('simDurVal').textContent = c.dur.toFixed(1) + 'h';
  $('simDem').value = c.demand;
  $('simDemVal').textContent = c.demand + '%';
  setMode('sim');
  toast(`已选择挑战：${c.name}`);
}

/* ---------------- 仿真控制 ---------------- */
$('simDur').addEventListener('input', () => { $('simDurVal').textContent = (+$('simDur').value).toFixed(1) + 'h'; });
$('simDem').addEventListener('input', () => { $('simDemVal').textContent = $('simDem').value + '%'; });

function startRun() {
  if (App.sim && App.sim.running) { toast('仿真正在进行'); return; }
  const duration = +$('simDur').value;
  const demand = +$('simDem').value / 100;
  startSim({ duration, demand });
  App.report = null;
  App.reportShown = false;
  $('simIdle').style.display = 'none';
  $('simRunning').style.display = 'block';
  $('livePanel').classList.add('show');
  setMode('sim');
  App.sim.paused = false;
  el.footPlay.textContent = '⏸';
  App.dirty = true;
  toast('仿真开始 · 07:00 早高峰');
}
$('btnStartSim').addEventListener('click', startRun);

function stopRun(showCard = true) {
  const sim = App.sim;
  if (!sim) return;
  if (sim.running) finishSim(sim);
  $('simIdle').style.display = 'block';
  $('simRunning').style.display = 'none';
  el.footPlay.textContent = '▶';
  App.dirty = true;
  if (showCard) showReport();
}
$('btnStopSim').addEventListener('click', () => stopRun(true));

$('speedRow').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  for (const x of $('speedRow').children) x.classList.remove('active');
  b.classList.add('active');
  if (App.sim) App.sim.speed = +b.dataset.speed;
});

el.footPlay.addEventListener('click', () => {
  const sim = App.sim;
  if (!sim) { setMode('sim'); return; }
  if (!sim.running) { if (App.report) showReport(); return; }
  sim.paused = !sim.paused;
  el.footPlay.textContent = sim.paused ? '▶' : '⏸';
});

/* ---------------- 成绩单 ---------------- */
function showReport() {
  const r = App.report;
  if (!r) { toast('还没有可用的仿真结果'); return; }
  const pct = x => (x * 100).toFixed(0) + '%';
  const lineRows = r.lines.slice(0, 5).map(l => {
    const rate = Math.min(1, l.loadRate);
    const col = rate > 0.9 ? '#ff5f74' : rate > 0.7 ? '#ffb545' : '#3ad99b';
    return `<div class="liveRow">
      <span class="nm" style="width:74px;color:${l.color}">${l.name}</span>
      <span class="liveBar"><i style="width:${Math.round(rate * 100)}%;background:${col}"></i></span>
      <span class="pv">${Math.round(rate * 100)}%</span>
    </div>`;
  }).join('');
  const advices = makeAdvice(r).map(t => `<li>${t}</li>`).join('');
  let challengeLine = '';
  if (r.challenge) {
    const c = CHALLENGES.find(x => x.id === r.challenge);
    const ok = checkGoal(r, c);
    challengeLine = `<div class="statCard" style="grid-column:1/-1;margin-bottom:10px">
      <div class="k">挑战 · ${c.name}</div>
      <div class="v" style="font-size:13px;color:${ok ? '#3ad99b' : '#ffb545'}">${ok ? '✓ 目标达成' : '未达成 · ' + c.desc}</div></div>`;
  }
  openDialog(`
    <h3>早高峰运行报告</h3>
    <p>${fmtClock(r.finishAt)} 收班 · 有效样本 ${r.done.toLocaleString()} 人 · 生成需求 ${r.gen.toLocaleString()} 人</p>
    <div class="grade">
      <div class="gradeBig ${r.grade.grade}">${r.grade.grade}</div>
      <div class="gradeMeta">
        <div class="t">综合评分 ${r.grade.score} / 100</div>
        <div class="d">平均门到门通勤 ${r.avg.toFixed(1)} 分钟 · 平均换乘 ${r.trRate.toFixed(2)} 次<br>
        需求流失率 ${pct(r.lostRate)} · 平均候车 ${r.wait.toFixed(1)} 分钟</div>
      </div>
    </div>
    <div class="metricGrid">
      ${challengeLine}
      <div class="statCard"><div class="k">完成行程</div><div class="v good">${r.done.toLocaleString()}</div></div>
      <div class="statCard"><div class="k">流失人数</div><div class="v ${r.lostRate > 0.03 ? 'bad' : 'warn'}">${r.lost.toLocaleString()}</div></div>
      <div class="statCard"><div class="k">运营时长</div><div class="v">${(r.duration / 60).toFixed(1)}h</div></div>
    </div>
    <div class="block" style="padding:0;border:0;margin-bottom:10px">
      <h2 style="margin-bottom:6px">线路断面负荷 TOP5</h2>
      ${lineRows}
    </div>
    <div class="block" style="padding:0;border:0;margin-bottom:12px">
      <h2 style="margin-bottom:6px">调度建议</h2>
      <ul class="adviceList">${advices}</ul>
    </div>
    <div class="dialogFoot">
      <button class="btn ghost" data-act="close">关闭</button>
      <button class="btn primary" data-act="again">调整后再跑</button>
    </div>`, root => {
    root.querySelector('[data-act=close]').addEventListener('click', closeDialog);
    root.querySelector('[data-act=again]').addEventListener('click', () => { closeDialog(); setMode('edit'); });
  });
}
function pct(x) { return (x * 100).toFixed(1) + '%'; }

function makeAdvice(r) {
  const out = [];
  const worst = r.lines[0];
  if (worst && worst.loadRate > 0.9) {
    const target = Math.max(90, Math.round(worst.headway * worst.cap / (worst.peak * 1.15) / 5) * 5);
    out.push(`<b>${worst.name}</b> 断面满载率 ${(worst.loadRate * 100).toFixed(0)}%，是全网最大瓶颈，建议发车间隔 ${worst.headway}s → ${target}s，或改用大编组。`);
  }
  if (r.avg > 48) out.push(`平均通勤 ${r.avg.toFixed(0)} 分钟偏高，在主要居住区（桥北、江宁、仙林）与就业中心之间补一条<b>直达或大站快线</b>收益最大。`);
  else if (r.avg > 42) out.push(`平均通勤 ${r.avg.toFixed(0)} 分钟仍有压缩空间，可对换乘量最大的 2-3 个站做<b>同台换乘</b>改造。`);
  if (r.trRate > 1.5) out.push('换乘率偏高，说明线网以放射结构为主、缺少斜向连接，建议增加<b>切向线路</b>减少绕行。');
  if (r.lostRate > 0.02) out.push(`${pct(r.lostRate)} 的乘客因满载或限流放弃出行，优先给最挤线路<b>加密班次</b>，其次扩建站台。`);
  if (r.hot && r.hot[0] && r.hot[0].board > 260) out.push(`<b>${r.hot[0].name}</b> 是全网最繁忙车站（上车 ${r.hot[0].board} 人次），建议加密接驳、增开进站闸机。`);
  if (!out.length) out.push('各项指标健康，可以挑战更高客流强度或更紧的预算约束。');
  return out;
}

function checkGoal(r, c) {
  if (!c || !c.goal) return true;
  const g = c.goal;
  if (g.avg && r.avg > g.avg) return false;
  if (g.lostRate && r.lostRate > g.lostRate) return false;
  if (g.od) {
    const sim = App.sim;
    const ag = sim && sim.odAgg ? sim.odAgg.get(g.od[0] + '|' + g.od[1]) : null;
    if (!ag || !ag.n) return false;
    return ag.sum / ag.n <= g.odMax;
  }
  if (g.minNewStations && App.newStations < g.minNewStations) return false;
  return true;
}

/* ---------------- 实时 UI 同步 ---------------- */
let uiTick = 0, lastListRefresh = 0;
function syncUI() {
  const sim = App.sim;
  const now = performance.now();
  if (sim) {
    el.hudClock.textContent = fmtClock(sim.t);
    el.hudFlow.innerHTML = `${sim.active.toLocaleString()}<small>人</small>`;
    const st = sim.stats;
    const avg = st.samples ? st.totalTime / st.samples : 0;
    el.hudAvg.textContent = avg ? avg.toFixed(1) + '′' : '—';
    $('lvDone').textContent = st.done.toLocaleString();
    $('lvAvg').textContent = avg ? avg.toFixed(1) + '′' : '—';
    $('lvTransfer').textContent = st.samples ? (st.transfers / st.samples).toFixed(2) : '—';
    $('lvLost').textContent = st.lost.toLocaleString();
    const tr = st.gen ? st.lost / st.gen : 0;
    $('lvLost').className = 'v ' + (tr > 0.03 ? 'bad' : tr > 0.01 ? 'warn' : '');
    $('lvOntime').textContent = sim.trains.length ? Math.min(100, 100 - (st.lost / Math.max(1, st.gen)) * 400).toFixed(0) + '%' : '—';

    // 最挤站台
    const hot = [];
    for (const [id, ss] of sim.stationStats) if (ss.queue > 0) hot.push({ name: App.stations.get(id)?.name, q: ss.queue });
    hot.sort((a, b) => b.q - a.q);
    $('lvHot').textContent = hot[0] ? `${hot[0].name} ${hot[0].q}人` : '—';
    $('hotList').innerHTML = hot.slice(0, 5).map(h => {
      const ratio = Math.min(1, h.q / K.PLATFORM_CAP);
      const col = ratio > 0.7 ? '#ff5f74' : ratio > 0.4 ? '#ffb545' : '#3ad99b';
      return `<div class="liveRow"><span class="nm">${h.name || ''}</span>
        <span class="liveBar"><i style="width:${Math.round(ratio * 100)}%;background:${col}"></i></span>
        <span class="pv">${h.q}</span></div>`;
    }).join('');

    // 线路实时
    if (now - lastListRefresh > 1200) {
      lastListRefresh = now;
      const rows = App.lines.filter(l => l.enabled).map(l => {
        const capEff = l.capEff || Math.max(6, Math.round(l.cap * K.CAP_RATIO));
        const avgLoad = l.loadCount ? l.loadSum / l.loadCount : 0;
        const rate = Math.min(1, avgLoad / capEff);
        const col = rate > 0.9 ? '#ff5f74' : rate > 0.7 ? '#ffb545' : '#3ad99b';
        return `<div class="liveRow"><span class="nm" style="color:${l.color}">${l.name}</span>
          <span class="liveBar"><i style="width:${Math.round(rate * 100)}%;background:${col}"></i></span>
          <span class="pv">${Math.round(rate * 100)}%</span></div>`;
      }).join('');
      $('liveLines').innerHTML = rows;
      renderLineList();
      renderDetail();
    }

    // 进度
    const prog = Math.min(100, Math.max(0, (sim.t - sim.t0) / (sim.tEnd - sim.t0) * 100));
    el.tlFill.style.width = prog + '%';
    el.tlMark.style.left = Math.min(97.5, Math.max(2.5, prog)) + '%';

    // 事件
    if (sim.events.length) {
      const ev = sim.events[sim.events.length - 1];
      el.eventLog.innerHTML = `<b>${fmtClock(ev.t)}</b> ${ev.msg}`;
    }
    el.tlFill.style.opacity = sim.running ? 1 : 0.5;
    el.tlRange.textContent = fmtClock(sim.t0) + ' — ' + fmtClock(sim.tEnd);

    // 仿真自然结束 → 自动收起并弹出成绩单
    if (!sim.running && sim.ended && !App.reportShown) {
      App.reportShown = true;
      $('simIdle').style.display = 'block';
      $('simRunning').style.display = 'none';
      el.footPlay.textContent = '▶';
      showReport();
    }
  } else {
    el.hudClock.textContent = '07:00';
    el.hudFlow.innerHTML = `0<small>人</small>`;
    el.hudAvg.textContent = '—';
    el.tlRange.textContent = '07:00 — 09:00';
  }
}

/* ---------------- 本地自动存档 ---------------- */
const SAVE_VER = 3;           // 线网数据结构版本，升级会作废旧存档
// 内置线网指纹：改动 LINE_DEFS（例如新增线路）后旧存档自动作废，避免覆盖新数据
const DATA_SIG = LINE_DEFS.map(l => l.id + ':' + l.stations.length).join('|');
let lastSnapStr = '';

function loadSave() {
  try {
    const raw = localStorage.getItem(SAVE_KEY) ?? (typeof LEGACY_SAVE_KEY !== 'undefined' ? localStorage.getItem(LEGACY_SAVE_KEY) : null);
    if (!raw) return null;
    const j = JSON.parse(raw);
    if (!j || j.ver !== SAVE_VER || j.sig !== DATA_SIG) return null;
    if (!j.snap || !Array.isArray(j.snap.lines) || !Array.isArray(j.snap.stations)) return null;
    if (!j.snap.stations.length) return null;
    return j;
  } catch (e) { return null; }
}

function clearSave() {
  // 保留空值，重置后不再回读旧的共用存档。
  try { localStorage.setItem(SAVE_KEY, ''); } catch (e) {}
  try { lastSnapStr = JSON.stringify(snapshot()); } catch (e) { lastSnapStr = ''; }
  const badge = document.getElementById('hudSave');
  if (badge) { badge.textContent = '—'; badge.className = 'v'; }
}

function saveNow(force) {
  const badge = document.getElementById('hudSave');
  let snapStr;
  try { snapStr = JSON.stringify(snapshot()); } catch (e) { return; }
  if (!force && snapStr === lastSnapStr) return;
  try {
    localStorage.setItem(SAVE_KEY, JSON.stringify({ ver: SAVE_VER, sig: DATA_SIG, t: Date.now(), snap: JSON.parse(snapStr), track: App.trackOff || {} }));
    lastSnapStr = snapStr;
    if (badge) {
      const d = new Date();
      badge.textContent = String(d.getHours()).padStart(2, '0') + ':' + String(d.getMinutes()).padStart(2, '0');
      badge.className = 'v ok';
      badge.title = `已保存 ${d.toLocaleTimeString('zh-CN', { hour12: false })}`;
    }
  } catch (e) {
    if (badge) { badge.textContent = '不可用'; badge.className = 'v bad'; }
  }
}

function startAutoSave() {
  saveNow(true);
  setInterval(() => {
    if (App.sim && App.sim.running) return;   // 仿真运行时不写盘
    saveNow(false);
  }, 2500);
  window.addEventListener('beforeunload', () => saveNow(true));
}

/* ---------------- 换乘方式面板 ---------------- */
const XFER_ORDER = ['same', 'node', 'pass', 'virtual', 'newx'];
function renderXfers() {
  if (!el.xfList) return;
  const XFDB = (typeof XFER !== 'undefined') ? XFER : {};
  const XFTY = (typeof XFER_TYPES !== 'undefined' && XFER_TYPES) ? XFER_TYPES : {
    same: { name: '同台换乘', color: '#ffc247' }, node: { name: '节点换乘', color: '#28d7c0' },
    pass: { name: '通道换乘', color: '#4da3ff' }, virtual: { name: '虚拟换乘', color: '#c08cff' },
    newx: { name: '规划换乘', color: '#8fa3bb' }
  };
  const items = [];
  for (const [id, st] of App.stations) {
    if (!st.lines || st.lines.length < 2) continue;
    const xf = XFDB[st.name];
    const shortOf = x => { const L = getLine(x); return L ? L.short : x; };
    items.push({
      id, n: st.name, t: xf ? xf.t : 'newx',
      l: xf ? xf.l : st.lines.map(shortOf).join('·'),
      b: !!(xf && xf.b), d: xf ? xf.d : '规划线网新增换乘站'
    });
  }
  items.sort((a, b) => XFER_ORDER.indexOf(a.t) - XFER_ORDER.indexOf(b.t)
    || b.b - a.b || a.n.localeCompare(b.n, 'zh'));
  const cnt = t => items.filter(i => i.t === t).length;
  if (el.xfBadge) el.xfBadge.textContent = items.length + ' 站';
  if (el.xfStats) {
    el.xfStats.innerHTML = XFER_ORDER.filter(t => cnt(t) > 0).map(t => {
      const ty = XFTY[t];
      return `<div><b style="color:${ty.color}">${cnt(t)}</b>${ty.name.replace('换乘', '')}</div>`;
    }).join('');
  }
  el.xfList.innerHTML = items.map(i => {
    const ty = XFTY[i.t];
    return `<div class="xfItem" data-sid="${i.id}" data-nm="${i.n}" title="${i.n} · ${ty.name}${i.b ? '（在建线路）' : ''}：${i.d}">`
      + `<i style="background:${ty.color}"></i><span class="nm">${i.n}</span>`
      + (i.b ? '<span class="bld">在建</span>' : '')
      + `<span class="ln">${i.l}</span></div>`;
  }).join('');
}
function locateStation(sid) {
  const st = App.stations.get(sid);
  if (!st) return;
  App.cam.x = st.x; App.cam.y = st.y;
  App.cam.s = Math.max(App.cam.s, 46);
  App.hover = sid; App.dirty = true;
}

/* ---------------- 初始化 ---------------- */
function init() {
  buildWorld();
  const saved = loadSave();
  if (saved) {
    try {
      restore(saved.snap);
      App.trackOff = saved.track || {};
      lastSnapStr = JSON.stringify(saved.snap);
    } catch (e) {}
  }
  resizeCanvas();
  fitCity();
  renderLineList();
  renderChallenges();
  renderXfers();
  if (el.xfList) {
    el.xfList.addEventListener('click', ev => {
      const it = ev.target.closest && ev.target.closest('.xfItem');
      if (!it) return;
      locateStation(it.dataset.sid);
      toast(`定位到 ${it.dataset.nm}`);
    });
  }
  if (el.eventLog) {
    const inBuild = App.lines.filter(l => BUILDING_IDS.includes(l.id)).length;
    el.eventLog.innerHTML = `<b>系统就绪</b> · 线上 ${App.lines.length} 条线路` + (inBuild ? ` · ${inBuild} 条在建` : '');
  }
  setMode('view');
  syncBudget();
  bindMap();
  setTool('station');
  startAutoSave();
  if (saved) {
    const mins = Math.round((Date.now() - (saved.t || Date.now())) / 60000);
    const when = mins < 1 ? '刚刚' : mins < 60 ? `${mins} 分钟前` : `${Math.round(mins / 60)} 小时前`;
    const modified = (saved.snap.stations || []).some(s => s.custom) ||
      (saved.snap.lines || []).some(l => l.custom) || (saved.snap.spent || 0) > 0;
    const badge = document.getElementById('hudSave');
    if (badge) {
      const d = new Date(saved.t || Date.now());
      badge.textContent = modified ? '已恢复' : String(d.getHours()).padStart(2, '0') + ':' + String(d.getMinutes()).padStart(2, '0');
      badge.className = 'v ok';
      badge.title = `上次保存 ${when} · ${saved.snap.lines.length} 条线 / ${saved.snap.stations.length} 站`;
    }
    if (modified) toast(`已恢复上次规划（${when}）`);
  }
  window.addEventListener('resize', () => { resizeCanvas(); });
  window.addEventListener('keydown', e => {
    if (e.key === 'Escape') {
      if (el.modal.classList.contains('show')) { closeDialog(); return; }
      if (App.editingLine && App.mode === 'edit') { App.editingLine = null; App.drawAnchor = null; renderEditSelect(); toast('已结束画线'); }
    }
    if (e.key === ' ' && App.sim) {
      e.preventDefault();
      if (App.sim.running) { App.sim.paused = !App.sim.paused; el.footPlay.textContent = App.sim.paused ? '▶' : '⏸'; }
    }
  });
  requestAnimationFrame(loop);
  // 调试 / 二次开发接口
  window.MetroLab = { App, K, Chart, computeChart, fitChart, chartExport, startSim, stepSim, finishSim, syncUI, setMode, startRun,
    getLine, buildWorld, rebuildGraph, fitView, fitCity, showReport };
}

if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
else init();
