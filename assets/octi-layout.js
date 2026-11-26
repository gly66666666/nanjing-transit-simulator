/* OCTI-Lite: 地铁图布局（基于 Bast et al. EuroVis 2020 思路，独立编写）。
   核心：带行进方向的网格搜索和按线路顺序布站。
   硬约束：禁止锐角转弯（转弯内角 ≥90°，即方向差 ≤90°=2步）。
   软偏好：水平/竖直段代价更低（主干尽可能横平竖直），45°斜段允许但略贵。
   至多一个换乘站的单支非环线采用直线。倒角在绘制层处理。
   零依赖，纯 JS。

   方向编号（顺时针）：0=E,1=SE,2=S,3=SW,4=W,5=NW,6=N,7=NE
   ============================================================ */

const DIRV = [[1,0],[1,1],[0,1],[-1,1],[-1,0],[-1,-1],[0,-1],[1,-1]];

// 转弯代价（以 45° 步长为索引）：0=直行(免费), 1=135°内角(钝角), 2=90°内角
// 方向差 3 步(45°内角=锐角)与 4 步(掉头)一律禁止 → 硬约束无锐角。
const TURN_COST = [0, 2.2, 3.0];   // 135°转弯比90°稍便宜（更平滑）
function turnSteps(dirA, dirB) {
  let d = Math.abs(dirB - dirA);
  if (d > 4) d = 8 - d;
  return d; // 0=直行,1=45°方向差(135°内角),2=90°(90°内角),3=锐角(禁),4=掉头(禁)
}

class OctiQueue {
  constructor() {
    this.items = [];
  }
  push(state, score) {
    const items = this.items;
    let index = items.length;
    while (index > 0) {
      const parent = (index - 1) >> 1;
      if (items[parent].score <= score) break;
      items[index] = items[parent];
      index = parent;
    }
    items[index] = { state, score };
  }
  pop() {
    const items = this.items;
    if (!items.length) return null;
    const first = items[0];
    const last = items.pop();
    if (!items.length) return first;
    let index = 0;
    while (2 * index + 1 < items.length) {
      let child = 2 * index + 1;
      if (child + 1 < items.length && items[child + 1].score < items[child].score) child++;
      if (items[child].score >= last.score) break;
      items[index] = items[child];
      index = child;
    }
    items[index] = last;
    return first;
  }
}

function octiCell(point) {
  return point.x + ',' + point.y;
}

function octiHeading(from, to) {
  return octSnap(to.x - from.x, to.y - from.y);
}

class OctiGrid {
  constructor(positions) {
    const bounds = [...positions.values()];
    this.left = Math.min(...bounds.map(p => p.x)) - 14;
    this.top = Math.min(...bounds.map(p => p.y)) - 14;
    this.width = Math.max(...bounds.map(p => p.x)) - this.left + 15;
    this.height = Math.max(...bounds.map(p => p.y)) - this.top + 15;
    const cells = this.width * this.height;
    this.blocked = new Uint8Array(cells);
    this.load = new Uint16Array(cells);
    this.tracks = new Uint8Array(cells * 4);
    this.stationEdges = new Uint8Array(cells * 4);
    this.g = new Float64Array(cells * 8);
    this.parent = new Int32Array(cells * 8);
    this.seen = new Uint32Array(cells * 8);
    this.committed = new Uint32Array(cells * 8);
    this.search = 0;
    for (const p of bounds) this.blocked[this.cell(p.x, p.y)] = 1;
  }
  cell(x, y) {
    return (y - this.top) * this.width + x - this.left;
  }
  point(cell) {
    return { x: this.left + cell % this.width, y: this.top + Math.floor(cell / this.width) };
  }
  edge(cell, next, heading) {
    return (heading < 4 ? cell : next) * 4 + heading % 4;
  }
  step(a, b) {
    return this.edge(this.cell(a.x, a.y), this.cell(b.x, b.y), octiHeading(a, b));
  }
  reserve(path, marks = []) {
    for (const p of path.slice(1, -1)) this.load[this.cell(p.x, p.y)]++;
    for (let i = 1; i < path.length; i++) this.tracks[this.step(path[i - 1], path[i])] = 1;
    for (const mark of marks) this.stationEdges[mark.edge] = 1;
  }

  // 方向只在实际走一步时改变。同格连续旋转会绕过转角约束。
  route(from, to, incoming, nextHeading, closeHeading, trunk, exclusive) {
    const start = this.cell(from.x, from.y), goal = this.cell(to.x, to.y);
    const queue = new OctiQueue(), search = ++this.search;
    const diag = trunk ? 1.88 : 1.57;
    const h = (x, y) => {
      const dx = Math.abs(x - to.x), dy = Math.abs(y - to.y);
      return Math.max(dx, dy) + (diag - 1) * Math.min(dx, dy);
    };
    const advance = (x, y, cell, heading, cost, state) => {
      const px = x - this.left, py = y - this.top;
      for (let d = 0; d < DIRV.length; d++) {
        const turn = heading == null ? 0 : turnSteps(heading, d);
        if (turn > 2) continue;
        const [dx, dy] = DIRV[d];
        const nx = px + dx, ny = py + dy;
        if (nx < 0 || nx >= this.width || ny < 0 || ny >= this.height) continue;
        const next = cell + dy * this.width + dx;
        if (next === start || (next !== goal && this.blocked[next])) continue;
        if (next === goal && closeHeading != null && turnSteps(d, closeHeading) > 2) continue;
        const edge = this.edge(cell, next, d);
        if (this.stationEdges[edge] || (exclusive && this.tracks[edge])) continue;
        const nextState = next * 8 + d;
        if (this.committed[nextState] === search) continue;
        const arrival = next === goal && nextHeading != null ? turnSteps(d, nextHeading) * 1.1 : 0;
        const candidate = cost + (dx && dy ? diag : 1) + TURN_COST[turn] +
          Math.min(5, this.load[next]) * 1.2 + this.tracks[edge] * 0.9 + arrival;
        if (this.seen[nextState] === search && candidate >= this.g[nextState]) continue;
        this.seen[nextState] = search;
        this.g[nextState] = candidate;
        this.parent[nextState] = state;
        queue.push(nextState, candidate + h(x + dx, y + dy));
      }
    };
    advance(from.x, from.y, start, incoming, 0, -1);
    let item;
    while ((item = queue.pop())) {
      const state = item.state;
      if (this.committed[state] === search) continue;
      this.committed[state] = search;
      const cell = Math.floor(state / 8);
      if (cell === goal) {
        const path = [];
        for (let p = state; p !== -1; p = this.parent[p]) path.push(this.point(Math.floor(p / 8)));
        path.push(from);
        return path.reverse();
      }
      const { x, y } = this.point(cell);
      advance(x, y, cell, state % 8, this.g[state], state);
    }
    return null;
  }
}

function octSnap(dx, dy) {
  if (!dx && !dy) return 0;
  const k = ((Math.round(Math.atan2(dy, dx) / (Math.PI/4)) % 8) + 8) % 8;
  return k;
}

function networkComponents(input) {
  const groups = new Map();
  const parent = new Map();
  function root(id) {
    if (!parent.has(id)) parent.set(id, id);
    let top = id;
    while (parent.get(top) !== top) top = parent.get(top);
    while (parent.get(id) !== top) {
      const next = parent.get(id);
      parent.set(id, top);
      id = next;
    }
    return top;
  }
  const lines = input.lines.map(line => ({
    ...line,
    arms: line.arms.map(arm => arm.filter((id, i) => i === 0 || id !== arm[i - 1]))
      .filter(arm => arm.length > 1)
  })).filter(line => line.arms.length);
  for (const line of lines) {
    const station = line.arms[0][0];
    for (const id of line.arms.flat()) {
      if (!Number.isFinite(input.stations[id]?.x) || !Number.isFinite(input.stations[id]?.y)) {
        throw new Error('站点坐标无效：' + id);
      }
      parent.set(root(id), root(station));
    }
  }
  for (const line of lines) {
    const key = root(line.arms[0][0]);
    if (!groups.has(key)) groups.set(key, { lines: [], ids: new Set() });
    const group = groups.get(key);
    group.lines.push(line);
    for (const arm of line.arms) for (const id of arm) group.ids.add(id);
  }
  return [...groups.values()];
}

function routeBounds(routes) {
  const box = { minX: Infinity, minY: Infinity, maxX: -Infinity, maxY: -Infinity };
  for (const route of routes) for (const p of route.points) {
    box.minX = Math.min(box.minX, p.x); box.maxX = Math.max(box.maxX, p.x);
    box.minY = Math.min(box.minY, p.y); box.maxY = Math.max(box.maxY, p.y);
  }
  return box;
}

// 连通分量独立求解。摆放时保留大致地理方位，有换乘关系的线路始终在同一张局部图。
function octiLayout(input, opt = {}) {
  const outPos = Object.create(null), routes = [], routed = [], pos = new Map();
  let turns = 0, straights = 0, retries = 0, keyNodes = 0, edges = 0;
  let collisions = 0, acuteTurns = 0, octViolations = 0;
  const components = networkComponents(input).sort((a, b) => b.ids.size - a.ids.size);
  const parts = components.map(group => {
    const { ids, lines } = group;
    const stations = Object.create(null);
    let x = 0, y = 0;
    for (const id of ids) {
      const point = input.stations[id];
      stations[id] = point;
      x += point.x; y += point.y;
    }
    const radius = opt.radius ?? Math.max(46, Math.min(250, Math.round(28 + Math.sqrt(ids.size) * 4.5)));
    const settings = { pow: 0.85, keyPasses: 14, ...opt, radius };
    let local;
    for (const spacing of [2, 3, 4]) {
      try {
        local = layoutConnectedNetwork({ lines, stations }, { ...settings, spacing });
        break;
      } catch (error) {
        if (spacing === 4 || error.name !== 'OctiRoutingError') throw error;
        retries++;
      }
    }
    const box = routeBounds(local.routes);
    return {
      x: x / ids.size, y: y / ids.size, box, local,
      w: Math.max(1, Math.ceil(box.maxX - box.minX)), h: Math.max(1, Math.ceil(box.maxY - box.minY))
    };
  });
  if (parts.length) {
    const gap = 12;
    const extent = Math.max(1, Math.max(...parts.map(p => p.x)) - Math.min(...parts.map(p => p.x)),
      Math.max(...parts.map(p => p.y)) - Math.min(...parts.map(p => p.y)));
    const size = Math.sqrt(parts.reduce((sum, p) => sum + (p.w + gap) * (p.h + gap), 0));
    const projection = size / extent;
    const origin = parts[0], placed = [];
    for (const p of parts) {
      const targetX = Math.round((p.x - origin.x) * projection - p.w / 2);
      const targetY = Math.round((p.y - origin.y) * projection - p.h / 2);
      const xs = [targetX], ys = [targetY];
      for (const box of placed) {
        xs.push(box.x - p.w - gap, box.x + box.w + gap);
        ys.push(box.y - p.h - gap, box.y + box.h + gap);
      }
      let best;
      for (const x of xs) for (const y of ys) {
        const score = (x - targetX) ** 2 + (y - targetY) ** 2;
        if (best && best.score <= score) continue;
        if (placed.some(b => x < b.x + b.w + gap && x + p.w + gap > b.x &&
          y < b.y + b.h + gap && y + p.h + gap > b.y)) continue;
        best = { x, y, score };
      }
      placed.push({ x: best.x, y: best.y, w: p.w, h: p.h });
      const dx = Math.round(best.x - p.box.minX), dy = Math.round(best.y - p.box.minY);
      const move = point => ({ ...point, x: point.x + dx, y: point.y + dy });
      for (const [id, point] of Object.entries(p.local.outPos)) outPos[id] = move(point);
      for (const [id, point] of p.local.pos) pos.set(id, move(point));
      for (const route of p.local.routes) routes.push({ ...route, points: route.points.map(move) });
      for (const edge of p.local.routed) routed.push({ ...edge, path: edge.path.map(move) });
      const m = p.local.metrics;
      keyNodes += m.keyNodes; edges += m.edges;
      turns += m.totalCorners; straights += m.straightRate * m.totalCorners;
      collisions += m.collisions; acuteTurns += m.acuteTurns; octViolations += m.octViolations;
    }
  }
  return { pos, outPos, routed, failed: [], routes, bounds: routes.length ? routeBounds(routes) : null,
    metrics: { components: parts.length, retries, keyNodes, edges, routed: edges, failed: 0, collisions,
      acuteTurns, octViolations, totalCorners: turns, straightRate: turns ? straights / turns : 1 } };
}

class OctiRoutingError extends Error {
  name = 'OctiRoutingError';
}

function layoutConnectedNetwork(input, opt) {

  const GRID_PAD = opt.pad ?? 3;

  let seed = opt.seed ?? 20261124;
  const rnd = () => { seed=(seed*1664525+1013904223)>>>0; return seed/4294967296; };

  const lines = input.lines.filter(line => line.arms?.some(arm => arm.length > 1));
  const stData = input.stations || {};

  // ---------- 1. deg-2 收缩：关键节点 = 换乘站 + 端点 ----------
  const use = new Map(), services = new Map(), terminals = new Set();
  for (const line of lines) for (const arm of line.arms) {
    if (arm.length < 2) continue;
    terminals.add(arm[0]);
    terminals.add(arm.at(-1));
    for (const station of arm) {
      use.set(station, (use.get(station) || 0) + 1);
      if (!services.has(station)) services.set(station, new Set());
      services.get(station).add(line.id);
    }
  }
  const isKey = station => terminals.has(station) || use.get(station) > 1;
  if (!use.size) return { pos: new Map(), outPos: {}, routes: [], metrics: { octViolations: 0, acuteTurns: 0, collisions: 0, straightRate: 1, totalCorners: 0 } };
  // 换乘点很少的闭环也需要多个锚点，否则首尾同一站会被当成零长线段。
  for (const line of lines) for (const arm of line.arms) {
    if (arm.length < 3 || arm[0] !== arm.at(-1)) continue;
    const ring = arm.slice(0, -1), count = ring.length;
    const chosen = ring.flatMap((id, i) => isKey(id) ? [i] : []);
    const minimum = Math.min(3, new Set(ring).size);
    while (chosen.length < minimum) {
      let best = -1, separation = -1;
      for (const [i, id] of ring.entries()) {
        if (isKey(id)) continue;
        const space = Math.min(...chosen.map(j => Math.min(Math.abs(i - j), count - Math.abs(i - j))));
        if (space > separation) {
          best = i;
          separation = space;
        }
      }
      if (best < 0) break;
      terminals.add(ring[best]);
      chosen.push(best);
    }
  }
  const keyStations = [...use.keys()].filter(isKey);

  // ---------- 2. 关键节点吸附到网格 ----------
  let minX=1e18,maxX=-1e18,minY=1e18,maxY=-1e18;
  for (const s of keyStations) {
    const p = stData[s]; if (!p) continue;
    minX=Math.min(minX,p.x);maxX=Math.max(maxX,p.x);
    minY=Math.min(minY,p.y);maxY=Math.max(maxY,p.y);
  }
  const cx=(minX+maxX)/2, cy=(minY+maxY)/2;
  const span=Math.max(maxX-minX, maxY-minY)||1;
  const R = opt.radius ?? 90;  // 网格半径（格）
  const W = 2*R+1+GRID_PAD*2, H = W;
  const mid = W/2;
  // 径向压缩（官方挂图做法）：远处郊区按幂函数拉近，主城相对放大
  const POW = opt.pow ?? 1.0;
  const keyPts = keyStations.map(s=>({dx:stData[s].x-cx, dy:stData[s].y-cy}));
  const maxR = Math.max(...keyPts.map(p=>Math.hypot(p.dx,p.dy))) || 1;
  const warp = p => {
    const r=Math.hypot(p.dx,p.dy);
    const f = r>0.01 ? (maxR*Math.pow(r/maxR, POW))/r : 0;
    return {x:p.dx*f, y:p.dy*f};
  };
  const warped = new Map(keyStations.map((s,i)=>{ const w=warp(keyPts[i]); const rr=Math.hypot(w.x,w.y); const boost=1+0.30*Math.exp(-Math.pow(rr/(maxR*0.42),2)); return [s,{x:w.x*boost,y:w.y*boost}]; }));
  const gx = s => Math.round(mid + (warped.get(s).x/span)*R*1.5);
  const gy = s => Math.round(mid + (warped.get(s).y/span)*R*1.2);
  // 相邻关键站若夹了很多普通站，需要更长的路径 → 调整吸附目标距离

  // 去重合（螺旋）——按真实方位吸附，不做间距推开（避免共享点被反复推到边界）
  const occupied=new Set();
  const pos=new Map();
  for (const s of keyStations) {
    let x=gx(s), y=gy(s);
    for (let rad=0; rad<10; rad++) {
      let done=false;
      for (let dx=-rad;dx<=rad&&!done;dx++) for(let dy=-rad;dy<=rad&&!done;dy++) {
        if(Math.max(Math.abs(dx),Math.abs(dy))!==rad)continue;
        if(!occupied.has((x+dx)+','+(y+dy))) { x+=dx;y+=dy;done=true; }
      }
      if(done)break;
    }
    occupied.add(x+','+y);
    pos.set(s,{x,y});
  }
  // 初始吸附后修正间距：相邻关键站必须留出中间普通站的格点
  // （与 3b 的 spacingOK 同约束，避免初始就违规导致后续无法补救）
  {
    const nb0 = new Map();
    for (const l of lines) for (const arm of l.arms) {
      const seq = arm.filter(x => isKey(x));
      for (let k = 0; k < seq.length - 1; k++) {
        const need = Math.abs(arm.indexOf(seq[k+1]) - arm.indexOf(seq[k]));
        if (!nb0.has(seq[k])) nb0.set(seq[k], []);
        if (!nb0.has(seq[k+1])) nb0.set(seq[k+1], []);
        nb0.get(seq[k]).push([seq[k+1], need]);
        nb0.get(seq[k+1]).push([seq[k], need]);
      }
    }
    for (let iter = 0; iter < 8; iter++) {
      let fixed = 0;
      for (const [s, nbs] of nb0) {
        const P = pos.get(s); if (!P) continue;
        for (const [nb, need] of nbs) {
          const Q = pos.get(nb); if (!Q) continue;
          let d = Math.max(Math.abs(P.x-Q.x), Math.abs(P.y-Q.y));
          if (d >= need) continue;
          // 沿连线方向把 P 推远（若 P 端点则推 Q）
          const ux = d>0 ? (P.x-Q.x)/d : 1, uy = d>0 ? (P.y-Q.y)/d : 0;
          const step = need - d;
          for (let t = 0; t <= step; t++) {
            const nx = Math.round(P.x + ux*(step+t)), ny = Math.round(P.y + uy*(step+t));
            if (!occupied.has(nx+','+ny)) {
              occupied.delete(P.x+','+P.y);
              P.x=nx; P.y=ny; occupied.add(nx+','+ny); fixed++; break;
            }
          }
        }
      }
      if (!fixed) break;
    }
  }

  // ---------- 3. 线图边（收缩后） ----------
  // 对每条线的每个臂：压缩为关键站序列，相邻关键站形成一条待布线边
  const edges=[];
  const lineDeg=new Map();
  for (const l of lines) for (const arm of l.arms) {
    const seq=arm.filter(s=>isKey(s));
    for (let k=0;k<seq.length-1;k++) {
      edges.push({a:seq[k], b:seq[k+1], line:l.id, color:l.color,
        between: Math.abs(arm.indexOf(seq[k+1])-arm.indexOf(seq[k]))-1});
    }
    for (const s of seq) lineDeg.set(s,(lineDeg.get(s)||0)+1);
  }
  // 边排序：端点 line-degree 高的优先
  edges.sort((e1,e2)=>{
    const d=(e)=>Math.max(lineDeg.get(e.a)||0, lineDeg.get(e.b)||0);
    return d(e2)-d(e1);
  });

  // ---------- 3b. 换乘站位置优化：移动关键站使共线三元组最多（拐角最少） ----------
  // 用户思路：先固定换乘站骨架，再通过移动换乘站减少拐角，最后插回普通站。
  // 评分 = 共线三元组数（越大越直） - 地理偏移惩罚 - 重合惩罚。
  // 每个关键站记录所有经过它的 (prev, self, next) 上下文；移动时联合评估。
  {
    const ctxOf = new Map(); // station -> [[prev, next], ...]
    for (const l of lines) for (const arm of l.arms) {
      const seq = arm.filter(s => isKey(s));
      for (let k = 1; k < seq.length - 1; k++) {
        const s = seq[k];
        if (!ctxOf.has(s)) ctxOf.has(s) || ctxOf.set(s, []);
        ctxOf.get(s).push([seq[k - 1], seq[k + 1]]);
      }
    }
    // 占位表：位置 -> station
    const at = new Map();
    for (const [s, p] of pos) at.set(p.x + ',' + p.y, s);
    // 软评分：用“转角步数”衡量弯曲，0=完全直，1=135°钝角，2=90°直角。
    // 旧版只在“恰好共线”时 +1，导致 45° 小折弯没有代价、整条线仍像楼梯。
    const bendAt = (A, X, C) => {
      const ax = X.x - A.x, ay = X.y - A.y;
      const bx = C.x - X.x, by = C.y - X.y;
      if ((!ax && !ay) || (!bx && !by)) return 0;
      let d = Math.abs(octSnap(bx, by) - octSnap(ax, ay));
      if (d > 4) d = 8 - d;
      return d >= 3 ? 4 : d;
    };
    // 局部评分：只看受 B 移动影响的三元组；越低越直
    const scoreAt = (s, X, otherPos) => {
      let sc = 0, n = 0;
      for (const [p, q] of (ctxOf.get(s) || [])) {
        const A = otherPos(p), C = otherPos(q);
        if (!A || !C) continue;
        sc += bendAt(A, X, C); n++;
      }
      return n ? sc / n : 0;
    };
    const getPos = s => pos.get(s);
    // s 的每个相邻关键站：必须保留足够格距容纳中间普通站，否则插回时会丢站
    const keyNeighbors = new Map(); // s -> [[neighbor, minDist], ...]
    for (const l of lines) for (const arm of l.arms) {
      const seq = arm.filter(x => isKey(x));
      for (let k = 0; k < seq.length - 1; k++) {
        const between = Math.abs(arm.indexOf(seq[k+1]) - arm.indexOf(seq[k])) - 1;
        const need = between + 1;
        if (!keyNeighbors.has(seq[k])) keyNeighbors.set(seq[k], []);
        if (!keyNeighbors.has(seq[k+1])) keyNeighbors.set(seq[k+1], []);
        keyNeighbors.get(seq[k]).push([seq[k+1], need]);
        keyNeighbors.get(seq[k+1]).push([seq[k], need]);
      }
    }
    const spacingOK = (s, X) => {
      for (const [nb, need] of (keyNeighbors.get(s) || [])) {
        const Q = pos.get(nb); if (!Q) continue;
        // 八方向路径的最短格数是切比雪夫距离，不是欧氏距离
        if (Math.max(Math.abs(X.x - Q.x), Math.abs(X.y - Q.y)) < need) return false;
      }
      return true;
    };
    const OPT_PASSES = opt.keyPasses ?? 6;
    for (let pass = 0; pass < OPT_PASSES; pass++) {
      // 随机顺序，避免总是同一批站先动
      const order = [...keyStations];
      for (let i = order.length - 1; i > 0; i--) {
        const j = (rnd() * (i + 1)) | 0;
        [order[i], order[j]] = [order[j], order[i]];
      }
      let moved = 0;
      for (const s of order) {
        const ctx = ctxOf.get(s) || [];
        if (!ctx.length) continue; // 端点/孤立站不参与（移动它没有共线收益）
        const P = pos.get(s), home = { x: gx(s), y: gy(s) };
        const oldKey = P.x + ',' + P.y;
        const baseScore = scoreAt(s, P, getPos);
        let best = null, bestGain = 0.01;
        // 候选：周围 ±4 格（先近后远），且与邻居共线的方向优先
        for (let rad = 1; rad <= 8; rad++) {
          for (let dx = -rad; dx <= rad; dx++) for (let dy = -rad; dy <= rad; dy++) {
            if (Math.max(Math.abs(dx), Math.abs(dy)) !== rad) continue;
            const X = { x: P.x + dx, y: P.y + dy };
            const k = X.x + ',' + X.y;
            if (k !== oldKey && at.has(k)) continue; // 不重合
            if (!spacingOK(s, X)) continue; // 必须给中间普通站留够格点
            // 地理保真：离吸附原位越远惩罚越大（主城权重更高）
            const dist = Math.hypot(X.x - home.x, X.y - home.y);
            const gain = baseScore - scoreAt(s, X, getPos) - dist * (opt.homeWeight ?? 0.012);
            if (gain > bestGain) { bestGain = gain; best = X; }
          }
          if (best) break; // 近处有改善就不再试更远
        }
        if (best) {
          at.delete(oldKey);
          P.x = best.x; P.y = best.y;
          at.set(best.x + ',' + best.y, s);
          moved++;
        }
      }
      if (opt.verbose && pass % 2 === 0) console.error('  key-opt pass', pass, 'moved', moved);
      if (!moved) break;
    }
  }

  // ---------- 3b. 方向松弛：把关键站整体拉向“邻居—八方向”位置 ----------
  // 局部换位只能消掉个别折角；这里让整条走廊一起收敛，避免每个换乘站都拐一下。
  {
    const relax = new Map();
    const home = new Map();
    for (const s of keyStations) {
      const p = pos.get(s); if (!p) continue;
      relax.set(s, { x: p.x, y: p.y });
      home.set(s, { x: gx(s), y: gy(s) });
    }
    const nbr = new Map();
    for (const e of edges) {
      if (!relax.has(e.a) || !relax.has(e.b)) continue;
      if (!nbr.has(e.a)) nbr.set(e.a, []);
      if (!nbr.has(e.b)) nbr.set(e.b, []);
      nbr.get(e.a).push(e.b); nbr.get(e.b).push(e.a);
    }
    let step = 0.30;
    for (let it = 0; it < 90; it++) {
      const moved = [];
      for (const s of keyStations) {
        const P = relax.get(s); if (!P) continue;
        const ns = nbr.get(s) || [];
        if (!ns.length) continue;
        let tx = 0, ty = 0, c = 0;
        for (const q of ns) {
          const Q = relax.get(q); if (!Q) continue;
          const dx = Q.x - P.x, dy = Q.y - P.y;
          if (!dx && !dy) continue;
          const dir = octSnap(dx, dy);
          const len = Math.max(Math.abs(dx), Math.abs(dy), 2.4);
          tx += Q.x - DIRV[dir][0] * len;
          ty += Q.y - DIRV[dir][1] * len;
          c++;
        }
        if (!c) continue;
        const H = home.get(s);
        const ax = tx / c, ay = ty / c;
        moved.push([s, P.x + (ax - P.x) * step + (H.x - P.x) * 0.001,
                       P.y + (ay - P.y) * step + (H.y - P.y) * 0.001]);
      }
      for (const [s, x, y] of moved) { const P = relax.get(s); P.x = x; P.y = y; }
      step *= 0.98;
    }
    // 回整数格：优先保留原格，冲突时退回旧坐标，避免站点重合
    const taken = new Set([...pos.values()].map(octiCell));
    for (const station of keyStations) {
      const target = relax.get(station);
      const old = pos.get(station);
      const point = { x: Math.round(target.x), y: Math.round(target.y) };
      taken.delete(octiCell(old));
      if (!taken.has(octiCell(point))) pos.set(station, point);
      taken.add(octiCell(pos.get(station)));
    }
  }

  // 保留站点周围的进出站方向。密集换乘站逐个落位，避免被邻站堵死。
  const separated = new Set();
  const spacing = opt.spacing;
  for (const id of [...pos.keys()].sort((a, b) => use.get(b) - use.get(a))) {
    const origin = pos.get(id);
    let point;
    for (let ring = 0; !point; ring++) {
      for (let x = -ring; !point && x <= ring; x++) {
        for (let y = -ring; !point && y <= ring; y++) {
          if (Math.max(Math.abs(x), Math.abs(y)) !== ring) continue;
          const p = { x: origin.x + x, y: origin.y + y };
          if (!separated.has(octiCell(p))) point = p;
        }
      }
    }
    pos.set(id, point);
    for (let x = 1 - spacing; x < spacing; x++) for (let y = 1 - spacing; y < spacing; y++) {
      separated.add(octiCell({ x: point.x + x, y: point.y + y }));
    }
  }

  // 先安排只有一条运行臂、至多一个换乘站的线路。共用站作为锚点，整条线共线。
  const keyCells = new Map([...pos].map(([name, point]) => [octiCell(point), name]));
  const linear = new Map();
  const straightCells = new Set();
  for (const line of lines) {
    if (line.arms.length !== 1) continue;
    const [arm] = line.arms;
    if (arm.length < 2 || new Set(arm).size !== arm.length) continue;
    const shared = arm.filter(id => services.get(id).size > 1);
    if (shared.length > 1) continue;
    const oldEndpoints = arm.filter(id => pos.has(id) && !shared.includes(id));
    for (const id of oldEndpoints) keyCells.delete(octiCell(pos.get(id)));
    const start = pos.get(arm[0]), finish = pos.get(arm.at(-1));
    const preferred = octiHeading(stData[arm[0]], stData[arm.at(-1)]);
    const anchorIndex = shared.length ? arm.indexOf(shared[0]) : Math.floor(arm.length / 2);
    const center = shared.length ? pos.get(shared[0]) : {
      x: Math.round((start.x + finish.x) / 2), y: Math.round((start.y + finish.y) / 2),
    };
    const directions = DIRV.map((_, i) => i).sort((a, b) =>
      turnSteps(a, preferred) - turnSteps(b, preferred) || a % 2 - b % 2);
    let best;
    for (let ring = 0; !best && ring <= (shared.length ? 0 : 48); ring++) {
      for (let dx = -ring; !best && dx <= ring; dx++) {
        for (let dy = -ring; !best && dy <= ring; dy++) {
          if (Math.max(Math.abs(dx), Math.abs(dy)) !== ring) continue;
          for (const dir of directions) {
            if (best) break;
            const [ux, uy] = DIRV[dir];
            for (const spacing of [3, 4, 2, 5, 6, 7]) {
              const origin = { x: center.x + dx - anchorIndex * ux * spacing, y: center.y + dy - anchorIndex * uy * spacing };
              const path = Array.from({ length: (arm.length - 1) * spacing + 1 },
                (_, i) => ({ x: origin.x + i * ux, y: origin.y + i * uy }));
              if (path.some(p => keyCells.has(octiCell(p)) && keyCells.get(octiCell(p)) !== shared[0])) continue;
              if (arm.some((id, i) => id !== shared[0] && straightCells.has(octiCell(path[i * spacing])))) continue;
              best = { line: line.id, arm, path, stations: arm.map((_, i) => i * spacing) };
              break;
            }
          }
        }
      }
    }
    if (!best) {
      for (const id of oldEndpoints) keyCells.set(octiCell(pos.get(id)), id);
      continue;
    }
    for (const [i, id] of arm.entries()) {
      const point = best.path[best.stations[i]];
      pos.set(id, point);
      keyCells.set(octiCell(point), id);
    }
    linear.set(line.id, best);
    for (const point of best.path) straightCells.add(octiCell(point));
  }

  const grid = new OctiGrid(pos);
  const plans = [], routed = [];
  const outPos = Object.create(null), usedPoints = new Set();
  for (const [id, point] of pos) {
    outPos[id] = { ...point, key: isKey(id) };
    usedPoints.add(octiCell(point));
  }
  for (const plan of linear.values()) grid.reserve(plan.path);

  function stationMarks(path, arm, start, end) {
    const marks = [], taken = new Set();
    const interval = (path.length - 1) / (end - start);
    for (let i = start + 1; i < end; i++) {
      const target = (i - start) * interval;
      let mark;
      // 同一停靠序列各有自己的弧长区间。优先选择最接近等距分布的独占轨段。
      for (let attempt = 0; attempt < 40 && !mark; attempt++) {
        const offset = attempt === 0 ? 0 : (attempt % 2 ? -1 : 1) * Math.ceil(attempt / 2) * 0.022;
        const at = target + offset * interval;
        const j = Math.floor(at), f = at - j;
        if (f < 0.0001 || f > 0.9999 || Math.abs(f - 0.5) < 0.0001) continue;
        const a = path[j], b = path[j + 1];
        const edge = grid.step(a, b);
        if (grid.tracks[edge]) continue;
        const point = { x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f };
        const key = octiCell(point);
        if (usedPoints.has(key) || taken.has(key)) continue;
        mark = { id: arm[i], at, point: { ...point, station: true }, edge };
        taken.add(key);
      }
      if (!mark) return null;
      marks.push(mark);
    }
    return marks;
  }

  // 每个运行臂独立接续方向。包含普通站的轨段会保留给本线，后续线路可以跨过轨段但不会穿过其站点。
  for (const line of lines) {
    if (linear.has(line.id)) {
      plans.push(linear.get(line.id));
      continue;
    }
    const sharedTracks = new Map();
    const trackKey = (a, b) => JSON.stringify([a, b]);
    for (const arm of line.arms) {
      if (arm.length < 2) continue;
      const anchors = arm.flatMap((id, i) => pos.has(id) ? [i] : []);
      const firstTransfer = arm.findIndex(id => services.get(id).size > 1);
      const lastTransfer = arm.findLastIndex(id => services.get(id).size > 1);
      const fragments = [];
      let incoming = null;
      let firstHeading = null;
      for (let i = 1; i < anchors.length; i++) {
        const start = anchors[i - 1], end = anchors[i];
        const a = arm[start], b = arm[end], c = arm[anchors[i + 1]];
        const from = pos.get(a), to = pos.get(b), next = pos.get(c);
        const closes = i === anchors.length - 1 && arm[0] === arm.at(-1);
        const trunk = start >= firstTransfer && end <= lastTransfer;
        const heading = next ? octiHeading(to, next) : null;
        const cached = end === start + 1 ? sharedTracks.get(trackKey(a, b)) : null;
        const joining = anchors[i + 1] === end + 1 ? sharedTracks.get(trackKey(b, c)) : null;
        const closing = closes ? firstHeading : (joining ? octiHeading(joining[0], joining[1]) : null);
        const continueIn = !cached || incoming == null || turnSteps(incoming, octiHeading(cached[0], cached[1])) <= 2;
        const continueOut = !cached || closing == null || turnSteps(octiHeading(cached.at(-2), cached.at(-1)), closing) <= 2;
        let path = cached && continueIn && continueOut ? cached
          : grid.route(from, to, incoming, heading, closing, trunk, false);
        let marks = path && stationMarks(path, arm, start, end);
        if (path && !marks) {
          path = grid.route(from, to, incoming, heading, closing, trunk, true);
          marks = path && stationMarks(path, arm, start, end);
        }
        if (!marks) throw new OctiRoutingError('无法布线：' + line.id + ' ' + arm[start] + ' → ' + arm[end]);
        if (firstHeading == null) firstHeading = octiHeading(path[0], path[1]);
        incoming = octiHeading(path.at(-2), path.at(-1));
        if (path !== cached) grid.reserve(path, marks);
        if (end === start + 1 && !cached) {
          sharedTracks.set(trackKey(a, b), path);
          sharedTracks.set(trackKey(b, a), path.slice().reverse());
        }
        for (const { id, point } of marks) {
          outPos[id] = { x: point.x, y: point.y, key: false };
          usedPoints.add(octiCell(point));
        }
        routed.push({ a: arm[start], b: arm[end], line: line.id, path });
        fragments.push({ path, marks });
      }
      plans.push({ line: line.id, arm, fragments });
    }
  }

  function compact(path) {
    const result = [];
    for (const point of path) {
      const last = result.at(-1), prev = result.at(-2);
      if (last && octiCell(last) === octiCell(point)) continue;
      if (prev && !last.station && octiHeading(prev, last) === octiHeading(last, point)) result.pop();
      result.push(point);
    }
    return result;
  }
  const routes = [];
  for (const plan of plans) {
    const points = [];
    if (plan.path) {
      for (const at of plan.stations) points.push({ ...plan.path[at], station: true });
    } else {
      for (const { path, marks } of plan.fragments) {
        if (!points.length) points.push({ ...path[0], station: true });
        for (let i = 1, mark = 0; i < path.length; i++) {
          while (mark < marks.length && marks[mark].at < i) points.push(marks[mark++].point);
          points.push(i === path.length - 1 ? { ...path[i], station: true } : path[i]);
        }
      }
    }
    routes.push({ line: plan.line, arm: plan.arm.slice(), points: compact(points) });
  }

  let total = 0, straight = 0, acuteTurns = 0, octViolations = 0;
  for (const route of routes) {
    const points = route.points;
    let previous = null;
    for (let i = 1; i < points.length; i++) {
      const a = points[i - 1], b = points[i];
      const dx = Math.abs(b.x - a.x), dy = Math.abs(b.y - a.y);
      if (dx > 1e-7 && dy > 1e-7 && Math.abs(dx - dy) > 1e-7) octViolations++;
      const heading = octiHeading(a, b);
      if (previous != null) {
        total++;
        if (heading === previous) straight++;
        if (turnSteps(previous, heading) > 2) acuteTurns++;
      }
      previous = heading;
    }
    if (route.arm[0] === route.arm.at(-1) && turnSteps(previous, octiHeading(points[0], points[1])) > 2) acuteTurns++;
  }
  return {
    pos, outPos, routed, failed: [], routes,
    metrics: {
      keyNodes: keyStations.length, edges: edges.length, routed: edges.length, failed: 0,
      octViolations, acuteTurns, collisions: Object.keys(outPos).length - usedPoints.size,
      straightRate: total ? straight / total : 1, totalCorners: total,
      grid: [grid.width, grid.height],
    },
  };
}
