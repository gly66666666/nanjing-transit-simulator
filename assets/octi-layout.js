/* OCTI-Lite: Metro Maps on Octilinear Grid Graphs (Bast et al. EuroVis 2020) 近似实现。开源算法思路，独立编写。 */
/* ============================================================
   OCTI-Lite：基于 Bast/Brosi/Storandt (EuroVis 2020)
   "Metro Maps on Octilinear Grid Graphs" 的近似算法实现。
   核心：8 端口扩展网格图 + 角度转弯代价 + Dijkstra 最短路。
   零依赖，纯 JS。

   端口方向编号（顺时针）：0=E,1=SE,2=S,3=SW,4=W,5=NW,6=N,7=NE
   ============================================================ */

const DIRV = [[1,0],[1,1],[0,1],[-1,1],[-1,0],[-1,-1],[0,-1],[1,-1]];

// 角度差（以 45° 为单位）：0=直行(180°视觉), 1=135°, 2=90°, 3=45°
// 论文：c180=0, c135=1, c90=1.5, c45=2；加 offset a=1 后 ch=0，
// 实际便于实现的边权：直行=1, 135°=2, 90°=2.5, 45°=3（含每跳基础代价1）
const TURN_COST = [0, 2, 2.5, 3]; // 直行(180°)免费，转弯按角度惩罚
function turnSteps(dirA, dirB) {
  // dirA 为进入方向的反向（即当前朝向），dirB 为离开方向
  let d = Math.abs(dirB - dirA);
  if (d > 4) d = 8 - d;
  return d; // 0..4；4 表示掉头
}

class OctiGrid {
  constructor(W, H) {
    this.W = W; this.H = H;
    this.N = W * H;
    // 端口节点索引：node(x,y,port) = ((y*W+x)*8 + port)
    // 但我们需要"原始格节点"用于起终点，用 port=-1 表示为 (y*W+x)*8+8
    this.blocked = new Uint8Array(this.N * 9);     // 端口是否被封（ bend-closed ）
    this.sinkClosed = new Uint8Array(this.N);      // 该格节点 sink 是否封
    this.sinkExtra = new Float64Array(this.N * 9); // sink 额外代价（位置偏好/线序）
    this.usedNode = new Uint8Array(this.N);        // 已被某条路径占用（防止交叉）
    this.edgeCost = new Float64Array(this.N * 9).fill(1); // 每格每方向的额外代价（地形/障碍）
    this.closedDiag = new Set();                   // 被封的对角边
  }
  cellIndex(x, y) { return y * this.W + x; }
  inBounds(x, y) { return x >= 0 && y >= 0 && x < this.W && y < this.H; }
  portIndex(x, y, p) { return (y * this.W + x) * 9 + p; }
  centerIndex(x, y) { return (y * this.W + x) * 9 + 8; }
  cellOfNode(u) { return Math.floor(u / 9); }

  // Dijkstra：从起点格 (sx,sy) 的任意出口端口，到目标格集合 targets 的任意入口端口
  // 返回 { cost, path:[{x,y}], startPort, endPort } 或 null
  route(sx, sy, targets, opt = {}) {
    const { W, H, N } = this;
    const allowUsed = opt.allowUsed || null; // 允许复用的节点（起终点格）
    const maxCost = opt.maxCost ?? Infinity;
    const totalNodes = N * 9; // 8 端口 + 1 中心
    const dist = new Float64Array(totalNodes).fill(Infinity);
    const prev = new Int32Array(totalNodes).fill(-1);
    // 最小堆
    const heap = [];
    const push = (idx, d) => {
      heap.push([d, idx]);
      let i = heap.length - 1;
      while (i > 0) {
        const p = (i - 1) >> 1;
        if (heap[p][0] <= heap[i][0]) break;
        [heap[p], heap[i]] = [heap[i], heap[p]]; i = p;
      }
    };
    const pop = () => {
      const top = heap[0], last = heap.pop();
      if (heap.length) {
        heap[0] = last;
        let i = 0;
        for (;;) {
          const l = 2*i+1, r = l+1; let m = i;
          if (l < heap.length && heap[l][0] < heap[m][0]) m = l;
          if (r < heap.length && heap[r][0] < heap[m][0]) m = r;
          if (m === i) break;
          [heap[m], heap[i]] = [heap[i], heap[m]]; i = m;
        }
      }
      return top;
    };

    const targetSet = new Set(targets.map(t => this.cellIndex(t.x, t.y)));
    const startCell = this.cellIndex(sx, sy);
    // 起点：从中心节点出发，进入各端口（sink 代价）
    const startCenter = this.centerIndex(sx, sy);
    for (let p = 0; p < 8; p++) {
      const pi = this.portIndex(sx, sy, p);
      if (this.blocked[pi]) continue;
      const c = this.sinkExtra[pi];
      dist[pi] = c; prev[pi] = startCenter;
      push(pi, c);
    }
    dist[startCenter] = 0;

    let goalIdx = -1, goalCost = Infinity;
    while (heap.length) {
      const [d, u] = pop();
      if (d > dist[u] + 1e-9) continue;
      if (d >= goalCost || d > maxCost) break;
      const isPort = u % 9 !== 8;
      const cell = Math.floor(u / 9);
      const x = cell % W, y = (cell / W) | 0;

      if (isPort) {
        const p = u % 9;
        // 到达目标格：通过 sink 进入中心（的目标端口）
        if (targetSet.has(cell) && cell !== startCell) {
          if (!this.sinkClosed[cell]) {
            // 到达代价 = sinkExtra（目标端口的入口代价）
            const arrive = d + this.sinkExtra[this.portIndex(x,y,p)];
            if (arrive < goalCost) { goalCost = arrive; goalIdx = u; }
          }
        }
        // 端口 p = 当前行进方向。转弯到同格其它方向 q：转角=|p-q|（1=135°,2=90°,3=45°,4=掉头）
        for (let step = 1; step <= 4; step++) {
          for (const q of [(p + step) % 8, (p - step + 8) % 8]) {
            const vi = this.portIndex(x, y, q);
            if (this.blocked[vi]) continue;
            const nd = d + TURN_COST[Math.min(step,3)] * (step === 4 ? 2 : 1);
            if (nd < dist[vi] - 1e-9) { dist[vi] = nd; prev[vi] = u; push(vi, nd); }
          }
        }
        // 沿方向 p 移动到邻居，行进方向保持 p
        const [dx, dy] = DIRV[p];
        const nx = x + dx, ny = y + dy;
        if (this.inBounds(nx, ny)) {
          const vi = this.portIndex(nx, ny, p);
          if (!this.blocked[vi]) {
            const nd = d + this.edgeCost[vi] + 1; // 每跳基础代价
            if (nd < dist[vi] - 1e-9) { dist[vi] = nd; prev[vi] = u; push(vi, nd); }
          }
        }
      } else {
        // 中心节点：只允许在起点（已处理）；其他中心节点不用于穿越
      }
    }
    if (goalIdx < 0) return null;
    // 回溯端口路径
    const portPath = [];
    for (let u = goalIdx; u >= 0; u = prev[u]) {
      if (u % 9 !== 8) {
        const cell = Math.floor(u/9), p = u%9;
        portPath.push({ x: cell % W, y: (cell/W)|0, p });
      }
      if (portPath.length > W*H) break;
    }
    portPath.reverse();
    // 提取格子路径（去重连续相同格）
    const cells = [];
    for (const q of portPath) {
      if (!cells.length || cells[cells.length-1].x !== q.x || cells[cells.length-1].y !== q.y)
        cells.push({x:q.x, y:q.y});
    }
    return { cost: goalCost, path: cells, ports: portPath };
  }
}

/* ============================================================
   OCTI-Layout —— 完整布局器（近似算法，Bast et al. EuroVis 2020 §4）
   流程：
     1. 提取线图，deg-2 收缩（只保留换乘站+端点）
     2. 关键节点吸附到网格（按真实方位，Voronoi 分离）
     3. 按 line-degree 排序边
     4. 逐边 Dijkstra 寻路（8端口网格+转角代价），已用节点封禁防交叉
     5. 局部搜索优化（移动单个站并重路由邻边）
     6. 普通站沿八方向曲线均匀插回
   ============================================================ */


function octSnap(dx, dy) {
  const k = ((Math.round(Math.atan2(dy, dx) / (Math.PI/4)) % 8) + 8) % 8;
  return k;
}
function octLegal(ax, ay, bx, by) {
  const dx = Math.abs(bx-ax), dy = Math.abs(by-ay);
  return dx===0 || dy===0 || dx===dy;
}

function octiLayout(input, opt = {}) {
  const SCALE = opt.scale ?? 1;          // 经纬度→网格缩放（数据已是 world 坐标）
  const GRID_PAD = opt.pad ?? 3;
  const PASSES = opt.passes ?? 8;
  let seed = opt.seed ?? 20261124;
  const rnd = () => { seed=(seed*1664525+1013904223)>>>0; return seed/4294967296; };

  const lines = input.lines.filter(l => l.arms && l.arms.some(a => a.length > 1));
  const stData = input.stations || {};

  // ---------- 1. deg-2 收缩：关键节点 = 换乘站 + 端点 ----------
  const use = new Map(), adj = new Map();
  for (const l of lines) for (const arm of l.arms) {
    for (const s of arm) use.set(s, (use.get(s)||0)+1);
    for (let k=0;k<arm.length-1;k++) {
      const a=arm[k], b=arm[k+1];
      if(!adj.has(a))adj.set(a,new Set()); if(!adj.has(b))adj.set(b,new Set());
      adj.get(a).add(b); adj.get(b).add(a);
    }
  }
  const isKey = s => (use.get(s)||0)>1 || (adj.get(s)?.size===1);
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
  const warped = new Map(keyStations.map((s,i)=>[s, warp(keyPts[i])]));
  const gx = s => Math.round(mid + (warped.get(s).x/span)*R*1.3);
  const gy = s => Math.round(mid + (warped.get(s).y/span)*R*1.3);
  // 相邻关键站若夹了很多普通站，需要更长的路径 → 调整吸附目标距离
  const betweenCount=new Map();
  for (const l of lines) for (const arm of l.arms) {
    const seq=arm.filter(s=>isKey(s));
    for(let k=0;k<seq.length-1;k++){
      const n=Math.abs(arm.indexOf(seq[k+1])-arm.indexOf(seq[k]))-1;
      const kk=seq[k]<seq[k+1]?seq[k]+'|'+seq[k+1]:seq[k+1]+'|'+seq[k];
      betweenCount.set(kk,Math.max(betweenCount.get(kk)||0,n));
    }
  }
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

  // ---------- 4. 逐边 Dijkstra 布线 ----------
  const grid=new OctiGrid(W,H);
  const routed=[];   // 每条边的路径与端口
  const failed=[];
  // 已确定位置的站允许被多条边复用（sink 重开）
  const settled=new Set();
  for (const e of edges) {
    const A=pos.get(e.a), B=pos.get(e.b);
    if(!A||!B){failed.push(e);continue;}
    // 目标端口集合：B 格的所有端口（若 B 已服务其它线，重开其 sink）
    const targets=[{x:B.x,y:B.y}];
    // 起点 A：清空 A 格的 blocked 以便出发
    for(let p=0;p<8;p++) grid.blocked[grid.portIndex(A.x,A.y,p)]=0;
    const r=grid.route(A.x,A.y,targets,{});
    if(!r){failed.push(e);continue;}
    // 已用格点加高代价（软避让）而非完全封死——完全封死会让后续边无路可走。
    // 论文用硬封禁+圆序约束保证拓扑，这里接受少量共享以换取全部边布通。
    for (const q of r.path) {
      if ((q.x===A.x&&q.y===A.y)||(q.x===B.x&&q.y===B.y)) continue;
      const ci=grid.cellIndex(q.x,q.y);
      grid.usedNode[ci]=1;
      for(let p=0;p<8;p++) grid.edgeCost[grid.portIndex(q.x,q.y,p)] += 8;
    }
    routed.push({...e, path:r.path, ports:r.ports, cost:r.cost});
    settled.add(e.a); settled.add(e.b);
  }

  // ---------- 5. 局部搜索优化（可选，移动站点并重路由） ----------
  // 简化版：对直线率低的站做邻位试探，保持不重合/八方向；后续可扩展完整重路由
  // （论文 §4.6 需要重路由所有邻边，成本高；本实现先跳过，靠 §4 的转角代价已足够）

  // ---------- 6. 普通站均匀插回 ----------
  const finalPos=new Map(pos);
  for (const r of routed) {
    const path=r.path;
    if(path.length<2) continue;
    // 计算路径的八方向弧长（每格算1）
    const L=path.length-1;
    const k=r.between;
    if(k<=0) continue;
    // 从 A 到 B 按索引均匀取 k 个格点
    for(let t=1;t<=k;t++){
      const f=t/(k+1);
      const idx=Math.min(path.length-1, Math.max(0, Math.round(f*(path.length-1))));
      const q=path[idx];
      finalPos.set(`__tmp_${r.a}_${r.b}_${t}`, {x:q.x,y:q.y, via:r});
    }
  }
  // 把普通站分配到各线的臂上（按在臂中的位置）
  const outPos={};
  for(const [s,p] of finalPos){ if(!s.startsWith('__tmp_')) outPos[s]={...p,key:true}; }
  const usedCells=new Set(Object.values(outPos).map(p=>p.x+','+p.y));
  // 对每条臂：用布线路径的长度比例决定普通站位置
  for (const l of lines) for (const arm of l.arms) {
    const keyIdx=[];
    for(let k=0;k<arm.length;k++) if(isKey(arm[k])) keyIdx.push(k);
    for(let t=0;t<keyIdx.length-1;t++){
      const si=keyIdx[t], ei=keyIdx[t+1];
      const A=pos.get(arm[si]), B=pos.get(arm[ei]);
      if(!A||!B)continue;
      // 找对应的 routed 边
      const rr=routed.find(r=>((r.a===arm[si]&&r.b===arm[ei])||(r.a===arm[ei]&&r.b===arm[si])));
      const mid=arm.slice(si+1,ei);
      let seq;
      if(rr){
        const fwd=rr.a===arm[si];
        seq=fwd?rr.path:rr.path.slice().reverse();
      } else {
        // 布线失败：构造 A→B 的八方向楼梯路径，保证普通站有独立格位
        seq=[{x:A.x,y:A.y}];
        let cx=A.x, cy=A.y;
        const dx=B.x-A.x, dy=B.y-A.y;
        const adx=Math.abs(dx), ady=Math.abs(dy);
        const sx=Math.sign(dx), sy=Math.sign(dy);
        const diag=Math.min(adx,ady);
        for(let t=0;t<diag;t++){cx+=sx;cy+=sy;seq.push({x:cx,y:cy});}
        for(let t=0;t<adx-diag;t++){cx+=sx;seq.push({x:cx,y:cy});}
        for(let t=0;t<ady-diag;t++){cy+=sy;seq.push({x:cx,y:cy});}
        if(seq[seq.length-1].x!==B.x||seq[seq.length-1].y!==B.y)seq.push({x:B.x,y:B.y});
      }
      // 沿路径按等间隔选格点：确保站间距≥1且严格落在路径的八方向格上
      const usable=seq.filter(c=>{
        // 排除起终点（已放关键站），其余只要未被占用
        const isA=(c.x===A.x&&c.y===A.y), isB=(c.x===B.x&&c.y===B.y);
        return !isA && !isB && !usedCells.has(c.x+','+c.y);
      });
      const m=mid.length;
      // 若路径格点不够容纳中间站，沿路径插入额外格点（保持八方向）
      while(seq.length < m+2){
        let extended=false;
        for(let j=0;j<seq.length-1 && !extended;j++){
          const a=seq[j], b=seq[j+1];
          const dx=b.x-a.x, dy=b.y-a.y;
          if(Math.abs(dx)+Math.abs(dy)<=1)continue;
          // 在 a,b 间插入一个八方向中间点
          let mx,my;
          if(dx===0){mx=a.x;my=a.y+Math.sign(dy);}
          else if(dy===0){mx=a.x+Math.sign(dx);my=a.y;}
          else {mx=a.x+Math.sign(dx);my=a.y+Math.sign(dy);}
          if(!usedCells.has(mx+','+my)){seq.splice(j+1,0,{x:mx,y:my});extended=true;}
        }
        if(!extended)break;
      }
      const usable2=seq.filter(c=>{
        const isA=(c.x===A.x&&c.y===A.y), isB=(c.x===B.x&&c.y===B.y);
        return !isA && !isB && !usedCells.has(c.x+','+c.y);
      });
      const pool=usable2.length?usable2:usable;
      for(let k=0;k<m;k++){
        const idx=Math.min(pool.length-1,k);
        const q=pool[idx]||seq[Math.min(seq.length-1,k+1)];
        outPos[mid[k]]={x:q.x,y:q.y,key:false};
        usedCells.add(q.x+','+q.y);
      }
    }
    // 端点外侧普通站：沿首尾方向外推
    const fk=keyIdx[0], lk=keyIdx[keyIdx.length-1];
    for(let k=0;k<fk;k++){
      const A=pos.get(arm[fk]), B=pos.get(arm[fk+1])||A;
      const d=octSnap(A.x-B.x,A.y-B.y);
      outPos[arm[k]]={x:A.x+DIRV[d][0]*(fk-k),y:A.y+DIRV[d][1]*(fk-k),key:false};
    }
    for(let k=lk+1;k<arm.length;k++){
      const A=pos.get(arm[lk]), B=pos.get(arm[lk-1])||A;
      const d=octSnap(A.x-B.x,A.y-B.y);
      outPos[arm[k]]={x:A.x+DIRV[d][0]*(k-lk),y:A.y+DIRV[d][1]*(k-lk),key:false};
    }
  }

  // ---------- 6b. 合法性修复：把违规站移到前后站的八方向合法格 ----------
  // 对每个普通站，若与相邻站不成八方向，在相邻站周围找合法且不重合的格点
  const usedAfter=new Set(Object.values(outPos).map(p=>p.x+','+p.y));
  for(let iter=0;iter<10;iter++){
    let fixed=0;
    for(const l of lines)for(const arm of l.arms){
      for(let k=0;k<arm.length;k++){
        const s=arm[k]; const C=outPos[s];
        if(!C)continue;
        // 关键站也修复：同步更新 pos（布线图）与 outPos
        const isKeyC=C.key;
        const prev=arm[k-1], next=arm[k+1];
        const PA=prev?outPos[prev]:null, PB=next?outPos[next]:null;
        const A=outPos[arm[k-1]], B=outPos[arm[k+1]];
        if(!A||!B)continue;
        if(octLegal(A.x,A.y,C.x,C.y) && octLegal(C.x,C.y,B.x,B.y))continue;
        // 候选：以 A 为中心，朝 B 方向的八方向格点；或 A/B 周围的合法格
        const cands=[];
        const dx=B.x-A.x,dy=B.y-A.y;
        const dirs=DIRV;
        for(const [ux,uy] of dirs)for(let L=1;L<=8;L++){
          cands.push({x:A.x+ux*L,y:A.y+uy*L});
          cands.push({x:B.x+ux*L,y:B.y+uy*L});
        }
        cands.sort((p,q)=>{
          const sp=Math.hypot(p.x-(A.x+B.x)/2,p.y-(A.y+B.y)/2);
          const sq=Math.hypot(q.x-(A.x+B.x)/2,q.y-(A.y+B.y)/2);
          return sp-sq;
        });
        let best=null;
        for(const c of cands){
          if(usedAfter.has(c.x+','+c.y))continue;
          if(!octLegal(A.x,A.y,c.x,c.y)||!octLegal(c.x,c.y,B.x,B.y))continue;
          best=c;break;
        }
        if(best){
          usedAfter.delete(C.x+','+C.y);
          C.x=best.x;C.y=best.y;
          usedAfter.add(best.x+','+best.y);
          if(isKeyC && pos.has(s)) { pos.get(s).x=best.x; pos.get(s).y=best.y; }
          fixed++;
        }
      }
    }
    if(!fixed)break;
  }

  // ---------- 7. 指标 ----------
  let viol=0,straight=0,total=0,col=0;
  const seen=new Set();
  for(const p of Object.values(outPos)){const k=p.x+','+p.y;if(seen.has(k))col++;seen.add(k);}
  for(const l of lines)for(const arm of l.arms){
    for(let k=0;k<arm.length-1;k++){
      const A=outPos[arm[k]],B=outPos[arm[k+1]];if(!A||!B)continue;
      if(!octLegal(A.x,A.y,B.x,B.y))viol++;
    }
    for(let k=1;k<arm.length-1;k++){
      const a=outPos[arm[k-1]],b=outPos[arm[k]],c=outPos[arm[k+1]];if(!a||!b||!c)continue;
      const d1=octSnap(b.x-a.x,b.y-a.y),d2=octSnap(c.x-b.x,c.y-b.y);
      total++;if(d1===d2)straight++;
    }
  }
  return {
    pos, outPos, routed, failed,
    metrics:{
      keyNodes:keyStations.length, edges:edges.length, routed:routed.length, failed:failed.length,
      octViolations:viol, collisions:col,
      straightRate: total?+(straight/total).toFixed(3):0, totalCorners:total,
      grid:[W,H]
    }
  };
}
