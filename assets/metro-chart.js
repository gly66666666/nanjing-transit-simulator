/* 全部城市和区域共用的拓扑图。模拟引擎只提供当前线网、相机和画布。 */
const MetroChart = (() => {
  function attach({ app: App, canvasContext: ctx, size, scopeLines, lineArms, toast,
    subtitle = '', officialStyle = false }) {
    const Chart = { ready: false, sig: '', cell: 0.6, fitScale: 3, pos: new Map(), routes: [] };
    const CHART_FONT = '"Microsoft YaHei","Segoe UI",sans-serif';
    const getLine = id => Chart.lineById.get(id);

    function computeChart(force) {
      const lines = [], data = [], stData = Object.create(null), services = new Map();
      for (const line of scopeLines()) {
        const arms = lineArms(line).filter(arm => !arm.hidden)
          .map(arm => arm.stations.filter((id, i) => i === 0 || id !== arm.stations[i - 1]))
          .filter(arm => arm.length > 1);
        if (!arms.length) continue;
        lines.push(line);
        data.push({ id: line.id, arms });
        for (const id of new Set(arms.flat())) {
          const station = App.stations.get(id);
          stData[id] = station && { x: station.x, y: station.y };
          if (!services.has(id)) services.set(id, new Set());
          services.get(id).add(line.id);
        }
      }
      const sig = JSON.stringify([data, stData]);
      const lineById = new Map(lines.map(line => [line.id, line]));
      const stations = [...services.keys()].map(id => App.stations.get(id));
      Object.assign(Chart, { lines, lineById, services, stations });
      if (!force && Chart.sig === sig) return false;
      const start = performance.now();
      Object.assign(Chart, {
        ready: false, sig: '', bounds: null, pos: new Map(), routes: [], tracks: new Map(),
        error: null, octiMetrics: null, edges: 0, viol: 0
      });
      if (!lines.length) {
        Chart.sig = sig;
        return false;
      }
      try {
        const layout = octiLayout({ lines: data, stations: stData });
        const m = layout.metrics;
        if (Object.keys(layout.outPos).length !== services.size || m.acuteTurns || m.collisions || m.octViolations) {
          throw new Error('拓扑图几何校验未通过');
        }
        const z = Chart.cell;
        const scale = point => ({ x: point.x * z, y: point.y * z, i: point.x, j: point.y,
          station: point.station });
        Chart.pos = new Map(Object.entries(layout.outPos).map(([id, point]) => [id, scale(point)]));
        Chart.bounds = Object.fromEntries(Object.entries(layout.bounds).map(([key, value]) => [key, value * z]));
        Chart.routes = layout.routes.map(route => ({ line: route.line, arm: route.arm, pts: route.points.map(scale) }));
        for (const r of Chart.routes) {
          if (!Chart.tracks.has(r.line)) Chart.tracks.set(r.line, []);
          Chart.tracks.get(r.line).push(r);
        }
        Chart.octiMetrics = m;
        Chart.edges = m.edges;
        Chart.ready = true;
        Chart.sig = sig;
        return true;
      } catch (error) {
        Chart.error = error.message;
        console.error('拓扑图生成失败', error);
        return false;
      } finally {
        Chart.ms = Math.round(performance.now() - start);
      }
    }

    function chartMinSheetWidth(vw, k, official) {
      const normalWidth = Chart.routes?.length ? 680 : 840;
      return Math.min((official ? 760 : normalWidth) * k, vw - 24 * k);
    }

    function chartLegendSpec(sheetW, height, k, nLine, compact) {
      const cols = Math.max(2, Math.min(8, Math.floor((sheetW / k - 60) / 96)));
      const rows = Math.max(1, Math.ceil(nLine / cols));
      const fullBand = (26 + rows * 21) * k;
      const minimal = !Chart.exporting && (compact ?? fullBand > height * 0.34);
      return { cols, band: minimal ? 32 * k : fullBand, compact: minimal };
    }

    function fitChart() {
      if (!Chart.bounds) return;
      const { W, H } = size();
      const { minX, minY, maxX, maxY } = Chart.bounds;
      const legendBand = chartLegendSpec(chartMinSheetWidth(W, 1, false), H, 1, Chart.lines.length).band;
      const headerH = 92;
      const bw = Math.max(1, maxX - minX), bh = Math.max(1, maxY - minY);
      const cw = Math.max(1, W - 44 * 2 - 24);
      const chh = Math.max(1, H - headerH - legendBand - 48);
      const s = Math.min(140, cw / bw, chh / bh);
      Chart.fitScale = s;
      App.cam.s = s;
      const boxCy = headerH + 24 + chh / 2;
      App.cam.x = (minX + maxX) / 2;
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

    function drawChartTo(g, vw, vh, cam, k) {
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
      // 浅色线用深色字，深色线用白字；官方图的 7/9/13/14 号线就是黑字。
      const inkOn = (hex) => {
        const h = String(hex || '').replace('#', '');
        if (h.length < 6) return '#ffffff';
        const r = parseInt(h.slice(0, 2), 16), gg = parseInt(h.slice(2, 4), 16), b = parseInt(h.slice(4, 6), 16);
        return (0.299 * r + 0.587 * gg + 0.114 * b) > 172 ? '#132033' : '#ffffff';
      };
      /* --- 版面：一张“挂图”海报贴在深色底板上 --- */
      const bounds = Chart.bounds;
      const topLeft = bounds ? px(bounds.minX, bounds.minY) : { x: vw * 0.45, y: vh * 0.45 };
      const bottomRight = bounds ? px(bounds.maxX, bounds.maxY) : { x: vw * 0.55, y: vh * 0.55 };
      const { x: cX0, y: cY0 } = topLeft;
      const { x: cX1, y: cY1 } = bottomRight;

      // 官方挂图风格：只作用于“导出挂图”，屏幕总览仍保持轻量 LOD。
      const official = officialStyle && Chart.exporting;
      const sidePad = (official ? 52 : 44) * k;
      const headerH = (official ? 158 : 92) * k;
      const footerBand = official ? 54 * k : 0;
      const drawnLines = Chart.lines;
      const nLine = drawnLines.length;
      const sheetW = Math.max(cX1 - cX0 + sidePad * 2, chartMinSheetWidth(vw, k, official));
      const fittedLegend = chartLegendSpec(chartMinSheetWidth(vw, k, official), vh, k, nLine);
      const legend = chartLegendSpec(sheetW, vh, k, nLine, fittedLegend.compact);
      const legendBand = official ? 0 : legend.band;
      const sheetH = (cY1 - cY0) + headerH + legendBand + footerBand + (official ? 10 : 24) * k;
      const sx0 = (cX0 + cX1) / 2 - sheetW / 2;
      const sy0 = cY0 - headerH - 12 * k;
      const sx1 = sx0 + sheetW;
      const sy1 = sy0 + sheetH;
      const area = { x0: sx0 + sidePad, y0: sy0 + headerH, x1: sx1 - sidePad, y1: sy1 - legendBand - footerBand };
      const cityCn = ((document.title.split('·')[0] || '城市').replace(/地铁.*$/, '')).trim() || '城市';
      const cityEn = cityCn === '北京' ? 'Beijing Rail Transit Lines'
        : (subtitle ? subtitle.replace(/\s+/g, ' ').trim() : 'CITY METRO NETWORK MAP');
      const legendCard = official
        ? { x: sx0 + 24 * k, y: sy0 + headerH + 18 * k, w: 196 * k, h: (42 + Math.ceil(nLine / 3) * 18) * k }
        : null;
      if (legendCard) claim(legendCard.x, legendCard.y, legendCard.w, legendCard.h);
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
      if (official) {
        g.fillStyle = '#fffdf8';
        g.fillRect(sx0, sy0, sheetW, sheetH);
      } else {
        const pg = g.createLinearGradient(0, sy0, 0, sy1);
        pg.addColorStop(0, '#ffffff');
        pg.addColorStop(0.6, '#fcfcf7');
        pg.addColorStop(1, '#f5f6f0');
        g.fillStyle = pg;
        g.fillRect(sx0, sy0, sheetW, sheetH);
      }

      /* --- 官方挂图页眉：深蓝标题带 --- */
      if (official) {
        g.fillStyle = '#062a56';
        g.fillRect(sx0, sy0, sheetW, headerH);
        // 顶部细金线，增加挂印感
        g.fillStyle = 'rgba(255,255,255,0.14)';
        g.fillRect(sx0, sy0, sheetW, 2 * k);

        const hx = sx0 + 50 * k, hy = sy0 + headerH * 0.50;
        g.beginPath(); g.arc(hx, hy, 27 * k, 0, Math.PI * 2);
        g.fillStyle = '#ffffff'; g.fill();
        g.beginPath(); g.arc(hx, hy, 21 * k, 0, Math.PI * 2);
        g.strokeStyle = '#0b3a70'; g.lineWidth = 3 * k; g.stroke();
        g.fillStyle = '#0b3a70';
        g.font = `800 ${Math.round(28 * k)}px ${CHART_FONT}`;
        g.textAlign = 'center'; g.textBaseline = 'middle';
        g.fillText('B', hx, hy + 1 * k);

        g.textAlign = 'left'; g.textBaseline = 'alphabetic';
        g.fillStyle = '#ffffff';
        g.font = `700 ${Math.round(44 * k)}px ${CHART_FONT}`;
        g.fillText(`${cityCn}城市轨道交通线网图`, sx0 + 96 * k, sy0 + 66 * k);
        g.fillStyle = 'rgba(255,255,255,0.78)';
        g.font = `600 ${Math.round(17 * k)}px ${CHART_FONT}`;
        g.fillText(cityEn, sx0 + 98 * k, sy0 + 105 * k);

        const nStHead = Chart.stations.length;
        g.textAlign = 'right';
        g.fillStyle = 'rgba(255,255,255,0.92)';
        g.font = `600 ${Math.round(15 * k)}px ${CHART_FONT}`;
        g.fillText(`2026.11 · ${nLine} 条线 · ${nStHead} 座车站`, sx1 - 32 * k, sy0 + 62 * k);
        g.fillStyle = 'rgba(255,255,255,0.42)';
        g.font = `500 ${Math.round(9.5 * k)}px ${CHART_FONT}`;
        g.fillText('OFFICIAL NETWORK MAP / POSTER EDITION', sx1 - 32 * k, sy0 + 88 * k);

        g.fillStyle = 'rgba(255,255,255,0.16)';
        g.fillRect(sx0, sy0 + headerH - 1.2 * k, sheetW, 1.2 * k);
      }

      /* --- 格网点阵 --- */
      const cellPx = Chart.cell * s;
      const denseOverview = !Chart.exporting && cellPx < 4 &&
        (cX1 - cX0) * (cY1 - cY0) < Chart.stations.length * 120;
      if (!official && cellPx > 9 * k && cellPx < 90 * k) {
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

      const lw = Math.max(1.4, Math.min(4.8, cellPx / k * 0.27)) * k;
      const visible = p => p.x > -70 && p.x < vw + 70 && p.y > -70 && p.y < vh + 70;

      /* --- 线路 --- */
      const drawOrder = drawnLines.slice().sort((a, b) => b.stations.length - a.stations.length);

      const strokePath = (pts) => {
        g.beginPath();
        g.moveTo(pts[0].x, pts[0].y);
        for (let i = 1; i < pts.length; i++) g.lineTo(pts[i].x, pts[i].y);
        g.stroke();
      };

      const strokeRound = (pts) => {
        if (pts.length < 3) return strokePath(pts);
        const rad = Math.max(4.5 * k, Math.min(11 * k, cellPx * 0.26));
        g.beginPath(); g.moveTo(pts[0].x, pts[0].y);
        for (let i = 1; i < pts.length - 1; i++) {
          const pv = pts[i - 1], v = pts[i], nx = pts[i + 1];
          if (v.station) { g.lineTo(v.x, v.y); continue; }
          const d1 = Math.hypot(v.x - pv.x, v.y - pv.y) || 1;
          const d2 = Math.hypot(nx.x - v.x, nx.y - v.y) || 1;
          const r1 = Math.min(rad, d1 * 0.45), r2 = Math.min(rad, d2 * 0.45);
          const ax = v.x + (pv.x - v.x) * r1 / d1, ay = v.y + (pv.y - v.y) * r1 / d1;
          const bx = v.x + (nx.x - v.x) * r2 / d2, by = v.y + (nx.y - v.y) * r2 / d2;
          g.lineTo(ax, ay); g.quadraticCurveTo(v.x, v.y, bx, by);
        }
        const last = pts[pts.length - 1]; g.lineTo(last.x, last.y); g.stroke();
      };
      /* 线网占位格：站名只落在空白处，不压线 */
      const inkStep = 5 * k;
      const inkSet = new Set();
      const inkKey = (i, j) => i * 100003 + j;
      const markInk = (pts, halfW) => {
        for (let i = 0; i < pts.length - 1; i++) {
          const a = pts[i], b = pts[i + 1];
          if (Math.max(a.x, b.x) < -30 || Math.min(a.x, b.x) > vw + 30 ||
              Math.max(a.y, b.y) < -30 || Math.min(a.y, b.y) > vh + 30) continue;
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
        for (const track of Chart.tracks.get(line.id)) {
          const route = track.pts.map(q => ({ ...px(q.x, q.y), station: q.station }));
          if (route.every(p => p.x < -70) || route.every(p => p.x > vw + 70) ||
              route.every(p => p.y < -70) || route.every(p => p.y > vh + 70)) continue;
          markInk(route, lw / 2);
          g.lineCap = 'round';
          g.lineJoin = 'round';

          if (!line.enabled) {
            g.setLineDash([7 * k, 7 * k]);
            g.strokeStyle = 'rgba(95,110,128,0.5)';
            g.lineWidth = Math.max(1.6, lw * 0.45);
            strokeRound(route);
            g.setLineDash([]);
            continue;
          }

          // 白色描边（交叉处形成过线桥）
          if (lw > 1.8) {
            g.strokeStyle = 'rgba(255,255,255,0.95)';
            g.lineWidth = lw + 1.9 * k;
            strokeRound(route);
          }
          g.strokeStyle = line.color;
          g.lineWidth = lw;
          strokeRound(route);
        }
      }

      /* --- 车站符号 --- */
      const rNorm = official ? Math.max(1.65, lw * 0.38) : Math.max(cellPx < 4 ? 0.8 : 1.35, lw * 0.30);
      for (const st of Chart.stations) {
        const cp = Chart.pos.get(st.id);
        const p = px(cp.x, cp.y);
        if (!visible(p)) continue;
        const trans = Chart.services.get(st.id).size > 1;
        if (denseOverview && !trans && !st.custom) continue;
        const r = trans ? rNorm * (official ? 2.05 : 1.9) : rNorm;
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

      /* --- 线号牌：端头 + 长线中段（官方图的关键识别符号） --- */
      if (cellPx > 12) {
        const tagText = (line) => (official ? line.name : line.short);
        const putBadge = (line, p, ux, uy) => {
          const text = tagText(line);
          const fsTag = (official ? 7.7 : 10) * k;
          g.font = `700 ${Math.round(fsTag)}px ${CHART_FONT}`;
          const tw = g.measureText(text).width;
          const bw = Math.max((official ? 19 : 17) * k, tw + (official ? 9 : 6) * k);
          const bh = (official ? 14 : 15) * k;
          const off = rNorm + 7 * k + (Math.abs(ux) >= Math.abs(uy) ? bw / 2 : bh / 2);
          const cx = p.x + ux * off, cy = p.y + uy * off;
          const x = cx - bw / 2, y = cy - bh / 2;
          if (x < area.x0 + 2 * k || x + bw > area.x1 - 2 * k) return false;
          if (y < area.y0 + 2 * k || y + bh > area.y1 - 2 * k) return false;
          if (!labelBox(x - 1.5 * k, y - 1.5 * k, bw + 3 * k, bh + 3 * k)) return false;
          const rr = 3.5 * k;
          g.beginPath();
          g.moveTo(x + rr, y);
          g.lineTo(x + bw - rr, y); g.quadraticCurveTo(x + bw, y, x + bw, y + rr);
          g.lineTo(x + bw, y + bh - rr); g.quadraticCurveTo(x + bw, y + bh, x + bw - rr, y + bh);
          g.lineTo(x + rr, y + bh); g.quadraticCurveTo(x, y + bh, x, y + bh - rr);
          g.lineTo(x, y + rr); g.quadraticCurveTo(x, y, x + rr, y);
          g.closePath();
          g.fillStyle = line.color;
          g.fill();
          g.strokeStyle = 'rgba(255,255,255,0.72)';
          g.lineWidth = 0.9 * k;
          g.stroke();
          g.fillStyle = inkOn(line.color);
          g.font = `700 ${Math.round(fsTag)}px ${CHART_FONT}`;
          g.textAlign = 'center';
          g.textBaseline = 'middle';
          g.fillText(text, cx, cy + 0.4 * k);
          return true;
        };

        for (const line of drawOrder) {
          for (const arm of lineArms(line)) {
            const ss = arm.stations;
            if (ss.length < 2) continue;
            const a = Chart.pos.get(ss[0]), b = Chart.pos.get(ss[1]);
            if (a && b) {
              const pa = px(a.x, a.y), pb = px(b.x, b.y);
              const d = Math.hypot(pa.x - pb.x, pa.y - pb.y) || 1;
              putBadge(line, pa, (pa.x - pb.x) / d, (pa.y - pb.y) / d);
            }
            const c = Chart.pos.get(ss[ss.length - 1]), e = Chart.pos.get(ss[ss.length - 2]);
            if (c && e) {
              const pc = px(c.x, c.y), pe = px(e.x, e.y);
              const d = Math.hypot(pc.x - pe.x, pc.y - pe.y) || 1;
              putBadge(line, pc, (pc.x - pe.x) / d, (pc.y - pe.y) / d);
            }
          }
        }

        // 长线中段各放一枚，避免官方图那种“整条线找不到线号”的问题。
        if (official) {
          for (const line of drawOrder) {
            const arms = lineArms(line).filter(a => a.stations.length >= 8)
              .sort((a, b) => b.stations.length - a.stations.length);
            if (!arms.length) continue;
            const arm = arms[0], ss = arm.stations, n = ss.length;
            let at = -1;
            for (let d = 0; d < n; d++) {
              for (const idx of [Math.floor(n * 0.5) + d, Math.floor(n * 0.5) - d]) {
                if (idx <= 0 || idx >= n - 1 || at >= 0) continue;
                const st = App.stations.get(ss[idx]);
                if (st && Chart.services.get(st.id)?.size === 1) at = idx;
              }
              if (at >= 0) break;
            }
            if (at < 0) at = Math.floor(n * 0.5);
            const cur = Chart.pos.get(ss[at]), prev = Chart.pos.get(ss[at - 1]), next = Chart.pos.get(ss[at + 1]);
            if (!cur || !prev || !next) continue;
            const pc = px(cur.x, cur.y), pp = px(prev.x, prev.y), pn = px(next.x, next.y);
            const dx = pn.x - pp.x, dy = pn.y - pp.y;
            const d = Math.hypot(dx, dy) || 1;
            const nx = -dy / d, ny = dx / d;
            if (!putBadge(line, pc, nx, ny)) putBadge(line, pc, -nx, -ny);
          }
        }
      }

      /* --- 站名 --- */
      const fs = cellPx > 34 ? 10 : cellPx > 17 ? 9 : 7.5;
      const items = [];
      const terminals = new Set();
      for (const route of Chart.routes) {
        const arm = route.arm;
        terminals.add(arm[0]);
        terminals.add(arm.at(-1));
      }
      const showAll = Chart.exporting || cellPx > 13;
      const majorOnly = !showAll && cellPx < 5.4;
      for (const st of Chart.stations) {
        const cp = Chart.pos.get(st.id);
        const serviceCount = Chart.services.get(st.id).size;
        const trans = serviceCount > 1;
        if ((denseOverview || (majorOnly && trans)) && serviceCount < 3) continue;
        if (!trans && !terminals.has(st.id) && !showAll) continue;
        items.push({ st, cp, trans, term: terminals.has(st.id) });
      }
      items.sort((a, b) => (b.trans - a.trans) || (b.term - a.term) || (b.st.w - a.st.w));

      // 标签候选：三档半径 × 八方位，先近后远。大画布(导出)时给文字更多落位机会，
      // 减少站名压在站点/线路上的情况（官方图的"站名零压线"做法）。
      const cands = [];
      for (const ring of [1, 1.55, 2.2]) {
        cands.push(
          [ring, 0, 'left', 'middle'], [-ring, 0, 'right', 'middle'],
          [0, -ring, 'center', 'bottom'], [0, ring, 'center', 'top'],
          [ring, -ring, 'left', 'bottom'], [ring, ring, 'left', 'top'],
          [-ring, -ring, 'right', 'bottom'], [-ring, ring, 'right', 'top']
        );
      }
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
        for (const lid of Chart.services.get(it.st.id)) {
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
        const dirKey = c => Math.sign(c[0]) + ',' + Math.sign(c[1]);
        const ordered = cands.filter(c => !along.has(dirKey(c)))
          .concat(cands.filter(c => along.has(dirKey(c))));

        // 先在空白处找位置；重点站（换乘/终点）找不到时允许压线（带白色描边）
        const passes = it.trans || it.term ? [false, true] : [false];
        let done = false;
        for (const allowInk of passes) {
          if (done) break;
          for (const [dx, dy, align, base] of ordered) {
            // dx/dy 为方向×档位系数：1/1.55/2.2 三档半径，让文字有更多落位空间
            const ox = dx * rr, oy = dy * rr;
            const x = align === 'left' ? p.x + ox : align === 'right' ? p.x + ox - tw : p.x + ox - tw / 2;
            const y = base === 'top' ? p.y + oy : base === 'bottom' ? p.y + oy - th : p.y + oy - th / 2;
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

      g.restore();

      if (!official) {
        /* --- 页眉（纸面上方） --- */
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
        g.fillText((subtitle || 'METRO NETWORK MAP').replace(/_/g, ' '), sx0 + 35 * k, sy0 + 64 * k);

        const compactSheet = sheetW < 540 * k;
        const statsX = compactSheet ? sx0 + 34 * k : sx1 - 34 * k;
        g.textAlign = compactSheet ? 'left' : 'right';
        g.fillStyle = '#55637a';
        g.font = `600 ${Math.round(10.5 * k)}px ${CHART_FONT}`;
        g.fillText(`${nLine} 条线 · ${Chart.pos.size} 座车站`, statsX, sy0 + (compactSheet ? 79 : 44) * k);

        /* --- 页脚图例 --- */
        const ly = sy1 - legendBand;
        g.strokeStyle = 'rgba(28,46,66,0.18)';
        g.lineWidth = 1 * k;
        g.beginPath(); g.moveTo(sx0 + 14 * k, ly); g.lineTo(sx1 - 14 * k, ly); g.stroke();

        g.textAlign = 'left';
        g.textBaseline = 'middle';
        g.font = `600 ${Math.round(9.5 * k)}px ${CHART_FONT}`;
        g.fillStyle = '#8a95a5';
        if (legend.compact) {
          g.fillText('放大查看线路编号和站名 · 挂图包含完整图例', sx0 + 20 * k, ly + 17 * k);
        } else {
          g.fillText('图例 / LEGEND', sx0 + 34 * k, ly + 13 * k);

          const startX = sx0 + 34 * k, startY = ly + 30 * k;
          const colW = (sheetW - 68 * k) / legend.cols;
          let ci = 0;
          for (const line of drawnLines) {
            const col = ci % legend.cols, row = Math.floor(ci / legend.cols);
            const x = startX + col * colW, y = startY + row * 21 * k;
            g.fillStyle = line.color;
            g.fillRect(x, y - 5 * k, 11 * k, 10 * k);
            g.strokeStyle = 'rgba(20,30,46,0.25)';
            g.lineWidth = 0.8 * k;
            g.strokeRect(x, y - 5 * k, 11 * k, 10 * k);
            g.fillStyle = line.enabled ? '#26313f' : '#98a2b1';
            g.font = `500 ${Math.round(10 * k)}px ${CHART_FONT}`;
            g.fillText(line.name, x + 16 * k, y, Math.max(1, colW - 20 * k));
            ci++;
          }

          g.textAlign = 'right';
          g.textBaseline = 'middle';
          g.fillStyle = '#9aa5b5';
          g.font = `500 ${Math.round(9 * k)}px ${CHART_FONT}`;
          g.fillText('灰色虚线为停运线路', sx1 - 32 * k, ly + 13 * k);
        }
      } else {
        /* --- 官方图例卡：左上角白卡，替代页脚长条图例 --- */
        if (legendCard) {
          g.save();
          g.shadowColor = 'rgba(12,30,52,0.16)';
          g.shadowBlur = 16 * k;
          g.shadowOffsetY = 3 * k;
          g.fillStyle = '#ffffff';
          roundRectPath(g, legendCard.x, legendCard.y, legendCard.w, legendCard.h, 5 * k);
          g.fill();
          g.restore();
          g.strokeStyle = 'rgba(16,44,78,0.18)';
          g.lineWidth = 1 * k;
          roundRectPath(g, legendCard.x, legendCard.y, legendCard.w, legendCard.h, 5 * k);
          g.stroke();

          const lx = legendCard.x, ly = legendCard.y;
          g.textAlign = 'left';
          g.textBaseline = 'alphabetic';
          g.fillStyle = '#0b2748';
          g.font = `700 ${Math.round(10 * k)}px ${CHART_FONT}`;
          g.fillText('图例 / LEGEND', lx + 12 * k, ly + 20 * k);
          g.fillStyle = '#8492a4';
          g.font = `500 ${Math.round(6 * k)}px ${CHART_FONT}`;
          const nStLeg = Chart.stations.length;
          g.fillText(`${nLine} LINES · ${nStLeg} STATIONS`, lx + 12 * k, ly + 29 * k);

          const cols = 3;
          const padX = 12 * k, top = ly + 38 * k;
          const colW = (legendCard.w - padX * 2) / cols;
          const rowH = 18 * k;
          let ci = 0;
          for (const line of drawnLines) {
            const col = ci % cols, row = Math.floor(ci / cols);
            const x = lx + padX + col * colW, y = top + row * rowH;
            const cw = colW - 4 * k, chh = 14 * k;
            g.fillStyle = line.enabled ? line.color : '#aab4c2';
            roundRectPath(g, x, y, cw, chh, 3 * k);
            g.fill();
            g.fillStyle = inkOn(line.color);
            g.font = `700 ${Math.round((line.name.length > 5 ? 4.9 : 5.8) * k)}px ${CHART_FONT}`;
            g.textAlign = 'center';
            g.textBaseline = 'middle';
            g.fillText(line.name, x + cw / 2, y + chh / 2 + 0.5 * k);
            ci++;
          }
        }

        /* --- 指北针 --- */
        const nx = sx1 - 58 * k, ny = sy0 + headerH + 62 * k;
        g.save();
        g.translate(nx, ny);
        g.strokeStyle = '#0b3a70';
        g.lineWidth = 1.4 * k;
        g.beginPath(); g.arc(0, 0, 33 * k, 0, Math.PI * 2); g.stroke();
        g.beginPath();
        g.moveTo(0, 24 * k); g.lineTo(-9 * k, -8 * k); g.lineTo(0, -1 * k); g.lineTo(9 * k, -8 * k); g.closePath();
        g.fillStyle = '#0b3a70'; g.fill();
        g.beginPath(); g.moveTo(0, -32 * k); g.lineTo(0, 24 * k); g.strokeStyle = 'rgba(11,58,112,0.25)'; g.stroke();
        g.fillStyle = '#0b3a70';
        g.font = `700 ${Math.round(10 * k)}px ${CHART_FONT}`;
        g.textAlign = 'center'; g.textBaseline = 'middle';
        g.fillText('N', 0, -46 * k);
        g.restore();

        /* --- 页脚 --- */
        const nStFoot = Chart.stations.length;
        g.strokeStyle = 'rgba(20,44,72,0.14)';
        g.lineWidth = 1 * k;
        g.beginPath(); g.moveTo(sx0 + 30 * k, sy1 - 44 * k); g.lineTo(sx1 - 30 * k, sy1 - 44 * k); g.stroke();
        g.textAlign = 'left'; g.textBaseline = 'middle';
        g.fillStyle = '#6f7e90';
        g.font = `500 ${Math.round(8.2 * k)}px ${CHART_FONT}`;
        g.fillText(`${cityCn} · 2026年11月`, sx0 + 30 * k, sy1 - 27 * k);
        g.textAlign = 'right';
        g.fillStyle = '#8b97a7';
        g.font = `500 ${Math.round(7.8 * k)}px ${CHART_FONT}`;
        g.fillText(`${cityEn} · ${nLine} LINES / ${nStFoot} STATIONS`, sx1 - 30 * k, sy1 - 27 * k);
      }

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
      const { W, H } = size();
      if (!Chart.ready) {
        ctx.fillStyle = '#fdfdfa';
        ctx.fillRect(0, 0, W, H);
        ctx.fillStyle = '#24304a';
        ctx.font = '15px ' + CHART_FONT;
        ctx.textAlign = 'center';
        ctx.fillText(Chart.error ? '拓扑图暂时无法生成' : '添加两座相连的车站后可生成拓扑图', W / 2, H / 2);
        return;
      }
      drawChartTo(ctx, W, H, App.cam, 1);
    }

    /* ---------------- 6. 交互与导出 ---------------- */
    function chartExport() {
      if (!Chart.ready || !Chart.bounds) return false;
      const { minX, minY, maxX, maxY } = Chart.bounds;
      const spanX = Math.max(1, maxX - minX), spanY = Math.max(1, maxY - minY);
      const k = 2.5, maxSize = 6000;
      const targetWidth = Chart.stations.length > 250 ? 5600 : 3800;
      const padX = 64 * k;
      const padY = Math.min(700, Math.max(180, 45 + 21 * Math.ceil(Chart.lines.length / 5))) * k;
      const scale = Math.min((targetWidth - 2 * padX) / spanX, (maxSize - 2 * padY) / spanY);
      const width = Math.ceil(Math.max(850 * k, spanX * scale + 2 * padX));
      const height = Math.min(maxSize, Math.ceil(spanY * scale + 2 * padY));
      const source = document.createElement("canvas");
      source.width = width; source.height = height;
      const screenSheet = Chart.sheetRect;
      let sheet;
      Chart.exporting = true;
      try {
        const cam = { x: (minX + maxX) / 2, y: (minY + maxY) / 2, s: scale };
        drawChartTo(source.getContext("2d"), width, height, cam, k);
        sheet = Chart.sheetRect;
      } finally {
        Chart.exporting = false;
        Chart.sheetRect = screenSheet;
      }
      if (!sheet) return false;
      const x = Math.max(0, Math.floor(sheet.x)), y = Math.max(0, Math.floor(sheet.y));
      const w = Math.min(width, Math.ceil(sheet.x + sheet.w)) - x;
      const h = Math.min(height, Math.ceil(sheet.y + sheet.h)) - y;
      if (w < 1 || h < 1) return false;
      const crop = document.createElement("canvas");
      crop.width = w; crop.height = h;
      crop.getContext("2d").drawImage(source, x, y, w, h, 0, 0, w, h);
      source.width = 0;
      const png = crop.toDataURL("image/png");
      crop.width = 0;
      if (!png.startsWith("data:image/png;base64,")) return false;
      Chart.lastExport = { w, h };
      const link = document.createElement("a");
      link.download = (document.title.split("·")[0] || "线网").trim() + "线网图.png";
      link.href = png;
      link.click();
      return true;
    }

    (function bindChartUI() {
      const bind = (id, fn) => { const b = document.getElementById(id); if (b) b.addEventListener('click', fn); };
      bind('btnChartRegen', () => {
        computeChart(true);
        fitChart();
        toast(Chart.ready ? '拓扑图已重新生成' : '当前线网无法生成拓扑图');
      });
      bind('btnChartFit', () => fitChart());
      bind('btnChartPng', () => { toast(chartExport() ? '高清挂图已导出' : '当前线网还没有可导出的拓扑图'); });
    })();
    return { Chart, computeChart, fitChart, drawChart, chartExport };
  }
  return { attach };
})();
