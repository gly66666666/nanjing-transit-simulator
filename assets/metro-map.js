const MetroMap = (() => {
  const dark = {
    ground: ['#07101f', '#081424', '#060d19'],
    chartGround: ['#080f1b', '#0c1626', '#070c15'],
    grid: 'rgba(84,132,196,0.07)',
    region: 'rgba(122,164,206,0.26)',
    hill: 'rgba(36,84,52,0.42)',
    hillEnd: 'rgba(36,84,52,0)',
    lake: 'rgba(28,74,102,0.5)',
    lakeEdge: 'rgba(70,140,180,0.28)',
    riverBank: 'rgba(10,26,42,0.9)',
    river: 'rgba(21,52,78,0.92)',
    riverCenter: 'rgba(58,116,158,0.12)',
    riverName: 'rgba(132,190,230,0.34)',
    areaName: 'rgba(219,238,255,0.94)',
    areaNameHalo: 'rgba(4,10,18,0.8)',
    areaDetail: 'rgba(124,178,226,0.85)',
    lightLineEdge: 'rgba(6,14,26,0.8)',
    darkLineEdge: 'rgba(206,226,248,0.22)',
    constructionGap: 'rgba(6,13,24,0.96)',
    orphan: 'rgba(150,185,225,0.10)',
    orphanEdge: 'rgba(160,195,232,0.9)',
    station: '#dfe9f8',
    stationEdge: null,
    transferRing: '#f2f8ff',
    transferCenter: '#0b1524',
    transferEdge: 'rgba(10,20,35,0.65)',
    terminalRing: 'rgba(255,255,255,0.62)',
    labelHalo: 'rgba(5,10,18,0.88)',
    labelTerminal: '#ffffff',
    labelTransfer: '#eaf3ff',
    label: 'rgba(190,208,230,0.78)',
    editAccent: '#28d7c0',
    editHalo: 'rgba(40,215,192,0.35)',
    finishedShade: 'rgba(0,0,0,0.32)',
  };
  const light = {
    ground: ['#f7f9fc', '#edf3f9', '#e8eff7'],
    chartGround: ['#eaf0f6', '#e0e9f3', '#e6eef6'],
    grid: 'rgba(55,88,124,0.10)',
    region: '#60758b',
    hill: 'rgba(117,174,117,0.32)',
    hillEnd: 'rgba(117,174,117,0)',
    lake: 'rgba(153,205,231,0.58)',
    lakeEdge: 'rgba(98,159,194,0.55)',
    riverBank: '#c9dfed',
    river: '#b3d7e9',
    riverCenter: 'rgba(245,253,255,0.25)',
    riverName: '#406d8b',
    areaName: '#294b65',
    areaNameHalo: 'rgba(249,252,255,0.9)',
    areaDetail: '#4e6f89',
    lightLineEdge: 'rgba(31,50,71,0.72)',
    darkLineEdge: 'rgba(255,255,255,0.88)',
    constructionGap: '#edf3f9',
    orphan: 'rgba(70,101,134,0.10)',
    orphanEdge: '#42617f',
    station: '#c5daee',
    stationEdge: '#294761',
    transferRing: '#ffffff',
    transferCenter: '#273d55',
    transferEdge: '#294761',
    terminalRing: 'rgba(39,61,85,0.7)',
    labelHalo: 'rgba(255,255,255,0.96)',
    labelTerminal: '#142941',
    labelTransfer: '#1b334c',
    label: '#3c546d',
    editAccent: '#087d72',
    editHalo: 'rgba(8,125,114,0.34)',
    finishedShade: 'rgba(27,56,88,0.12)',
  };

  function palette() {
    return document.documentElement.dataset.theme === 'light' ? light : dark;
  }

  function fillOrdinaryStation(context, colors, radius) {
    context.fillStyle = colors.station;
    context.fill();
    if (colors.stationEdge) {
      context.strokeStyle = colors.stationEdge;
      context.lineWidth = Math.min(1.35, radius * 0.7);
      context.stroke();
    }
  }

  function isPlannedArm(stations, definition, index) {
    const matches = original => original?.length === stations.length &&
      stations.every((id, i) => id === original[i]);
    if (index === 0) return !matches(definition?.stations);
    return !definition?.arms?.some(arm => matches(arm.stations));
  }

  // 相邻段共用站点切线，控制柄受较短站间距限制。
  function tangent(previous, point, next) {
    const dx = next.x - point.x, dy = next.y - point.y;
    if (!previous) return { x: dx / 3, y: dy / 3 };
    const ax = point.x - previous.x, ay = point.y - previous.y;
    const before = Math.hypot(ax, ay), after = Math.hypot(dx, dy);
    if (!before || !after) return { x: 0, y: 0 };
    const x = ax / before + dx / after;
    const y = ay / before + dy / after;
    const scale = Math.min(before, after) * 0.11;
    return { x: x * scale, y: y * scale };
  }

  function controls(previous, start, end, next) {
    const outgoing = tangent(previous, start, end);
    const incoming = tangent(next, end, start);
    return [
      { x: start.x + outgoing.x, y: start.y + outgoing.y },
      { x: end.x + incoming.x, y: end.y + incoming.y },
    ];
  }

  function tracePlannedPath(context, points, first = 0, last = points.length - 1) {
    context.beginPath();
    if (first >= last) return;
    context.moveTo(points[first].x, points[first].y);
    if (points.length === 2) {
      context.lineTo(points[last].x, points[last].y);
      return;
    }
    for (let i = first; i < last; i++) {
      const end = points[i + 1];
      const [a, b] = controls(points[i - 1], points[i], end, points[i + 2]);
      context.bezierCurveTo(a.x, a.y, b.x, b.y, end.x, end.y);
    }
  }

  function trainPose(stations, route, i, progress, reverse) {
    const start = stations.get(route[i]), end = stations.get(route[i + 1]);
    const [a, b] = controls(stations.get(route[i - 1]), start, end, stations.get(route[i + 2]));
    const t = reverse ? 1 - progress : progress;
    const u = 1 - t;
    const x = u ** 3 * start.x + 3 * u * u * t * a.x + 3 * u * t * t * b.x + t ** 3 * end.x;
    const y = u ** 3 * start.y + 3 * u * u * t * a.y + 3 * u * t * t * b.y + t ** 3 * end.y;
    const dx = u * u * (a.x - start.x) + 2 * u * t * (b.x - a.x) + t * t * (end.x - b.x);
    const dy = u * u * (a.y - start.y) + 2 * u * t * (b.y - a.y) + t * t * (end.y - b.y);
    const angle = dx || dy ? Math.atan2(dy, dx) : Math.atan2(end.y - start.y, end.x - start.x);
    return { x, y, angle: angle + (reverse ? Math.PI : 0) };
  }

  function writeNetworkSave(storage, key, record) {
    let old;
    try { old = JSON.parse(storage.getItem(key)); } catch {}
    if (typeof old?.sig === 'string' && old.snap && (old.sig !== record.sig || old.ver !== record.ver)) {
      const backupKey = key + ':backup:' + old.ver + ':' + old.sig;
      if (storage.getItem(backupKey) === null) storage.setItem(backupKey, JSON.stringify(old));
    }
    storage.setItem(key, JSON.stringify(record));
  }
  function copyArm(arm) {
    const route = { stations: [...arm.stations] };
    if (arm.hidden) Object.assign(route, { hidden: true, name: arm.name, headway: arm.headway });
    return route;
  }

  function restoreServiceArms(arms, definition) {
    const services = definition?.arms?.filter(arm => arm.hidden);
    if (!services?.length) return;
    const visibleStations = new Set(arms.filter(arm => !arm.hidden).flatMap(arm => arm.stations));
    for (const route of services) {
      if (!route.stations.every(station => visibleStations.has(station))) continue;
      const existing = arms.findIndex((arm, index) => index > 0 &&
        arm.stations.length === route.stations.length &&
        arm.stations.every((station, i) => station === route.stations[i]));
      if (existing === -1) arms.push(copyArm(route));
      else arms[existing] = copyArm(route);
    }
  }

  return { palette, fillOrdinaryStation, isPlannedArm, tracePlannedPath, trainPose, writeNetworkSave, copyArm, restoreServiceArms };
})();
