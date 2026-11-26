const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');
const vm = require('node:vm');

const root = path.join(__dirname, '..');
const read = name => fs.readFileSync(path.join(root, name), 'utf8');
const layout = vm.compileFunction(read('assets/octi-layout.js') + '\nreturn octiLayout;')();
const epsilon = 1e-7;

function cityData(file) {
  const html = read(file);
  const data = [...html.matchAll(/<script\b[^>]*>([\s\S]*?)<\/script>/g)]
    .map(match => match[1]).find(script => script.includes('const LINE_DEFS'));
  return vm.runInNewContext(data + '\n;(' + function () {
    return {
      lines: LINE_DEFS.map(line => ({
        id: line.id,
        arms: [line.stations, ...(line.arms || []).filter(arm => !arm.hidden).map(arm => arm.stations || arm)]
      })),
      stations: Object.fromEntries(Object.entries(COORD).map(([id, [lng, lat]]) =>
        [id, { x: (lng - LNG0) * KX, y: (LAT0 - lat) * KY }]))
    };
  } + ')()');
}

function heading(a, b) {
  const dx = b.x - a.x, dy = b.y - a.y;
  assert(Math.hypot(dx, dy) > epsilon);
  assert(Math.min(Math.abs(dx), Math.abs(dy), Math.abs(Math.abs(dx) - Math.abs(dy))) < epsilon);
  return { x: dx, y: dy };
}

function assertTurn(previous, next, lineId) {
  const dot = (previous.x * next.x + previous.y * next.y) /
    (Math.hypot(previous.x, previous.y) * Math.hypot(next.x, next.y));
  assert(dot >= -epsilon, lineId + ' has a turn with an interior angle below 90°');
  return dot;
}

function meetsSegment(p, a, b) {
  if (p.x < Math.min(a.x, b.x) - epsilon || p.x > Math.max(a.x, b.x) + epsilon ||
      p.y < Math.min(a.y, b.y) - epsilon || p.y > Math.max(a.y, b.y) + epsilon) return false;
  const dx = b.x - a.x, dy = b.y - a.y;
  return Math.abs((p.x - a.x) * dy - (p.y - a.y) * dx) <= epsilon * Math.hypot(dx, dy);
}

function assertNetwork(data) {
  const result = layout(data);
  const { routes, outPos } = result;
  const lines = data.lines.map(line => ({
    ...line,
    // 同一个站连续出现时仍只有一个可绘制的站位和停靠标记。
    arms: line.arms.map(arm => arm.filter((id, i) => i === 0 || id !== arm[i - 1]))
      .filter(arm => arm.length > 1)
  }));
  const services = new Map();
  const positions = new Set();
  for (const point of Object.values(outPos)) {
    const key = [point.x, point.y].map(n => n.toFixed(7)).join(',');
    assert(!positions.has(key), 'Distinct stations share a position');
    positions.add(key);
  }
  for (const line of lines) {
    for (const station of new Set(line.arms.flat())) {
      if (!services.has(station)) services.set(station, new Set());
      services.get(station).add(line.id);
    }
  }
  assert.equal(positions.size, services.size);
  const allStops = Object.entries(outPos);
  const sharedTracks = new Map();
  for (const line of lines) {
    const transfers = new Set(line.arms.flat().filter(id => services.get(id).size > 1));
    for (const arm of line.arms.filter(stations => stations.length > 1)) {
      const route = routes.find(r => r.line === line.id && r.arm.length === arm.length &&
        r.arm.every((id, i) => id === arm[i]));
      assert(route, line.id + ' is missing an arm');
      const markers = route.points.flatMap((point, i) => point.station ? [i] : []);
      assert.equal(markers.length, arm.length, line.id + ' is missing a stop');
      for (const [i, id] of arm.entries()) {
        assert(outPos[id], id + ' is missing its position');
        const point = route.points[markers[i]];
        assert(Math.hypot(point.x - outPos[id].x, point.y - outPos[id].y) < epsilon,
          line.id + ' does not reach ' + id + ' in order');
        if (!i) continue;
        const prev = arm[i - 1];
        const key = JSON.stringify([line.id, ...[prev, id].sort()]);
        const track = route.points.slice(markers[i - 1], markers[i] + 1).map(p => [p.x, p.y]);
        if (prev > id) track.reverse();
        if (sharedTracks.has(key)) assert.deepEqual(track, sharedTracks.get(key),
          line.id + ' has multiple tracks for the same pair of stops');
        else sharedTracks.set(key, track);
      }
      const served = new Set(arm);
      for (const [id, p] of allStops) {
        if (served.has(id)) continue;
        for (let i = 1; i < route.points.length; i++) {
          if (meetsSegment(p, route.points[i - 1], route.points[i])) {
            assert.fail(line.id + ' passes through a station it does not serve: ' + id);
          }
        }
      }
      const closed = arm[0] === arm.at(-1);
      const straight = line.arms.length === 1 && transfers.size <= 1 && !closed;
      const directions = route.points.slice(1).map((p, i) => heading(route.points[i], p));
      if (closed) directions.push(directions[0]);
      for (let i = 1; i < directions.length; i++) {
        const dot = assertTurn(directions[i - 1], directions[i], line.id);
        if (straight) assert(dot > 1 - epsilon, line.id + ' must be straight');
      }
    }
  }
  return result;
}

const pages = fs.readdirSync(root).filter(file => /(?:模拟器|总图)\.html$/.test(file));
for (const page of pages) {
  test(page + ' — station order, shared track, false stops and angles', () => assertNetwork(cityData(page)));
}

test('cross-city branch, cycle and disconnected line with conflicting coordinates', () => {
  const data = {
    lines: [
      { id: 'Cross-city', arms: [['west', 'union', 'union', 'mid', 'east'], ['north', 'union', 'mid', 'south']] },
      { id: 'Loop', arms: [['union', 'loop-one', 'loop-two', 'union']] },
      { id: 'Airport', arms: [['east', 'airport']] },
      { id: 'Independent', arms: [['independent-west', 'independent-east']] }
    ],
    stations: Object.fromEntries(Object.entries({
      west: [-18, 0], union: [0, 0], mid: [0, 0], east: [10, 0], north: [-4, -5], south: [8, 8],
      'loop-one': [4, -8], 'loop-two': [6, -2], airport: [16, 3],
      'independent-west': [-18, 0], 'independent-east': [16, 3]
    }).map(([id, [x, y]]) => [id, { x, y }]))
  };
  const result = assertNetwork(data);
  assert.equal(result.metrics.components, 2);
  assert.deepEqual(layout(data).routes, result.routes);
});
