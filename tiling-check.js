/* tessellation-mobile-workspace-v2 / tiling-check.js  (v5.5-fx: FX-1 tolerant matching, FX-2 signed corner angles; see FX_REPORT.md)
 * INDEPENDENT tiling proof. It does NOT use the engine's tile list or its centroid de-duplication.
 * It re-generates the tile group from the glue relations, keyed by the full matrix, and tests the tessellation
 * combinatorially on the CURRENT (deformed) boundary:
 *   1. FREENESS   – no two different group elements place the cell on the same spot (else tiles would overlap and be hidden by de-dup)
 *   2. EDGES      – every interior edge polyline coincides with exactly one other tile's edge (0 = gap, >1 = overlap)
 *   3. VERTICES   – at every interior vertex the straight-cell interior angles of the incident tiles sum to 360°
 *   4. CLOSURE    – for each tile and each glue relation, the neighbour's matching edge coincides with ours in world space
 *   5. ENGINE     – the engine's own (centroid-deduplicated) tile list has the same number of tiles as the independent group
 * v5.5 (FX): points, matrices and edges are matched WITH A TOLERANCE (a spatial hash that also looks in the neighbouring cells), never by
 * rounding, so a coordinate on a rounding boundary can no longer split one thing into two; corner angles are SIGNED, so a corner over 180°
 * (a non-convex cell) is measured correctly.
 */
(function (root) {
'use strict';
const E = root.TessEngine, { mmul, mapp, P, N } = E;

// a set of points with a tolerance: items are found within `tol` of a point, looking in the 3×3 neighbouring hash cells
function nearSet(cell, tol) {
  const cells = new Map(), key = (i, j) => i + ',' + j;
  return {
    find(p, accept) { const i = Math.floor(p.x / cell), j = Math.floor(p.y / cell);
      for (let a = -1; a <= 1; a++) for (let b = -1; b <= 1; b++) { const l = cells.get(key(i + a, j + b)); if (!l) continue;
        for (const it of l) if (Math.hypot(it.p.x - p.x, it.p.y - p.y) < tol && (!accept || accept(it))) return it; }
      return null; },
    add(p, item) { const k = key(Math.floor(p.x / cell), Math.floor(p.y / cell)); if (!cells.has(k)) cells.set(k, []); item.p = p; cells.get(k).push(item); return item; }
  };
}
const sameMatrix = (m, n, tol) => m.every((v, i) => Math.abs(v - n[i]) < (i < 4 ? 1e-9 : tol));

function check(opts = {}) {
  const st = E.state, V = st.cons.verts, n = V.length, edges = st.edges, maxR = opts.radius || 5;
  const xs = V.map(p => p.x), ys = V.map(p => p.y), size = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys));
  const c0 = P(V.reduce((s, p) => s + p.x, 0) / n, V.reduce((s, p) => s + p.y, 0) / n), R = maxR * size;
  const TOL = 1e-6 * size, CELL = 1e-3 * size;
  const gens = []; st.rels.forEach(r => { if (r.role !== 'glue') return; gens.push({ r, m: r.m, which: r.self !== undefined ? 'self' : 'to' }); if (r.self === undefined) gens.push({ r, m: r.inv, which: 'from' }); });

  // group, de-duplicated by the whole matrix (indexed by the image of a generic point, compared entry by entry)
  const IDM = [1, 0, 0, 1, 0, 0], probe = P(c0.x + 0.1234 * size, c0.y + 0.0567 * size), group = nearSet(CELL, TOL), list = [IDM], q = [IDM];
  group.add(mapp(IDM, probe), { m: IDM });
  while (q.length && list.length < 6000) { const m = q.shift();
    gens.forEach(g => { const nm = mmul(m, g.m), pr = mapp(nm, probe); if (group.find(pr, it => sameMatrix(it.m, nm, TOL))) return;
      const p = mapp(nm, c0); if (Math.hypot(p.x - c0.x, p.y - c0.y) > R) return; group.add(pr, { m: nm }); list.push(nm); q.push(nm); }); }

  // 1. freeness: different group elements that put the cell centre on the same spot
  const places = nearSet(CELL, TOL), placeItems = [];
  list.forEach(m => { const p = mapp(m, c0), it = places.find(p); if (it) it.count++; else placeItems.push(places.add(p, { count: 1 })); });
  const collisions = placeItems.filter(it => it.count > 1).length;

  // 2. edge multiplicity (interior = tile centroid within 0.55 R): an edge is indexed by its middle sample and matched point by point,
  //    in either direction
  const emap = nearSet(CELL, TOL), interior = list.filter(m => { const p = mapp(m, c0); return Math.hypot(p.x - c0.x, p.y - c0.y) <= 0.55 * R; });
  const samePts = (a, b) => { let f = true, r = true; for (let k = 0; k <= N && (f || r); k++) { if (f && Math.hypot(a[k].x - b[k].x, a[k].y - b[k].y) >= TOL) f = false; if (r && Math.hypot(a[k].x - b[N - k].x, a[k].y - b[N - k].y) >= TOL) r = false; } return f || r; };
  const edgeOf = (m, ei) => edges[ei].pts.map(p => mapp(m, p));
  const groupOf = pts => emap.find(pts[N / 2], it => samePts(it.pts, pts));
  list.forEach(m => { for (let ei = 0; ei < n; ei++) { const pts = edgeOf(m, ei), it = groupOf(pts); if (it) it.count++; else emap.add(pts[N / 2], { pts, count: 1 }); } });
  let edgesOnce = 0, edgesTwice = 0, edgesMore = 0;
  interior.forEach(m => { for (let ei = 0; ei < n; ei++) { const c = groupOf(edgeOf(m, ei)).count; if (c === 1) edgesOnce++; else if (c === 2) edgesTwice++; else edgesMore++; } });

  // 3. vertex angle sums on the straight cell (corners are pinned, so this is exact). FX-2: SIGNED interior angles (0°–360°), measured
  //    with the cell's own orientation, so a corner over 180° counts as such
  let ar = 0; V.forEach((p, i) => { const r2 = V[(i + 1) % n]; ar += p.x * r2.y - r2.x * p.y; }); const orient = ar > 0 ? 1 : -1;
  const ang = i => { const a = V[(i + n - 1) % n], b = V[i], c = V[(i + 1) % n], wx = c.x - b.x, wy = c.y - b.y, ux = a.x - b.x, uy = a.y - b.y;
    let t = Math.atan2(orient * (wx * uy - wy * ux), wx * ux + wy * uy); if (t <= 0) t += 2 * Math.PI; return t * 180 / Math.PI; };
  const angles = V.map((_, i) => ang(i)), vsum = nearSet(CELL, TOL);
  list.forEach(m => V.forEach((v, i) => { const p = mapp(m, v), it = vsum.find(p); if (it) it.sum += angles[i]; else vsum.add(p, { sum: angles[i] }); }));
  let vertsChecked = 0, vertsBad = 0, worstVertex = 0;
  interior.forEach(m => V.forEach(v => { const p = mapp(m, v); if (Math.hypot(p.x - c0.x, p.y - c0.y) > 0.45 * R) return; const t = vsum.find(p).sum; vertsChecked++; const d = Math.abs(t - 360); worstVertex = Math.max(worstVertex, d); if (d > 1e-6) vertsBad++; }));

  // 4. closure in world space: for every tile and relation the neighbour's matching edge coincides
  let maxMismatch = 0, closureChecks = 0;
  interior.forEach(m => gens.forEach(g => {
    const r = g.r, nm = mmul(m, g.m), src = g.which === 'from' ? r.to : r.self !== undefined ? r.self : r.from;
    const shared = g.which === 'from' ? r.from : r.self !== undefined ? r.self : r.to, mine = edges[shared].pts.map(p => mapp(m, p)), theirs = edges[src].pts.map(p => mapp(nm, p));
    const f2 = Math.max(...mine.map((p, k) => Math.hypot(p.x - theirs[k].x, p.y - theirs[k].y))), r2 = Math.max(...mine.map((p, k) => Math.hypot(p.x - theirs[N - k].x, p.y - theirs[N - k].y)));
    maxMismatch = Math.max(maxMismatch, Math.min(f2, r2)); closureChecks++;
  }));
  const engineCount = opts.engineCount === undefined ? E.makeTiling(maxR).list.length : opts.engineCount;
  const bruteSame = list.length === engineCount;
  const ok = collisions === 0 && edgesOnce === 0 && edgesMore === 0 && vertsBad === 0 && maxMismatch < 1e-9 && bruteSame;
  return { id: st.cons.id, ok, tiles: list.length, interiorTiles: interior.length, collisions, edgesTwice, edgesOnce, edgesMore, vertsChecked, vertsBad, worstVertexDeg: worstVertex, closureChecks, maxMismatch, engineTiles: engineCount, countsMatch: bruteSame };
}
root.TilingCheck = { check };
})(window);
