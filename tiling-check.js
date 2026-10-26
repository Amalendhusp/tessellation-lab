/* tessellation-mobile-workspace-v2 / tiling-check.js
 * INDEPENDENT tiling proof. It does NOT use the engine's tile list or its centroid de-duplication.
 * It re-generates the tile group from the glue relations, keyed by the full matrix, and tests the tessellation
 * combinatorially on the CURRENT (deformed) boundary:
 *   1. FREENESS   – no two different group elements place the cell on the same spot (else tiles would overlap and be hidden by de-dup)
 *   2. EDGES      – every interior edge polyline coincides with exactly one other tile's edge (0 = gap, >1 = overlap)
 *   3. VERTICES   – at every interior vertex the straight-cell interior angles of the incident tiles sum to 360°
 *   4. CLOSURE    – for each tile and each glue relation, the neighbour's matching edge coincides with ours in world space
 *   5. ENGINE     – the engine's own (centroid-deduplicated) tile list has the same number of tiles as the independent group
 */
(function (root) {
'use strict';
const E = root.TessEngine, { mmul, minv, mapp, det, P, N } = E;
const key6 = m => m.map(v => Math.round(v * 1e4)).join(',');
// the irrational-ish offset keeps lattice coordinates (e.g. k/96 multiples) off exact rounding boundaries, which gave false 'edge shared once' results
const rk = (x, y) => Math.round(x * 1e5 + 0.3719) + ',' + Math.round(y * 1e5 + 0.2713);

function check(opts = {}) {
  const st = E.state, V = st.cons.verts, n = V.length, edges = st.edges, maxR = opts.radius || 5;
  const xs = V.map(p => p.x), ys = V.map(p => p.y), size = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys));
  const c0 = P(V.reduce((s, p) => s + p.x, 0) / n, V.reduce((s, p) => s + p.y, 0) / n), R = maxR * size;
  const gens = []; st.rels.forEach(r => { if (r.role !== 'glue') return; gens.push({ r, m: r.m, which: r.self !== undefined ? 'self' : 'to' }); if (r.self === undefined) gens.push({ r, m: r.inv, which: 'from' }); });

  // group, keyed by the whole matrix
  const IDM = [1, 0, 0, 1, 0, 0], seen = new Map([[key6(IDM), IDM]]), list = [IDM], q = [IDM];
  while (q.length && list.length < 6000) { const m = q.shift();
    gens.forEach(g => { const nm = mmul(m, g.m), k = key6(nm); if (seen.has(k)) return; const p = mapp(nm, c0); if (Math.hypot(p.x - c0.x, p.y - c0.y) > R) return; seen.set(k, nm); list.push(nm); q.push(nm); }); }

  // 1. freeness
  const place = new Map(); list.forEach(m => { const p = mapp(m, c0), k = rk(p.x, p.y); place.set(k, (place.get(k) || 0) + 1); });
  const collisions = [...place.values()].filter(c => c > 1).length;

  // 2. edge multiplicity (interior = tile centroid within 0.55 R)
  const edgeKey = (m, ei) => { const pts = edges[ei].pts.map(p => mapp(m, p)).map(p => rk(p.x, p.y)); pts.sort(); return pts.join(';'); };
  const emap = new Map(), interior = list.filter(m => { const p = mapp(m, c0); return Math.hypot(p.x - c0.x, p.y - c0.y) <= 0.55 * R; });
  list.forEach(m => { for (let ei = 0; ei < n; ei++) { const k = edgeKey(m, ei); emap.set(k, (emap.get(k) || 0) + 1); } });
  let edgesOnce = 0, edgesTwice = 0, edgesMore = 0;
  interior.forEach(m => { for (let ei = 0; ei < n; ei++) { const c = emap.get(edgeKey(m, ei)); if (c === 1) edgesOnce++; else if (c === 2) edgesTwice++; else edgesMore++; } });
  // 3. vertex angle sums on the straight cell (corners are pinned, so this is exact)
  const ang = i => { const a = V[(i + n - 1) % n], b = V[i], c = V[(i + 1) % n], u = P(a.x - b.x, a.y - b.y), w = P(c.x - b.x, c.y - b.y);
    return Math.acos((u.x * w.x + u.y * w.y) / (Math.hypot(u.x, u.y) * Math.hypot(w.x, w.y))) * 180 / Math.PI; };
  const vsum = new Map(); list.forEach(m => V.forEach((v, i) => { const p = mapp(m, v), k = rk(p.x, p.y); vsum.set(k, (vsum.get(k) || 0) + ang(i)); }));
  let vertsChecked = 0, vertsBad = 0, worstVertex = 0;
  interior.forEach(m => V.forEach(v => { const p = mapp(m, v), t = vsum.get(rk(p.x, p.y)); if (Math.hypot(p.x - c0.x, p.y - c0.y) > 0.45 * R) return; vertsChecked++; const d = Math.abs(t - 360); worstVertex = Math.max(worstVertex, d); if (d > 1e-6) vertsBad++; }));
  // 4. closure in world space: for every tile and relation the neighbour's matching edge coincides
  let maxMismatch = 0, closureChecks = 0;
  interior.forEach(m => gens.forEach(g => {
    const r = g.r, nm = mmul(m, g.m), src = g.which === 'from' ? r.to : r.self !== undefined ? r.self : r.from, dst = g.which === 'from' ? r.from : r.self !== undefined ? r.self : r.to;
    const a = edges[src].pts.map(p => mapp(nm, p)), b = edges[dst].pts.map(p => mapp(m, p));
    // our edge `dst` of tile m must coincide with the neighbour's edge `src` (same set of points, order may be reversed)
    const fwd = Math.max(...a.map((p, k) => Math.hypot(p.x - b[k].x, p.y - b[k].y))), rev = Math.max(...a.map((p, k) => Math.hypot(p.x - b[N - k].x, p.y - b[N - k].y)));
    // the neighbour edge is the image of the *partner* edge; compare to the edge of m that the neighbour shares
    const shared = g.which === 'from' ? r.from : r.self !== undefined ? r.self : r.to, mine = edges[shared].pts.map(p => mapp(m, p)), theirs = edges[src].pts.map(p => mapp(nm, p));
    const f2 = Math.max(...mine.map((p, k) => Math.hypot(p.x - theirs[k].x, p.y - theirs[k].y))), r2 = Math.max(...mine.map((p, k) => Math.hypot(p.x - theirs[N - k].x, p.y - theirs[N - k].y)));
    void fwd; void rev; maxMismatch = Math.max(maxMismatch, Math.min(f2, r2)); closureChecks++;
  }));
  const engineCount = opts.engineCount === undefined ? E.makeTiling(maxR).list.length : opts.engineCount;
  const bruteSame = list.length === engineCount;
  const ok = collisions === 0 && edgesOnce === 0 && edgesMore === 0 && vertsBad === 0 && maxMismatch < 1e-9 && bruteSame;
  return { id: st.cons.id, ok, tiles: list.length, interiorTiles: interior.length, collisions, edgesTwice, edgesOnce, edgesMore, vertsChecked, vertsBad, worstVertexDeg: worstVertex, closureChecks, maxMismatch, engineTiles: engineCount, countsMatch: bruteSame };
}
root.TilingCheck = { check };
})(window);
