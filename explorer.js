/* tessellation-mobile-workspace-v6.6-grid-m2b-split / explorer.js — the GRID EXPLORER: merge faces of the triangular grid (M2A), classified
 * (v6.2), shared vertex movement (checkpoint 1), adding / moving / removing points (checkpoint 2), merging two junctions by dragging one
 * onto the other, two-finger zoom and pan (v6.5), and now ADD AN EDGE THAT SPLITS A SHAPE.
 *   - ＋ Edge: tap a first point on a shape (a corner, an added point, or any place on an edge), then a second point on the same shape.
 *     The new edge and the two shapes it makes are shown in EVERY copy, with a note saying what changes; “Add this edge” keeps it — only
 *     if the full checks pass — and “Cancel” leaves the grid as it was. A pair that cannot be joined shows a red line and the reason.
 *   - Tap an edge: a menu offers “Add a point here” and “Merge the two shapes”.
 *   - Drag a dot: it follows the finger as far as the tiling stays valid. When the FINGER comes within reach of another junction (or
 *     point), the merge of the two is worked out (move.js contract): if it is possible, the grid is shown as it would be after the merge
 *     (every copy) with a note saying what changes; if not, the other point is ringed in red and the note says why. Releasing there
 *     commits the merge — only if the full checks pass — or, if it is not possible, puts everything back as it was before the drag.
 *   - Tap a dot: remove an added point or a point between two shapes; a junction explains why it cannot simply be removed.
 *   - Two fingers: pinch to zoom, move to pan (the view stays within one repeat block: the picture is the same one block over).
 *   - Undo / Redo cover every step, and keep the zoom. The title shows the classified NAME; the pill shows VALIDITY only.
 * The Grid Lab stays a separate page. window.__ex is for the test tools. */
(() => {
'use strict';
const G = window.TessGrid, T = window.TessTopo, Mg = window.TessMerge, Mv = window.TessMove, C = window.TessClassify, P = G.P, $ = id => document.getElementById(id);
const cv = $('cv'), ctx = cv.getContext('2d');
const FILL = { 3: '#f7e6b8', 4: '#cde9e2', 5: '#e6d6f3', 6: '#d6e4f7', 7: '#f6d5c8', 8: '#f4d7dc', 9: '#efe0c8', 10: '#d9ecf0', 11: '#ece3f5', 12: '#dcedcb' };
const fillFor = n => FILL[n] || '#e9e3d6', EDGE = '#1d1b18', HI = '#f2a93b', BAD = '#ff4d4d', NODE = '#2bb3a3', HIT_PX = 22, TAP_PX = 12, VTX_PX = 16, DRAG_PX = 5, SNAP_PX = 22, SPAN_MIN = 2.5, SPAN_MAX = 16;
const X = { hist: [Mv.newState('2')], hp: 0, span: 7.2, center: null, snap: null, add: null, showBlock: false, patch: null, view: null, pressed: null, flash: null, last: null, info: null, checks: new Map(), drag: null, lastDrag: null };
const cur = () => X.hist[X.hp];

/* ---------------- view and patch ---------------- */
function lattice() { return Mg.base(cur().block).sc.lattice; }
// the view keeps its zoom (span: world units across the shorter side) and centre through Undo, merges and new blocks
function fit() {
  const dpr = Math.min(3, window.devicePixelRatio || 1), w = window.innerWidth, h = window.innerHeight; cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
  const top = 62, bottom = $('dock').offsetHeight + 4, availH = Math.max(160, h - top - bottom), L = lattice(), c = X.center || P((L.b1.x + L.b2.x) / 2, (L.b1.y + L.b2.y) / 2);
  X.view = { dpr, w, h, base: Math.min(w, availH), s: Math.min(w, availH) / X.span, cx: w / 2, cy: top + availH / 2, x: c.x, y: c.y }; wrapView();
}
// the picture is the same one repeat block over: keep the view's centre in the central block
function wrapView() { const L = lattice(), uv = G.toLat(L, P(X.view.x, X.view.y)), fx = Math.floor(uv[0]), fy = Math.floor(uv[1]); let sh = P(0, 0);
  if (fx || fy) { sh = G.fromLat(L, fx, fy); X.view.x -= sh.x; X.view.y -= sh.y; } X.center = P(X.view.x, X.view.y); return sh; }
const patchN = (g, v) => { const L = g.lattice, R = Math.hypot(v.w, v.h) / (2 * v.s) + 1 + Math.hypot(L.b1.x + L.b2.x, L.b1.y + L.b2.y), hmin = Math.abs(G.latDet(L)) / Math.max(Math.hypot(L.b1.x, L.b1.y), Math.hypot(L.b2.x, L.b2.y)); return Math.min(24, Math.ceil(R / hmin) + 1); };
const w2s = p => P(X.view.cx + (p.x - X.view.x) * X.view.s, X.view.cy - (p.y - X.view.y) * X.view.s);
const s2w = (x, y) => P(X.view.x + (x - X.view.cx) / X.view.s, X.view.y - (y - X.view.cy) / X.view.s);
function rebuild() {
  const st = cur(), g = Mv.gridOf(st), L = g.lattice, n = patchN(g, X.view);
  const patch = G.buildPatch(g, { n }), d = Mv.describe(st), corners = new Map(d.faces.map(f => [f.id, f.corners]));
  patch.faces.forEach(f => { f.fill = fillFor(corners.get(f.cls)); });
  // one copy of each shape: the one whose centre lies in the central block
  const rep = new Map(); patch.faces.forEach(f => { const [u, w] = G.toLat(L, f.centroid); if (u >= -1e-9 && u < 1 - 1e-9 && w >= -1e-9 && w < 1 - 1e-9 && !rep.has(f.cls)) rep.set(f.cls, f.id); });
  patch.faces.forEach(f => { if (!rep.has(f.cls) && f.at[0] === 0 && f.at[1] === 0) rep.set(f.cls, f.id); });
  X.patch = patch; X.rep = new Set(rep.values()); X.info = d; syncUI();
}
// the grid of another state, ready to draw (the merge preview): only what drawing needs — each shape's outline, edge and point, copied
// over the copies on screen (no half-edges or neighbour links, so it is quick to make while a finger is moving)
function previewPatch(st) {
  const g = Mv.gridOf(st), d = Mv.describe(st), corners = new Map(d.faces.map(f => [f.id, f.corners])), L = g.lattice, v = X.view, R = Math.hypot(v.w, v.h) / (2 * v.s) + 1, c = P(v.x, v.y);
  const offs = [], n = patchN(g, v); for (let i = -n; i <= n; i++) for (let j = -n; j <= n; j++) { const o = G.latVec(L, [i, j]); if (Math.hypot(o.x + L.b1.x / 2 + L.b2.x / 2 - c.x, o.y + L.b1.y / 2 + L.b2.y / 2 - c.y) <= R + Math.hypot(L.b1.x + L.b2.x, L.b1.y + L.b2.y)) offs.push([i, j, o]); }
  const sh = (pts, o) => pts.map(p => P(p.x + o.x, p.y + o.y)), faces = [], edges = [], vertices = [];
  g.faces.forEach(fc => { const ol = G.faceOutline(g, fc, [0, 0]).pts, fill = fillFor(corners.get(fc.id)); offs.forEach(([i, j, o]) => faces.push({ cls: fc.id, at: [i, j], outline: sh(ol, o), fill })); });
  g.edges.forEach(ec => { const l = G.edgeLine(g, ec, [0, 0]), nd = G.edgeNodes(g, ec, [0, 0]); offs.forEach(([i, j, o]) => edges.push({ cls: ec.id, at: [i, j], pts: sh(l, o), nodes: sh(nd, o) })); });
  g.vertices.forEach(vc => offs.forEach(([i, j, o]) => vertices.push({ cls: vc.id, at: [i, j], pos: P(vc.pos.x + o.x, vc.pos.y + o.y) })));
  return { faces, edges, vertices, grid: g, n };
}

/* ---------------- drawing ---------------- */
function path(pts) { ctx.beginPath(); pts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); }
function draw() {
  const v = X.view, snapOK = X.snap && X.snap.r.ok, addOK = !!(X.add && X.add.r && X.add.r.ok), patch = snapOK ? X.snap.r.patch : addOK ? X.add.r.patch : X.patch, now = performance.now(); ctx.setTransform(v.dpr, 0, 0, v.dpr, 0, 0); ctx.fillStyle = '#0f1624'; ctx.fillRect(0, 0, v.w, v.h);
  patch.faces.forEach(f => { path(f.outline); ctx.closePath(); ctx.fillStyle = f.fill; ctx.fill(); });
  if (X.showBlock) patch.faces.forEach(f => { if (X.rep.has(f.id)) return; path(f.outline); ctx.closePath(); ctx.fillStyle = 'rgba(15,22,36,.58)'; ctx.fill(); });
  const fl = X.flash && now - X.flash.t0 < X.flash.ms ? X.flash : null; if (!fl) X.flash = null;
  if (fl && fl.kind === 'ok') { const a = 0.75 * (1 - (now - fl.t0) / fl.ms); patch.faces.forEach(f => { if (f.cls !== fl.cls) return; path(f.outline); ctx.closePath(); ctx.fillStyle = `rgba(255,255,255,${a})`; ctx.fill(); }); }
  if (X.pressed && X.pressed.faces) { const sides = X.pressed.faces; patch.faces.forEach(f => { if (!sides.includes(f.cls)) return; path(f.outline); ctx.closePath(); ctx.fillStyle = 'rgba(255,255,255,.28)'; ctx.fill(); }); }
  // adding an edge: the two shapes the new edge makes, in every copy (one teal, one amber); before that, the shapes at the first point
  if (addOK) { const [fa, fb] = X.add.r.faces; patch.faces.forEach(f => { if (f.cls !== fa && f.cls !== fb) return; path(f.outline); ctx.closePath(); ctx.fillStyle = f.cls === fa ? 'rgba(43,179,163,.45)' : 'rgba(242,169,59,.48)'; ctx.fill(); }); }
  else if (X.add && X.add.A) patch.faces.forEach(f => { if (!X.add.A.faces.has(f.id)) return; path(f.outline); ctx.closePath(); ctx.fillStyle = 'rgba(255,255,255,.55)'; ctx.fill(); });
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  ctx.beginPath(); patch.edges.forEach(e => { e.pts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); }); ctx.strokeStyle = EDGE; ctx.lineWidth = 1.7; ctx.stroke();
  // the proposed edge on every copy (dashed amber); a pair that cannot be joined: a dashed red line between the two points
  if (addOK) { ctx.save(); ctx.setLineDash([9, 6]); ctx.beginPath(); patch.edges.forEach(e => { if (e.cls !== X.add.r.edge) return; e.pts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); }); ctx.strokeStyle = HI; ctx.lineWidth = 4.5; ctx.stroke(); ctx.restore(); }
  else if (X.add && X.add.A && X.add.B) { ctx.save(); ctx.setLineDash([6, 6]); path([X.add.A.pos, X.add.B.pos]); ctx.strokeStyle = BAD; ctx.lineWidth = 3; ctx.stroke(); ctx.restore(); }
  const hiCls = X.pressed && X.pressed.cls ? X.pressed.cls : fl && fl.kind === 'bad' ? fl.cls : null;
  if (hiCls) { const bad = !X.pressed; ctx.globalAlpha = bad ? Math.max(0, 1 - (now - fl.t0) / fl.ms) : 1;
    patch.edges.forEach(e => { if (e.cls !== hiCls) return; path(e.pts); ctx.strokeStyle = bad ? BAD : HI; ctx.lineWidth = 5; ctx.stroke(); }); ctx.globalAlpha = 1; }
  // the dots that can be dragged: structural vertices (white circles) and added points (teal squares); every copy of the one being
  // touched or dragged is ringed in amber
  const sel = snapOK ? { kind: 'vertex', cls: X.snap.r.root } : X.drag ? X.drag.hp : X.pressed && X.pressed.point, isSel = (kind, cls, k) => sel && sel.kind === kind && sel.cls === cls && (kind === 'vertex' || sel.k === k);
  const on = q => q.x > -8 && q.y > -8 && q.x < v.w + 8 && q.y < v.h + 8;
  ctx.beginPath(); patch.vertices.forEach(x => { if (isSel('vertex', x.cls)) return; const q = w2s(x.pos); if (!on(q)) return; ctx.moveTo(q.x + 2.6, q.y); ctx.arc(q.x, q.y, 2.6, 0, 6.2832); });
  ctx.fillStyle = 'rgba(255,255,255,.92)'; ctx.fill(); ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(29,27,24,.85)'; ctx.stroke();
  ctx.beginPath(); patch.edges.forEach(e => (e.nodes || []).forEach((p, k) => { if (isSel('node', e.cls, k)) return; const q = w2s(p); if (on(q)) ctx.rect(q.x - 3.2, q.y - 3.2, 6.4, 6.4); }));
  ctx.fillStyle = NODE; ctx.fill(); ctx.lineWidth = 1; ctx.strokeStyle = EDGE; ctx.stroke();
  if (sel) { ctx.beginPath();
    if (sel.kind === 'vertex') patch.vertices.forEach(x => { if (x.cls !== sel.cls) return; const q = w2s(x.pos); ctx.moveTo(q.x + 5, q.y); ctx.arc(q.x, q.y, 5, 0, 6.2832); });
    else patch.edges.forEach(e => { if (e.cls !== sel.cls || !e.nodes[sel.k]) return; const q = w2s(e.nodes[sel.k]); ctx.rect(q.x - 5, q.y - 5, 10, 10); });
    ctx.fillStyle = HI; ctx.fill(); ctx.lineWidth = 1.5; ctx.strokeStyle = EDGE; ctx.stroke();
    if (!snapOK && X.drag && X.drag.blocked && X.drag.finger && !X.snap) { const p = sel.kind === 'vertex' ? sel.pv.pos : sel.pe.nodes[sel.k], q = w2s(p); ctx.beginPath(); ctx.arc(q.x, q.y, 11, 0, 6.2832); ctx.strokeStyle = BAD; ctx.lineWidth = 2.5; ctx.stroke(); } }
  // adding an edge: the points that can be joined to the first one (thin rings), and the chosen points
  if (X.add && X.add.A) { const A = X.add;
    if (!addOK) { ctx.beginPath(); A.targets.forEach(p => { const q = w2s(p); if (!on(q)) return; ctx.moveTo(q.x + 8, q.y); ctx.arc(q.x, q.y, 8, 0, 6.2832); }); ctx.strokeStyle = HI; ctx.lineWidth = 2; ctx.stroke(); }
    [A.A, A.B].forEach((E, i) => { if (!E) return; const q = w2s(E.pos); ctx.beginPath(); ctx.arc(q.x, q.y, 6.5, 0, 6.2832); ctx.fillStyle = i && !addOK ? BAD : HI; ctx.fill(); ctx.lineWidth = 1.5; ctx.strokeStyle = EDGE; ctx.stroke(); }); }
  // a merge that is not possible: the point the finger is over, ringed in red
  if (X.snap && !snapOK) { const q = w2s(X.snap.v.pos); ctx.beginPath(); ctx.arc(q.x, q.y, 12, 0, 6.2832); ctx.strokeStyle = BAD; ctx.lineWidth = 3; ctx.stroke(); }
  // a merge that is possible: the merged point (every copy) ringed twice
  if (snapOK) { ctx.beginPath(); patch.vertices.forEach(x => { if (x.cls !== X.snap.r.root) return; const q = w2s(x.pos); ctx.moveTo(q.x + 10, q.y); ctx.arc(q.x, q.y, 10, 0, 6.2832); }); ctx.strokeStyle = HI; ctx.lineWidth = 2.5; ctx.stroke(); }
  if (X.showBlock) { const L = lattice(), o = P(0, 0), c = [o, P(L.b1.x, L.b1.y), P(L.b1.x + L.b2.x, L.b1.y + L.b2.y), P(L.b2.x, L.b2.y)];
    ctx.save(); ctx.setLineDash([3, 5]); ctx.strokeStyle = 'rgba(255,255,255,.35)'; ctx.lineWidth = 1;
    for (let i = -6; i <= 6; i++) { [[L.b1, L.b2], [L.b2, L.b1]].forEach(([d, s]) => { const a = P(s.x * i - d.x * 20, s.y * i - d.y * 20), b = P(s.x * i + d.x * 20, s.y * i + d.y * 20); path([a, b]); ctx.stroke(); }); }
    ctx.setLineDash([7, 5]); ctx.strokeStyle = '#fff'; ctx.lineWidth = 2.2; path(c); ctx.closePath(); ctx.stroke(); ctx.restore(); }
  if (X.flash) requestAnimationFrame(draw);
}

/* ---------------- interaction: tap an edge (add a point or merge), tap a dot (remove), drag a dot (move) ---------------- */
function hitEdge(x, y) {
  let best = null;
  X.patch.edges.forEach(e => { for (let i = 0; i < e.pts.length - 1; i++) { const a = w2s(e.pts[i]), b = w2s(e.pts[i + 1]), dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1e-9;
    const t = Math.max(0, Math.min(1, ((x - a.x) * dx + (y - a.y) * dy) / l2)), d = Math.hypot(x - a.x - dx * t, y - a.y - dy * t);
    if (d <= HIT_PX && (!best || d < best.d)) best = { cls: e.cls, edge: e, d, mid: s2w(x, y) }; } });
  return best;
}
// the nearest dot within reach: a structural vertex or an added point (any copy)
function hitPoint(x, y) {
  let best = null; const g = X.patch.grid;
  X.patch.vertices.forEach(v => { const q = w2s(v.pos), d = Math.hypot(q.x - x, q.y - y); if (d <= VTX_PX && (!best || d < best.d)) best = { kind: 'vertex', cls: v.cls, pv: v, pos: v.pos, d }; });
  X.patch.edges.forEach(e => { if (!e.nodes || !e.nodes.length) return; const ge = G.ecls(g, e.cls);
    e.nodes.forEach((p, k) => { const q = w2s(p), d = Math.hypot(q.x - x, q.y - y); if (d <= VTX_PX && (!best || d < best.d)) best = { kind: 'node', cls: e.cls, k, pe: e, ref: ge.refs[k], pos: p, d }; }); });
  return best;
}
const hitVertex = (x, y) => { const h = hitPoint(x, y); return h && h.kind === 'vertex' ? h.pv : null; };
let down = null, toastT = 0, raf = 0, pend = null, popOpen = false;
function toast(msg, bad, ms) { const t = $('toast'); t.textContent = msg; t.classList.toggle('bad', !!bad); t.classList.add('on'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('on'), ms || (bad ? 4200 : 2400)); }
// the small menu at the finger
function openPop(x, y, title, text, buttons) {
  const pop = $('pop'); $('pop-title').textContent = title; $('pop-text').textContent = text || ''; $('pop-text').hidden = !text; const box = $('pop-btns'); box.innerHTML = '';
  buttons.forEach(b => { const el = document.createElement('button'); el.id = b.id; el.disabled = !!b.disabled; el.textContent = b.label; if (b.sub) { const sm = document.createElement('small'); sm.textContent = b.sub; el.appendChild(sm); }
    el.onclick = ev => { ev.stopPropagation(); b.onClick(); }; box.appendChild(el); });
  pop.hidden = false; popOpen = true; const r = pop.getBoundingClientRect(), W = window.innerWidth, H = window.innerHeight;
  let top = y - r.height - 22; if (top < 76) top = y + 22; if (top + r.height > H - 8) top = Math.max(8, H - r.height - 8);
  pop.style.left = Math.round(Math.min(Math.max(10, x - r.width / 2), W - r.width - 10)) + 'px'; pop.style.top = Math.round(top) + 'px';
}
function closePop() { $('pop').hidden = true; popOpen = false; X.pressed = null; draw(); }
function edgeMenu(h, x, y) {
  const st = cur(), w = s2w(x, y), at = G.latVec(lattice(), h.edge.at), lat = Mv.latticeEdgeOf(st, h.cls), add = Mv.addNode(st, h.cls, P(w.x - at.x, w.y - at.y));
  X.pressed = { cls: h.cls, faces: Mv.beside(st, h.cls) }; draw();
  openPop(x, y, 'This edge', '', [
    { id: 'pop-add', label: 'Add a point here', sub: add.ok ? `then drag it to bend the edge · ${add.count} of ${add.max} on this edge` : add.message, disabled: !add.ok,
      onClick: () => { closePop(); commit(add.state); X.lastAdd = add; draw(); audit(add.state, add); toast('Point added: drag it to bend the edge (every copy bends)'); } },
    { id: 'pop-merge', label: 'Merge the two shapes', sub: 'the edge disappears everywhere it repeats', onClick: () => { closePop(); attempt(lat, h.cls, h.mid); } },
    { id: 'pop-cancel', label: 'Cancel', onClick: closePop }]);
}
function pointMenu(h, x, y) {
  const st = cur(); X.pressed = { point: h }; draw();
  if (h.kind === 'node') { const r = Mv.removeNode(st, h.ref), lat = Mv.latticeEdgeOf(st, h.cls);
    // the edge it lies on can still be merged from here (an edge covered with points has no free spot to tap)
    return openPop(x, y, 'Added point', 'A point you added on an edge. Drag it to bend the edge: every copy follows.', [
      { id: 'pop-remove', label: 'Remove this point', sub: r.ok ? 'the edge straightens here' : r.message, disabled: !r.ok, onClick: () => { closePop(); commit(r.state); draw(); audit(r.state, r); toast('Point removed'); } },
      { id: 'pop-merge', label: 'Merge the two shapes', sub: 'the edge it lies on disappears everywhere it repeats', onClick: () => { closePop(); attempt(lat, h.cls, h.pos); } },
      { id: 'pop-cancel', label: 'Cancel', onClick: closePop }]); }
  const info = Mv.pointInfo(st, h.cls);
  if (info.kind === 'junction') return openPop(x, y, `Junction: ${info.shapes} shapes meet here`, info.message, [{ id: 'pop-ok', label: 'OK', onClick: closePop }]);
  const r = Mv.removePoint(st, h.cls);
  openPop(x, y, 'Point between two shapes', info.message, [
    { id: 'pop-remove', label: 'Remove this point', sub: r.ok ? 'its two edges become one' : r.message, disabled: !r.ok, onClick: () => { closePop(); commit(r.state); draw(); audit(r.state, r); toast('Point removed: its two edges are now one'); } },
    { id: 'pop-cancel', label: 'Cancel', onClick: closePop }]);
}
// one finger: tap or drag (above). Two fingers: pinch to zoom, move to pan; a single-finger action in progress is cancelled.
const touches = new Map(); let pinch = null, waitAllUp = false, praf = 0;
const requestDraw = () => { if (!praf) praf = requestAnimationFrame(() => { praf = 0; draw(); }); };
function cancelSingle() { if (!down) return; down = null; X.pressed = null; if (X.drag) { if (raf) { cancelAnimationFrame(raf); raf = 0; } X.drag = null; setSnap(null); rebuild(); } }
function pinchStart() { const [a, b] = [...touches.values()], m = P((a.x + b.x) / 2, (a.y + b.y) / 2); pinch = { d0: Math.max(10, Math.hypot(a.x - b.x, a.y - b.y)), s0: X.view.s, w0: s2w(m.x, m.y), moved: 0 }; }
function pinchMove() {
  const [a, b] = [...touches.values()], m = P((a.x + b.x) / 2, (a.y + b.y) / 2), d = Math.max(10, Math.hypot(a.x - b.x, a.y - b.y)), v = X.view;
  v.s = Math.min(v.base / SPAN_MIN, Math.max(v.base / SPAN_MAX, pinch.s0 * d / pinch.d0)); X.span = v.base / v.s;
  v.x = pinch.w0.x - (m.x - v.cx) / v.s; v.y = pinch.w0.y + (m.y - v.cy) / v.s;
  const sh = wrapView(); pinch.w0 = P(pinch.w0.x - sh.x, pinch.w0.y - sh.y); pinch.moved++;
  if (patchN(X.patch.grid, v) > X.patch.n) rebuild(); requestDraw();
}
cv.addEventListener('pointerdown', e => {
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  touches.set(e.pointerId, P(e.clientX, e.clientY)); try { cv.setPointerCapture(e.pointerId); } catch (_) {}
  if (touches.size === 2) { cancelSingle(); if (popOpen) { $('pop').hidden = true; popOpen = false; X.pressed = null; } pinchStart(); draw(); return; }
  if (touches.size > 2 || pinch || waitAllUp || down) return;
  if (popOpen) { closePop(); return; }                 // a tap outside the menu only closes it
  closeSheets();
  if (X.add) { down = { id: e.pointerId, x0: e.clientX, y0: e.clientY, mode: 'add' }; return; }       // adding an edge: taps choose points, nothing is dragged
  const hp = hitPoint(e.clientX, e.clientY);
  if (hp) { down = { id: e.pointerId, x0: e.clientX, y0: e.clientY, mode: 'point', hp }; X.pressed = { point: hp }; }
  else { const h = hitEdge(e.clientX, e.clientY); if (!h) return;
    down = { id: e.pointerId, x0: e.clientX, y0: e.clientY, mode: 'edge', hit: h }; X.pressed = { cls: h.cls, faces: Mv.beside(cur(), h.cls) }; }
  draw();
});
cv.addEventListener('pointermove', e => {
  if (touches.has(e.pointerId)) touches.set(e.pointerId, P(e.clientX, e.clientY));
  if (pinch) { if (touches.size >= 2) pinchMove(); return; }
  if (!down || e.pointerId !== down.id) return; const far = Math.hypot(e.clientX - down.x0, e.clientY - down.y0);
  if (down.mode === 'edge' || down.mode === 'add') { if (far > TAP_PX) { down = null; X.pressed = null; draw(); } return; }
  if (!X.drag) { if (far <= DRAG_PX) return; startDrag(down.hp, down.x0, down.y0); }
  pend = { x: e.clientX, y: e.clientY }; if (!raf) raf = requestAnimationFrame(dragFrame);
});
function pointerEnd(e, cancelled) {
  touches.delete(e.pointerId);
  if (pinch) { if (touches.size < 2) { pinch = null; waitAllUp = touches.size > 0; wrapView(); rebuild(); draw(); } return; }
  if (waitAllUp) { if (!touches.size) waitAllUp = false; return; }
  if (!down || e.pointerId !== down.id) return; const d = down; down = null;
  if (cancelled) { X.pressed = null; if (X.drag) { if (raf) { cancelAnimationFrame(raf); raf = 0; } X.drag = null; setSnap(null); rebuild(); } draw(); return; }
  if (d.mode === 'add') { addTap(e.clientX, e.clientY); return; }
  if (d.mode === 'edge') { edgeMenu(d.hit, e.clientX, e.clientY); return; }
  if (X.drag) { if (raf) { cancelAnimationFrame(raf); raf = 0; dragFrame(); } endDrag(); } else pointMenu(d.hp, e.clientX, e.clientY);
}
cv.addEventListener('pointerup', e => pointerEnd(e, false));
cv.addEventListener('pointercancel', e => pointerEnd(e, true));
// desktop: ctrl + wheel (or a trackpad pinch) zooms about the pointer, the wheel alone pans
cv.addEventListener('wheel', e => { e.preventDefault(); const v = X.view;
  if (e.ctrlKey) { const w0 = s2w(e.clientX, e.clientY); v.s = Math.min(v.base / SPAN_MIN, Math.max(v.base / SPAN_MAX, v.s * Math.exp(-e.deltaY / 200))); X.span = v.base / v.s; v.x = w0.x - (e.clientX - v.cx) / v.s; v.y = w0.y + (e.clientY - v.cy) / v.s; }
  else { v.x += e.deltaX / v.s; v.y -= e.deltaY / v.s; }
  wrapView(); if (patchN(X.patch.grid, v) > X.patch.n) rebuild(); requestDraw(); }, { passive: false });

/* ---------------- add an edge: two points on one shape, a preview on every copy, then keep it or cancel ---------------- */
const ADD_FIRST = 'Add an edge: tap the first point on a shape — a corner, an added point, or any place on an edge.';
const facesAt = hs => new Set(hs.map(h => X.patch.half[h].face));
// what a tap chooses: a structural vertex, an added point, or the nearest place on an edge where a new corner has room
function endAt(x, y) {
  const hp = hitPoint(x, y);
  if (hp && hp.kind === 'vertex') return { spec: { v: hp.cls, at: hp.pv.at.slice() }, pos: hp.pv.pos, faces: facesAt(hp.pv.out), what: 'vertex' };
  if (hp) return { spec: { p: hp.pos }, pos: hp.pos, faces: facesAt(hp.pe.half), what: 'node' };
  const h = hitEdge(x, y); if (!h) return null;
  const ep = Mv.edgePoint(cur(), h.cls, h.edge.at, s2w(x, y)); if (!ep.ok) return { error: ep.message };
  return { spec: { p: ep.p }, pos: ep.p, faces: facesAt(h.edge.half), what: 'edge' };
}
function addBar(text, bad, canKeep) { const b = $('addbar'); b.hidden = false; $('hint').hidden = true; b.classList.toggle('bad', !!bad); $('add-text').textContent = text; $('add-ok').disabled = !canKeep; }
function startAdd() { closeSheets(); cancelSingle(); X.add = { A: null, B: null, r: null, targets: [] }; $('addedge').setAttribute('aria-pressed', 'true'); addBar(ADD_FIRST, false, false); draw(); }
function cancelAdd(quiet) { if (!X.add) return; X.add = null; $('addbar').hidden = true; $('hint').hidden = false; $('addedge').setAttribute('aria-pressed', 'false'); if (!quiet) draw(); }
// the corners and added points of the lit shapes that can be joined to the first point (worked out once, when it is chosen)
function targetsOf(E) {
  const st = cur(), out = [], seen = new Set(), tryP = (spec, pos) => { const k = pos.x.toFixed(6) + ',' + pos.y.toFixed(6); if (seen.has(k) || Math.hypot(pos.x - E.pos.x, pos.y - E.pos.y) < 1e-9) return; seen.add(k); if (Mv.split(st, E.spec, spec).ok) out.push(pos); };
  E.faces.forEach(fid => { X.patch.faces[fid].half.forEach(hid => { const h = X.patch.half[hid], v = X.patch.vertices[h.origin], e = X.patch.edges[h.edge]; tryP({ v: v.cls, at: v.at }, v.pos); e.nodes.forEach(p => tryP({ p }, p)); }); });
  return out;
}
function addTap(x, y) {
  const A = X.add, E = endAt(x, y); if (!E) return;                                   // a tap on empty space chooses nothing
  if (E.error) { addBar(E.error, true, !!(A.r && A.r.ok)); return; }
  if (A.A && Math.hypot(E.pos.x - A.A.pos.x, E.pos.y - A.A.pos.y) < 1e-9) { A.A = null; A.B = null; A.r = null; A.targets = []; addBar(ADD_FIRST, false, false); draw(); return; }   // the first point again: let go of it
  if (!A.A) { A.A = E; const t0 = performance.now(); A.targets = targetsOf(E); A.targetsMs = +(performance.now() - t0).toFixed(1);
    addBar(A.targets.length ? 'Now tap a second point on one of the lit shapes: a ringed point, or any place on an edge.'
      : 'Now tap a second point on one of the lit shapes. No corner can be joined to this point by a straight edge inside the shape, so tap a place on an edge.', false, false); draw(); return; }
  A.B = E; const t0 = performance.now(), r = Mv.split(cur(), A.A.spec, E.spec); if (r.ok) r.patch = previewPatch(r.state); r.ms = +(performance.now() - t0).toFixed(1); A.r = r;
  addBar(r.ok ? splitNote(r) : r.message + ' Nothing has changed: tap another second point, or Cancel.', !r.ok, r.ok); draw();
}
const splitParts = c => { const [a, b] = c.after.slice().sort((x, y) => x - y); return `${C.article(Mg.polyName(c.before))} becomes ${a === b ? 'two ' + C.plural(Mg.polyName(a)) : C.article(Mg.polyName(a)) + ' and ' + C.article(Mg.polyName(b))}`; };
function splitNote(r) {
  const c = r.change, head = r.kind === 'restore' ? (c.restored === 1 ? 'This brings back an edge of the triangular grid' : `This brings back ${c.restored} edges of the triangular grid, in one straight line`) : 'A new edge';
  const pins = !c.pins ? '' : c.pins === 1 ? ' One new corner is made on an edge; the shape across that edge gets it too.' : ` ${c.pins} new corners are made on edges; the shapes across those edges get them too.`;
  return `${head}: ${splitParts(c)}, in every copy.${pins}`;
}
// “Add this edge”: the full checks first (M1's 13 checks among them); only then is it kept
function confirmAdd() {
  const A = X.add; if (!A || !A.r || !A.r.ok) return; const r = A.r, t0 = performance.now(), j = Mv.judge(r.state);
  X.lastSplit = { ok: j.ok, kind: r.kind, stored: r.stored, previewMs: r.ms, targetsMs: A.targetsMs, judgeMs: +(performance.now() - t0).toFixed(1), change: r.change, failing: j.validator.failing };
  if (!j.ok) { addBar('This edge cannot be added: an independent check failed. Nothing has changed.', true, false); A.r = null; draw(); return; }
  X.checks.set(Mv.stateKey(r.state), { ok: true, topo: j.topology, geo: j.validator.ok, indep: j.independent }); cancelAdd(true); commit(r.state); draw();
  toast(`${r.kind === 'restore' ? 'Edge restored' : 'Edge added'}: ${splitParts(r.change)} (every copy)`, false, 3000);
}

/* a drag (a structural vertex or an added point): only the patch items touching what moves are recomputed each frame */
function startDrag(hp, x0, y0) {
  const patch = X.patch, st = cur(), f0 = s2w(x0, y0), ses = hp.kind === 'vertex' ? Mv.session(st, hp.cls) : Mv.nodeSession(st, hp.ref);
  const es = patch.edges.filter(e => ses.changed.has(e.cls)), eIds = new Set(es.map(e => e.id)), fs = patch.faces.filter(f => f.half.some(h => eIds.has(patch.half[h].edge)));
  X.drag = { hp, ses, s0: st, snapCache: new Map(), start: Mv.stateKey(st), grab: P(hp.pos.x - f0.x, hp.pos.y - f0.y), at: G.latVec(lattice(), hp.kind === 'vertex' ? hp.pv.at : hp.pe.at),
    es, fs, vs: hp.kind === 'vertex' ? patch.vertices.filter(v => v.cls === hp.cls) : [], geById: new Map(patch.grid.edges.map(e => [e.id, e])), blocked: false, finger: null, frames: [], steps: [], checks: 0, everBlocked: false };
  X.pressed = null;
}
function dragFrame() {
  raf = 0; const D = X.drag; if (!D || !pend) return; const t0 = performance.now(), f = s2w(pend.x, pend.y); D.finger = f;
  const target = P(f.x + D.grab.x - D.at.x, f.y + D.grab.y - D.at.y);
  const r = D.hp.kind === 'vertex' ? D.ses.step(P(target.x - D.ses.base.x, target.y - D.ses.base.y)) : D.ses.step(target), t1 = performance.now();
  D.blocked = r.blocked; D.everBlocked = D.everBlocked || r.blocked; D.checks += r.checks;
  // the grid at this moment (positions and edge points from the drag), then the affected patch items
  const w = D.ses.w, frame = { lattice: lattice(), vertices: D.ses.st.vertices.map(v => ({ id: v.id, pos: w.pos.get(v.id) })) };
  D.vs.forEach(v => { v.pos = G.vpos(frame, v.cls, v.at); });
  D.es.forEach(e => { const ge = D.geById.get(e.cls), eo = { id: ge.id, v0: ge.v0, v1: ge.v1, shift: ge.shift, nodes: w.nodes.get(ge.id), curve: null }; e.pts = G.edgeLine(frame, eo, e.at); e.nodes = G.edgeNodes(frame, eo, e.at); });
  D.fs.forEach(fc => { fc.outline = []; fc.half.forEach(hid => { const h = X.patch.half[hid], e = X.patch.edges[h.edge], line = h.dir > 0 ? e.pts : e.pts.slice().reverse(); for (let i = 0; i < line.length - 1; i++) fc.outline.push(line[i]); }); });
  // a structural vertex near another one (judged by the FINGER, not by the guarded vertex): the merge of the two, previewed
  if (D.hp.kind === 'vertex') { const fsx = w2s(P(f.x + D.grab.x, f.y + D.grab.y)); let best = null;
    X.patch.vertices.forEach(v => { if (v.cls === D.hp.cls) return; const q = w2s(v.pos), dd = Math.hypot(q.x - fsx.x, q.y - fsx.y); if (dd <= SNAP_PX && (!best || dd < best.d)) best = { v, d: dd }; });
    setSnap(best && best.v); }
  draw(); const t2 = performance.now(); D.steps.push(t1 - t0); D.frames.push(t2 - t0);
}
// the merge preview: worked out once per target during a drag
function setSnap(v) {
  const D = X.drag; if (!v || !D) { if (X.snap) { X.snap = null; $('snap').classList.remove('on'); } return; }
  const key = v.cls + '@' + v.at.join(','); if (X.snap && X.snap.key === key) return;
  let r = D.snapCache.get(key);
  if (!r) { const t0 = performance.now(); r = Mv.contract(D.s0, D.hp.cls, D.hp.pv.at, v.cls, v.at); if (r.ok) r.patch = previewPatch(r.state); r.ms = +(performance.now() - t0).toFixed(1); D.snapCache.set(key, r); }
  X.snap = { key, v, r }; const el = $('snap'); el.classList.toggle('bad', !r.ok); el.classList.add('on');
  el.textContent = r.ok ? mergeNote(r.change) : r.message;
}
function mergeNote(c) {
  const kind = k => k >= 3 ? `a junction of ${k} edges` : 'a point between two shapes', faces = [];
  c.before.forEach((b, i) => { const t = `${Mg.polyName(b)} → ${Mg.polyName(c.after[i])}`; if (!faces.includes(t)) faces.push(t); });
  return `Release to merge ${kind(c.from[0])} with ${kind(c.from[1])}: ${c.to} edges will meet here, in every copy. The edge between them disappears; beside it: ${faces.join(', ')}.`;
}
function endDrag() {
  const D = X.drag, snap = X.snap, ns = D.ses.result(), moved = Mv.stateKey(ns) !== D.start; X.drag = null;
  const st0 = a => { const s = a.slice().sort((x, y) => x - y); return s.length ? { n: s.length, mean: +(s.reduce((x, y) => x + y, 0) / s.length).toFixed(2), p95: +s[Math.min(s.length - 1, Math.floor(s.length * 0.95))].toFixed(2), max: +s[s.length - 1].toFixed(2) } : { n: 0 }; };
  if (snap) { setSnap(null); X.lastDrag = { kind: D.hp.kind, cls: D.hp.cls, frames: st0(D.frames), merge: true };
    // released over another point: merge (only if the full checks pass), or keep everything as it was before the drag and say why
    if (snap.r.ok) { const t0 = performance.now(), j = Mv.judge(snap.r.state); X.lastMerge = { ok: j.ok, judgeMs: +(performance.now() - t0).toFixed(1), previewMs: snap.r.ms, change: snap.r.change, failing: j.validator.failing };
      if (j.ok) { X.checks.set(Mv.stateKey(snap.r.state), { ok: true, topo: j.topology, geo: j.validator.ok, indep: j.independent }); commit(snap.r.state); draw(); toast(`Merged: ${snap.r.change.to} edges now meet at this point (every copy)`); return; }
      rebuild(); draw(); toast('These two cannot be merged: an independent check failed. Nothing changed.', true); return; }
    X.lastMerge = { ok: false, kind: snap.r.kind, message: snap.r.message }; rebuild(); draw(); toast(snap.r.message + ' Nothing changed.', true, 4600); return; }
  const stats = a => { const s = a.slice().sort((x, y) => x - y); return s.length ? { n: s.length, mean: +(s.reduce((x, y) => x + y, 0) / s.length).toFixed(2), p95: +s[Math.min(s.length - 1, Math.floor(s.length * 0.95))].toFixed(2), max: +s[s.length - 1].toFixed(2) } : { n: 0 }; };
  X.lastDrag = { kind: D.hp.kind, cls: D.hp.cls, frames: stats(D.frames), checkStep: stats(D.steps), checksPerFrame: D.frames.length ? +(D.checks / D.frames.length).toFixed(1) : 0, blockedAtEnd: D.blocked, everBlocked: D.everBlocked, moved };
  if (!moved) { rebuild(); draw(); return; }
  const t0 = performance.now(), c = Mv.checkAll(ns); X.lastDrag.checkAllMs = +(performance.now() - t0).toFixed(2);
  if (!c.ok) { rebuild(); draw(); toast(Mg.MESSAGES.disagree, true); return; }
  const t1 = performance.now(); commitMoved(ns, D); draw(); X.lastDrag.commitMs = +(performance.now() - t1).toFixed(1);
  if (D.blocked) toast(`The ${D.hp.kind === 'vertex' ? 'vertex' : 'point'} stopped where a shape would collapse, fold over or overlap`, false, 2600);
  audit(ns, X.lastDrag);
}
// M1's 13 checks (and the other judges) on the new geometry, just after the screen has been drawn: an independent second opinion
function audit(st, rec) {
  setTimeout(() => { const t0 = performance.now(), j = Mv.judge(st); if (rec) { rec.auditMs = +(performance.now() - t0).toFixed(1); rec.audit = j.ok; }
    X.checks.set(Mv.stateKey(st), { ok: j.ok, topo: j.topology, geo: j.validator.ok, indep: j.independent }); X.audits = (X.audits || 0) + 1;
    if (!j.ok && cur() === st) { X.hist.splice(X.hp, 1); X.hp--; fit(); rebuild(); draw(); toast(Mg.MESSAGES.disagree, true); } }, 30);
}
function attempt(lat, gid, mid) {
  const st = cur(), t0 = performance.now(), r = Mv.merge(st, lat); r.ms = performance.now() - t0; X.last = r;
  if (r.ok) {
    commit(r.state); if (r.state.x) X.checks.set(Mv.stateKey(r.state), { ok: true, topo: true, geo: r.validator.ok, indep: r.independent.ok }); else if (r.state.moves.length || r.state.nodes.length || r.state.dissolved.length) audit(r.state, r); let fc = null;
    if (mid) X.patch.faces.forEach(f => { if (!fc && G.winding(f.outline, mid) !== 0) fc = f.cls; });
    const nf = fc && X.info.faces.find(f => f.id === fc);
    X.flash = { kind: 'ok', cls: fc, t0: performance.now(), ms: 650 };
    toast(nf ? `Merged: ${C.article(nf.name)}${nf.triangles ? ` of ${nf.triangles} triangles` : ''}${r.boundary.edges.length > 1 ? ' (its whole shared boundary went)' : ''}` : 'Merged');
  } else { X.flash = { kind: 'bad', cls: gid, t0: performance.now(), ms: 1100 }; toast(r.message, true); }
  draw();
}
function commit(st) { if (X.add) cancelAdd(true); X.hist = X.hist.slice(0, X.hp + 1); X.hist.push(st); X.hp = X.hist.length - 1; rebuild(); }
// after a drag the patch already shows the new geometry: keep it, and refresh only the description, the colours and the block copies
function commitMoved(st, D) {
  X.hist = X.hist.slice(0, X.hp + 1); X.hist.push(st); X.hp = X.hist.length - 1;
  const g = Mv.gridOf(st), L = g.lattice, d = Mv.describe(st), corners = new Map(d.faces.map(f => [f.id, f.corners])); X.patch.grid = g;   // (same boundaries, new positions)
  D.fs.forEach(f => { f.centroid = G.centroid(f.outline); }); X.patch.faces.forEach(f => { f.fill = fillFor(corners.get(f.cls)); });
  const rep = new Map(); X.patch.faces.forEach(f => { const [u, w] = G.toLat(L, f.centroid); if (u >= -1e-9 && u < 1 - 1e-9 && w >= -1e-9 && w < 1 - 1e-9 && !rep.has(f.cls)) rep.set(f.cls, f.id); });
  X.patch.faces.forEach(f => { if (!rep.has(f.cls) && f.at[0] === 0 && f.at[1] === 0) rep.set(f.cls, f.id); });
  X.rep = new Set(rep.values()); X.info = d; syncUI();
}
function go(d) { const to = X.hp + d; if (to < 0 || to >= X.hist.length) return; if (X.add) cancelAdd(true); X.hp = to; X.flash = null; fit(); rebuild(); draw(); }

/* ---------------- UI ---------------- */
function syncUI() {
  const d = X.info, cl = d.classification, tp = cl.topology, rg = cl.regularity, st = cur();
  // the title: the NAME (what was verified) and, below it, the arrangement or the kind of regular tiling
  const arr = rg.named ? (rg.kind === 'regular' ? 'regular tiling' : 'Archimedean tiling')
    : tp.arrangement ? `arrangement ${tp.arrangement.notation} (${tp.arrangement.name})` : tp.vertexTypes.length === 1 ? `arrangement ${tp.vertexTypes[0]}` : `${tp.vertexTypes.length} vertex types`;
  $('name').textContent = cl.name; $('sub').textContent = arr;
  $('blk').textContent = `${d.block.name} block · ` + (d.explicit ? `${d.shapesPerBlock} shapes` : `${st.removed.length} edge${st.removed.length === 1 ? '' : 's'} removed`) + (d.cuts ? ` · ${d.cuts} edge${d.cuts === 1 ? '' : 's'} added` : '') + (d.moved ? ` · ${d.moved} vert${d.moved === 1 ? 'ex' : 'ices'} moved` : '') + (d.added ? ` · ${d.added} point${d.added === 1 ? '' : 's'} added` : '') + (d.merged ? ` · ${d.merged} merge${d.merged === 1 ? '' : 's'} of vertices` : '');
  $('toast').style.top = Math.round($('top').getBoundingClientRect().bottom + 6) + 'px';
  $('status').textContent = '✓ valid';      // validity only: every state in the history passed the full checks
  $('undo').disabled = X.hp === 0; $('redo').disabled = X.hp >= X.hist.length - 1; $('block').setAttribute('aria-pressed', String(X.showBlock));
  $('m-zoom').firstChild.textContent = X.span > 10 ? 'Zoom in' : 'Zoom out';
  if (!$('sheet-info').hidden) renderInfo();
}
function checksOf(st) { const k = Mv.stateKey(st); if (!X.checks.has(k)) { const j = Mv.judge(st); X.checks.set(k, { ok: j.ok, topo: j.topology, geo: j.validator.ok, indep: j.independent }); } return X.checks.get(k); }
const REASON = { R1: 'not every shape is a regular polygon', R2: 'some vertices lie on the straight side of a shape', R3: 'the edges are not all the same length', R4: 'the vertices are not all alike' };
function renderInfo() {
  const d = X.info, cl = d.classification, tp = cl.topology, ge = cl.geometry, rg = cl.regularity, c = checksOf(cur()), yes = b => `<b class="${b ? '' : 'n'}">${b ? '✓' : '✗'}</b>`;
  // the summary a participant reads first
  const fail = rg.conditions.find(x => !x.ok), firstOff = fail && fail.key === 'R1' ? fail.detail.split('; ')[0] : '';
  const regular = rg.named ? `${yes(true)}<span>Yes: ${rg.kind === 'regular' ? 'a regular tiling' : 'an Archimedean tiling'}. Every shape is a regular polygon and every vertex is alike.</span>`
    : rg.kind === 'regular-polygons' ? `${yes(false)}<span>No: the shapes are regular polygons, but the vertices are not all alike.</span>`
    : `${yes(false)}<span>No: ${REASON[fail.key]}${firstOff ? ` <small>(${firstOff})</small>` : ''}.</span>`;
  const like = tp.arrangement ? `every ${tp.arrangement.by} <b>${tp.arrangement.notation}</b>, like the ${tp.arrangement.name} tiling` : tp.vertexTypes.length === 1 ? `every vertex <b>${tp.vertexTypes[0]}</b>` : `${tp.vertexTypes.length} kinds of vertex`;
  // the same name once: e.g. “6 × scalene triangle · 6 different shapes” (each different shape is listed under More details)
  const byName = []; d.groups.forEach(g => { const x = byName.find(y => y.name === g.name); if (x) { x.faces += g.faces; x.kinds++; x.tri.add(g.triangles); } else byName.push({ name: g.name, corners: g.corners, faces: g.faces, kinds: 1, tri: new Set([g.triangles]) }); });
  const shapesShort = byName.map(g => { const t = g.tri.size === 1 ? [...g.tri][0] : 0, notes = [g.kinds > 1 ? `${g.kinds} different shapes` : '', t > 1 ? `${t} triangles each` : ''].filter(Boolean).join(' · ');
    return `<div class="shape"><i style="background:${fillFor(g.corners)}"></i><span>${g.faces} × ${g.name}${notes ? ` <small>· ${notes}</small>` : ''}</span></div>`; }).join('');
  // the details (v6.2's full Info)
  const arrangement = tp.arrangement ? `Every ${tp.arrangement.by} <b>${tp.arrangement.notation}</b>: the arrangement of the <b>${tp.arrangement.name}</b> tiling.`
    : tp.vertexTypes.length === 1 ? `Every vertex <b>${tp.vertexTypes[0]}</b>.` : `${tp.vertexTypes.length} kinds of vertex: ${tp.vertexTypes.map(t => '<b>' + t + '</b>').join(' · ')}.`;
  const faceKinds = tp.faceKinds.map(k => `<div class="chk"><span>Faces with <b>${k.vertices}</b> vertices (${k.faces.length} per block) · neighbours going round: <b>${k.neighbours}</b></span></div>`).join('');
  const shapes = d.groups.map(g => `<div class="shape"><i style="background:${fillFor(g.corners)}"></i><span>${g.faces} × ${g.name} <small>· angles ${g.angles.map(a => a + '°').join(', ')} · side${g.sides.length > 1 ? 's' : ''} ${g.sides.join(', ')}${g.triangles > 1 ? ` · ${g.triangles} triangles each` : ''}</small></span></div>`).join('');
  const e2e = ge.edgeToEdge ? 'Shapes meet corner to corner (edge-to-edge).' : `Not corner to corner: ${rg.conditions.find(x => x.key === 'R2').detail}.`;
  const open = $('more-details') && $('more-details').open;
  $('info-body').innerHTML = `<p class="name">${cl.name}</p>
    <h3>Shapes in each block</h3>${shapesShort}
    <div class="sum"><span class="k">Arrangement</span><span>${like}</span></div>
    <div class="sum"><span class="k">Regular?</span><span class="chk">${regular}</span></div>
    <div class="sum"><span class="k">Valid tiling?</span><span class="chk">${yes(c.ok)}<span>${c.ok ? 'Yes: it passed all three checks' : 'No'}</span></span></div>
    <details id="more-details"${open ? ' open' : ''}><summary>More details</summary>
    <p class="kv"><span>Repeat block:</span> ${d.block.name} · ${d.trianglesPerBlock} triangles · ${d.shapesPerBlock} shape${d.shapesPerBlock === 1 ? '' : 's'} in each block${d.moved ? ` · ${d.moved} vert${d.moved === 1 ? 'ex' : 'ices'} moved` : ''}${d.added ? ` · ${d.added} point${d.added === 1 ? '' : 's'} added on edges` : ''}${d.dissolved ? ` · ${d.dissolved} point${d.dissolved === 1 ? '' : 's'} between two shapes removed or hidden inside a restored edge` : ''}${d.merged ? ` · ${d.merged} pair${d.merged === 1 ? '' : 's'} of vertices merged` : ''}${d.cuts ? ` · ${d.cuts} edge${d.cuts === 1 ? '' : 's'} added that ${d.cuts === 1 ? 'is' : 'are'} not of the triangular grid` : ''}</p>
    <p class="kv"><span>Added points and points between only two shapes are not vertices of the arrangement: adding, moving or removing them changes the shapes, never which shapes meet.</span></p>
    <h3>1 · Arrangement (topology)</h3><p class="kv">${arrangement}</p>${faceKinds}
    <p class="kv"><span>A vertex is a point where three or more edges meet. The numbers count each face's vertices, going round a vertex (or round a face). Lengths and angles play no part, so the arrangement stays the same however the shapes are stretched.</span></p>
    <h3>2 · Shapes (geometry)</h3>${shapes}<p class="kv">${e2e}</p>
    <p class="kv"><span>Corners are where a shape's angle is not 180°. Sides are measured from corner to corner, in units of the shortest side.</span></p>
    <h3>3 · Regularity</h3>` + rg.conditions.map(x => `<div class="chk">${yes(x.ok)}<span>${x.label} <small>· ${x.detail}</small></span></div>`).join('') +
    `<p class="kv verdict">${rg.verdict.charAt(0).toUpperCase() + rg.verdict.slice(1)}.</p>
    <p class="kv"><span>Measured, not judged by eye: angles to within ${(cl.tolerance.angle * 180 / Math.PI).toPrecision(1)}°, lengths to within ${cl.tolerance.length} of the average side. A regular or Archimedean name is used only when all four conditions hold.</span></p>
    <h3>4 · Validity (all must pass before a merge, a split or a move is kept)</h3>
    <div class="chk">${yes(c.topo)}<span>shapes fit together: none wraps round the repeat, has a hole, touches itself, holds a loose edge or is folded over</span></div>
    <div class="chk">${yes(c.geo)}<span>the 13 tiling checks (no gaps, no overlaps, no crossings, 360° at every vertex)</span></div>
    <div class="chk">${yes(c.indep)}<span>${d.explicit ? 'an independent check of the arrangement alone: every edge has one shape on each side, the shapes round every vertex form one ring, and vertices − edges + shapes = 0' : 'an independent count of the triangles in each shape'}</span></div>
    <p class="kv"><span>Validity does not depend on the name: a valid tiling may be irregular and have no name at all.</span></p></details>`;
}
function closeSheets() { ['sheet-info', 'sheet-more', 'sheet-blocks'].forEach(id => { $(id).hidden = true; }); if (popOpen) { $('pop').hidden = true; popOpen = false; } }
function blocksSheet(mode) {
  const st = cur(), list = mode === 'new' ? Mg.BLOCKS : Mg.BLOCKS.filter(b => Mg.refinable(st.block, b.key));
  $('blocks-title').textContent = mode === 'new' ? 'New grid' : 'Bigger repeat block';
  $('blocks-note').textContent = mode === 'new' ? 'Choose how many triangles repeat. A bigger block lets neighbouring copies become different shapes. Undo brings back the current grid.'
    : list.length ? 'Your shapes stay exactly as they are (moved vertices too); from now on, merges and moves repeat less often.' : 'No block in the list contains this one. Start a new grid instead.';
  const det = M => M[0][0] * M[1][1] - M[0][1] * M[1][0];
  $('blocks-list').innerHTML = list.map(b => `<button data-k="${b.key}">${b.name}${b.key === st.block ? ' (current)' : ''}<small>${2 * det(b.M)} triangles repeat</small></button>`).join('');
  $('blocks-list').onclick = e => { const b = e.target.closest('button'); if (!b) return; closeSheets();
    const next = mode === 'new' ? Mv.newState(b.dataset.k) : Mv.refine(cur(), b.dataset.k); if (!next) return;
    commit(next); fit(); rebuild(); draw(); toast(mode === 'new' ? `New grid · repeat block ${Mg.blockOf(b.dataset.k).name}` : `Repeat block ${Mg.blockOf(b.dataset.k).name}: same shapes, finer repeat`); };
  closeSheets(); $('sheet-blocks').hidden = false;
}
$('undo').onclick = () => go(-1); $('redo').onclick = () => go(1);
$('addedge').onclick = () => { if (X.add) cancelAdd(); else startAdd(); }; $('add-cancel').onclick = () => cancelAdd(); $('add-ok').onclick = confirmAdd;
$('block').onclick = () => { X.showBlock = !X.showBlock; syncUI(); draw(); if (X.showBlock) toast('One copy of each shape stays bright: everything else is a copy of it'); };
$('info').onclick = $('status').onclick = () => { closeSheets(); renderInfo(); $('sheet-info').hidden = false; };
$('more').onclick = () => { closeSheets(); $('sheet-more').hidden = false; };
$('m-new').onclick = () => blocksSheet('new'); $('m-bigger').onclick = () => blocksSheet('bigger');
$('m-zoom').onclick = () => { X.span = X.span > 10 ? 7.2 : 14; closeSheets(); fit(); rebuild(); draw(); };
$('m-lab').onclick = () => { location.href = 'grid-lab.html'; };
document.querySelectorAll('[data-close]').forEach(b => b.onclick = () => { $(b.dataset.close).hidden = true; });
window.addEventListener('resize', () => { fit(); rebuild(); draw(); });
window.addEventListener('keydown', e => { if ((e.metaKey || e.ctrlKey) && e.key === 'z') { e.preventDefault(); go(e.shiftKey ? 1 : -1); } else if (e.key === 'Escape' && X.add) cancelAdd(); });

fit(); rebuild(); draw();
// for tests: the screen point of the copy of an edge class / a vertex class nearest the middle of the view
const nearestMid = list => { let best = null; list.forEach(m => { const d = Math.hypot(m.x - X.view.cx, m.y - X.view.cy); if (!best || d < best.d) best = { x: m.x, y: m.y, d, item: m.item }; }); return best; };
const edgeScreen = cls => nearestMid(X.patch.edges.filter(e => e.cls === cls).map(e => Object.assign(w2s(P((e.pts[0].x + e.pts[e.pts.length - 1].x) / 2, (e.pts[0].y + e.pts[e.pts.length - 1].y) / 2)), { item: e })));
const vertexScreen = cls => nearestMid(X.patch.vertices.filter(v => v.cls === cls).map(v => Object.assign(w2s(v.pos), { item: v })));
const nodeScreen = (gid, k) => nearestMid(X.patch.edges.filter(e => e.cls === gid && e.nodes[k]).map(e => Object.assign(w2s(e.nodes[k]), { item: e })));
// tests in a hidden pane (no animation frames): run a pending drag frame now
const flush = () => { if (raf) { cancelAnimationFrame(raf); raf = 0; dragFrame(); } if (praf) { cancelAnimationFrame(praf); praf = 0; draw(); } };
window.__ex = { X, Mg, Mv, G, T, C, cur, commit, go, attempt, fit, rebuild, draw, edgeScreen, vertexScreen, nodeScreen, w2s, s2w, hitEdge, hitVertex, hitPoint, checksOf, flush, closePop, popOpen: () => popOpen, setSnap, startAdd, cancelAdd, addTap, confirmAdd, endAt, previewPatch, capture: () => cv.toDataURL('image/png') };
})();
