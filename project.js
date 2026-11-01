/* tessellation-mobile-workspace-v5.2-classroom / project.js  (CR1: keep the work; format 5 since v5.8-f1a1)
 * The PROJECT FORMAT, the project FILE (Save project / Open project…) and the automatic save on this device (IndexedDB).
 * It knows nothing about drawing or geometry: app.js builds a project object from its own state and restores it with its own functions.
 * The format is described in CR1_PROJECT_FORMAT.md.
 *
 *   project file   JSON. Bulky number lists (boundary samples, stroke points) are typed arrays, written in the file as
 *                  {"f64": base64 of little-endian IEEE-754 doubles} (exact: every number comes back bit for bit) and {"u8": base64} for
 *                  image bytes. Everything else is plain JSON.
 *   device save    the same object, stored as it is (typed arrays included) in IndexedDB. Two slots, written alternately; a small
 *                  'meta' record says which slot is the latest. Each save is one transaction, so a save that is interrupted leaves the
 *                  previous one untouched, and the previous slot is kept as a fallback.
 */
(() => {
'use strict';
const FORMAT = 'tessellation-project', VERSION = 7;          // 2 (CR3): up to 40 points, Polygon sketches with one Undo timeline, the process recording; 3 (T1): the Mirror rule, mirrored drawing; 4 (T2): Mirror's Alternating arrangement; 5 (F1a-1): Two figures; 6 (F1r): Two figures' corners move, fills belong to a figure; 7 (F1a-2): Mirror · Two figures, Tessellate colours per figure, a new construction keeps the previous one

/* ---------------- typed arrays <-> base64 (exact) ---------------- */
const LE = new Uint8Array(new Uint16Array([1]).buffer)[0] === 1;
function bytesToB64(u8) { let s = ''; for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000)); return btoa(s); }
function b64ToBytes(b64) { const s = atob(b64), u8 = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) u8[i] = s.charCodeAt(i); return u8; }
function f64ToB64(a) {
  if (LE) return bytesToB64(new Uint8Array(a.buffer, a.byteOffset, a.byteLength));
  const dv = new DataView(new ArrayBuffer(a.length * 8)); a.forEach((v, i) => dv.setFloat64(i * 8, v, true)); return bytesToB64(new Uint8Array(dv.buffer));
}
function b64ToF64(b64) {
  const u8 = b64ToBytes(b64); if (u8.length % 8) throw new Error('number list has a broken length');
  if (LE) return new Float64Array(u8.buffer, 0, u8.length / 8);
  const dv = new DataView(u8.buffer), out = new Float64Array(u8.length / 8); for (let i = 0; i < out.length; i++) out[i] = dv.getFloat64(i * 8, true); return out;
}
function toFileText(project) {
  return JSON.stringify(project, (k, v) => v instanceof Float64Array ? { f64: f64ToB64(v) } : v instanceof Uint8Array ? { u8: bytesToB64(v) } : v);
}
function fromFileText(text) {
  return JSON.parse(text, (k, v) => {
    if (v && typeof v === 'object' && !Array.isArray(v)) { const ks = Object.keys(v);
      if (ks.length === 1 && ks[0] === 'f64' && typeof v.f64 === 'string') return b64ToF64(v.f64);
      if (ks.length === 1 && ks[0] === 'u8' && typeof v.u8 === 'string') return b64ToBytes(v.u8); }
    return v;
  });
}

/* ---------------- reading a file: is it a project, and can this version open it? ---------------- */
// Each later format version adds a step here that turns version n into n + 1, so every older file keeps opening.
const UPGRADE = {
  1: p => Object.assign({}, p, { version: 2 }),  // version 1 → 2: nothing to convert (version 2 only adds optional parts)
  2: p => Object.assign({}, p, { version: 3 }),  // version 2 → 3: nothing to convert (version 3 adds the Mirror rule and mirrored strokes/fills; an
                                                 //   older app refuses a version-3 file as "newer", rather than drawing mirrored strokes un-mirrored)
  3: p => Object.assign({}, p, { version: 4 }),  // version 3 → 4: nothing to convert (version 4 adds Mirror's Alternating arrangement, the
                                                 //   construction 'mirror-flip'; v5.6 refuses a version-4 file rather than show it as Same orientation)
  4: p => Object.assign({}, p, { version: 5 }),  // version 4 → 5: nothing to convert (version 5 adds Two figures: a two-figure unit, 'fg-slide', whose
                                                 //   boundaries have a seventh side, the side between Figure A and Figure B; v5.7.1 refuses a version-5 file)
  5: p => Object.assign({}, p, { version: 6 }),  // version 5 → 6: nothing to convert (version 6 lets Two figures' six corners move and gives a fill its
                                                 //   figure, 'A' or 'B'; v5.8 refuses a version-6 file rather than show moved corners as an error)
  6: p => {                                      // version 6 → 7 (F1a-2): Tessellate colours belong to a FIGURE. A two-figure project of version 6 kept its
    const g = p.geometry, two = !!g && !!g.unit && g.unit.tiles === 2, cp = p.composition;   //   group colours on the figure then emphasised; they move to that figure
    if (!two || !cp || typeof cp.groups !== 'object' || !cp.groups) return Object.assign({}, p, { version: 7 });   //   ('A:' or 'B:' keys), so the project looks the same
    const f = p.view && p.view.figureFocus === 'B' ? 'B' : 'A', groups = {};
    Object.keys(cp.groups).forEach(m => { const src = cp.groups[m]; if (!src || typeof src !== 'object') return; groups[m] = {}; Object.keys(src).forEach(k => { groups[m][/^[AB]:/.test(k) ? k : f + ':' + k] = src[k]; }); });
    return Object.assign({}, p, { version: 7, composition: Object.assign({}, cp, { groups }) });
  }
};                                               //   v5.8.1 refuses a version-7 file rather than show Mirror · Two figures or the figure colours wrongly
function readProject(text) {      // → { project } or { problem: a sentence for the student }
  let p;
  try { p = fromFileText(text); } catch (_) { return { problem: 'This file is not a tessellation project, or it is damaged.' }; }
  return checkProject(p);
}
function checkProject(p) {         // the same check for a file and for the save on this device
  if (!p || typeof p !== 'object' || p.format !== FORMAT) return { problem: 'This file is not a tessellation project.' };
  if (!Number.isInteger(p.version) || p.version < 1) return { problem: 'This project file is damaged (no format version).' };
  if (p.version > VERSION) return { problem: 'This project was saved by a newer version of the app, so this version cannot open it.' };
  try { while (p.version < VERSION) { const up = UPGRADE[p.version]; if (!up) throw new Error('no upgrade from version ' + p.version); p = up(p); } }
  catch (e) { return { problem: 'This project file could not be updated to the current format (' + e.message + ').' }; }
  return { project: p };
}

/* ---------------- automatic save on this device (IndexedDB) ---------------- */
const DB_NAME = 'tessellation-classroom', DB_STORE = 'save';
const store = { db: null, ok: null, reason: '', meta: null, busy: false };
function openDB(timeoutMs) {
  return new Promise(resolve => {
    let done = false; const finish = (db, why) => { if (done) return; done = true; store.db = db; store.ok = !!db; store.reason = why || ''; resolve(!!db); };
    try {
      if (!window.indexedDB) { finish(null, 'no-indexeddb'); return; }
      const rq = indexedDB.open(DB_NAME, 1);
      rq.onupgradeneeded = () => { if (!rq.result.objectStoreNames.contains(DB_STORE)) rq.result.createObjectStore(DB_STORE); };
      rq.onsuccess = () => { const db = rq.result; db.onversionchange = () => db.close(); finish(db); };
      rq.onerror = () => finish(null, (rq.error && rq.error.name) || 'open-error');
      rq.onblocked = () => finish(null, 'blocked');
      setTimeout(() => finish(null, 'timeout'), timeoutMs || 4000);   // some Safari versions never answer the first open
    } catch (e) { finish(null, e && e.name || 'open-error'); }
  });
}
function get(key) {
  return new Promise((resolve, reject) => {
    try { const rq = store.db.transaction(DB_STORE, 'readonly').objectStore(DB_STORE).get(key); rq.onsuccess = () => resolve(rq.result); rq.onerror = () => reject(rq.error); }
    catch (e) { reject(e); }
  });
}
async function readMeta() { if (!store.ok) return null; try { store.meta = (await get('meta')) || null; } catch (_) { store.meta = null; } return store.meta; }
async function readSlot(slot) { if (!store.ok) return null; const p = await get(slot); return p && p.format === FORMAT ? p : null; }
// write the project into the slot that is NOT the latest, then point 'meta' at it — one transaction, so all or nothing
function save(project, info) {
  return new Promise(resolve => {
    if (!store.ok) { resolve({ ok: false, reason: store.reason || 'unavailable' }); return; }
    const m0 = store.meta || { slots: {} }, slot = m0.latest === 'a' ? 'b' : 'a', at = Date.now();
    const meta = { format: FORMAT, version: VERSION, latest: slot, slots: { ...m0.slots, [slot]: { at, ...info } } };
    let tx; const t0 = performance.now();
    try {
      tx = store.db.transaction(DB_STORE, 'readwrite'); const os = tx.objectStore(DB_STORE);
      os.put(project, slot); os.put(meta, 'meta');
    } catch (e) { resolve({ ok: false, reason: (e && e.name) || 'write-error' }); return; }
    const queued = performance.now() - t0;                    // the part that runs on the page's own time (copying the project)
    store.busy = true;
    tx.oncomplete = () => { store.meta = meta; store.busy = false; resolve({ ok: true, at, slot, queuedMs: queued }); };
    tx.onabort = tx.onerror = () => { store.busy = false; resolve({ ok: false, reason: (tx.error && tx.error.name) || 'write-error' }); };
  });
}
// the Continue card's picture only (the project itself is unchanged)
function setThumb(thumb) {
  return new Promise(resolve => {
    const m = store.meta; if (!store.ok || store.busy || !m || !m.latest || !m.slots[m.latest]) { resolve(false); return; }   // never while a save is being written
    const meta = { ...m, slots: { ...m.slots, [m.latest]: { ...m.slots[m.latest], thumb } } };
    try { const tx = store.db.transaction(DB_STORE, 'readwrite'); tx.objectStore(DB_STORE).put(meta, 'meta'); tx.oncomplete = () => { store.meta = meta; resolve(true); }; tx.onabort = tx.onerror = () => resolve(false); }
    catch (_) { resolve(false); }
  });
}
async function clearAll() { if (!store.ok) return; await new Promise(r => { const tx = store.db.transaction(DB_STORE, 'readwrite'); tx.objectStore(DB_STORE).clear(); tx.oncomplete = tx.onerror = tx.onabort = r; }); store.meta = null; }

window.TessProject = {
  FORMAT, VERSION, toFileText, fromFileText, readProject, checkProject, f64ToB64, b64ToF64, bytesToB64, b64ToBytes,
  store, openDB, readMeta, readSlot, save, setThumb, clearAll
};
})();
