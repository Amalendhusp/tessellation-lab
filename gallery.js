/* tessellation-mobile-workspace-v5.11-ph2-gallery / gallery.js  (Phase 2: My Gallery)
 * STORAGE ONLY: it knows nothing about drawing or geometry (app.js makes the projects and the pictures).
 *
 *   database   'tessellation-gallery', version 1 — a database of its own, so the automatic save ('tessellation-classroom', version 1, project.js)
 *              is never changed: every older build at the same address keeps opening it, and keeps keeping its work.
 *   stores     cards     key = id · small: { id, name, created, updated, label, shape, construction, stage, build, bytes, check, thumbs: { tile, pattern } }
 *              projects  key = id · the complete project (format 7), stored as the automatic save stores it (typed arrays included)
 *              meta      key = name · e.g. 'backup': { at, count, bytes }
 *   writes     every change (save, update, rename, duplicate, delete, restore) is ONE transaction over the stores it touches: all of it, or none.
 *   ids        'p-' + time (base 36) + 8 random hex digits. crypto.getRandomValues works on an http:// address (crypto.randomUUID does not).
 *   check      FNV-1a (32 bit) of a project's file text: finds damage and identical copies. (crypto.subtle does not exist on an http:// address.)
 */
(() => {
'use strict';
const DB_NAME = 'tessellation-gallery', DB_VERSION = 1, STORES = ['cards', 'projects', 'meta'];
const g = { db: null, ok: null, reason: '' };

function open(timeoutMs) {
  return new Promise(resolve => {
    let done = false; const finish = (db, why) => { if (done) { if (db) db.close(); return; } done = true; g.db = db; g.ok = !!db; g.reason = why || ''; resolve(!!db); };
    try {
      if (!window.indexedDB) { finish(null, 'no-indexeddb'); return; }
      const rq = indexedDB.open(DB_NAME, DB_VERSION);
      rq.onupgradeneeded = () => { const db = rq.result; STORES.forEach(s => { if (!db.objectStoreNames.contains(s)) db.createObjectStore(s); }); };
      rq.onsuccess = () => { const db = rq.result; db.onversionchange = () => { db.close(); g.db = null; g.ok = false; g.reason = 'newer'; }; finish(db); };
      rq.onerror = () => finish(null, (rq.error && rq.error.name) || 'open-error');   // VersionError: a newer app changed the Gallery; it is left alone
      rq.onblocked = () => finish(null, 'blocked');
      setTimeout(() => finish(null, 'timeout'), timeoutMs || 4000);   // some Safari versions never answer the first open
    } catch (e) { finish(null, (e && e.name) || 'open-error'); }
  });
}
const lost = e => /InvalidState|TransactionInactive|Unknown/.test((e && e.name) || String(e));
async function withDB(fn) {                      // Safari can drop the connection (as in the automatic save): reopen once and try again
  if (!g.ok) throw Object.assign(new Error('My Gallery is not available'), { name: g.reason || 'unavailable' });
  try { return await fn(g.db); } catch (e) { if (!lost(e)) throw e; await open(); if (!g.ok) throw e; return fn(g.db); }
}
function read(store, how, key) {
  return withDB(db => new Promise((resolve, reject) => {
    const os = db.transaction(store, 'readonly').objectStore(store), rq = how === 'all' ? os.getAll() : os.get(key);
    rq.onsuccess = () => resolve(rq.result); rq.onerror = () => reject(rq.error);
  }));
}
const list = () => read('cards', 'all');
const getCard = id => read('cards', 'one', id);
const getProject = id => read('projects', 'one', id);
const getMeta = k => read('meta', 'one', k);
// ops: [{ store, put: value, key } | { store, del: key }] — one transaction; resolves { ok, reason }
function write(ops) {
  const stores = [...new Set(ops.map(o => o.store))];
  return withDB(db => new Promise(resolve => {
    let tx; try { tx = db.transaction(stores, 'readwrite'); ops.forEach(o => { const os = tx.objectStore(o.store); if ('del' in o) os.delete(o.del); else os.put(o.put, o.key); }); }
    catch (e) { try { if (tx) tx.abort(); } catch (_) {} if (lost(e)) throw e; resolve({ ok: false, reason: (e && e.name) || 'write-error' }); return; }   // nothing of it is kept
    tx.oncomplete = () => resolve({ ok: true });
    tx.onabort = tx.onerror = () => resolve({ ok: false, reason: (tx.error && tx.error.name) || 'write-error' });
  })).catch(e => ({ ok: false, reason: (e && e.name) || 'write-error' }));
}
const putEntry = (card, project) => write([{ store: 'projects', put: project, key: card.id }, { store: 'cards', put: card, key: card.id }]);
const delEntry = id => write([{ store: 'cards', del: id }, { store: 'projects', del: id }]);
const setMeta = (k, v) => write([{ store: 'meta', put: v, key: k }]);

function newId() {
  const r = new Uint8Array(4); crypto.getRandomValues(r);
  return 'p-' + Date.now().toString(36) + '-' + Array.from(r, b => b.toString(16).padStart(2, '0')).join('');
}
function fnv(text) {                             // FNV-1a over the UTF-16 code units: the same text always gives the same 8 hex digits
  let h = 0x811c9dc5;
  for (let i = 0; i < text.length; i++) { h ^= text.charCodeAt(i); h = Math.imul(h, 0x01000193) >>> 0; }
  return h.toString(16).padStart(8, '0');
}
async function estimate() { try { return navigator.storage && navigator.storage.estimate ? await navigator.storage.estimate() : null; } catch (_) { return null; } }

window.TessGallery = { DB_NAME, DB_VERSION, state: g, open, list, getCard, getProject, getMeta, setMeta, write, putEntry, delEntry, newId, fnv, estimate };
})();
