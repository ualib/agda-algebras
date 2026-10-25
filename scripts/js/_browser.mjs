/* File: scripts/js/_browser.mjs
 *
 * A minimal Chrome DevTools Protocol driver, and an HTTP server for site/,
 * shared by the theme's three browser audits (audit_contrast.mjs,
 * audit_fonts.mjs, audit_offline.mjs; `make design-audit`, #621).  Ported
 * unchanged in substance from williamdemeo.org's audits, where the design
 * and these checks come from; the MIME table gained `.jpeg`, which this
 * site's portraits use.
 *
 * The design audits have to run in a real browser: whether a glyph falls back
 * to a substitute font, and what color a pixel ends up, are questions only a
 * layout engine can answer.  Puppeteer or Playwright would do this in a line,
 * at the cost of a node_modules tree and a second browser download.  These
 * scripts need node and nothing from npm: node 22 ships a global `WebSocket`,
 * which is the only thing CDP actually requires.
 *
 * Serving over HTTP is not optional.  Under file:// Material's bundle never
 * initializes (`document$` is undefined), so the site's scripts never run and
 * the instant-navigation styles never apply.  An audit run from disk would be
 * measuring a page no visitor ever sees.
 */
import { spawn } from 'child_process';
import fs from 'fs';
import http from 'http';
import os from 'os';
import path from 'path';

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.webp': 'image/webp',
  '.woff2': 'font/woff2',
  '.pdf': 'application/pdf',
  '.xml': 'application/xml',
  '.txt': 'text/plain; charset=utf-8',
};

/** Serve `root` on an ephemeral port.  Resolves to { origin, close }. */
export function serve(root) {
  const server = http.createServer((req, res) => {
    let p = decodeURIComponent(new URL(req.url, 'http://x').pathname);
    if (p.endsWith('/')) p += 'index.html';
    const file = path.resolve(root, '.' + p);
    // Refuse to serve outside the root even though this only ever faces a
    // browser we launched: a traversal bug here would be a real one if the
    // script were ever pointed at a wider directory.  The trailing separator
    // matters -- without it a sibling directory whose name merely starts with
    // the root's, `site-scratch` next to `site`, passes the prefix test.
    const base = path.resolve(root) + path.sep;
    if (file !== path.resolve(root) && !file.startsWith(base)) {
      res.writeHead(403).end();
      return;
    }
    fs.readFile(file, (err, buf) => {
      if (err) {
        res.writeHead(404, { 'content-type': 'text/plain' }).end('not found');
        return;
      }
      res.writeHead(200, { 'content-type': MIME[path.extname(file)] || 'application/octet-stream' });
      res.end(buf);
    });
  });
  return new Promise(resolve => {
    server.listen(0, '127.0.0.1', () => {
      const { port } = server.address();
      resolve({
        origin: `http://127.0.0.1:${port}`,
        close: () => new Promise(r => server.close(r)),
      });
    });
  });
}

const CANDIDATES = [
  process.env.CHROME,
  process.env.CHROMIUM,
  process.env.PLAYWRIGHT_BROWSERS_PATH && path.join(process.env.PLAYWRIGHT_BROWSERS_PATH, 'chromium'),
  '/usr/bin/chromium',
  '/usr/bin/chromium-browser',
  '/usr/bin/google-chrome',
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  '/Applications/Chromium.app/Contents/MacOS/Chromium',
];

export function findChrome() {
  for (const c of CANDIDATES) {
    if (c && fs.existsSync(c)) return c;
  }
  for (const dir of (process.env.PATH || '').split(path.delimiter)) {
    for (const n of ['chromium', 'chromium-browser', 'google-chrome', 'google-chrome-stable']) {
      const c = path.join(dir, n);
      if (fs.existsSync(c)) return c;
    }
  }
  return null;
}

/** Launch headless Chromium and attach to a fresh tab over CDP. */
export async function launch() {
  const bin = findChrome();
  if (!bin) {
    throw new Error(
      'no Chromium found.  Install one, or set CHROME=/path/to/chrome.\n' +
      '       These audits render the page in a real browser; there is no offline substitute.');
  }
  const profile = fs.mkdtempSync(path.join(os.tmpdir(), 'site-audit-'));
  const proc = spawn(bin, [
    '--headless=new',
    '--remote-debugging-port=0',
    `--user-data-dir=${profile}`,
    '--no-sandbox',            // required in the containers this runs in
    '--disable-gpu',
    '--hide-scrollbars',
    '--force-device-scale-factor=1',
    '--disable-lcd-text',      // greyscale antialiasing, so screenshots diff cleanly
    'about:blank',
  ], { stdio: ['ignore', 'ignore', 'pipe'] });

  // Chromium prints the DevTools endpoint on stderr once, before anything else.
  const wsUrl = await new Promise((resolve, reject) => {
    let buf = '';
    const t = setTimeout(() => reject(new Error('chromium did not report a DevTools endpoint')), 30000);
    proc.stderr.on('data', d => {
      buf += d;
      const m = buf.match(/ws:\/\/[^\s]+/);
      if (m) { clearTimeout(t); resolve(m[0]); }
    });
    proc.on('exit', c => { clearTimeout(t); reject(new Error(`chromium exited with ${c}: ${buf.slice(0, 400)}`)); });
  });

  const session = await connect(wsUrl);
  const { targetId } = await session.send('Target.createTarget', { url: 'about:blank' });
  const { sessionId } = await session.send('Target.attachToTarget', { targetId, flatten: true });
  const page = wrap(session, sessionId);

  return {
    page,
    close: async () => {
      session.ws.close();
      const exited = new Promise(r => proc.once('exit', r));
      proc.kill();
      await Promise.race([exited, new Promise(r => setTimeout(r, 3000))]);
      // Chromium can still be flushing its profile as it goes down, which
      // makes the removal race and throw ENOTEMPTY.  A leftover temp
      // directory is not worth failing an audit over.
      try {
        fs.rmSync(profile, { recursive: true, force: true });
      } catch { /* ignore */ }
    },
  };
}

function connect(url) {
  return new Promise((resolve, reject) => {
    const ws = new WebSocket(url);
    const pending = new Map();
    const listeners = [];
    let id = 0;
    ws.addEventListener('message', ev => {
      const msg = JSON.parse(ev.data);
      if (msg.id !== undefined && pending.has(msg.id)) {
        const { res, rej } = pending.get(msg.id);
        pending.delete(msg.id);
        msg.error ? rej(new Error(`${msg.error.message} (${JSON.stringify(msg.error.data ?? '')})`)) : res(msg.result);
      } else if (msg.method) {
        for (const fn of listeners) fn(msg);
      }
    });
    ws.addEventListener('error', e => reject(new Error(`CDP socket error: ${e.message ?? e}`)));
    ws.addEventListener('open', () => resolve({
      ws,
      listeners,
      send(method, params = {}, sessionId) {
        const msg = { id: ++id, method, params };
        if (sessionId) msg.sessionId = sessionId;
        return new Promise((res, rej) => {
          pending.set(msg.id, { res, rej });
          ws.send(JSON.stringify(msg));
        });
      },
    }));
  });
}

function wrap(session, sessionId) {
  const page = {
    session,
    sessionId,
    send: (method, params) => session.send(method, params, sessionId),
    on(method, fn) {
      session.listeners.push(msg => {
        if (msg.method === method && msg.sessionId === sessionId) fn(msg.params);
      });
    },
    /** Navigate and wait for the load event plus a settle tick for the scripts. */
    async goto(url, { settle = 400 } = {}) {
      const loaded = new Promise(res => {
        const fn = msg => {
          if (msg.method === 'Page.loadEventFired' && msg.sessionId === sessionId) res();
        };
        session.listeners.push(fn);
      });
      await page.send('Page.navigate', { url });
      await loaded;
      await new Promise(r => setTimeout(r, settle));
    },
    async eval(fn, arg) {
      const expr = `(${fn.toString()})(${JSON.stringify(arg ?? null)})`;
      const { result, exceptionDetails } = await page.send('Runtime.evaluate', {
        expression: expr, returnByValue: true, awaitPromise: true,
      });
      if (exceptionDetails) throw new Error(exceptionDetails.exception?.description || exceptionDetails.text);
      return result.value;
    },
    // The scale factor is a parameter rather than a constant because the
    // preview thumbnails (#97) are captured to be downscaled: rendering at 2x
    // and shrinking is what keeps small type in a 480px-wide shot legible.
    // The audits pass nothing and keep the 2x they were written against.
    async setViewport(width, height, deviceScaleFactor = 2) {
      await page.send('Emulation.setDeviceMetricsOverride', {
        width, height, deviceScaleFactor, mobile: false,
      });
    },
    async screenshot(file, opts = {}) {
      const { data } = await page.send('Page.captureScreenshot', { format: 'png', ...opts });
      fs.writeFileSync(file, Buffer.from(data, 'base64'));
    },
  };
  return page;
}

/** Fonts Chromium actually used to rasterise a node's text, by CSS selector. */
export async function platformFonts(page, selector) {
  const { root } = await page.send('DOM.getDocument', { depth: -1, pierce: false });
  const { nodeId } = await page.send('DOM.querySelector', { nodeId: root.nodeId, selector });
  if (!nodeId) return null;
  const { fonts } = await page.send('CSS.getPlatformFontsForNode', { nodeId });
  return fonts;
}
