/* File: scripts/js/audit_offline.mjs
 *
 * Load every page in a real browser and record every request it makes
 * (#531, #621).
 *
 * "No page requests a font, a script or a stylesheet from another origin" is
 * a claim about runtime behavior.  scripts/python/theme/check_offline.py,
 * which CI runs, reads every page and stylesheet for the references that
 * fetch; what it cannot see is a request a script makes, such as the call
 * Material's bundle makes to api.github.com when the repository chip carries
 * the attribute that asks for it.  So this audit loads each page and reads
 * the network log.  Ported unchanged in substance from williamdemeo.org's.
 *
 * The site is served from 127.0.0.1, so "same origin as the page" is the test.
 * data: and blob: URLs are inlined content and count as local.
 *
 * Usage:  node scripts/js/audit_offline.mjs [site-dir] [path-prefix ...]
 *         make offline-audit
 */
import fs from 'fs';
import path from 'path';
import { serve, launch } from './_browser.mjs';

const SITE = process.argv[2] || 'site';
const PREFIXES = process.argv.slice(3);

function pages(dir) {
  const out = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) out.push(...pages(p));
    else if (e.name.endsWith('.html')) out.push(p);
  }
  return out;
}

const server = await serve(SITE);
const browser = await launch();
const { page } = browser;
await page.send('Page.enable');
await page.send('Network.enable');

let current = '';
const external = [];
const byType = new Map();

page.on('Network.requestWillBeSent', ({ request, type }) => {
  const url = request.url;
  byType.set(type || 'Other', (byType.get(type || 'Other') || 0) + 1);
  if (url.startsWith(server.origin) || url.startsWith('data:') || url.startsWith('blob:')
      || url === 'about:blank') {
    return;
  }
  external.push({ page: current, url, type: type || 'Other' });
});

const files = pages(SITE).sort().filter(f => {
  const rel = path.relative(SITE, f);
  return PREFIXES.length === 0 || PREFIXES.some(p => rel.startsWith(p));
});
let stubs = 0;
for (const file of files) {
  const rel = path.relative(SITE, file);
  // A redirect stub is a <meta refresh> to somewhere else on purpose; letting
  // the browser follow it would report the destination as an external request
  // the site made, which is the opposite of what it means.
  if (/<meta[^>]+http-equiv=["']?refresh/i.test(fs.readFileSync(file, 'utf8'))) {
    stubs++;
    continue;
  }
  current = rel;
  await page.goto(server.origin + '/' + rel.replace(/index\.html$/, ''));
}

// Fonts are fetched lazily, and only for text that is actually laid out.  A
// page can therefore look clean simply because nothing on it needed the face
// that would have gone to a CDN.  Force every declared @font-face to load, and
// watch where the bytes come from.
current = '(forced font load)';
await page.goto(server.origin + '/');
const faceCount = await page.eval(() => {
  const faces = [...document.fonts];
  return Promise.all(faces.map(f => f.load().catch(() => null))).then(() => faces.length);
});
await new Promise(r => setTimeout(r, 500));

console.log(`pages loaded  : ${files.length - stubs}  (${stubs} redirect stub(s) skipped)`);
console.log(`@font-face    : ${faceCount} declared, all forced to load`);
console.log(`requests      : ${[...byType].map(([t, n]) => `${t} ${n}`).join(', ')}`);

if (external.length) {
  console.log(`\n--- requests to another origin (${external.length}) ---`);
  const seen = new Set();
  for (const e of external) {
    const key = e.url;
    if (seen.has(key)) continue;
    seen.add(key);
    console.log(`  [${e.type}] ${e.url}\n      first seen on ${e.page}`);
  }
}

await browser.close();
await server.close();

console.log(external.length
  ? `\nFAIL: ${external.length} external request(s)`
  : `\nOK: every request was same-origin`);
process.exit(external.length ? 1 : 0);
