/* File: scripts/js/audit_fonts.mjs
 *
 * Report every font Chromium actually rasterized text with, and fail on any
 * that is not one of the site's own webfonts (#531, #621).
 *
 * Agda's notation has to render in JuliaMono with no fallback substitution.
 * A font's cmap can be inspected offline, but whether the *browser* used that
 * face for a given character depends on the cascade, the unicode-range split
 * in fonts.css, and what happens to be installed locally.  Only the layout
 * engine knows, and CSS.getPlatformFontsForNode is how it can be asked.  This
 * is the check that caught the subsetting trap #531 describes: a subset built
 * from agda-input.el's list misses ℓ, Π and the subscript digits, which Agda's
 * input method inherits from Emacs' TeX method.
 *
 * How it scales.  williamdemeo.org's audit asks about every text node, one
 * DevTools call each, which on this site would be millions of calls (a long
 * module page has 25,000 tokens).  The face a character falls to depends only
 * on the character and the element's font properties (family stack, weight,
 * style), so this audit asks once per distinct pair, site-wide: on each page
 * it finds the pairs not yet seen, appends to one element carrying each a
 * span holding only that character, and asks about the spans.  Every
 * character on every page is still covered, in the context it appears in.
 *
 * The test: every face Chromium reports must be a downloaded webfont
 * (`isCustomFont`).  A system font means a character fell out of every
 * subset that ships, which is exactly the mid-line substitution at issue.
 * The scaffolding blocks the site hides by default are revealed first, so
 * their characters count.  A fixed probe of characters Agda cannot avoid
 * runs too, so the check does not depend on any page containing them.
 *
 * Usage:  node scripts/js/audit_fonts.mjs [site-dir] [path-prefix ...]
 *         make font-audit
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

// Runs in the page.  For every (font properties, character) pair not in
// `seen`, append a probe span holding only that character to an element that
// has it, and return the new pairs.  Material's icons are SVG and carry no
// text; the screen-reader-only and display:none parts are skipped because
// nothing rasterizes them.
const PLANT = seen => {
  const known = new Set(seen);
  const planted = [];
  document.body.classList.add('reveal-agda-source');
  const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
  for (let t = walker.nextNode(); t; t = walker.nextNode()) {
    const el = t.parentElement;
    if (!el || el.closest('script,style,noscript,title,svg')) continue;
    if (el.offsetParent === null && getComputedStyle(el).position !== 'fixed') continue;
    const cs = getComputedStyle(el);
    if (cs.visibility === 'hidden') continue;
    const props = `${cs.fontFamily}|${cs.fontWeight}|${cs.fontStyle}`;
    for (const ch of new Set(t.nodeValue)) {
      if (/\s/u.test(ch) || ch.codePointAt(0) < 0x21) continue;
      const key = props + '\u0000' + ch;
      if (known.has(key)) continue;
      known.add(key);
      const span = document.createElement('span');
      span.textContent = ch;
      span.setAttribute('data-fontprobe', String(planted.length));
      el.appendChild(span);
      planted.push({ key, ch, family: cs.fontFamily.split(',')[0].trim(),
                     where: (el.tagName + (el.className && typeof el.className === 'string'
                       ? '.' + el.className.split(' ')[0] : '')).toLowerCase() });
    }
  }
  return document.fonts.ready.then(() => planted);
};

const server = await serve(SITE);
const browser = await launch();
const { page } = browser;
await page.send('Page.enable');
await page.send('DOM.enable');
await page.send('CSS.enable');

// The fonts of every probe still in the document, by probe id.  A script
// may re-render an element after the probes are planted (Material rewrites
// the header's title as the page scrolls), and a probe that went with it is
// simply not measured on this page; its pair stays unseen, so a later page
// that carries it measures it there.
async function probeFonts() {
  const { root } = await page.send('DOM.getDocument', { depth: 0 });
  const { nodeIds } = await page.send('DOM.querySelectorAll',
    { nodeId: root.nodeId, selector: '[data-fontprobe]' });
  const out = new Map();
  for (const nodeId of nodeIds) {
    const { attributes } = await page.send('DOM.getAttributes', { nodeId });
    const id = +attributes[attributes.indexOf('data-fontprobe') + 1];
    const { fonts } = await page.send('CSS.getPlatformFontsForNode', { nodeId });
    out.set(id, fonts);
  }
  return out;
}

const files = pages(SITE).sort().filter(f => {
  const rel = path.relative(SITE, f);
  return PREFIXES.length === 0 || PREFIXES.some(p => rel.startsWith(p));
});
const seen = [];
const faces = new Map();       // familyName -> { custom, glyphs, pages: Set }
const failures = [];
const lost = [];
let stubs = 0;

for (const file of files) {
  const rel = path.relative(SITE, file);
  if (/<meta[^>]+http-equiv=["']?refresh/i.test(fs.readFileSync(file, 'utf8'))) {
    stubs++;
    continue;
  }
  await page.goto(server.origin + '/' + rel.replace(/index\.html$/, ''));
  const planted = await page.eval(PLANT, seen);
  if (!planted.length) continue;
  await new Promise(r => setTimeout(r, 150));
  const reports = await probeFonts();
  planted.forEach((p, i) => {
    if (!reports.has(i)) { lost.push(p); return; }
    seen.push(p.key);
    for (const f of reports.get(i)) {
      const rec = faces.get(f.familyName) || { custom: f.isCustomFont, glyphs: 0, pages: new Set() };
      rec.glyphs += f.glyphCount;
      rec.pages.add(rel);
      faces.set(f.familyName, rec);
      if (!f.isCustomFont) failures.push({ page: rel, ch: p.ch, stack: p.family, where: p.where, face: f.familyName });
    }
  });
}

// The characters a page of Agda cannot avoid, measured in a code block on
// the landing page so the check does not depend on any page containing
// them: #531's 𝑨 𝓤 𝑆 𝔸 𝕏 𝒦 𝓞 𝓥, the subset trap's ℓ Π ₀ ₁ ₂, and the
// operators and brackets of the library's signatures.
const PROBE = [...'𝑨𝓤𝑆≅⨅⊔∀∘⟨⟩→₀₁₂ₙᵢ𝔸𝕏λΠΣ≡×⊤⊥¬∈∉⊢⇒↦∙≤⊑⊎∅ℕℓ𝒦𝓞𝓥·⟦⟧∧∨≢ʳ✓≈≋⊆⋯'];
await page.goto(server.origin + '/');
await page.eval(chars => {
  const host = document.createElement('pre');
  host.className = 'Agda';
  for (const [i, c] of chars.entries()) {
    const a = document.createElement('a');
    a.className = 'Function';
    a.id = 'probe-' + i;
    a.textContent = c;
    host.appendChild(a);
  }
  document.querySelector('.md-typeset').appendChild(host);
  return document.fonts.ready.then(() => true);
}, PROBE);
await new Promise(r => setTimeout(r, 300));
const probeBad = [];
for (const [i, c] of PROBE.entries()) {
  const { root } = await page.send('DOM.getDocument', { depth: 0 });
  const { nodeId } = await page.send('DOM.querySelector', { nodeId: root.nodeId, selector: '#probe-' + i });
  const { fonts } = await page.send('CSS.getPlatformFontsForNode', { nodeId });
  const wrong = fonts.filter(f => !f.isCustomFont || f.familyName !== 'JuliaMono');
  if (wrong.length || fonts.length === 0) {
    probeBad.push({ ch: c, cp: c.codePointAt(0), fonts: fonts.map(f => f.familyName).join(', ') || '(none)' });
  }
}

await browser.close();
await server.close();

console.log(`pages audited : ${files.length - stubs}  (${stubs} redirect stub(s) skipped)`);
console.log(`probes        : ${seen.length} distinct (font properties, character) pairs`);
console.log(`\nfaces used, across the whole site:`);
console.log(`${'family'.padEnd(26)} ${'webfont'.padStart(8)} ${'glyphs'.padStart(8)}  pages`);
for (const [family, rec] of [...faces].sort((a, b) => b[1].glyphs - a[1].glyphs)) {
  console.log(`${family.padEnd(26)} ${String(rec.custom).padStart(8)} ${String(rec.glyphs).padStart(8)}  ${rec.pages.size}`);
}
const unmeasured = lost.filter(p => !seen.includes(p.key));
console.log(`unmeasured    : ${unmeasured.length} pair(s) whose every probe was re-rendered away` +
            (unmeasured.length ? ` (${[...new Set(unmeasured.map(p => p.where))].join(', ')})` : ''));
console.log(`\nAgda probe: ${PROBE.length - probeBad.length}/${PROBE.length} characters rendered in JuliaMono`);
if (failures.length) {
  console.log(`\n--- characters rendered in a system font (${failures.length}) ---`);
  for (const f of failures.slice(0, 40)) {
    console.log(`  ${f.ch}  U+${f.ch.codePointAt(0).toString(16).toUpperCase().padStart(4, '0')}  ` +
                `-> ${f.face}  (stack ${f.stack}, <${f.where}>, first on ${f.page})`);
  }
}
if (probeBad.length) {
  console.log(`\n--- probe characters that did not render in JuliaMono (${probeBad.length}) ---`);
  for (const f of probeBad) {
    console.log(`  ${f.ch}  U+${f.cp.toString(16).toUpperCase().padStart(4, '0')}  -> ${f.fonts}`);
  }
}
const bad = failures.length + probeBad.length;
console.log(bad ? `\nFAIL: ${bad} substitution(s)` : `\nOK: no fallback substitution`);
process.exit(bad ? 1 : 0);
