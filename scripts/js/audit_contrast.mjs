/* File: scripts/js/audit_contrast.mjs
 *
 * Measure WCAG contrast on the rendered pages, in both themes (#531, #621).
 *
 * Checking a table of token pairs by hand proves something about the table.
 * What has to hold is a property of the page: every run of text a visitor can
 * read clears 4.5:1 against whatever is actually behind it, including the
 * parts nobody chose, like Material's footer, its admonition titles, and every
 * one of Agda's token classes in every code block.  So the ratio is computed
 * from the *computed* style of every text-bearing element, with the
 * background resolved by walking up the ancestor chain until something opaque
 * is found, as a browser composites it, and element opacity folded into the
 * foreground's alpha.
 *
 * AA is 4.5:1 for body text and 3:1 for large text, where large means >= 24px,
 * or >= 18.66px when bold.  Both thresholds are applied per element.
 *
 * Ported from williamdemeo.org's audit, with three changes for this site:
 *
 *   +  The scaffolding blocks the site hides by default (`hidden-source`,
 *      shown by the "Show all Agda" switch) are revealed before measuring,
 *      so their tokens are measured too.
 *   +  A page whose <body> carries no `data-md-color-scheme` (the /classic/
 *      pages, which are Agda's own HTML with the light tokens) is measured
 *      once, as it is, and not forced into a dark scheme it never shows.
 *   +  Extra arguments after the site directory restrict the run to pages
 *      whose path starts with one of them, for a quick look at one area.
 *
 * Usage:  node scripts/js/audit_contrast.mjs [site-dir] [path-prefix ...]
 *         make contrast-audit
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

// Runs in the page.  Returns one record per text-bearing element.
const MEASURE = () => {
  const parse = c => {
    // Chromium serializes a color it cannot write as rgb() (the result of a
    // color-mix(), for one) in the css-color-4 form `color(srgb r g b)`,
    // whose channels are 0..1 rather than 0..255.  Read as 0..255 they are
    // near-black: a false failure against a dark surface and, worse, a false
    // pass against a light one.  Alpha is 0..1 in every form.  (The exponent
    // matters too: Chromium writes tiny channels like `6e-05`.)
    const m = c.match(/[\d.]+(?:e-?\d+)?/gi);
    if (!m) return null;
    const k = c.startsWith('color(') ? 255 : 1;
    return { r: m[0] * k, g: m[1] * k, b: m[2] * k, a: m.length > 3 ? +m[3] : 1 };
  };
  const lin = v => (v /= 255) <= 0.04045 ? v / 12.92 : ((v + 0.055) / 1.055) ** 2.4;
  const lum = c => 0.2126 * lin(c.r) + 0.7152 * lin(c.g) + 0.0722 * lin(c.b);
  const over = (fg, bg) => ({            // fg composited onto opaque bg
    r: fg.r * fg.a + bg.r * (1 - fg.a),
    g: fg.g * fg.a + bg.g * (1 - fg.a),
    b: fg.b * fg.a + bg.b * (1 - fg.a),
    a: 1,
  });

  // The effective background: the first opaque ancestor color, with any
  // translucent layers above it composited back down in order.
  const background = el => {
    const stack = [];
    for (let n = el; n; n = n.parentElement) {
      const c = parse(getComputedStyle(n).backgroundColor);
      if (!c || c.a === 0) continue;
      stack.push(c);
      if (c.a === 1) break;
    }
    let acc = stack.pop() || { r: 255, g: 255, b: 255, a: 1 };
    while (stack.length) acc = over(stack.pop(), acc);
    return acc;
  };

  const out = [];
  for (const el of document.querySelectorAll('body *')) {
    if (el.offsetParent === null && getComputedStyle(el).position !== 'fixed') continue;
    let text = '';
    for (const c of el.childNodes) if (c.nodeType === 3) text += c.nodeValue;
    text = text.trim();
    if (!text) continue;
    // An SVG <title> is a tooltip, never painted as text.
    if (el instanceof SVGElement && el.closest('title')) continue;
    const cs = getComputedStyle(el);
    if (cs.visibility === 'hidden' || +cs.opacity === 0) continue;
    // SVG text is painted with `fill`, not `color`; reading `color` measures
    // a value the reader never sees.
    const paint = el instanceof SVGElement ? cs.fill : cs.color;
    const fg = parse(paint);
    if (!fg) continue;
    // Opacity dims the text exactly as an alpha channel would, and ignoring
    // it reports a better ratio than the reader gets.  An ancestor's opacity
    // counts too (Material sets `small { opacity: .75 }`), so the walk goes
    // up the tree, where the original audit read the element's own alone.
    let op = 1;
    for (let n = el; n; n = n.parentElement) {
      const o = +getComputedStyle(n).opacity;
      if (Number.isFinite(o)) op *= o;
    }
    fg.a *= op;
    if (fg.a === 0) continue;            // invisible on purpose
    const bg = background(el);
    const composited = fg.a < 1 ? over(fg, bg) : fg;
    const [hi, lo] = [lum(composited), lum(bg)].sort((a, b) => b - a);
    const ratio = (hi + 0.05) / (lo + 0.05);
    const px = parseFloat(cs.fontSize);
    const bold = parseInt(cs.fontWeight, 10) >= 700;
    const large = px >= 24 || (bold && px >= 18.66);
    out.push({
      ratio: Math.round(ratio * 100) / 100,
      need: large ? 3 : 4.5,
      px: Math.round(px * 10) / 10,
      tag: el.tagName.toLowerCase(),
      cls: (el.className && el.className.baseVal !== undefined ? '' : String(el.className || '')).slice(0, 40),
      fg: paint,
      bg: `rgb(${Math.round(bg.r)}, ${Math.round(bg.g)}, ${Math.round(bg.b)})`,
      text: text.slice(0, 44),
    });
  }
  return out;
};

const server = await serve(SITE);
const browser = await launch();
const { page } = browser;
await page.send('Page.enable');

const files = pages(SITE).sort().filter(f => {
  const rel = path.relative(SITE, f);
  return PREFIXES.length === 0 || PREFIXES.some(p => rel.startsWith(p));
});
const results = { default: [], slate: [] };
let stubs = 0;
let unthemed = 0;

for (const scheme of ['default', 'slate']) {
  for (const file of files) {
    const rel = path.relative(SITE, file);
    const html = fs.readFileSync(file, 'utf8');
    if (/<meta[^>]+http-equiv=["']?refresh/i.test(html)) {
      if (scheme === 'default') stubs++;
      continue;
    }
    const themed = /<body[^>]*data-md-color-scheme/.test(html);
    if (!themed && scheme === 'slate') continue;
    if (!themed) unthemed++;
    await page.goto(server.origin + '/' + rel.replace(/index\.html$/, ''));
    // Material animates color on a scheme change, and getComputedStyle
    // during that animation returns an interpolated value belonging to
    // neither theme.  Kill transitions first, then switch, then measure.
    await page.eval(([s, themed]) => {
      const stop = document.createElement('style');
      stop.textContent = '*,*::before,*::after{transition:none !important;animation:none !important}';
      document.head.appendChild(stop);
      if (themed) document.body.setAttribute('data-md-color-scheme', s);
      document.body.classList.add('reveal-agda-source');
      return new Promise(r => requestAnimationFrame(() => setTimeout(r, 50)));
    }, [scheme, themed]);
    for (const rec of await page.eval(MEASURE)) results[scheme].push({ page: rel, ...rec });
  }
}

await browser.close();
await server.close();

let failed = 0;
for (const scheme of ['default', 'slate']) {
  const rows = results[scheme];
  const bad = rows.filter(r => r.ratio < r.need);
  failed += bad.length;
  if (!rows.length) continue;
  const min = rows.reduce((a, b) => (a.ratio <= b.ratio ? a : b), rows[0]);
  console.log(`\n${scheme === 'default' ? 'light' : 'dark'} (${scheme}): ${rows.length} text elements, ` +
              `${bad.length} below AA`);
  console.log(`  lowest ratio: ${min.ratio}:1 on <${min.tag}${min.cls ? ' class="' + min.cls + '"' : ''}> ` +
              `"${min.text}" (${min.page})`);

  // The interesting summary is the worst case per kind of element, not
  // thousands of rows saying the same thing about body copy.  Agda's tokens
  // are `<a class="Function">` and kin, so the class is the kind.
  const worst = new Map();
  for (const r of rows) {
    const key = `${r.tag}${r.cls ? '.' + r.cls.split(' ')[0] : ''}`;
    if (!worst.has(key) || worst.get(key).ratio > r.ratio) worst.set(key, r);
  }
  const shown = [...worst.values()].sort((a, b) => a.ratio - b.ratio).slice(0, 40);
  console.log(`  worst ratio by element kind:`);
  for (const r of shown) {
    const mark = r.ratio < r.need ? ' FAIL' : '';
    console.log(`    ${String(r.ratio).padStart(6)}:1  need ${r.need}  ${r.px}px  ` +
                `<${r.tag}${r.cls ? ' class="' + r.cls + '"' : ''}>  ${r.fg} on ${r.bg}${mark}`);
  }
  if (bad.length) {
    console.log(`  --- below AA ---`);
    const seen = new Set();
    for (const r of bad.sort((a, b) => a.ratio - b.ratio)) {
      const key = `${r.tag}.${r.cls}.${r.fg}.${r.bg}`;
      if (seen.has(key)) continue;
      seen.add(key);
      console.log(`    ${String(r.ratio).padStart(6)}:1 (need ${r.need})  ${r.page}  ` +
                  `<${r.tag}${r.cls ? ' class="' + r.cls + '"' : ''}>  ${r.fg} on ${r.bg}  "${r.text}"`);
    }
  }
}

const n = files.length - stubs;
console.log(`\n${n} page(s): ${n - unthemed} in both themes, ${unthemed} without a scheme switch ` +
            `in light only; ${stubs} redirect stub(s) skipped`);
console.log(failed ? `\nFAIL: ${failed} element(s) below WCAG AA` : `\nOK: every text element meets WCAG AA`);
process.exit(failed ? 1 : 0);
