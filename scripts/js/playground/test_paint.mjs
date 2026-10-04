// File: scripts/js/playground/test_paint.mjs
//
// The playground editor's colored mirror (`docs/assets/js/playground-paint.js`):
// the conversion of Agda's highlighting to the editor's offsets (`offsetOf`,
// `fromAgda`), the bookkeeping that keeps it on the right characters while
// the reader types (`shift`), the painter (`paint`), and the reading of the
// build's highlighted block (`rangesOf`).
//
// The mirror is a `<pre>` under a transparent `<textarea>`, so the reader
// sees the colors and the box's caret together.  Every defect here is
// silent.  A mirror that differs from the box by one character puts every
// caret after it in the wrong place; a range one unit off colors half of a
// two-unit character, and this library's names (𝑨, 𝔻, 𝑆, 𝓞) are two units
// each; a range kept across an edit it touched colors the reader's new text
// as whatever stood there before.  So this pins, each where it is checked,
// the following:
//
//   +  `offsetOf` agrees with `edits.js`'s, which the worker's edits use, at
//      every position of every text here (two counts of the same positions
//      that disagree put a goal's mark and the text Agda edited in different
//      places);
//   +  `fromAgda` gives each of Agda's atoms the class the site colors, drops
//      what it cannot color, and orders the ranges, on a load captured from
//      the real checker;
//   +  `shift` keeps what an edit did not touch, moves what follows it, and
//      drops what it touched, for ranges and marks alike;
//   +  `paint` writes the text back exactly, plus one newline, with each span
//      over exactly its range and a mark cutting across ranges;
//   +  `rangesOf` reads back from a painted block the ranges it was painted
//      with, and from a block shaped as the build writes it, the token spans
//      and nothing else.
//
// `paint` and `rangesOf` need a DOM, and the stand-in below has only what
// they touch: creating a fragment, an element and a text node, appending, the
// `textContent` setter, and the walk (`firstChild`, `nextSibling`,
// `nodeType`, `nodeValue`, `nodeName`, `className`).  The script is a classic
// one that sets `globalThis.AgdaPaint` when there is no `window`, so it is
// loaded as a browser would run it, for its effect.
//
// Usage:  node scripts/js/playground/test_paint.mjs
//         make playground-test

import { readFileSync } from 'node:fs';
import { offsetOf as editsOffsetOf } from '../../../docs/assets/js/playground/edits.js';

await import('../../../docs/assets/js/playground-paint.js');
const { offsetOf, fromAgda, shift, paint, rangesOf } = globalThis.AgdaPaint;

const failures = [];
let asserted = 0;
const check = (ok, what) => { asserted += 1; if (!ok) failures.push(what); };
const same = (got, want, what) => check(
  JSON.stringify(got) === JSON.stringify(want),
  `${what}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);

// ---- a DOM, as much as paint and rangesOf touch ------------------------------

function makeDocument() {
  const doc = {};
  class Node {
    constructor(nodeType, nodeName) {
      this.nodeType = nodeType;
      this.nodeName = nodeName;
      this.nodeValue = null;
      this.className = '';
      this.childNodes = [];
      this.parentNode = null;
      this.ownerDocument = doc;
    }

    get firstChild() { return this.childNodes[0] || null; }

    get nextSibling() {
      if (!this.parentNode) return null;
      const siblings = this.parentNode.childNodes;
      return siblings[siblings.indexOf(this) + 1] || null;
    }

    // A fragment's children move into the parent and leave it empty, as in
    // a browser; any other node moves from wherever it was.
    appendChild(child) {
      const moving = child.nodeType === 11 ? child.childNodes.splice(0) : [child];
      for (const c of moving) {
        const from = c.parentNode ? c.parentNode.childNodes.indexOf(c) : -1;
        if (from !== -1) c.parentNode.childNodes.splice(from, 1);
        c.parentNode = this;
        this.childNodes.push(c);
      }
      return child;
    }

    get textContent() {
      return this.nodeType === 3 ? this.nodeValue : this.childNodes.map((c) => c.textContent).join('');
    }

    set textContent(value) {
      for (const c of this.childNodes) c.parentNode = null;
      this.childNodes = [];
      if (value) this.appendChild(doc.createTextNode(value));
    }
  }
  doc.createDocumentFragment = () => new Node(11, '#document-fragment');
  doc.createElement = (tag) => new Node(1, tag.toUpperCase());
  doc.createTextNode = (text) => {
    const node = new Node(3, '#text');
    node.nodeValue = String(text);
    return node;
  };
  return doc;
}

function element(doc, tag, className, children = []) {
  const el = doc.createElement(tag);
  el.className = className;
  for (const c of children) el.appendChild(typeof c === 'string' ? doc.createTextNode(c) : c);
  return el;
}

const newPre = () => element(makeDocument(), 'pre', 'Agda agda-editor__mirror');

/** A block's children as markup, to compare a painted structure whole. */
function markup(node) {
  if (node.nodeType === 3) return node.nodeValue;
  const inner = node.childNodes.map(markup).join('');
  const tag = node.nodeName.toLowerCase();
  return `<${tag}${node.className ? ` class="${node.className}"` : ''}>${inner}</${tag}>`;
}
const inside = (pre) => pre.childNodes.map(markup).join('');

/** Every text node in order, with the class of the span and of the mark that
 * hold it ('' for none). */
function pieces(pre) {
  const out = [];
  const walk = (node, cls, mark) => {
    if (node.nodeType === 3) { out.push({ text: node.nodeValue, cls, mark }); return; }
    const inSpan = node.nodeName === 'SPAN' ? node.className : cls;
    const inMark = node.nodeName === 'MARK' ? node.className : mark;
    node.childNodes.forEach((c) => walk(c, inSpan, inMark));
  };
  pre.childNodes.forEach((c) => walk(c, '', ''));
  return out;
}

// ---- offsetOf agrees with edits.js -------------------------------------------

const TEXTS = [
  '', 'a', 'abc', '𝑨', '𝑨𝑩', 'a𝑨b', '𝑨 ⊙ 𝔻 ≈ ℊ x', '\n𝓞\n\n𝓥 x\n',
  '𝑆 : Signature 𝓞 𝓥\n  𝑨 ⊙ 𝑩 ≈ 𝑪 ⟶ 𝕌', 'emoji 👩‍🔬 joins several code points',
  'graft : Term {𝑆 = 𝑆} Y → (Y → Term {𝑆 = 𝑆} X) → Term {𝑆 = 𝑆} X\ngraft t σ = ?',
];
for (const text of TEXTS) {
  // From before the first position to well past the end: Agda's exclusive
  // end of a range that closes the file is one past its last code point.
  for (let pos = -1; pos <= [...text].length + 3; pos++) {
    const mine = offsetOf(text, pos);
    const theirs = editsOffsetOf(text, pos);
    check(mine === theirs,
      `offsetOf(${JSON.stringify(text)}, ${pos}) is ${mine} here, ${theirs} in edits.js`);
  }
}
// And both are right, not merely alike: 𝑨 and 𝔻 are two units each.
same([1, 2, 5, 6, 12].map((p) => offsetOf('𝑨 ⊙ 𝔻 ≈ ℊ x', p)), [0, 2, 5, 7, 13],
  'offsetOf on a line with two astral names');

// ---- fromAgda ----------------------------------------------------------------

// By hand.  'ab𝑨cd ef' is code points a1 b2 𝑨3 c4 d5 ␠6 e7 f8 and units
// a0 b1 𝑨2-3 c4 d5 ␠6 e7 f8.  An atom the site does not color is dropped
// from a range's classes (`unsolvedmeta` is one Agda sends; this page marks
// problems with its own marks), a range with nothing left is dropped, and so
// is an empty one.
same(fromAgda('ab𝑨cd ef', [
  { from: 4, to: 6, atoms: ['keyword'] },
  { from: 1, to: 3, atoms: ['function', 'operator'] },
  { from: 3, to: 4, atoms: ['inductiveconstructor'] },
  { from: 5, to: 5, atoms: ['keyword'] },
  { from: 7, to: 9, atoms: ['bound', 'unsolvedmeta'] },
  { from: 6, to: 7, atoms: ['unsolvedmeta'] },
  { from: 6, to: 7, atoms: [] },
]), [
  [0, 2, 'Function Operator'],
  [2, 4, 'InductiveConstructor'],
  [4, 6, 'Keyword'],
  [7, 9, 'Bound'],
], 'fromAgda maps, drops and sorts');

// The table is the build's (`ASPECT_CLASSES` in build_assets.py says so,
// and this file's comment says the same), so that the first frame, colored
// by the build, and every frame after it, colored here, agree.  Read from
// the builder's source rather than copied, so that a class added to one
// table and not the other fails here.
{
  const python = readFileSync(new URL('../../python/playground/build_assets.py', import.meta.url), 'utf8');
  const block = python.match(/ASPECT_CLASSES[^{]*\{([^}]*)\}/);
  const table = block ? [...block[1].matchAll(/"([a-z]+)":\s*"([A-Za-z]+)"/g)].map((m) => [m[1], m[2]]) : [];
  check(table.length >= 20, `read only ${table.length} entries of ASPECT_CLASSES from build_assets.py`);
  for (const [atom, cls] of table) {
    same(fromAgda('x', [{ from: 1, to: 2, atoms: [atom] }]), [[0, 1, cls]],
      `the atom ${atom}, which the build colors ${cls}`);
  }
}

// Captured (2026-10-04) from the page's checker, Agda 2.8.0 compiled to
// WebAssembly: this text's load, its highlighting as `readLoad` reads it.
// Agda sends highlighting more than once in a load (a lexical pass, then the
// full one), so ranges repeat; and the second 𝔻 comes after the first, which
// is two units, so a range taken without conversion would color half of it.
const PAINT = `module Paint where

open import Agda.Builtin.Bool

_⊙_ : Bool → Bool → Bool
true ⊙ 𝔻 = 𝔻
false ⊙ _ = false
`;
const LOADED = [{ from: 1, to: 7, atoms: ['keyword'] }, { from: 14, to: 19, atoms: ['keyword'] }, { from: 21, to: 25, atoms: ['keyword'] }, { from: 26, to: 32, atoms: ['keyword'] }, { from: 56, to: 57, atoms: ['symbol'] }, { from: 63, to: 64, atoms: ['symbol'] }, { from: 70, to: 71, atoms: ['symbol'] }, { from: 86, to: 87, atoms: ['symbol'] }, { from: 98, to: 99, atoms: ['symbol'] }, { from: 100, to: 101, atoms: ['symbol'] }, { from: 1, to: 7, atoms: ['keyword'] }, { from: 8, to: 13, atoms: ['module'] }, { from: 14, to: 19, atoms: ['keyword'] }, { from: 33, to: 50, atoms: ['module'] }, { from: 52, to: 55, atoms: ['function', 'operator'] }, { from: 58, to: 62, atoms: ['datatype'] }, { from: 65, to: 69, atoms: ['datatype'] }, { from: 72, to: 76, atoms: ['datatype'] }, { from: 77, to: 81, atoms: ['inductiveconstructor'] }, { from: 82, to: 83, atoms: ['function', 'operator'] }, { from: 84, to: 85, atoms: ['bound'] }, { from: 88, to: 89, atoms: ['bound'] }, { from: 90, to: 95, atoms: ['inductiveconstructor'] }, { from: 96, to: 97, atoms: ['function', 'operator'] }, { from: 102, to: 107, atoms: ['inductiveconstructor'] }, { from: 21, to: 25, atoms: ['keyword'] }, { from: 26, to: 32, atoms: ['keyword'] }, { from: 33, to: 50, atoms: ['module'] }, { from: 52, to: 55, atoms: ['function', 'operator'] }, { from: 58, to: 62, atoms: ['datatype'] }, { from: 65, to: 69, atoms: ['datatype'] }, { from: 72, to: 76, atoms: ['datatype'] }, { from: 52, to: 55, atoms: ['function', 'operator'] }, { from: 77, to: 81, atoms: ['inductiveconstructor'] }, { from: 82, to: 83, atoms: ['function', 'operator'] }, { from: 84, to: 85, atoms: ['bound'] }, { from: 86, to: 87, atoms: ['symbol'] }, { from: 88, to: 89, atoms: ['bound'] }, { from: 90, to: 95, atoms: ['inductiveconstructor'] }, { from: 96, to: 97, atoms: ['function', 'operator'] }, { from: 98, to: 99, atoms: ['symbol'] }, { from: 100, to: 101, atoms: ['symbol'] }, { from: 102, to: 107, atoms: ['inductiveconstructor'] }, { from: 1, to: 7, atoms: ['keyword'] }, { from: 8, to: 13, atoms: ['module'] }, { from: 14, to: 19, atoms: ['keyword'] }, { from: 56, to: 57, atoms: ['symbol'] }, { from: 63, to: 64, atoms: ['symbol'] }, { from: 70, to: 71, atoms: ['symbol'] }];

// What each token of PAINT is, read off the source by hand.
const TOKENS = [
  ['module', 'Keyword'], ['Paint', 'Module'], ['where', 'Keyword'],
  ['open', 'Keyword'], ['import', 'Keyword'], ['Agda.Builtin.Bool', 'Module'],
  ['_⊙_', 'Function Operator'], [':', 'Symbol'], ['Bool', 'Datatype'], ['→', 'Symbol'],
  ['Bool', 'Datatype'], ['→', 'Symbol'], ['Bool', 'Datatype'],
  ['true', 'InductiveConstructor'], ['⊙', 'Function Operator'], ['𝔻', 'Bound'],
  ['=', 'Symbol'], ['𝔻', 'Bound'],
  ['false', 'InductiveConstructor'], ['⊙', 'Function Operator'], ['_', 'Symbol'],
  ['=', 'Symbol'], ['false', 'InductiveConstructor'],
];
const loaded = fromAgda(PAINT, LOADED);
check(loaded.every((r, i) => i === 0 || loaded[i - 1][0] <= r[0]), 'fromAgda: the ranges are not in order');
check(loaded.every((r) => r[0] < r[1] && r[1] <= PAINT.length && !/[\udc00-\udfff]/.test(PAINT[r[0]] + (PAINT[r[1]] || ''))),
  'fromAgda: a range is empty, past the end, or cuts a surrogate pair');
{
  const pre = newPre();
  paint(pre, PAINT, loaded, []);
  same(pieces(pre).filter((p) => p.cls).map((p) => [p.text, p.cls]), TOKENS,
    'the captured load, painted: each token and its class');
  // The block as the editor's first frame reads it back has each range once.
  const unique = loaded.filter((r, i) => i === 0 || JSON.stringify(r) !== JSON.stringify(loaded[i - 1]));
  same(rangesOf(pre), unique, 'rangesOf on the painted captured load');
}

// ---- shift -------------------------------------------------------------------

// One edit, as a keystroke makes one.  Each case: the text before and after,
// the ranges, and what should become of each (kept where it was, moved by the
// change in length, or dropped because the edit touched it).  The texts are
// chosen so that the changed span is unambiguous: an edit next to a copy of
// the text it inserts has more than one reading, and `shift` takes the one
// furthest right, which is a fact about the longest common prefix and not
// worth pinning here.
const SHIFTS = [
  {
    why: 'an insertion between two ranges',
    before: 'abcdefgh', after: 'abcdXYefgh',
    ranges: [[0, 2, 'A'], [2, 4, 'B'], [4, 6, 'C'], [3, 5, 'D'], [6, 8, 'E']],
    // B ends where the text went in and C starts there: neither was touched,
    // so B stays as it was and the new text is in no range (it is not B's,
    // whatever it turns out to be when Agda next colors it).
    want: [[0, 2, 'A'], [2, 4, 'B'], [6, 8, 'C'], [8, 10, 'E']],
  },
  {
    why: 'a deletion',
    before: 'abcdefgh', after: 'abgh',
    ranges: [[0, 2, 'A'], [1, 3, 'B'], [2, 6, 'C'], [3, 4, 'D'], [5, 7, 'E'], [6, 8, 'F']],
    want: [[0, 2, 'A'], [2, 4, 'F']],
  },
  {
    why: 'a replacement by something shorter',
    before: 'abcdefgh', after: 'abXYZgh',
    ranges: [[0, 2, 'A'], [1, 3, 'B'], [2, 6, 'C'], [6, 8, 'D']],
    want: [[0, 2, 'A'], [5, 7, 'D']],
  },
  {
    why: 'an astral name inserted, two units',
    before: 'f 𝑨 = x', after: 'f 𝑨 = 𝑩 x',
    ranges: [[0, 1, 'f'], [2, 4, 'A'], [5, 6, '='], [7, 8, 'x']],
    want: [[0, 1, 'f'], [2, 4, 'A'], [5, 6, '='], [10, 11, 'x']],
  },
  {
    // 𝑨 and 𝑩 share their first unit, so the edit is found inside the pair;
    // the name's range is touched all the same.
    why: 'an astral name replaced by another',
    before: '𝑨 x', after: '𝑩 x',
    ranges: [[0, 2, 'A'], [3, 4, 'x']],
    want: [[3, 4, 'x']],
  },
  {
    why: 'no change',
    before: '𝑨 x', after: '𝑨 x',
    ranges: [[0, 2, 'A'], [3, 4, 'x']],
    want: [[0, 2, 'A'], [3, 4, 'x']],
  },
];
for (const { why, before, after, ranges, want } of SHIFTS) {
  const marks = ranges.map(([from, to, kind]) => ({ from, to, kind }));
  const got = shift(before, after, ranges, marks);
  same(got.ranges, want, `shift, ranges (${why})`);
  same(got.marks, want.map(([from, to, kind]) => ({ from, to, kind })), `shift, marks (${why})`);
  // What is kept still covers the same characters it did (each case's
  // labels are distinct, so a label names its range before the edit).
  for (const [from, to, label] of got.ranges) {
    const was = ranges.find((r) => r[2] === label);
    same(after.slice(from, to), before.slice(was[0], was[1]), `shift (${why}): the text under ${label}`);
  }
}

// ---- paint -------------------------------------------------------------------

const ERROR = 'agda-mark agda-mark--error';
const GOAL = 'agda-mark agda-mark--goal';

// The whole structure, for the cases where its shape is the point.
const SHAPES = [
  {
    why: 'spans over exactly their ranges, an astral one included, and plain text between',
    text: 'ab𝑨 cd', ranges: [[0, 2, 'Function'], [2, 4, 'Bound'], [5, 7, 'Keyword']], marks: [],
    want: '<span class="Function">ab</span><span class="Bound">𝑨</span> <span class="Keyword">cd</span>\n',
  },
  {
    why: 'a mark that crosses a range splits it in two',
    text: 'abcdef', ranges: [[0, 4, 'Keyword']], marks: [{ from: 2, to: 6, kind: 'error' }],
    want: `<span class="Keyword">ab</span><mark class="${ERROR}"><span class="Keyword">cd</span>ef</mark>\n`,
  },
  {
    why: 'adjacent ranges of one class stay two spans',
    text: '::x', ranges: [[0, 1, 'Symbol'], [1, 2, 'Symbol']], marks: [],
    want: '<span class="Symbol">:</span><span class="Symbol">:</span>x\n',
  },
  {
    why: 'marks out of order are sorted; one overlapping a kept mark goes, as does an empty one, and one past the end stops at it',
    text: 'abcdefgh',
    ranges: [],
    marks: [{ from: 6, to: 99, kind: 'goal' }, { from: 3, to: 6, kind: 'goal' }, { from: 1, to: 4, kind: 'error' }, { from: 6, to: 6, kind: 'goal' }],
    want: `a<mark class="${ERROR}">bcd</mark>ef<mark class="${GOAL}">gh</mark>\n`,
  },
  {
    // An empty <mark> is not nothing: it can carry an outline or padding.
    why: 'a mark wholly past the end of the text is not painted, not even empty',
    text: 'abc', ranges: [[0, 3, 'Bound']], marks: [{ from: 5, to: 9, kind: 'error' }],
    want: '<span class="Bound">abc</span>\n',
  },
  {
    why: 'two marks that meet are both kept',
    text: 'abcd', ranges: [[0, 4, 'Bound']], marks: [{ from: 0, to: 2, kind: 'goal' }, { from: 2, to: 4, kind: 'error' }],
    want: `<mark class="${GOAL}"><span class="Bound">ab</span></mark><mark class="${ERROR}"><span class="Bound">cd</span></mark>\n`,
  },
  {
    why: 'the empty text is one newline',
    text: '', ranges: [], marks: [], want: '\n',
  },
];
for (const { why, text, ranges, marks, want } of SHAPES) {
  const pre = newPre();
  paint(pre, text, ranges, marks);
  same(inside(pre), want, `paint (${why})`);
}

// And everywhere: every text here, painted with a range for each word (the
// classes cycling) and marks across them, is the text and one newline; each
// character is in the span of the range that covers it and the mark that
// covers it, and the newline is in neither.  A range the reader sees is the
// range painted.
const CLASSES = ['Keyword', 'Function Operator', 'Bound', 'InductiveConstructor'];
function wordRanges(text) {
  return [...text.matchAll(/\S+/g)].map((m, i) => [m.index, m.index + m[0].length, CLASSES[i % CLASSES.length]]);
}
const snap = (text, x) => (/[\udc00-\udfff]/.test(text[x] || '') ? x + 1 : x);
for (const text of [...TEXTS, PAINT]) {
  const ranges = wordRanges(text);
  const third = Math.floor(text.length / 3);
  const marks = text.length < 6 ? [] : [
    { from: snap(text, 1), to: snap(text, third), kind: 'error' },
    { from: snap(text, 2 * third), to: text.length + 3, kind: 'goal' },
  ];
  const pre = newPre();
  paint(pre, text, ranges, marks);
  const got = pieces(pre);
  same(got.map((p) => p.text).join(''), `${text}\n`, `paint ${JSON.stringify(text)}: the text`);
  const last = got[got.length - 1];
  check(last && last.text.endsWith('\n') && last.cls === '' && last.mark === '',
    `paint ${JSON.stringify(text)}: the trailing newline is inside a span or a mark`);
  const classAt = (x) => (ranges.find((r) => r[0] <= x && x < r[1]) || [0, 0, ''])[2];
  const markAt = (x) => {
    const m = marks.find((k) => k.from <= x && x < k.to);
    return m ? `agda-mark agda-mark--${m.kind}` : '';
  };
  let at = 0;
  for (const p of got) {
    for (let i = 0; i < p.text.length && at + i < text.length; i++) {
      check(p.cls === classAt(at + i) && p.mark === markAt(at + i),
        `paint ${JSON.stringify(text)}: unit ${at + i} is in span ${JSON.stringify(p.cls)} and mark `
        + `${JSON.stringify(p.mark)}, expected ${JSON.stringify(classAt(at + i))} and ${JSON.stringify(markAt(at + i))}`);
    }
    at += p.text.length;
  }
  // Without marks, the block reads back as the ranges it was painted with.
  const plain = newPre();
  paint(plain, text, ranges, []);
  same(rangesOf(plain), ranges, `rangesOf after paint ${JSON.stringify(text)}`);
}

// Painting again replaces what was there: the editor repaints the same
// mirror on every keystroke.
{
  const pre = newPre();
  paint(pre, '𝑨 = 𝑩', [[0, 2, 'Function']], [{ from: 5, to: 7, kind: 'goal' }]);
  paint(pre, 'x', [[0, 1, 'Bound']], []);
  same(inside(pre), '<span class="Bound">x</span>\n', 'a second paint replaces the first');
}

// ---- rangesOf on the build's block ------------------------------------------

// The first frame's colors come from the block the build wrote: a `<code>`
// inside the `<pre>`, a span per highlighted range (`highlighted` in
// mkdocs_hook.py), and, once agda-copy.js has run, a copy button after the
// code.  Only the token spans are ranges: not the code element, not the
// button, and not a classed span with no text in it.
{
  const doc = makeDocument();
  const code = element(doc, 'code', '', [
    element(doc, 'span', 'Keyword', ['module']), ' ',
    element(doc, 'span', 'Module', ['𝑨']), ' ',
    element(doc, 'span', 'Keyword', ['where']), '\n',
    element(doc, 'span', 'Function Operator', ['_⊙_']), ' ', element(doc, 'span', 'Symbol', [':']), ' 𝔻\n',
  ]);
  const button = element(doc, 'button', 'ualib-agda-copy md-icon', [
    element(doc, 'svg', '', [element(doc, 'rect', ''), element(doc, 'path', '')]),
  ]);
  const pre = element(doc, 'pre', 'Agda agda-exercise__code', [code, button, element(doc, 'span', 'twemoji', [])]);
  // module0-6 ␠ 𝑨7-9 ␠ where10-15 ⏎ _⊙_16-19 ␠ :20-21
  same(rangesOf(pre), [[0, 6, 'Keyword'], [7, 9, 'Module'], [10, 15, 'Keyword'], [16, 19, 'Function Operator'], [20, 21, 'Symbol']],
    "rangesOf on the build's block");
}

// With a mark across a range, the block holds the range as two spans and
// reads back as two: the same characters with the same classes, which is all
// the editor asks of it.
{
  const pre = newPre();
  paint(pre, 'abcdef', [[0, 4, 'Keyword']], [{ from: 2, to: 6, kind: 'error' }]);
  same(rangesOf(pre), [[0, 2, 'Keyword'], [2, 4, 'Keyword']], 'rangesOf across a mark');
}

console.log(`playground paint: ${asserted} assertions over ${TEXTS.length + 1} texts, `
  + `${SHIFTS.length} edits and ${SHAPES.length} painted shapes`);
if (failures.length) {
  for (const line of failures.slice(0, 40)) console.error(`  ${line}`);
  if (failures.length > 40) console.error(`  ... and ${failures.length - 40} more`);
  console.error(`playground paint: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground paint: offsets agree with edits.js, ranges follow edits, and the mirror is the text');
