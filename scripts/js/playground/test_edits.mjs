// File: scripts/js/playground/test_edits.mjs
//
// The edits a goal command makes to the reader's text
// (`docs/assets/js/playground/edits.js`), held to what Agda's Emacs mode
// makes of the same answer.
//
// Two things go wrong here without any error to say so.  The first is
// counting.  Agda gives a position in code points from 1; the editor counts
// UTF-16 units; and this library's names are full of characters outside the
// Basic Multilingual Plane (𝑨, 𝔻, 𝑆, 𝓞), each of them two units.  A position
// used without converting it lands one unit to the left for each such
// character before it, and a give is spliced into the middle of a name.  So
// every case below that can puts one before its goal.  The second is the
// text a case split writes.  The page promises agda2-mode's layout, and a
// split that loses an indentation or a separator leaves a file that no longer
// parses, or that parses as something else.
//
// The expected strings are worked out by hand from `agda2-update`,
// `agda2-make-case-action` and `agda2-make-case-action-extendlam` in Agda
// 2.8.0's `agda2-mode.el` (quoted where each is used), and are written out
// rather than computed, so that they cannot share a mistake with the module.
//
// Some cases are Agda's own answers, captured once (2026-10-04) from the
// page's checker (Agda 2.8.0 compiled to WebAssembly, run under node by the
// page's own WASI host) on the texts written out beside them.  They are read
// with `protocol.js`'s `readAction`, as `session.js` reads them, so the
// objects handed to the edits are the ones the page hands them.  Every split
// result below was also loaded again by that checker, and loaded.
//
// One measured fact shapes the give cases.  The page sends every goal command
// with `noRange`, and to that the checker answered every give and refine with
// replacement text (`giveResult.str`), never with "use what you sent,
// parenthesized or not".  The `paren` cases are therefore written by hand, to
// `agda2-update`'s meaning.
//
// Usage:  node scripts/js/playground/test_edits.mjs
//         make playground-test

import {
  offsetOf, positionOf, span, holeContent, applyGive, applySplit,
} from '../../../docs/assets/js/playground/edits.js';
import { readAction } from '../../../docs/assets/js/playground/protocol.js';

const failures = [];
let asserted = 0;
const check = (ok, what) => { asserted += 1; if (!ok) failures.push(what); };
// Two texts that differ are reported at their first differing line, which
// is where a reader of the failure needs to look.
function same(got, want, what) {
  if (typeof got === 'string' && typeof want === 'string' && got !== want && /\n/.test(want)) {
    const g = got.split('\n');
    const w = want.split('\n');
    let i = 0;
    while (i < Math.min(g.length, w.length) && g[i] === w[i]) i++;
    check(false, `${what}: from line ${i + 1}, got ${JSON.stringify(g.slice(i, i + 3).join('\n'))}, `
      + `expected ${JSON.stringify(w.slice(i, i + 3).join('\n'))}`);
    return;
  }
  check(JSON.stringify(got) === JSON.stringify(want),
    `${what}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);
}

// A string's iterator walks code points, so this counts them without the
// module: an independent oracle for every position written below.
const points = (s) => [...s].length;

/** Agda's range for the `nth` occurrence of `needle` in `text`, in code
 * points from 1 with an exclusive end, as Agda writes one. */
function rangeOf(text, needle, nth = 0) {
  let at = -1;
  for (let i = 0; i <= nth; i++) {
    at = text.indexOf(needle, at + 1);
    if (at === -1) throw new Error(`fixture: ${JSON.stringify(needle)} is not in the text`);
  }
  const start = points(text.slice(0, at)) + 1;
  return { start: { pos: start }, end: { pos: start + points(needle) } };
}

/** `text` with the one line `from` replaced by `to`; the line must occur
 * exactly once, or the expectation would be ambiguous. */
function replaceLine(text, from, to) {
  const lines = text.split('\n');
  const hits = lines.filter((l) => l === from).length;
  if (hits !== 1) throw new Error(`fixture: ${JSON.stringify(from)} is ${hits} lines of the text`);
  return lines.map((l) => (l === from ? to : l)).join('\n');
}

/** Agda's answer as the session reads it. */
const action = (response) => readAction([response]);

// ---- counting ----------------------------------------------------------------

// 𝑨 and 𝔻 are two units each; ⊙, ≈ and ℊ are one (they are in the Basic
// Multilingual Plane, which is why ℊ is here: a script letter that is NOT
// astral, so a rule of "script letters are two units" fails too).
//
//   code point   1  2  3  4  5  6  7  8  9  10 11 | end
//   character    𝑨  ␠  ⊙  ␠  𝔻  ␠  ≈  ␠  ℊ  ␠  x  |
//   UTF-16 unit  0  2  3  4  5  7  8  9  10 11 12 | 13
const LINE = '𝑨 ⊙ 𝔻 ≈ ℊ x';
const UNITS = [[1, 0], [2, 2], [3, 3], [4, 4], [5, 5], [6, 7], [7, 8], [8, 9],
  [9, 10], [10, 11], [11, 12], [12, 13]];
for (const [pos, unit] of UNITS) {
  same(offsetOf(LINE, pos), unit, `offsetOf(${JSON.stringify(LINE)}, ${pos})`);
  same(positionOf(LINE, unit), pos, `positionOf(${JSON.stringify(LINE)}, ${unit})`);
}
// A position past the end is the end: Agda's exclusive end of a range that
// closes the file is one past its last code point.
same(offsetOf(LINE, 40), 13, 'offsetOf past the end');
same(offsetOf('', 1), 0, 'offsetOf of the empty text');
same(offsetOf('', 7), 0, 'offsetOf past the end of the empty text');
same(positionOf('', 0), 1, 'positionOf of the empty text');
same(offsetOf('abc', 2), 1, 'offsetOf in ASCII is pos - 1');

// The round trip, at every code point of texts like the library's.  Not a
// substitute for the table above (a pair of functions wrong in matching ways
// round-trips perfectly), but it covers every position of every text here.
const ROUND = [
  LINE, '', 'abc', '𝓞𝓥', '\n𝑨\n\n𝔻 x\n', '𝑆 : Signature 𝓞 𝓥\n  𝑨 ⊙ 𝑩 ≈ 𝑪',
  'emoji 👩‍🔬 is several code points', 'ℊ ∷ ⟨ ⟩ ✦ ⟶',
];
for (const text of ROUND) {
  let unit = 0;
  let pos = 1;
  for (const ch of [...text, '']) {
    check(offsetOf(text, pos) === unit && positionOf(text, unit) === pos,
      `${JSON.stringify(text)}: code point ${pos} is unit ${unit}, but offsetOf says `
      + `${offsetOf(text, pos)} and positionOf says ${positionOf(text, unit)}`);
    unit += ch.length;
    pos += 1;
  }
}

// ---- span and holeContent --------------------------------------------------

// `𝑨 𝔻 = ` is 6 code points and 8 units, so the hole starts at unit 8, not 6.
{
  const text = '𝑨 𝔻 = {! ℊ 𝔻 !}';
  same(span(text, rangeOf(text, '{! ℊ 𝔻 !}')), [8, 18], 'span of a hole after two astral names');
}

// What a goal holds is what Emacs sends with a command from inside it
// (`agda2-goal-cmd` takes the text between `{!` and `!}`); the page puts it
// in the goal's field, trimmed, and `?` holds nothing.
const HOLES = [
  ['graft t σ = ?', '?', '', 'a question mark'],
  ['𝑨 𝔻 = {!!}', '{!!}', '', 'an empty hole'],
  ['𝑨 𝔻 = {!   !}', '{!   !}', '', 'a hole of spaces'],
  ['𝑨 𝔻 = {! ℊ 𝔻 !}', '{! ℊ 𝔻 !}', 'ℊ 𝔻', 'an expression with a space on each side'],
  ['𝑨 𝔻 = {!ℊ 𝔻!}', '{!ℊ 𝔻!}', 'ℊ 𝔻', 'an expression with no spaces'],
  ['f 𝑨 = {! 𝑨 !} -- then a comment', '{! 𝑨 !}', '𝑨', 'a hole with text after it'],
  ['𝑨 = {!\n  σ x\n!}', '{!\n  σ x\n!}', 'σ x', 'newlines around the expression'],
  ['graft (node f t) σ = {! node f\n                       (λ i → graft (t i) σ) !}',
    '{! node f\n                       (λ i → graft (t i) σ) !}',
    'node f\n                       (λ i → graft (t i) σ)',
    'a multi-line hole, its inner layout kept'],
];
for (const [text, hole, want, why] of HOLES) {
  same(holeContent(text, rangeOf(text, hole)), want, `holeContent (${why})`);
}

// ---- give and refine --------------------------------------------------------

// Captured: this text, and Agda's answers to a give or a refine at each goal.
const ASTRAL = `module Astral where

open import Agda.Builtin.Bool

id : Bool → Bool
id b = b

𝑨 : Bool → Bool
𝑨 𝔻 = {! 𝔻 !}

𝑩 : Bool → Bool
𝑩 𝔻 = id {!  !}

𝑪 : Bool → Bool → Bool
𝑪 𝔻 𝕌 = ?
`;
const GIVES = [
  {
    sent: '𝔻',
    response: { giveResult: { str: '𝔻' }, interactionPoint: { id: 0, range: [{ end: { col: 14, line: 9, pos: 109 }, start: { col: 7, line: 9, pos: 102 } }] }, kind: 'GiveAction' },
    line: ['𝑨 𝔻 = {! 𝔻 !}', '𝑨 𝔻 = 𝔻'],
    why: 'a give of a variable',
  },
  {
    sent: ' id 𝔻 ',
    response: { giveResult: { str: '(id 𝔻)' }, interactionPoint: { id: 1, range: [{ end: { col: 16, line: 12, pos: 142 }, start: { col: 10, line: 12, pos: 136 } }] }, kind: 'GiveAction' },
    line: ['𝑩 𝔻 = id {!  !}', '𝑩 𝔻 = id (id 𝔻)'],
    why: 'a give that Agda parenthesized itself',
  },
  {
    sent: 'id  𝕌',
    response: { giveResult: { str: 'id 𝕌' }, interactionPoint: { id: 2, range: [{ end: { col: 10, line: 15, pos: 176 }, start: { col: 9, line: 15, pos: 175 } }] }, kind: 'GiveAction' },
    line: ['𝑪 𝔻 𝕌 = ?', '𝑪 𝔻 𝕌 = id 𝕌'],
    why: 'a give into a question mark, as Agda reprinted it',
  },
  {
    sent: 'id',
    response: { giveResult: { str: 'id ?' }, interactionPoint: { id: 2, range: [{ end: { col: 10, line: 15, pos: 176 }, start: { col: 9, line: 15, pos: 175 } }] }, kind: 'GiveAction' },
    line: ['𝑪 𝔻 𝕌 = ?', '𝑪 𝔻 𝕌 = id ?'],
    why: 'a refine, which answers with text holding a new goal',
  },
];
for (const { sent, response, line, why } of GIVES) {
  const { give } = action(response);
  check(give !== null && 'text' in give, `${why}: readAction found no text answer`);
  if (give === null) continue;
  same(applyGive(ASTRAL, give, sent), replaceLine(ASTRAL, line[0], line[1]), `applyGive (${why})`);
}

// By hand: "what you sent", as `agda2-update` reads `'paren` and
// `'no-paren`: the goal's braces go, and its text stays, inside a pair of
// parentheses for `'paren`.  The page's goal text is the field under the
// goal, which it sends trimmed, so the parentheses close on the expression
// and not on the spaces around it.
{
  const before = '𝑩 𝔻 = id {!  !}';
  const range = rangeOf(before, '{!  !}');
  same(applyGive(`${before}\nnext line\n`, { range, paren: true }, ' id 𝔻 '),
    '𝑩 𝔻 = id (id 𝔻)\nnext line\n', 'applyGive with paren true');
  same(applyGive(`${before}\nnext line\n`, { range, paren: false }, '  𝔻\n'),
    '𝑩 𝔻 = id 𝔻\nnext line\n', 'applyGive with paren false');
  same(applyGive(before, { range, text: 'ℊ 𝔻' }, 'what was sent'),
    '𝑩 𝔻 = id ℊ 𝔻', "applyGive puts Agda's text, not what was sent");
}

// ---- case split: a function clause ------------------------------------------

// agda2-make-case-action, Agda 2.8.0:
//
//   (p1 (goto-char (+ (current-indentation) (line-beginning-position))))
//   (indent (current-column))
//   (delete-region p1 (line-end-position))
//   (while (setq cl (pop newcls))
//     (insert cl)
//     (if newcls (insert "\n" (make-string indent ?  ))))
//
// So the goal's line, from its indentation to its end, becomes the clauses,
// each after the first on a line of its own at that indentation.  Anything
// after the goal on that line goes with it.

// Captured: the page's first exercise, split on `t`.  The goal's position,
// 523, is a code point position with eight astral characters before it, so
// taken as a unit offset it would miss the goal by eight.
const GRAFT = `module Graft where

open import Agda.Primitive        using () renaming ( Set to Type )
open import Level                 using ( Level )
open import Overture.Signatures   using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )
open import Overture.Terms.Basic  using ( Term ; ℊ ; node )

private variable
  χ ξ : Level
  X : Type χ
  Y : Type ξ
  𝑆 : Signature 𝓞 𝓥

-- Graft σ onto the leaves of t: replace each generator ℊ y by the term σ y.
graft : Term {𝑆 = 𝑆} Y → (Y → Term {𝑆 = 𝑆} X) → Term {𝑆 = 𝑆} X
graft t σ = ?
`;
const GRAFT_SPLIT = { clauses: ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'], interactionPoint: { id: 0, range: [{ end: { col: 14, line: 16, pos: 524 }, start: { col: 13, line: 16, pos: 523 } }] }, kind: 'MakeCase', variant: 'Function' };
{
  const { split } = action(GRAFT_SPLIT);
  same(split && split.clauses, ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'],
    "Graft: Agda's clauses for a split on t");
  same(GRAFT.slice(...span(GRAFT, split.range)), '?', 'Graft: the split range is the goal');
  check(GRAFT.slice(522, 523) !== '?', 'Graft: the fixture no longer exercises the conversion');
  same(applySplit(GRAFT, split),
    replaceLine(GRAFT, 'graft t σ = ?', 'graft (ℊ x) σ = ?\ngraft (node f t) σ = ?'),
    'applySplit on Graft, split on t');
}

// Captured: an indented clause in a module, with astral names on its line.
const BRACE = `module Brace where

open import Agda.Builtin.Bool

𝑓 : Bool → {Bool} → Bool
𝑓 = λ { x {𝔻} → {! x !} }

record R : Set where
  field
    op : Bool → Bool

r : R
r = record { op = λ where
               𝕌 → {! 𝕌 !} }

module M where
  go : Bool → Bool
  go 𝑨 = {! 𝑨 !}
`;
same(applySplit(BRACE, action({ clauses: ['go false = ?', 'go true = ?'], interactionPoint: { id: 2, range: [{ end: { col: 17, line: 18, pos: 267 }, start: { col: 10, line: 18, pos: 260 } }] }, kind: 'MakeCase', variant: 'Function' }).split),
  replaceLine(BRACE, '  go 𝑨 = {! 𝑨 !}', '  go false = ?\n  go true = ?'),
  'applySplit on an indented clause (captured)');

// By hand.  Each: the text, the goal, the clauses, and the text expected.
const FUNCTION_SPLITS = [
  {
    why: 'a where clause at indentation 2, the text after it kept',
    text: '𝑓 : ℕ → ℕ\n𝑓 n = go n\n  where\n  go : ℕ → ℕ\n  go 𝑚 = {! 𝑚 !}\n\nafter : ℕ\n',
    goal: '{! 𝑚 !}',
    clauses: ['go zero = ?', 'go (suc 𝑚) = ?'],
    want: '𝑓 : ℕ → ℕ\n𝑓 n = go n\n  where\n  go : ℕ → ℕ\n  go zero = ?\n  go (suc 𝑚) = ?\n\nafter : ℕ\n',
  },
  {
    why: 'a clause at column 1 on the last line, with no newline after it',
    text: '-- 𝑨 𝔻\ngraft : T\ngraft t σ = ?',
    goal: '?',
    clauses: ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'],
    want: '-- 𝑨 𝔻\ngraft : T\ngraft (ℊ x) σ = ?\ngraft (node f t) σ = ?',
  },
  {
    why: 'a clause at column 1 that is the first line of the text',
    text: 'f 𝑥 = {! 𝑥 !}\nnext',
    goal: '{! 𝑥 !}',
    clauses: ['f zero = ?', 'f (suc 𝑥) = ?'],
    want: 'f zero = ?\nf (suc 𝑥) = ?\nnext',
  },
  {
    why: 'three clauses at indentation 4, and a comment after the goal goes, as in Emacs',
    text: 'module M where\n  module N where\n    f : Three → Three\n    f 𝔻 = {! 𝔻 !} -- split here\n    g = f\n',
    goal: '{! 𝔻 !}',
    clauses: ['f a = ?', 'f b = ?', 'f c = ?'],
    want: 'module M where\n  module N where\n    f : Three → Three\n    f a = ?\n    f b = ?\n    f c = ?\n    g = f\n',
  },
  {
    why: 'one clause, an absurd one, so no separator at all',
    text: '  f : ⊥ → ⊥\n  f 𝑥 = {! 𝑥 !}\n',
    goal: '{! 𝑥 !}',
    clauses: ['f ()'],
    want: '  f : ⊥ → ⊥\n  f ()\n',
  },
];
for (const { why, text, goal, clauses, want } of FUNCTION_SPLITS) {
  same(applySplit(text, { range: rangeOf(text, goal), clauses, variant: 'Function' }), want,
    `applySplit, Function (${why})`);
}

// ---- case split: an extended lambda -----------------------------------------

// agda2-make-case-action-extendlam, Agda 2.8.0, from just inside the goal:
//
//   (pmax (re-search-forward "!}"))
//   (p1 (goto-char (+ (current-indentation) (line-beginning-position))))
//   ...
//   (re-search-backward "{!")
//   (while (and (not (equal (preceding-char) ?\;)) (>= bracketCount 0) (> (point) p1))
//     (backward-char)
//     (if (equal (preceding-char) ?}) (cl-incf bracketCount))
//     (if (equal (preceding-char) ?{) (cl-decf bracketCount)))
//   (let* ((is-lambda-where (= (point) p1)) ...)
//     (delete-region (point) pmax)
//     (if (not is-lambda-where) (insert " "))
//     ... clauses, separated by "\n" and the indentation if is-lambda-where,
//         and by " ; " if not.
//
// So: back from the goal to the `;` or the unmatched `{` that opens its
// clause, then the clauses, after one space and separated by ` ; `; or, when
// the walk reaches the line's indentation (a lambda laid out one clause per
// line), from the indentation, separated by newlines at that indentation.
// The text after the goal stays.

// Captured, one text, each goal split on x.
const EXTLAM = `module ExtLam where

open import Agda.Builtin.Bool

f : Bool → Bool
f = λ { x → {! x !} }

g : Bool → Bool → Bool
g = λ where
  x y → {! x !}

h : Bool → Bool
h = λ { true → false ; x → {! x !} }

k : Bool → Bool
k = λ { true → false
      ; x → {! x !}
      }
`;
const LAMBDAS = [
  [EXTLAM, { clauses: ['false → ?', 'true → ?'], interactionPoint: { id: 0, range: [{ end: { col: 20, line: 6, pos: 88 }, start: { col: 13, line: 6, pos: 81 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    'f = λ { x → {! x !} }', 'f = λ { false → ? ; true → ? }', 'one line, the clause opened by `{`'],
  [EXTLAM, { clauses: ['false y → ?', 'true y → ?'], interactionPoint: { id: 1, range: [{ end: { col: 16, line: 10, pos: 142 }, start: { col: 9, line: 10, pos: 135 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    '  x y → {! x !}', '  false y → ?\n  true y → ?', '`λ where`, one clause per line'],
  [EXTLAM, { clauses: ['false → ?'], interactionPoint: { id: 2, range: [{ end: { col: 35, line: 13, pos: 194 }, start: { col: 28, line: 13, pos: 187 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    'h = λ { true → false ; x → {! x !} }', 'h = λ { true → false ; false → ? }', 'one line, the clause opened by `;`'],
  [EXTLAM, { clauses: ['false → ?'], interactionPoint: { id: 3, range: [{ end: { col: 20, line: 17, pos: 254 }, start: { col: 13, line: 17, pos: 247 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    '      ; x → {! x !}', '      ; false → ?', 'braces laid out, the clause opened by a leading `;`'],
  [BRACE, { clauses: ['false {𝔻} → ?', 'true {𝔻} → ?'], interactionPoint: { id: 0, range: [{ end: { col: 24, line: 6, pos: 100 }, start: { col: 17, line: 6, pos: 93 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    '𝑓 = λ { x {𝔻} → {! x !} }', '𝑓 = λ { false {𝔻} → ? ; true {𝔻} → ? }', 'an implicit pattern in braces inside the clause'],
  [BRACE, { clauses: ['false → ?', 'true → ?'], interactionPoint: { id: 1, range: [{ end: { col: 27, line: 14, pos: 213 }, start: { col: 20, line: 14, pos: 206 } }] }, kind: 'MakeCase', variant: 'ExtendedLambda' },
    '               𝕌 → {! 𝕌 !} }', '               false → ?\n               true → ? }', '`λ where` inside a record, a brace after the goal kept'],
];
for (const [text, response, from, to, why] of LAMBDAS) {
  same(applySplit(text, action(response).split), replaceLine(text, from, to),
    `applySplit, ExtendedLambda (${why}, captured)`);
}

// By hand, as above.
const LAMBDA_SPLITS = [
  {
    why: 'one line, `f = λ { x → {! x !} }`',
    text: 'f : ℕ → ℕ\nf = λ { x → {! x !} }\n',
    goal: '{! x !}',
    clauses: ['zero → ?', '(suc x) → ?'],
    want: 'f : ℕ → ℕ\nf = λ { zero → ? ; (suc x) → ? }\n',
  },
  {
    why: 'one line, a question mark for the goal, astral names before it',
    text: '𝑓 = λ { 𝑥 → ? }',
    goal: '?',
    clauses: ['zero → ?', '(suc 𝑥) → ?', '(𝑨 𝔻) → ?'],
    want: '𝑓 = λ { zero → ? ; (suc 𝑥) → ? ; (𝑨 𝔻) → ? }',
  },
  {
    why: 'one clause per line at indentation 4, the lines around it kept',
    text: 'top = 0\n  where\n  𝑓 = λ where\n    𝑥 → {! 𝑥 !}\n  bottom = 1\n',
    goal: '{! 𝑥 !}',
    clauses: ['zero → ?', '(suc 𝑥) → ?'],
    want: 'top = 0\n  where\n  𝑓 = λ where\n    zero → ?\n    (suc 𝑥) → ?\n  bottom = 1\n',
  },
  {
    why: 'record braces before the clause: the walk counts them and stops at the `{` of the lambda',
    text: 'f = λ { record { fst = 𝑨 } → {! 𝑨 !} }',
    goal: '{! 𝑨 !}',
    clauses: ['record { fst = zero } → ?', 'record { fst = suc 𝑨 } → ?'],
    want: 'f = λ { record { fst = zero } → ? ; record { fst = suc 𝑨 } → ? }',
  },
];
for (const { why, text, goal, clauses, want } of LAMBDA_SPLITS) {
  same(applySplit(text, { range: rangeOf(text, goal), clauses, variant: 'ExtendedLambda' }), want,
    `applySplit, ExtendedLambda (${why})`);
}

console.log(`playground edits: ${asserted} assertions, ${GIVES.length + 2 + LAMBDAS.length} of the cases Agda's own answers`);
if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground edits: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground edits: positions convert at every code point, and every give and split '
  + 'writes what agda2-mode writes');
