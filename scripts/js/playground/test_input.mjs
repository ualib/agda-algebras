// File: scripts/js/playground/test_input.mjs
//
// The playground's input method (`docs/assets/js/playground-input.js`),
// without a browser.
//
// The script is a table and one rule, and both break quietly.  A binding that
// types the wrong character gives the reader a name Agda does not know, or,
// worse, a different name that it does: 𝑆 and 𝑺 are both letters this
// library could use.  And a rule that ate its terminator would change what a
// text means.  Agda's identifiers may contain symbol characters, so `≡b`
// lexes as one name and not as `_≡_` applied to `b`; an input method that
// consumed the space would turn `a \== b` into something else, with no error
// anywhere.  So the rule is: a space, a newline or a tab commits a pending
// `\name`, and is kept.
//
// The table is held to Agda 2.8.0's `agda-input.el` (the Emacs input method
// whose bindings the page promises), entry by entry, in the comments of
// LIBRARY and PALETTE_KEYS below.  This test does not read that file, since
// CI has no Nix store.  The glyphs were read from it, and every key in the
// two tables was also looked up in Emacs 29.3, in batch, with the Agda input
// method active (`quail-lookup-key` on `\key`, first candidate), on
// 2026-10-04.
//
// The script is a classic one that assigns `window.AgdaInput`, so it runs
// here as a browser runs it, against a `window` stand-in, and is driven
// through a box standing in for a `<textarea>`: `setRangeText` and the two
// selection offsets are the whole surface it touches.
//
// Ported from the personal site's `scripts/js/test_playground_input.mjs`
// (williamdemeo/williamdemeo.github.io), whose cases come first below.
//
// Usage:  node scripts/js/playground/test_input.mjs
//         make playground-test

import { readFileSync } from 'node:fs';

const SCRIPT = new URL('../../../docs/assets/js/playground-input.js', import.meta.url);

globalThis.window = {};
new Function(readFileSync(SCRIPT, 'utf8'))();
const input = globalThis.window.AgdaInput;

const failures = [];
let asserted = 0;
const check = (ok, what) => { asserted += 1; if (!ok) failures.push(what); };

/** The part of a <textarea> the input method actually uses. */
function box(value, caret) {
  return {
    value,
    selectionStart: caret === undefined ? value.length : caret,
    selectionEnd: caret === undefined ? value.length : caret,
    focused: false,
    focus() { this.focused = true; },
    setRangeText(text, start, end) {
      this.value = this.value.slice(0, start) + text + this.value.slice(end);
      this.selectionStart = this.selectionEnd = start + text.length;
    },
  };
}

// ---- the bindings this library adds, against agda-input.el ------------------

// Each: the key, the glyph, and the entry in Agda 2.8.0's agda-input.el that
// gives it (line number in that file), first candidate unless said otherwise.
const LIBRARY = [
  ['MIA', '𝑨'],  // 1010  ("MIA" . ("𝑨"))     bold italic: an algebra
  ['MIB', '𝑩'],  // 1011  ("MIB" . ("𝑩"))
  ['MIC', '𝑪'],  // 1012  ("MIC" . ("𝑪"))
  ['MiS', '𝑆'],  //  975  ("MiS" . ("𝑆"))     italic: a signature
  ['MCO', '𝓞'],  // 1131  ("MCO" . ("𝓞"))     script: universe levels
  ['MCV', '𝓥'],  // 1138  ("MCV" . ("𝓥"))
  ['bD', '𝔻'],   //  531  ("bD"   . ("𝔻"))    a setoid's domain
  ['bU', '𝕌'],   //  548  ("bU"   . ("𝕌"))    its carrier
  ['Mcg', 'ℊ'],  // 1096  ("Mcg" . ("ℊ"))     a term's generator
  ['o.', '⊙'],   //  342  ("o."  . ("⊙"))
  ['~~', '≈'],   //  193  ("~~"   . ("≈"))
  ['r--', '⟶'],  //  434  ("r--"  . ("⟶"))
  ['-->', '⟶'],  //  434  ("-->"  . ("⟶"))
  ['st4', '✦'],  //  521  ("st4"  . ,(agda-input-to-string-list "✦✧")), the first
  ['McA', '𝒜'],  // 1064  ("McA" . ("𝒜"))
  ['bT', '𝕋'],   //  547  ("bT"   . ("𝕋"))
  ['MiA', '𝐴'],  //  957  ("MiA" . ("𝐴"))
  ['MiT', '𝑇'],  //  976  ("MiT" . ("𝑇"))
  ['^a', 'ᵃ'],   // 1265  ("^a" . ("ᵃ"))
  ['^b', 'ᵇ'],   // 1266  ("^b" . ("ᵇ"))
  ['^c', 'ᶜ'],   // 1267  ("^c" . ("ᶜ"))
];
for (const [key, glyph] of LIBRARY) {
  check(input.bindings[key] === glyph,
    `\\${key} types ${JSON.stringify(input.bindings[key])}; agda-input.el gives ${glyph}`);
}

// ---- the inherited bindings that once disagreed with agda-input.el ----------

// williamdemeo.org's table, which this one began as, had fourteen keys that
// Emacs types differently or not at all (found 2026-10-04 by looking up every
// key with `quail-lookup-key` in batch Emacs, the Agda input method active).
// They are corrected here to what Emacs types, or dropped, and held so.
const CORRECTED = [
  ['sub', '⊂'],      //  229  ("sub"   . ("⊂"))
  ['sub=', '⊆'],     //  231  ("sub="  . ("⊆"))
  ['Gp', 'ψ'],       //  952  ("Gp"  . ("ψ"))
  ['GP', 'Ψ'],       //  952  ("GP"  . ("Ψ"))
  ['Go', 'ω'],       //  953  ("Go"  . ("ω"))
  ['GO', 'Ω'],       //  953  ("GO"  . ("Ω"))
  ['phi', 'ϕ'],      // TeX's \phi, inherited
  ['epsilon', 'ϵ'],  // TeX's \epsilon, inherited
  ['diamond', '⋄'],  // TeX's \diamond, inherited
];
for (const [key, glyph] of CORRECTED) {
  check(input.bindings[key] === glyph,
    `\\${key} types ${JSON.stringify(input.bindings[key])}; Emacs types ${glyph}`);
}
// No such key in agda-input (`\not` is TeX's combining slash, U+0338, and
// `\==>` types ≡> there, as `\==` and then `>`).
for (const key of ['Gw', 'GW', 'Gy', 'not', '==>', '/=', '/=n', 'compose']) {
  check(!(key in input.bindings), `\\${key} is bound here and not in agda-input`);
}

// The palette's buttons each name the sequences that type their glyph, and
// the page tells the reader the first of them ("type backslash ... then a
// space").  So every key the palette shows has to be one Emacs agrees with,
// or the palette teaches a sequence that works only here.
const PALETTE_KEYS = {
  'to': '→',          // TeX's \to, inherited (agda-input-inherit)
  '->': '→',          //  418  ("->"  . ("→"))
  'r': '→',           //  407  ("r" . ,(... "→⇒⇛...")), the first
  'rightarrow': '→',  // TeX's \rightarrow, inherited
  'lambda': 'λ',      // TeX's \lambda, inherited
  'Gl': 'λ',          //  940  ("Gl"  . ("λ"))
  'all': '∀',         //  287  ("all" . ("∀"))
  'forall': '∀',      // TeX's \forall, inherited
  '<': '⟨',           //  829  ("<" . ,(... "⟨<≪...")), the first
  '>': '⟩',           //  830  (">" . ,(... "⟩>≫...")), the first
  'equiv': '≡',       // TeX's \equiv, inherited
  '==': '≡',          //  200  ("=="   . ("≡"))
};
for (const [key, glyph] of LIBRARY) PALETTE_KEYS[key] = glyph;

check(input.palette.length > 0, 'the palette is empty');
for (const entry of input.palette) {
  // Every key on the palette has to be reachable by typing.
  check(entry.keys.length > 0, `palette key ${entry.glyph} has no binding`);
  for (const key of entry.keys) {
    check(input.bindings[key] === entry.glyph,
      `palette says \\${key} types ${entry.glyph}, table says ${input.bindings[key]}`);
    check(PALETTE_KEYS[key] === entry.glyph,
      `palette offers \\${key} for ${entry.glyph}, which is not checked against agda-input.el here`);
  }
}

// A binding whose value is more than one character is almost always a typo
// in the table: these are single glyphs, and a two-character value would be
// inserted whole with nothing to say it was wrong.
for (const [key, glyph] of Object.entries(input.bindings)) {
  check([...glyph].length === 1, `\\${key} maps to ${JSON.stringify(glyph)}, not one glyph`);
}

// ---- the rule ----------------------------------------------------------------

// What a reader types, and what the box should hold afterwards.  The
// terminator in each expectation is the point of the third column.
const TYPED = [
  // The personal site's cases.
  ['\\to ', '→ ', 'the common case'],
  ['\\== ', '≡ ', 'the terminator survives, or `≡b` becomes one identifier'],
  ['not (not b) \\== b', 'not (not b) ≡ b', 'mid-line, with the space kept'],
  ['\\to\n', '→\n', 'a newline commits and is kept'],
  ['\\bN ', 'ℕ ', 'a double-struck name'],
  ['\\_1 ', '₁ ', 'a subscript'],
  ['\\Gl ', 'λ ', "agda-input's two-letter Greek"],
  ['\\nope ', '\\nope ', 'an unknown name is left exactly as typed'],
  ['\\to', '\\to', 'nothing commits without a terminator'],
  ['x\\to ', 'x→ ', 'a sequence that starts mid-word'],
  ['(\\to ', '(→ ', 'a sequence after an opening bracket'],
  ['\\to \\to ', '→ → ', 'two in a row'],
  // This library's.
  ['\\~~\t', '≈\t', 'a tab commits and is kept'],
  ['\\MIA ', '𝑨 ', 'an astral glyph, two units in the box'],
  ['\\MIA \\o. \\MIB ', '𝑨 ⊙ 𝑩 ', "an expression in this library's notation"],
  ['\\o ', '∘ ', '`\\o` is its own name; only the dot makes it `\\o.`'],
  ['𝑨\\MCO ', '𝑨𝓞 ', 'a sequence right after an astral character'],
  ['\\st4 ', '✦ ', 'a name with a digit in it'],
  ['\\r-- \\--> ', '⟶ ⟶ ', 'both names of the long arrow'],
  ['\\Mcg x\n\\bD\n', 'ℊ x\n𝔻\n', 'over two lines, each newline kept'],
  ['\\sqsupseteq ', '⊒ ', 'the longest name: the lookback reaches its backslash'],
  ['\\MIA', '\\MIA', 'an astral binding waits for its terminator too'],
];

/* What a literal `\\to ` should do is deliberately not asserted.  A backslash
 * barely appears in Agda source, `agda-input`'s own answer is a binding this
 * table does not carry, and a test that encodes a guess about upstream is
 * worse than no test.  It currently substitutes on the last backslash. */

for (const [typed, expected, why] of TYPED) {
  // Typed one character at a time, because that is when the page calls it:
  // on every `input` event, not once at the end.  One character is one code
  // point: a reader's keyboard sends 𝑨 whole.
  const el = box('');
  for (const ch of typed) {
    el.setRangeText(ch, el.selectionStart, el.selectionEnd);
    input.commit(el);
  }
  check(el.value === expected,
    `typing ${JSON.stringify(typed)} gave ${JSON.stringify(el.value)}, `
    + `expected ${JSON.stringify(expected)} (${why})`);
  check(el.selectionStart === el.value.length && el.selectionEnd === el.value.length,
    `typing ${JSON.stringify(typed)} left the caret at ${el.selectionStart}, not at the end`);
}

// `commit` says whether it did anything.
{
  const el = box('a \\MIB ');
  check(input.commit(el) === true && el.value === 'a 𝑩 ', 'commit on `\\MIB ` did not report it');
  check(input.commit(box('a \\nope ')) === false, 'commit reported an unknown name');
  check(input.commit(box('')) === false, 'commit reported something in an empty box');
}

// A sequence before the caret, not at the end of the text: the reader went
// back to an earlier line and typed there.
{
  const el = box('x = \\bD \ny = 1', 8);
  check(input.commit(el) === true && el.value === 'x = 𝔻 \ny = 1' && el.selectionStart === 7,
    `a sequence before the caret gave ${JSON.stringify(el.value)} with the caret at ${el.selectionStart}`);
}

// A non-collapsed selection is a reader dragging over text, not typing.  It
// starts just after a complete `\to `, so that only the selection stands
// between it and a commit (the personal site's case started inside the
// sequence, where nothing would have committed anyway, and so tested nothing).
{
  const selected = box('\\to x', 4);
  selected.selectionEnd = 5;
  check(input.commit(selected) === false && selected.value === '\\to x', 'committed while a selection was open');
}

// A palette button replaces the selection with its glyph, leaves the caret
// after it, and gives the box back its focus.
{
  const el = box('x = ? y', 4);
  el.selectionEnd = 5;
  input.insert(el, '𝑨');
  check(el.value === 'x = 𝑨 y' && el.selectionStart === 6 && el.selectionEnd === 6 && el.focused,
    `insert gave ${JSON.stringify(el.value)}, caret ${el.selectionStart}-${el.selectionEnd}, focus ${el.focused}`);
}

console.log(`playground input: ${Object.keys(input.bindings).length} bindings, `
  + `${input.palette.length} palette keys, ${TYPED.length} typing cases, ${asserted} assertions`);
if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground input: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log("playground input: the library's bindings are agda-input's, the rule keeps its "
  + 'terminator, and every palette key types');
