/* File: docs/assets/js/playground-input.js
 *
 * Agda's input method, enough of it to type Agda.
 *
 * Provenance: `docs/javascripts/playground-input.js` of williamdemeo/website
 * at commit 952e5eb (MIT, Copyright 2026 William DeMeo; see NOTICE).  The
 * mechanism is unchanged.  The table gains this library's own notation, and
 * fourteen inherited bindings that disagreed with Emacs are corrected or
 * dropped (`\sub` is ⊂ and `\Gp` is ψ in agda-input, `\Gw` and `\compose`
 * do not exist there, `\phi` is TeX's ϕ): every binding now types what Agda
 * 2.8.0's input method types, as `scripts/js/playground/test_input.mjs`
 * records.  The palette shows the characters these exercises use.
 *
 * A proof assistant whose notation a visitor cannot type is a proof assistant
 * they can only read.  The two drafted exercises are completable in ASCII, so
 * this is not what stands between a reader and the verdict; it is what stands
 * between them and changing the *statement*, which is the first thing anybody
 * curious does.  `→` and `≡` are on no keyboard.
 *
 * ## The rule, and why it is one rule
 *
 * Type a backslash, the name, then a space: `\to ` becomes `→ `.  That is the
 * whole mechanism and the page says so in one sentence.  The space survives;
 * see `commit` for why that is not optional.
 *
 * Agda's own Emacs input method substitutes eagerly and keeps a candidate
 * list, which is better and is not portable to a `<textarea>`: `to` is a
 * proper prefix of `top`, so an eager rule either steals `\top` or never
 * fires for `\to`, and there is no sound way to choose without the
 * continuation machinery Quail has and a text box does not.  Committing on
 * whitespace has neither problem and is what a reader can be told in a line.
 * A newline commits too, and is kept rather than eaten, since a reader who
 * pressed Enter wanted the line break.
 *
 * ## The table is a subset, and says so
 *
 * These are `agda-input` bindings, not inventions, but they are perhaps a
 * hundred of several thousand: the ones this site's own Agda actually uses,
 * plus the Greek and double-struck alphabets, subscripts and superscripts,
 * which is where a reader who starts exploring goes first.  A name that is
 * missing does nothing, visibly, rather than inserting something surprising.
 */

(function () {
  "use strict";

  var BINDINGS = {
  // arrows and the equality that every one of these exercises needs
  'to': '→', '->': '→', 'r': '→', 'rightarrow': '→',
  '<-': '←', 'l': '←', 'leftarrow': '←',
  '=>': '⇒', '<->': '↔', 'iff': '⇔',
  'equiv': '≡', '==': '≡', '==n': '≢',
  'ne': '≠', 'le': '≤', '<=': '≤', 'ge': '≥', '>=': '≥',
  'cong': '≅', '~=': '≅', 'simeq': '≃',

  // logic and sets
  'all': '∀', 'forall': '∀', 'ex': '∃', 'exists': '∃',
  'neg': '¬', 'and': '∧', 'or': '∨',
  'top': '⊤', 'bot': '⊥', 'emptyset': '∅',
  'in': '∈', 'notin': '∉', 'subseteq': '⊆', 'sub': '⊂', 'sub=': '⊆', 'supseteq': '⊇',
  'cup': '∪', 'cap': '∩', 'uplus': '⊎', 'sqcup': '⊔', 'sqcap': '⊓',
  'lub': '⊔', 'glb': '⊓', 'sqsubseteq': '⊑', 'sqsupseteq': '⊒',

  // operators and punctuation Agda leans on
  'times': '×', 'x': '×', 'circ': '∘', 'o': '∘', 'cdot': '·',
  '::': '∷', '<': '⟨', '>': '⟩', '[[': '⟦', ']]': '⟧',
  'lambda': 'λ', 'Gl': 'λ', 'qed': '∎', 'square': '□', 'diamond': '⋄',
  'sum': '∑', 'prod': '∏',

  // double-struck, the type names
  'bN': 'ℕ', 'bZ': 'ℤ', 'bQ': 'ℚ', 'bR': 'ℝ', 'bC': 'ℂ', 'bB': '𝔹', 'bF': '𝔽',

  // Greek, by name and by agda-input's two-letter form
  'alpha': 'α', 'Ga': 'α', 'beta': 'β', 'Gb': 'β', 'gamma': 'γ', 'Gg': 'γ',
  'delta': 'δ', 'Gd': 'δ', 'epsilon': 'ϵ', 'Ge': 'ε', 'zeta': 'ζ', 'Gz': 'ζ',
  'eta': 'η', 'Gh': 'η', 'theta': 'θ', 'Gth': 'θ', 'iota': 'ι', 'Gi': 'ι',
  'kappa': 'κ', 'Gk': 'κ', 'mu': 'μ', 'Gm': 'μ', 'nu': 'ν', 'Gn': 'ν',
  'xi': 'ξ', 'Gx': 'ξ', 'pi': 'π', 'rho': 'ρ', 'Gr': 'ρ',
  'sigma': 'σ', 'Gs': 'σ', 'tau': 'τ', 'Gt': 'τ', 'phi': 'ϕ', 'Gf': 'φ',
  'chi': 'χ', 'Gc': 'χ', 'psi': 'ψ', 'Gp': 'ψ', 'omega': 'ω', 'Go': 'ω',
  'Gamma': 'Γ', 'GG': 'Γ', 'Delta': 'Δ', 'GD': 'Δ', 'Lambda': 'Λ', 'GL': 'Λ',
  'Pi': 'Π', 'GP': 'Ψ', 'Sigma': 'Σ', 'GS': 'Σ', 'Omega': 'Ω', 'GO': 'Ω',

    // script capitals, which this project's own Agda writes constantly
    'McA': '𝒜', 'bT': '𝕋', 'MiA': '𝐴', 'MiT': '𝑇',

    // agda-algebras' own notation: algebras are bold italic (𝑨), signatures
    // italic (𝑆), universe levels script (𝓞 𝓥), a setoid's domain is 𝔻 and
    // its carrier 𝕌, a term's generator ℊ.  `\st4` rather than `\st`,
    // whose first candidate is ⋆: this method has no candidates to pick.
    'MIA': '𝑨', 'MIB': '𝑩', 'MIC': '𝑪', 'MiS': '𝑆', 'MCO': '𝓞', 'MCV': '𝓥',
    'bD': '𝔻', 'bU': '𝕌', 'Mcg': 'ℊ', 'o.': '⊙', '~~': '≈', 'r--': '⟶',
    '-->': '⟶', 'st4': '✦', '^a': 'ᵃ', '^b': 'ᵇ', '^c': 'ᶜ'
  };

  // Subscripts and superscripts are ranges, not entries: `\_1` and `\^2`.
  for (var d = 0; d <= 9; d++) {
    BINDINGS['_' + d] = '₀₁₂₃₄₅₆₇₈₉'[d];
    BINDINGS['^' + d] = '⁰¹²³⁴⁵⁶⁷⁸⁹'[d];
  }

  /* The characters worth a button, each carrying the sequences that type it,
   * so the palette teaches the mechanism instead of replacing it. */
  var PALETTE = ['→', 'λ', '∀', '≈', '⊙', '⟶', 'ℊ', '✦', '𝑨', '𝑩', '𝑪', '𝑆', '𝔻', '⟨', '⟩', '≡']
    .map(function (glyph) {
      return {
        glyph: glyph,
        keys: Object.keys(BINDINGS).filter(function (k) { return BINDINGS[k] === glyph; }),
      };
    });

  /* The longest binding, so the lookback never scans further than it must. */
  var LONGEST = Object.keys(BINDINGS).reduce(function (n, k) {
    return Math.max(n, k.length);
  }, 0);

  /* Commit a pending `\name` in a text box, if the caret has just passed one.
   *
   * `setRangeText` rather than rewriting `value`: it keeps the caret where the
   * reader left it, and it does not blow away the box's own undo stack, which
   * a wholesale assignment does. */
  function commit(el) {
    var at = el.selectionStart;
    if (at === 0 || at !== el.selectionEnd) return false;
    var terminator = el.value[at - 1];
    if (terminator !== " " && terminator !== "\n" && terminator !== "\t") return false;

    var before = el.value.slice(Math.max(0, at - 1 - LONGEST - 1), at - 1);
    var match = before.match(/\\([^\s\\]+)$/);
    if (!match) return false;
    var glyph = BINDINGS[match[1]];
    if (glyph === undefined) return false;

    /* The terminator is kept, always, and that is a correctness matter rather
     * than a taste one.  Agda's identifiers may contain symbol characters, so
     * `≡b` lexes as one name and not as `_≡_` applied to `b`: an input method
     * that ate the space would silently turn `a \== b` into something that
     * means something else.  Costing a reader one backspace to put two glyphs
     * side by side is the cheaper mistake. */
    el.setRangeText(glyph + terminator, at - 1 - match[0].length, at, "end");
    return true;
  }

  /* Insert one character at the caret, replacing any selection. */
  function insert(el, glyph) {
    el.setRangeText(glyph, el.selectionStart, el.selectionEnd, "end");
    el.focus();
  }

  window.AgdaInput = {
    bindings: BINDINGS,
    palette: PALETTE,
    commit: commit,
    insert: insert,
  };
})();
