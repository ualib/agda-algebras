// File: docs/assets/js/playground/edits.js
//
// The edits a goal command makes to the reader's text, as pure functions on
// strings, so that `scripts/js/playground/test_edits.mjs` can hold them to
// what Agda's Emacs mode does.  The worker applies them to the file it hands
// Agda and reloads; the page receives the new text.
//
// ## Two ways of counting
//
// Agda gives a position as a code point offset from 1 (`pos`).  A JavaScript
// string, and so a `<textarea>`, counts UTF-16 code units, and a character
// outside the Basic Multilingual Plane is two of them.  This library writes
// such characters constantly (𝑨, 𝑩, 𝔻, 𝑆, 𝓞, 𝓥 are all astral), so a position
// used without converting it lands one unit further left for every one of
// them before it on the page: an error marked on the wrong token, or a give
// spliced into the middle of a name.

/** The UTF-16 offset of Agda's code point position `pos` (counted from 1)
 * in `text`.  A position past the end is the end. */
export function offsetOf(text, pos) {
  let units = 0;
  let points = 1;
  for (const ch of text) {
    if (points >= pos) return units;
    units += ch.length;
    points += 1;
  }
  return units;
}

/** The code point position (from 1) of UTF-16 offset `at` in `text`. */
export function positionOf(text, at) {
  let points = 1;
  let units = 0;
  for (const ch of text) {
    if (units >= at) return points;
    units += ch.length;
    points += 1;
  }
  return points;
}

/** A range from Agda, `{start, end}` each with `pos`, as UTF-16 offsets
 * `[from, to)` in `text`. */
export function span(text, range) {
  return [offsetOf(text, range.start.pos), offsetOf(text, range.end.pos)];
}

/** What a goal holds: the text between `{!` and `!}`, trimmed, or the empty
 * string for `?`.  This is what Emacs sends with a give or a case split when
 * the reader has written something into the goal. */
export function holeContent(text, range) {
  const [from, to] = span(text, range);
  const hole = text.slice(from, to);
  const m = hole.match(/^\{!([\s\S]*)!\}$/);
  return m ? m[1].trim() : '';
}

/** The text after a give or a refine: the goal replaced by Agda's answer.
 *
 * `give` is what `readAction` returns.  Agda answers either with the text to
 * put in (`text`: a refine's `cong suc ?`, or the given expression as Agda
 * reprinted it) or with "what you sent", parenthesized or not (`paren`), and
 * `sent` is what was sent.  Emacs's `agda2-update` does the same, removing
 * the goal's braces in both cases. */
export function applyGive(text, give, sent) {
  const [from, to] = span(text, give.range);
  const put = 'text' in give ? give.text : give.paren ? `(${sent.trim()})` : sent.trim();
  return text.slice(0, from) + put + text.slice(to);
}

/** The text after a case split, as agda2-mode's `agda2-make-case-action`
 * and `agda2-make-case-action-extendlam` make it.
 *
 * A function clause: the goal's line, from its indentation to its end, is
 * replaced by the clauses, one per line at that indentation.  Only that line:
 * Emacs assumes the clause being split fits on it, and so does this.
 *
 * An extended lambda: the clause around the goal, from the `;` or `{` that
 * opens it (or the line's indentation, for a lambda laid out one clause per
 * line) to the end of the goal, is replaced by the clauses, separated by
 * ` ; `, or by a newline and the indentation in the laid-out case. */
export function applySplit(text, split) {
  const [from, to] = span(text, split.range);
  const lineStart = text.lastIndexOf('\n', from - 1) + 1;
  const newline = text.indexOf('\n', from);
  const lineEnd = newline === -1 ? text.length : newline;
  const indent = text.slice(lineStart, lineEnd).match(/^ */)[0].length;
  const bodyStart = lineStart + indent;
  const pad = '\n' + ' '.repeat(indent);

  if (split.variant !== 'ExtendedLambda') {
    return text.slice(0, bodyStart) + split.clauses.join(pad) + text.slice(lineEnd);
  }

  // agda2-make-case-action-extendlam, step for step: back from the goal to
  // the clause's start, counting braces, stopping at a `;`, at an unmatched
  // `{`, or at the line's indentation.
  let at = from;
  let depth = 0;
  while (text[at - 1] !== ';' && depth >= 0 && at > bodyStart) {
    at -= 1;
    if (text[at - 1] === '}') depth += 1;
    if (text[at - 1] === '{') depth -= 1;
  }
  const laidOut = at === bodyStart;
  const lead = laidOut ? '' : ' ';
  return text.slice(0, at) + lead + split.clauses.join(laidOut ? pad : ' ; ') + text.slice(to);
}
