// File: docs/assets/js/playground/protocol.js
//
// The half of Agda's interaction protocol that the playground speaks: how to
// write a command, and how to read what comes back.  Pure functions only, so
// that `scripts/js/playground/test_protocol.mjs` can run them under node.
//
// The protocol is `--interaction-json`, the one Agda's Emacs mode and its
// language server speak.  It has no documentation worth the name; the source
// of truth is `src/full/Agda/Interaction/` in Agda 2.8.0 (`Base.hs` for the
// command grammar, `JSONTop.hs` for every response's shape), and every shape
// read below was also observed from this site's own checker.
//
// ## Writing a command
//
// One per line: `IOTCM <file> <level> <method> (<command>)`.  Strings are
// Haskell string literals, written the way agda2-mode's `agda2-string-quote`
// writes them: ASCII as itself, `"` and `\` escaped, and everything outside
// ASCII as `\xHEX\&`, where the `\&` ends the escape so that a digit after it
// is not read as part of the number.  This library's names are mostly
// outside ASCII (𝑨, 𝔻, ⊙, ℊ), so that is not an edge case.
//
// ## Reading the answers
//
// Agda writes the prompt `JSON> ` before it reads each command, and then one
// JSON object per line for each response.  So the prompts cut the output
// into the answers to each command in turn: what follows the first prompt
// answers the first command, and so on.  A command with no answer leaves two
// prompts on one line, which is why a line may start with several.

/** The forms a goal's type and context can be shown in, as the page offers
 * them: as written, simplified (agda-mode's default), or normalised. */
export const REWRITES = ['AsIs', 'Simplified', 'Normalised'];

/** A Haskell string literal for `text`, as agda2-mode quotes one. */
export function haskellString(text) {
  let out = '"';
  for (const ch of String(text)) {
    const code = ch.codePointAt(0);
    if (ch === '"') out += '\\"';
    else if (ch === '\\') out += '\\\\';
    else if (ch === '\n') out += '\\n';
    else if (code < 32 || code === 127) out += `\\${code}\\&`;
    else if (code < 128) out += ch;
    else out += `\\x${code.toString(16)}\\&`;
  }
  return out + '"';
}

const rewriteOf = (r) => (REWRITES.includes(r) ? r : 'Simplified');
const goalOf = (n) => {
  if (!Number.isInteger(n) || n < 0) throw new Error(`not a goal number: ${n}`);
  return n;
};

/** The command line for one operation on `path`, the file as the guest sees
 * it.  The operations are the playground's, not Agda's: `load`, and the
 * goal commands, each with the goal's number.  The load asks for Agda's own
 * highlighting inline (`NonInteractive Direct`), which is how the editor is
 * colored.  The goal commands ask for none (`None`), and `Direct` too: with
 * `Indirect`, a give that Agda refuses also answers a second error,
 * `/tmp: openTempFile: does not exist`, because Agda writes indirect
 * highlighting to a temporary file and the guest has no `/tmp` (measured,
 * 2026-10-04). */
export function command(path, op) {
  const file = haskellString(path);
  const line = (level, body) => `IOTCM ${file} ${level} (${body})`;
  const quiet = (body) => line('None Direct', body);
  const text = op.text === undefined || op.text === null ? '' : op.text;
  switch (op.op) {
    case 'load':
      return line('NonInteractive Direct', `Cmd_load ${file} []`);
    case 'context':
      return quiet(`Cmd_goal_type_context ${rewriteOf(op.rewrite)} ${goalOf(op.goal)} noRange ""`);
    case 'have':
      return quiet(`Cmd_goal_type_context_infer ${rewriteOf(op.rewrite)} ${goalOf(op.goal)} noRange ${haskellString(text)}`);
    case 'give':
      return quiet(`Cmd_give WithoutForce ${goalOf(op.goal)} noRange ${haskellString(text)}`);
    case 'refine':
      return quiet(`Cmd_refine_or_intro False ${goalOf(op.goal)} noRange ${haskellString(text)}`);
    case 'case':
      return quiet(`Cmd_make_case ${goalOf(op.goal)} noRange ${haskellString(text)}`);
    default:
      throw new Error(`not an operation: ${JSON.stringify(op)}`);
  }
}

const PROMPT = 'JSON> ';

/** Agda's output cut at its prompts: `answers[k]` holds the responses to the
 * k-th command (from 0), and `before` anything written before the first
 * prompt.  A line that is not JSON is kept as `{kind: 'Text', text}`: Agda
 * can print a panic that way, and a reader should see it rather than lose it. */
export function answers(output) {
  const parts = [[]];
  for (let line of String(output).split('\n')) {
    while (line.startsWith(PROMPT)) {
      parts.push([]);
      line = line.slice(PROMPT.length);
    }
    // The last prompt has no newline after it, and a trailing one stands alone.
    if (line.trim() === '' || line.trim() === PROMPT.trim()) continue;
    let parsed;
    try { parsed = JSON.parse(line); } catch { parsed = { kind: 'Text', text: line }; }
    parts[parts.length - 1].push(parsed);
  }
  return { before: parts[0], answers: parts.slice(1) };
}

const display = (rs, kind) => rs.filter((r) => r.kind === 'DisplayInfo' && r.info && r.info.kind === kind);
const last = (xs) => (xs.length ? xs[xs.length - 1] : null);

/** A range as Agda sends it, a list of intervals, reduced to its first
 * interval, or null when it has none (a goal a refine just created has
 * none: the buffer it lives in was never written). */
export function interval(range) {
  if (!Array.isArray(range) || range.length === 0) return null;
  const { start, end } = range[0];
  return { start: { ...start }, end: { ...end } };
}

/** The first error among some responses: its message, and the position
 * (a code point offset from 1) that a `JumpToError` names. */
export function errorOf(responses) {
  const shown = display(responses, 'Error')[0];
  if (!shown) return null;
  const jump = responses.find((r) => r.kind === 'JumpToError');
  return {
    message: shown.info.error && shown.info.error.message || '',
    warnings: (shown.info.warnings || []).map((w) => w.message),
    position: jump ? jump.position : null,
  };
}

/** What a load answered: whether it failed, the goals it left, the
 * diagnostics beside them, and the highlighting. */
export function readLoad(responses) {
  const all = last(display(responses, 'AllGoalsWarnings'));
  const info = all ? all.info : { visibleGoals: [], invisibleGoals: [], warnings: [], errors: [] };
  const points = last(responses.filter((r) => r.kind === 'InteractionPoints'));
  const running = responses.filter((r) => r.kind === 'RunningInfo').map((r) => r.message);
  return {
    error: errorOf(responses),
    // Unanchored: Agda indents a nested `Checking` line one space per level.
    checked: running.filter((m) => /^\s*Checking /.test(m)).length,
    // What Agda said while checking other than "Checking", which is where a
    // warning about the reader's own text appears.
    notes: running.filter((m) => !/^\s*Checking /.test(m)).map((m) => m.trim()),
    goals: (info.visibleGoals || []).map((g) => ({
      id: g.constraintObj.id,
      type: g.type,
      kind: g.kind,
      range: interval(g.constraintObj.range),
    })),
    hidden: (info.invisibleGoals || []).map((g) => ({
      name: g.constraintObj.name,
      type: g.type,
      kind: g.kind,
      range: interval(g.constraintObj.range),
    })),
    warnings: (info.warnings || []).map((w) => w.message),
    errors: (info.errors || []).map((e) => e.message),
    points: points ? points.interactionPoints.map((p) => ({ id: p.id, range: interval(p.range) })) : null,
    highlighting: responses
      .filter((r) => r.kind === 'HighlightingInfo' && r.direct && r.info)
      .flatMap((r) => r.info.payload || [])
      .map((h) => ({ from: h.range[0], to: h.range[1], atoms: h.atoms })),
  };
}

/** What a goal command answered: the goal's type and its context, newest
 * binding first, as Emacs shows it; a `have` adds the type of the given
 * expression.  Null for an answer that is not about a goal (the error for a
 * goal that no longer exists, say). */
export function readGoal(responses) {
  const shown = last(display(responses, 'GoalSpecific'));
  if (!shown || !shown.info.goalInfo) return null;
  const g = shown.info.goalInfo;
  return {
    id: shown.info.interactionPoint.id,
    rewrite: g.rewrite,
    type: g.type,
    have: g.typeAux && g.typeAux.kind === 'GoalAndHave' ? g.typeAux.expr : null,
    context: (g.entries || []).slice().reverse().map((e) => ({
      name: e.reifiedName,
      type: e.binding,
      inScope: e.inScope,
    })),
    constraints: g.outputForms || [],
  };
}

/** What a give, a refine or a case split answered: the change to make to
 * the text, or why there is none.  `give` is `{goal, range, text}` or
 * `{goal, range, paren}` (Agda's `giveResult`: replacement text verbatim, or
 * "use what you sent, parenthesized or not"); `split` is the clauses that
 * replace the line, with Agda's `variant`. */
export function readAction(responses) {
  const give = last(responses.filter((r) => r.kind === 'GiveAction'));
  const split = last(responses.filter((r) => r.kind === 'MakeCase'));
  const unknown = last(display(responses, 'IntroConstructorUnknown'));
  const none = last(display(responses, 'IntroNotFound'));
  return {
    error: errorOf(responses),
    give: give ? {
      goal: give.interactionPoint.id,
      range: interval(give.interactionPoint.range),
      ...('str' in give.giveResult ? { text: give.giveResult.str } : { paren: !!give.giveResult.paren }),
    } : null,
    split: split ? {
      goal: split.interactionPoint.id,
      range: interval(split.interactionPoint.range),
      clauses: split.clauses,
      variant: split.variant,
    } : null,
    // A refine on an empty goal whose type has several constructors, or
    // none it can see: Agda's answer, not an error.
    message: unknown
      ? `No single constructor fits; try one of: ${unknown.info.constructors.join(', ')}`
      : none ? 'Nothing introduces a goal of this type.' : null,
  };
}
