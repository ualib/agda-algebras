/* File: scripts/js/playground/test_protocol.mjs
 *
 * The playground's half of Agda's interaction protocol, held to what Agda
 * itself accepted and wrote.
 *
 * `protocol.js` is where a mistake costs the most and shows the least.  A
 * string escaped one way short is a different expression, with no error
 * anywhere: Haskell reads `\x2299` followed by the digit 1 as U+22991, a CJK
 * ideograph, and not as `⊙1`, which is why every escape ends in `\&`.  A
 * command line Agda cannot parse is answered with nothing that names it.  A
 * reader that looks for a response under the wrong kind, or in the wrong
 * order, reports a file with goals as having none, or shows the reader the
 * wrong one of two errors.  None of these throws.
 *
 * So the reading half is held to answers the real checker gave (Agda 2.8.0
 * compiled to WebAssembly, on this site's own image), captured once and
 * committed under `fixtures/`; the README there says how, and how to capture
 * them again.  The writing half is held to the command lines Agda accepted in
 * those same runs: `capture.mjs` spells its lines out rather than calling
 * `command()`, so a line here that matches one there is a line Agda parsed.
 * The cases that no recorded run can produce (a control character in a
 * string, a goal number that is not one) are written out below.
 *
 * Usage:  node scripts/js/playground/test_protocol.mjs
 *         make playground-test
 */
import { readFileSync } from 'node:fs';
import { isDeepStrictEqual } from 'node:util';
import {
  haskellString, command, answers, errorOf, readLoad, readGoal, readAction,
} from '../../../docs/assets/js/playground/protocol.js';

const FIXTURES = 'scripts/js/playground/fixtures';

const failures = [];
let checks = 0;
const check = (ok, what) => { checks += 1; if (!ok) failures.push(what); };
const same = (got, want, what) => check(isDeepStrictEqual(got, want),
  `${what}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);
const throws = (thunk, what) => {
  try { thunk(); } catch { checks += 1; return; }
  check(false, `${what}: did not throw`);
};
/* A reader that throws on a real answer is a failure like any other, and
 * the sections after it still run. */
const section = (name, body) => {
  try { body(); } catch (err) { check(false, `${name}: threw ${err.stack.split('\n').slice(0, 2).join(' ')}`); }
};

const sources = JSON.parse(readFileSync(`${FIXTURES}/sources.json`, 'utf8'));
const PATH = sources.path;

/** A recorded run: the lines Agda was sent, and what it wrote back, cut at
 * its prompts by the reader under test. */
function recorded(name) {
  const stdin = readFileSync(`${FIXTURES}/${name}.stdin`, 'utf8').split('\n').filter((l) => l !== '');
  const stdout = readFileSync(`${FIXTURES}/${name}.stdout`, 'utf8');
  let cut = { before: [], answers: [] };
  section(`answers ${name}`, () => { cut = answers(stdout); });
  return { stdin, stdout, ...cut };
}
const RUNS = Object.fromEntries(['load-context', 'load-error', 'give-refused', 'case-split',
  'refine-unknown', 'have', 'give', 'refine'].map((name) => [name, recorded(name)]));

/** A range as `interval` reduces one, from line, column and code point. */
const at = (line, col, pos, endCol, endPos) => ({
  start: { col, line, pos }, end: { col: endCol, line, pos: endPos },
});
const HOLE = at(16, 13, 523, 14, 524);       // `?` in `graft t σ = ?`
const LEAF = at(16, 17, 527, 18, 528);       // `?` in `graft (ℊ x) σ = ?`
const NODE = at(17, 22, 550, 23, 551);       // `?` in `graft (node f t) σ = ?`

// ## haskellString
//
// The table is what agda2-mode's `agda2-string-quote` writes.  Each row is a
// way of being one character short: a missing `\&`, a surrogate pair written
// as two escapes, a control character sent raw.

const QUOTED = [
  ['ASCII as itself', 'node f ?', '"node f ?"'],
  ['the empty string', '', '""'],
  ['a double quote', 'say "x"', '"say \\"x\\""'],
  ['a backslash', 'a\\b', '"a\\\\b"'],
  ['a newline', 'a\nb', '"a\\nb"'],
  ['a tab, as a decimal escape', 'a\tb', '"a\\9\\&b"'],
  ['DEL, as a decimal escape', '\x7f', '"\\127\\&"'],
  ['a control character before a digit', '\x01' + '2', '"\\1\\&2"'],
  ['the last character before DEL', '~', '"~"'],
  ['the first character after DEL', '\x80', '"\\x80\\&"'],
  ['Latin-1, which is not ASCII either', 'é', '"\\xe9\\&"'],
  ['non-ASCII in the BMP', '⊙', '"\\x2299\\&"'],
  ['non-ASCII before a digit', '⊙1', '"\\x2299\\&1"'],
  ['non-ASCII before a hex letter', '⊙f', '"\\x2299\\&f"'],
  ['an astral character, as one escape', '𝑨', '"\\x1d468\\&"'],
  ['an astral character before a digit', '𝑨1', '"\\x1d468\\&1"'],
  ['an expression of this library', 'h ⊙ g', '"h \\x2299\\& g"'],
];
section('haskellString', () => {
  for (const [what, text, want] of QUOTED) same(haskellString(text), want, `haskellString, ${what}`);
});

/* And back, the way Haskell's lexer reads an escape: greedily, as many
 * digits as follow.  A string that comes back different is one Agda would
 * read as different text, whatever the table says. */
function unquote(lit) {
  let out = '';
  for (let i = 1; i < lit.length - 1; i++) {
    if (lit[i] !== '\\') { out += lit[i]; continue; }
    const rest = lit.slice(i + 1);
    let m;
    if ((m = rest.match(/^x([0-9a-fA-F]+)/))) out += String.fromCodePoint(parseInt(m[1], 16));
    else if ((m = rest.match(/^([0-9]+)/))) out += String.fromCodePoint(parseInt(m[1], 10));
    else if ((m = rest.match(/^([n"\\&])/))) out += { n: '\n', '"': '"', '\\': '\\', '&': '' }[m[1]];
    else throw new Error(`an escape Haskell does not have: \\${rest.slice(0, 4)}`);
    i += m[0].length;
  }
  return out;
}
const AWKWARD = ['⊙1', '𝑨0', '𝔻[ 𝑪 ]', '\x01' + '9', '\x1f' + 'a', 'λ x → x', '"\\"', 'a\nb\n',
  'ℊ₁f', '\u00ff' + 'f', '\u{10ffff}' + '1'];
for (const text of AWKWARD) {
  let back;
  try { back = unquote(haskellString(text)); } catch (err) { back = err.message; }
  same(back, text, `haskellString ${JSON.stringify(text)} read back as Haskell reads it`);
}

// ## command
//
// Every operation's line, written out.  Where a recorded run sent the same
// operation, the line must also be the one Agda was sent there, which it
// parsed and answered.

const L = (body) => `IOTCM "/work/Graft.agda" None Direct (${body})`;
const COMMANDS = [
  [{ op: 'load' },
    'IOTCM "/work/Graft.agda" NonInteractive Direct (Cmd_load "/work/Graft.agda" [])', ['load-context', 0]],
  [{ op: 'context', goal: 0, rewrite: 'Simplified' },
    L('Cmd_goal_type_context Simplified 0 noRange ""'), ['load-context', 1]],
  [{ op: 'context', goal: 1, rewrite: 'Simplified' },
    L('Cmd_goal_type_context Simplified 1 noRange ""'), ['case-split', 4]],
  [{ op: 'context', goal: 3, rewrite: 'Normalised' },
    L('Cmd_goal_type_context Normalised 3 noRange ""')],
  [{ op: 'context', goal: 0, rewrite: 'AsIs' },
    L('Cmd_goal_type_context AsIs 0 noRange ""')],
  [{ op: 'context', goal: 0 },
    L('Cmd_goal_type_context Simplified 0 noRange ""')],
  [{ op: 'context', goal: 0, rewrite: 'Normalized' },
    L('Cmd_goal_type_context Simplified 0 noRange ""')],
  [{ op: 'have', goal: 0, text: 'σ x', rewrite: 'Simplified' },
    L('Cmd_goal_type_context_infer Simplified 0 noRange "\\x3c3\\& x"'), ['have', 1]],
  [{ op: 'have', goal: 2, text: 'h ⊙ g', rewrite: 'Normalised' },
    L('Cmd_goal_type_context_infer Normalised 2 noRange "h \\x2299\\& g"')],
  [{ op: 'give', goal: 0, text: 't' },
    L('Cmd_give WithoutForce 0 noRange "t"'), ['give-refused', 1]],
  [{ op: 'give', goal: 0, text: 'σ x' },
    L('Cmd_give WithoutForce 0 noRange "\\x3c3\\& x"'), ['give', 1]],
  [{ op: 'refine', goal: 0, text: '' },
    L('Cmd_refine_or_intro False 0 noRange ""'), ['refine-unknown', 1]],
  [{ op: 'refine', goal: 1, text: 'node f' },
    L('Cmd_refine_or_intro False 1 noRange "node f"'), ['refine', 1]],
  [{ op: 'case', goal: 0, text: 't' },
    L('Cmd_make_case 0 noRange "t"'), ['case-split', 1]],
  [{ op: 'case', goal: 12, text: 'x y' },
    L('Cmd_make_case 12 noRange "x y"')],
];
for (const [op, want, sentIn] of COMMANDS) {
  let got;
  try { got = command(PATH, op); } catch (err) { got = `threw ${err.message}`; }
  same(got, want, `command ${JSON.stringify(op)}`);
  check(/^[\x20-\x7e]*$/.test(got), `command ${JSON.stringify(op)}: a line that is not printable ASCII`);
  if (sentIn) {
    const [run, k] = sentIn;
    same(want, RUNS[run].stdin[k], `command ${JSON.stringify(op)}: the line ${run} sent Agda`);
  }
}
section('command, a path outside ASCII', () => same(command('/work/𝔻.agda', { op: 'load' }),
  'IOTCM "/work/\\x1d53b\\&.agda" NonInteractive Direct (Cmd_load "/work/\\x1d53b\\&.agda" [])',
  'command: a path outside ASCII is quoted in both places'));

/* A goal number goes into the line unquoted, so anything but a natural
 * number would be a different command, or none. */
for (const op of ['context', 'have', 'give', 'refine', 'case']) {
  for (const goal of [-1, 1.5, '0', '0) (Cmd_load "x" []', undefined, null, NaN]) {
    throws(() => command(PATH, { op, goal, text: 'x' }), `command ${op} at goal ${JSON.stringify(goal)}`);
  }
}
throws(() => command(PATH, { op: 'compute', goal: 0, text: 'x' }), 'command: an operation the page has not');

// ## answers

section('answers, two prompts on one line', () => {
  const cut = answers('JSON> JSON> {"kind":"A"}\nJSON> ');
  same(cut.answers[0], [], 'answers: two prompts on one line, the first command answered nothing');
  same(cut.answers[1], [{ kind: 'A' }], 'answers: two prompts on one line, the second command\'s answer');
  same(cut.answers.slice(2).flat(), [], 'answers: the trailing prompt answers nothing');
  same(cut.before, [], 'answers: nothing before the first prompt');
});
section('answers, a line that is not JSON', () => {
  const cut = answers('JSON> {"kind":"A"}\nagda: internal error\n{"kind":"B"}\nJSON>');
  same(cut.answers[0], [{ kind: 'A' }, { kind: 'Text', text: 'agda: internal error' }, { kind: 'B' }],
    'answers: a line that is not JSON is kept, in its place, as Text');
  same(cut.answers.slice(1).flat(), [], 'answers: a trailing prompt with its space trimmed is not Text');
});
section('answers, before the first prompt', () => {
  same(answers('starting\nJSON> {"kind":"A"}\n').before, [{ kind: 'Text', text: 'starting' }],
    'answers: what comes before the first prompt is kept apart');
  same(answers('').answers, [], 'answers: no output, no answers');
});

/* On real output: one answer per command sent, in order, and nothing after. */
for (const [name, run] of Object.entries(RUNS)) {
  same(run.before, [], `answers ${name}: Agda wrote nothing before its first prompt`);
  check(run.answers.slice(0, run.stdin.length).every((a) => a.length > 0),
    `answers ${name}: a command whose answer is empty`);
  same(run.answers.slice(run.stdin.length).flat(), [], `answers ${name}: responses after the last command`);
  check(run.answers.flat().every((r) => r.kind !== 'Text'), `answers ${name}: a line of Agda's that is not JSON`);
  /* One module checked per load: the reader's.  More would mean the image's
   * interfaces were not accepted, and a recapture over such an image records
   * answers the page never sees. */
  section(`readLoad ${name}, every load`, () => run.stdin.forEach((line, k) => {
    if (line.includes('(Cmd_load ')) same(readLoad(run.answers[k]).checked, 1, `readLoad ${name}: modules checked by command ${k}`);
  }));
}

// ## readLoad

section('readLoad load-context', () => {
  const load = readLoad(RUNS['load-context'].answers[0]);
  same(load.error, null, 'readLoad load-context: error');
  same(load.checked, 1, 'readLoad load-context: modules checked (the image\'s interfaces were accepted)');
  same(load.notes, [], 'readLoad load-context: notes');
  same(load.goals, [{ id: 0, type: 'Term X', kind: 'OfType', range: HOLE }], 'readLoad load-context: goals');
  same(load.hidden, [], 'readLoad load-context: hidden goals');
  same(load.warnings, [], 'readLoad load-context: warnings');
  same(load.errors, [], 'readLoad load-context: errors');
  same(load.points, [{ id: 0, range: HOLE }], 'readLoad load-context: interaction points');
  same(load.highlighting.length, 55, 'readLoad load-context: highlighting payloads in the one line kept');
  same(load.highlighting[0], { from: 1, to: 7, atoms: ['keyword'] }, 'readLoad load-context: first highlighting');
});
section('readLoad case-split', () => {
  const load = readLoad(RUNS['case-split'].answers[2]);
  same(load.goals.map((g) => [g.id, g.range]), [[0, LEAF], [1, NODE]], 'readLoad case-split reload: two goals');
});
section('readLoad load-error', () => {
  const load = readLoad(RUNS['load-error'].answers[0]);
  check(load.error !== null && load.error.message.startsWith(
    '/work/Graft.agda:16.13-14: error: [UnequalTerms]\nY.ξ != X.χ of type Level'),
  `readLoad load-error: error message ${JSON.stringify(load.error && load.error.message)}`);
  same(load.error && load.error.position, 523, 'readLoad load-error: the position JumpToError names');
  same(load.error && load.error.warnings, [], 'readLoad load-error: warnings beside the error');
  same(load.goals, [], 'readLoad load-error: goals');
  same(load.points, null, 'readLoad load-error: no InteractionPoints, so no points');
  same(load.checked, 1, 'readLoad load-error: modules checked');
});
section('readLoad refine', () => {
  /* A refine's answer lists the goal it created with no range: the buffer
   * it lives in was never written.  `interval` has to say so, not crash. */
  const load = readLoad(RUNS.refine.answers[1]);
  same(load.goals.map((g) => [g.id, g.range, g.type]),
    [[0, LEAF, 'Term X'], [2, null, '(ArityOf 𝑆 f → Term X)']], 'readLoad refine answer: a goal with no range');
  same(load.points, [{ id: 0, range: LEAF }, { id: 2, range: null }], 'readLoad refine answer: points');
});
section('readLoad, nested Checking lines', () => {
  const load = readLoad([
    { kind: 'RunningInfo', message: 'Checking Graft (/work/Graft.agda).\n' },
    { kind: 'RunningInfo', message: ' Checking Overture.Signatures (/lib/Overture/Signatures.agda).\n' },
    { kind: 'RunningInfo', message: '  Something worth saying.\n' },
    { kind: 'HighlightingInfo', direct: false, filepath: '/tmp/x' },
  ]);
  same(load.checked, 2, 'readLoad: a nested, indented Checking line still counts');
  same(load.notes, ['Something worth saying.'], 'readLoad: what is not Checking is a note');
  same(load.highlighting, [], 'readLoad: indirect highlighting is not read');
});

// ## readGoal

section('readGoal load-context', () => {
  const goal = readGoal(RUNS['load-context'].answers[1]);
  same(goal && [goal.id, goal.rewrite, goal.type, goal.have], [0, 'Simplified', 'Term X', null],
    'readGoal load-context: id, rewrite, type, have');
  same(goal && goal.context.map((e) => [e.name, e.type, e.inScope]), [
    ['σ', 'Y → Term X', true], ['t', 'Term Y', true],
    ['X', 'Type X.χ', false], ['X.χ', 'Level', false], ['Y', 'Type Y.ξ', false], ['Y.ξ', 'Level', false],
    ['𝑆', 'Signature 𝑆.𝓞 𝑆.𝓥', false], ['𝑆.𝓥', 'Level', false], ['𝑆.𝓞', 'Level', false],
  ], 'readGoal load-context: the context, newest binding first, with what is in scope');
  same(goal && goal.constraints, [], 'readGoal load-context: constraints');
  same(readGoal(RUNS['load-context'].answers[1]), goal, 'readGoal: reading an answer twice reads it the same');
});
section('readGoal case-split', () => {
  const goal = readGoal(RUNS['case-split'].answers[4]);
  same(goal && goal.id, 1, 'readGoal case-split: the goal asked about');
  same(goal && goal.context.slice(0, 3).map((e) => [e.name, e.type]),
    [['σ', 'Y → Term X'], ['t', 'ArityOf 𝑆 f → Term Y'], ['f', 'OperationSymbolsOf 𝑆']],
    'readGoal case-split: the node clause\'s variables, newest first');
});
section('readGoal have', () => {
  const goal = readGoal(RUNS.have.answers[1]);
  same(goal && [goal.id, goal.type, goal.have], [0, 'Term X', 'Term X'], 'readGoal have: the type of what was given');
  same(goal && goal.context.slice(0, 2).map((e) => e.name), ['σ', 'x'], 'readGoal have: its context');
});
section('readGoal, not a goal', () => {
  same(readGoal(RUNS['give-refused'].answers[1]), null, 'readGoal: an error is not about a goal');
  same(readGoal(RUNS['load-context'].answers[0]), null, 'readGoal: a load is not about a goal');
});

// ## readAction

section('readAction give-refused', () => {
  /* Sent `None Direct`, as the page sends it, a refused give is answered
   * with one error.  Sent `Indirect`, it was answered with a second `Error`
   * as well, saying Agda could not write the first one's highlighting to a
   * temporary file (the guest has no /tmp); `protocol.js` sends `Direct` for
   * that reason, and the reader would show the first error either way. */
  const answer = RUNS['give-refused'].answers[1];
  same(answer.filter((r) => r.kind === 'DisplayInfo' && r.info.kind === 'Error').length, 1,
    'give-refused fixture: one error, as recorded');
  const action = readAction(answer);
  check(action.error !== null && action.error.message.startsWith('1.1-2: error: [UnequalTerms]'),
    `readAction give-refused: the error shown is ${JSON.stringify(action.error && action.error.message)}`);
  same(action.error && action.error.position, null, 'readAction give-refused: no JumpToError, no position');
  same([action.give, action.split, action.message], [null, null, null], 'readAction give-refused: nothing to do');
});
section('readAction, the other answers', () => {
  same(readAction(RUNS.give.answers[1]),
    { error: null, give: { goal: 0, range: LEAF, text: 'σ x' }, split: null, message: null },
    'readAction give: the text Agda reprinted');
  same(readAction(RUNS.refine.answers[1]).give, { goal: 1, range: NODE, text: 'node f ?' },
    'readAction refine: the text with its new goal');
  same(readAction(RUNS['case-split'].answers[1]), {
    error: null, give: null, message: null,
    split: { goal: 0, range: HOLE, clauses: ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'], variant: 'Function' },
  }, 'readAction case-split: the clauses and their variant');
  same(readAction(RUNS['refine-unknown'].answers[1]),
    { error: null, give: null, split: null, message: 'No single constructor fits; try one of: ℊ, node' },
    'readAction refine-unknown: an answer, not an error');
  same(readAction(RUNS.have.answers[1]), { error: null, give: null, split: null, message: null },
    'readAction have: nothing to do to the text');
});

/* Agda answers `paren` only for a give whose range is not `noRange`
 * (`literally` in `give_gen`, InteractionTop.hs), and the page always sends
 * `noRange`, so no recorded run has one.  The real answer, with its result
 * swapped, stands in. */
section('readAction, paren', () => {
  for (const paren of [true, false]) {
    const swapped = RUNS.give.answers[1].map((r) => (r.kind === 'GiveAction' ? { ...r, giveResult: { paren } } : r));
    same(readAction(swapped).give, { goal: 0, range: LEAF, paren }, `readAction: a give answered paren ${paren}`);
  }
});
section('readAction, IntroNotFound', () => same(
  readAction([{ kind: 'DisplayInfo', info: { kind: 'IntroNotFound' } }]).message,
  'Nothing introduces a goal of this type.', 'readAction: IntroNotFound'));
section('errorOf, nothing', () => same(errorOf([]), null, 'errorOf: no responses, no error'));

console.log(`playground protocol: ${checks} checks over ${Object.keys(RUNS).length} recorded runs`);
if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground protocol: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground protocol: every line is one Agda accepted, and every answer reads as Agda meant it');
