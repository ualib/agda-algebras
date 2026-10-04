/* File: scripts/js/playground/test_session.mjs
 *
 * The playground's plan for one run of the checker, replayed against the
 * real checker's answers.
 *
 * `session.js` decides each next command from Agda's last answer, and every
 * way it can be wrong is quiet.  A query sent after a failed load makes Agda
 * check the file again for each one (measured: five loads for a load and four
 * queries).  A give whose edit reaches the guest's file one command late is
 * reloaded as the old text, and the page shows goals that are not there.  A
 * plan that reads the first load where it should read the last asks for goals
 * by numbers the reload has given to others.  Agda answers all of these
 * without an error.
 *
 * So the plan is driven here exactly as the WASI host drives it: `next` is
 * called with everything Agda has written so far, which is nothing before the
 * first command and after that a prompt before each command's answers, and
 * the prompt Agda writes as it waits for the next (measured on the real
 * checker; see `fixtures/README.md`).  The answers are the ones Agda wrote in
 * the runs recorded under `fixtures/`, and each of those runs sent the
 * commands this plan should send, so a replay must send exactly the lines
 * Agda was sent and write exactly the texts the run wrote.  A few cases put
 * answers from different runs together, where no single run has the shape a
 * case needs; every answer in them is still one Agda wrote.
 *
 * Usage:  node scripts/js/playground/test_session.mjs
 *         make playground-test
 */
import { readFileSync } from 'node:fs';
import { isDeepStrictEqual } from 'node:util';
import { session } from '../../../docs/assets/js/playground/session.js';

const FIXTURES = 'scripts/js/playground/fixtures';
const PROMPT = 'JSON> ';

const failures = [];
let checks = 0;
const check = (ok, what) => { checks += 1; if (!ok) failures.push(what); };
const same = (got, want, what) => check(isDeepStrictEqual(got, want),
  `${what}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);
/* A plan that throws on a real answer is a failure like any other, and the
 * cases after it still run. */
const section = (name, body) => {
  try { body(); } catch (err) { check(false, `${name}: threw ${err.stack.split('\n').slice(0, 2).join(' ')}`); }
};

/** Two lists of command lines, reported by the first place they part. */
function sameLines(got, want, what) {
  const k = got.findIndex((line, i) => line !== want[i]);
  if (k === -1 && got.length === want.length) { checks += 1; return; }
  const at = k === -1 ? Math.min(got.length, want.length) : k;
  check(false, `${what}: ${got.length} lines sent, expected ${want.length}; line ${at} is `
    + `${JSON.stringify(got[at] ?? null)}, expected ${JSON.stringify(want[at] ?? null)}`);
}

const sources = JSON.parse(readFileSync(`${FIXTURES}/sources.json`, 'utf8'));
const PATH = sources.path;

/** A recorded run: the lines Agda was sent, everything it wrote, and that cut
 * into each command's answer as Agda wrote it, text and all.  The cut is the
 * test's own, so that a fault in the page's reader shows as a wrong plan
 * here and not as a wrong recording. */
function recorded(name) {
  const stdin = readFileSync(`${FIXTURES}/${name}.stdin`, 'utf8').split('\n').filter((l) => l !== '');
  const stdout = readFileSync(`${FIXTURES}/${name}.stdout`, 'utf8');
  const [before, ...rest] = stdout.split(PROMPT);
  check(before === '' && rest.length === stdin.length + 1 && rest[stdin.length] === '',
    `${name}: the recording is not a prompt before each answer and one at the end`);
  return { stdin, stdout, answers: rest.slice(0, stdin.length) };
}
const RUN = Object.fromEntries(['load-context', 'load-error', 'give-refused', 'case-split',
  'refine-unknown', 'have', 'give', 'refine'].map((name) => [name, recorded(name)]));

/** What `next` sees once Agda has answered the first `k` commands. */
const seen = (answers, k) => (k === 0 ? '' : answers.slice(0, k).map((a) => PROMPT + a).join('') + PROMPT);

/** Run a plan over recorded answers, as the host would: ask it for a line
 * whenever Agda waits, until it says there are no more.  Each `write` is kept
 * with the number of lines sent when it happened. */
function drive({ answers, source, action = null, rewrite, limit }) {
  const lines = [];
  const writes = [];
  const plan = session({
    path: PATH, source, action, rewrite, limit, write: (text) => writes.push([lines.length, text]),
  });
  const output = () => seen(answers, Math.min(lines.length, answers.length));
  try {
    for (let i = 0; i < 100; i++) {
      const line = plan.next(seen(answers, lines.length));
      if (line === null) return { lines, writes, plan, output: output(), after: plan.next(output()) };
      lines.push(line);
    }
    check(false, 'a plan that never ended');
  } catch (err) {
    check(false, `next threw after ${lines.length} lines: ${err.stack.split('\n').slice(0, 2).join(' ')}`);
  }
  return { lines, writes, plan, output: output(), after: undefined };
}

const LOAD = RUN['load-context'].stdin[0];
const CONTEXT = (g) => `IOTCM "/work/Graft.agda" None Direct (Cmd_goal_type_context Simplified ${g} noRange "")`;
const ids = (goals) => goals.map((g) => g.id);

// ## Every recorded run, replayed
//
// Each row is the request the page made: the text, and the goal command if
// any.  `writes` names the texts the run wrote into the guest's file, in
// order (keys of `sources.json`); each is what Emacs leaves after the edit,
// spelled out when the fixture was captured, so a match here is the edit
// landing on the right characters in a text whose astral letters (𝑆, 𝓞, 𝓥)
// put Agda's code point positions and JavaScript's offsets apart.

const REPLAYS = [
  ['load-context', 'graft', null, []],
  ['load-error', 'bad', null, []],
  ['give-refused', 'graft', { op: 'give', goal: 0, text: 't' }, []],
  ['case-split', 'graft', { op: 'case', goal: 0, text: 't' }, ['split']],
  ['refine-unknown', 'graft', { op: 'refine', goal: 0, text: '' }, []],
  ['have', 'split', { op: 'have', goal: 0, text: 'σ x' }, []],
  ['give', 'split', { op: 'give', goal: 0, text: 'σ x' }, ['leaf']],
  ['refine', 'split', { op: 'refine', goal: 1, text: 'node f' }, ['refined']],
];
check(sources.graft.indexOf('?') !== [...sources.graft].indexOf('?'),
  'the fixtures no longer have astral characters before the goal, so offsets go untested');

const REPLAYED = {};
for (const [name, source, action, written] of REPLAYS) section(`replay ${name}`, () => {
  const run = RUN[name];
  const got = drive({ answers: run.answers, source: sources[source], action });
  REPLAYED[name] = got;
  sameLines(got.lines, run.stdin, `${name}: the lines sent`);
  same(got.writes.map(([, text]) => text), written.map((key) => sources[key]), `${name}: the texts written`);
  same(got.after, null, `${name}: next, after the run has ended`);
  /* The edit has to be in the guest's file before Agda reads it again, so it
   * is written in the same call that sends the reload (the third line). */
  same(got.writes.map(([k]) => k), written.map(() => 2), `${name}: when the texts were written`);
});

// ## The first command

for (const action of [null, { op: 'give', goal: 0, text: 'σ x' }]) section('the first line', () => {
  same(session({ path: PATH, source: sources.graft, action }).next(''), LOAD,
    `the first line, with action ${JSON.stringify(action)}`);
});

// ## A load that fails ends the run

section('a failed load, with a give waiting', () => {
  /* With a goal command waiting: it is not sent, and neither is anything
   * else, since every command after a failed load would load the file again. */
  const writes = [];
  const plan = session({ path: PATH, source: sources.bad, action: { op: 'give', goal: 0, text: 't' }, write: (t) => writes.push(t) });
  const answers = RUN['load-error'].answers;
  same(plan.next(''), LOAD, 'failed load: the load');
  same(plan.next(seen(answers, 1)), null, 'failed load: nothing after it, not even the waiting give');
  same(plan.next(seen(answers, 1) + '{"kind":"Status"}\n' + PROMPT), null, 'failed load: still nothing, whatever follows');
  same(writes, [], 'failed load: nothing written');
  const result = plan.result(seen(answers, 1));
  same([result.sent, result.action, result.contexts, result.edited], [['load'], null, {}, false],
    'failed load: the result has only the load');
  check(result.load && result.load.error && /UnequalTerms/.test(result.load.error.message),
    'failed load: the result carries the load\'s error');
});

// ## A load with two goals asks for each, in order, and stops

section('a load with two goals', () => {
  /* The load of the split text (two goals), and the two context answers Agda
   * gave for that same text after the case split's reload. */
  const answers = [RUN.have.answers[0], RUN['case-split'].answers[3], RUN['case-split'].answers[4]];
  const got = drive({ answers, source: sources.split });
  sameLines(got.lines, [LOAD, CONTEXT(0), CONTEXT(1)], 'two goals: the lines sent');
  same(got.writes, [], 'two goals: nothing written');
  const result = got.plan.result(got.output);
  same(Object.keys(result.contexts), ['0', '1'], 'two goals: a context for each');
  same(result.action, null, 'two goals: no action');
});
section('the rewrite', () => {
  const got = drive({ answers: [RUN.have.answers[0]], source: sources.split, rewrite: 'Normalised' });
  same(got.lines[1], CONTEXT(0).replace('Simplified', 'Normalised'), 'the context queries use the rewrite asked for');
});

// ## A goal command Agda refuses
//
// The text is left as it is, and every goal of the one load is asked about.
// The refused give's answer is the real one, put after a load with two goals.

section('a refused give, two goals', () => {
  const answers = [RUN.have.answers[0], RUN['give-refused'].answers[1],
    RUN['case-split'].answers[3], RUN['case-split'].answers[4]];
  const got = drive({ answers, source: sources.split, action: { op: 'give', goal: 1, text: 't' } });
  sameLines(got.lines, [LOAD, 'IOTCM "/work/Graft.agda" None Direct (Cmd_give WithoutForce 1 noRange "t")',
    CONTEXT(0), CONTEXT(1)], 'refused give with two goals: the lines sent');
  same(got.writes, [], 'refused give with two goals: nothing written');
  const result = got.plan.result(got.output);
  same([result.edited, result.source], [false, sources.split], 'refused give with two goals: the text is unchanged');
});

// ## A have answers its own goal's context

section('a have at goal 1', () => {
  const answers = [RUN.have.answers[0], RUN.have.answers[1], RUN['case-split'].answers[3]];
  const got = drive({ answers, source: sources.split, action: { op: 'have', goal: 1, text: 'σ x' } });
  sameLines(got.lines, [LOAD,
    'IOTCM "/work/Graft.agda" None Direct (Cmd_goal_type_context_infer Simplified 1 noRange "\\x3c3\\& x")',
    CONTEXT(0)], 'have at goal 1: it skips goal 1, not goal 0');
});

// A have Agda refuses answers with an error and no context, so its goal's
// context is asked for like any other's.  (A defect once: the plan skipped
// the have's goal whatever the answer, and the page showed it bare.)

section('a refused have', () => {
  const answers = [RUN.have.answers[0], RUN['give-refused'].answers[1],
    RUN['case-split'].answers[3], RUN['case-split'].answers[4]];
  const got = drive({ answers, source: sources.split, action: { op: 'have', goal: 1, text: 'nope' } });
  sameLines(got.lines, [LOAD,
    'IOTCM "/work/Graft.agda" None Direct (Cmd_goal_type_context_infer Simplified 1 noRange "nope")',
    CONTEXT(0), CONTEXT(1)], 'refused have: every goal is asked about, its own included');
});

// A have shows its goal in the form the reader chose for every goal.  (A
// defect once: the page's action carries no form, and the have went out
// Simplified while the other goals were Normalised.)

section('a have in the chosen form', () => {
  const answers = [RUN.have.answers[0], RUN.have.answers[1], RUN['case-split'].answers[3]];
  const got = drive({ answers, source: sources.split, rewrite: 'Normalised',
    action: { op: 'have', goal: 1, text: 'σ x' } });
  same(got.lines[1],
    'IOTCM "/work/Graft.agda" None Direct (Cmd_goal_type_context_infer Normalised 1 noRange "\\x3c3\\& x")',
    'a have uses the form the reader chose');
  same(got.lines[2], CONTEXT(0).replace('Simplified', 'Normalised'), 'and so does the context query after it');
});

// ## The limit

for (let limit = 1; limit <= 6; limit++) section(`limit ${limit}`, () => {
  const run = RUN['case-split'];
  const got = drive({ answers: run.answers, source: sources.graft, action: { op: 'case', goal: 0, text: 't' }, limit });
  check(got.lines.length <= limit, `limit ${limit}: ${got.lines.length} lines sent`);
  sameLines(got.lines, run.stdin.slice(0, limit), `limit ${limit}: the lines sent are the run's, as far as they go`);
  same(got.after, null, `limit ${limit}: next, after the run has ended`);
});

// ## What result() reports

section('result case-split', () => {
  const result = REPLAYED['case-split'].plan.result(RUN['case-split'].stdout);
  same(result.source, sources.split, 'result case-split: the text the run ended with');
  same(result.edited, true, 'result case-split: edited');
  same(result.sent, ['load', 'case', 'load', 'context', 'context'], 'result case-split: the operations sent');
  same(result.load && ids(result.load.goals), [0, 1], 'result case-split: the last load\'s goals');
  same(result.load && result.load.goals[0].range.start.pos, 527, 'result case-split: read from the reload, not the first load');
  same(result.firstLoad && result.firstLoad.goals.map((g) => [g.id, g.range.start.pos]), [[0, 523]],
    'result case-split: the first load is kept apart');
  same(Object.keys(result.contexts), ['0', '1'], 'result case-split: contexts by goal');
  same(result.contexts[1] && result.contexts[1].context.slice(0, 3).map((e) => e.name), ['σ', 't', 'f'],
    'result case-split: goal 1\'s context, newest first');
  same(result.action && result.action.split && result.action.split.clauses,
    ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'], 'result case-split: the action\'s clauses');
  same(result.action && [result.action.give, result.action.error, result.action.have], [null, null, null],
    'result case-split: nothing else in the action');
});
section('result have', () => {
  const result = REPLAYED.have.plan.result(RUN.have.stdout);
  same([result.source, result.edited], [sources.split, false], 'result have: the text is unchanged');
  same(result.sent, ['load', 'have', 'context'], 'result have: the operations sent');
  same(result.contexts[0] && [result.contexts[0].type, result.contexts[0].have], ['Term X', 'Term X'],
    'result have: goal 0\'s context is the have\'s answer');
  same(result.contexts[1] && [result.contexts[1].id, result.contexts[1].have], [1, null],
    'result have: goal 1\'s context is its query\'s');
  same(result.action && result.action.have, 'Term X', 'result have: the action carries the type');
});
section('result give', () => {
  const result = REPLAYED.give.plan.result(RUN.give.stdout);
  same([result.source, result.edited], [sources.leaf, true], 'result give: the text after the give');
  same(result.load && result.load.goals.map((g) => [g.id, g.range.start.pos]), [[0, 552]],
    'result give: the reload\'s one goal, renumbered');
  same(result.contexts[0] && result.contexts[0].context.slice(0, 3).map((e) => e.name), ['σ', 't', 'f'],
    'result give: goal 0 is now the node clause\'s');
  same(result.action && result.action.give && result.action.give.text, 'σ x', 'result give: the action');
});
section('result give-refused', () => {
  const result = REPLAYED['give-refused'].plan.result(RUN['give-refused'].stdout);
  same([result.source, result.edited], [sources.graft, false], 'result give-refused: the text is unchanged');
  check(result.action && result.action.error && /UnequalTerms/.test(result.action.error.message),
    'result give-refused: the action carries Agda\'s error');
  same(Object.keys(result.contexts), ['0'], 'result give-refused: the first load\'s goal');
});
section('result load-context', () => {
  const result = REPLAYED['load-context'].plan.result(RUN['load-context'].stdout);
  same([result.action, result.edited, Object.keys(result.contexts)], [null, false, ['0']],
    'result load-context: no action, one context');
});
section('result, nothing sent', () => {
  const result = session({ path: PATH, source: sources.graft }).result('');
  same([result.load, result.firstLoad, result.contexts, result.action, result.sent], [null, null, {}, null, []],
    'result before anything was sent');
});

console.log(`playground session: ${checks} checks, ${REPLAYS.length} recorded runs replayed`);
if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground session: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground session: every run sends what Agda was sent, and writes what Emacs would');
