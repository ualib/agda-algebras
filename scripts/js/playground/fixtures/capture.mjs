/* File: scripts/js/playground/fixtures/capture.mjs
 *
 * Records what the real checker answers, once, so that `test_protocol.mjs`
 * and `test_session.mjs` can hold the page's reader to Agda's own output
 * rather than to output written by hand.  A hand-written answer encodes the
 * author's idea of the protocol, which is exactly what the tests exist to
 * check; these are what Agda 2.8.0, compiled to WebAssembly, wrote.
 *
 * Each run is one process over a fresh copy of the image, with stdin paced the
 * way the page paces it (`next` in `wasi.js`): the next command is handed over
 * only when Agda waits for one.  The commands are spelled out below, not made
 * by `protocol.js`, so that a fixture records what Agda accepted from a line
 * the page's code did not write; `test_protocol.mjs` then checks that
 * `command()` writes the same lines.  Where a run rewrites the file before a
 * reload, the new text is spelled out too, as Emacs would leave it, and the
 * run fails unless Agda's answer says the same.
 *
 * Usage:  node scripts/js/playground/fixtures/capture.mjs AGDA_WASM TERMS_IMAGE [OUT]
 *
 * AGDA_WASM is the checker, `agda-opt.wasm` from agda-web/agda-wasm-dist or
 * the gzipped copy `make playground` writes, TERMS_IMAGE the `terms.tar.gz`
 * image that target builds, and OUT the directory to write into (this one by
 * default).  README.md says more.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { WASI, newFile } from '../../../../docs/assets/js/playground/wasi.js';
import { untar, cloneTree } from '../../../../docs/assets/js/playground/tar.js';

const HERE = dirname(fileURLToPath(import.meta.url));
const [wasmPath, imagePath, outDir = HERE] = process.argv.slice(2);
if (!wasmPath || !imagePath) {
  console.error('usage: node capture.mjs AGDA_WASM TERMS_IMAGE [OUT]');
  process.exit(2);
}

/* How many `HighlightingInfo` lines to keep in each command's answers.  A load
 * of Graft writes fifteen, the first two of them 5 KB and 8 KB; one shows the
 * shape, and the rest would only make the files large. */
const KEEP_HIGHLIGHTING = 1;

const FILE = 'Graft.agda';
const PATH = `/work/${FILE}`;

/* A Haskell string literal, as agda2-mode writes one, for the texts below
 * (no control characters among them).  Written out here rather than
 * imported, for the reason in the header. */
const hs = (s) => '"' + [...s].map((ch) => {
  const c = ch.codePointAt(0);
  if (ch === '"' || ch === '\\') return '\\' + ch;
  if (c < 128) return ch;
  return `\\x${c.toString(16)}\\&`;
}).join('') + '"';

const P = hs(PATH);
const LOAD = `IOTCM ${P} NonInteractive Direct (Cmd_load ${P} [])`;
const quiet = (body) => `IOTCM ${P} None Direct (${body})`;
const CONTEXT = (g) => quiet(`Cmd_goal_type_context Simplified ${g} noRange ""`);
const HAVE = (g, e) => quiet(`Cmd_goal_type_context_infer Simplified ${g} noRange ${hs(e)}`);
const GIVE = (g, e) => quiet(`Cmd_give WithoutForce ${g} noRange ${hs(e)}`);
const REFINE = (g, e) => quiet(`Cmd_refine_or_intro False ${g} noRange ${hs(e)}`);
const CASE = (g, e) => quiet(`Cmd_make_case ${g} noRange ${hs(e)}`);

/* The texts.  `graft` is the exercise as the page ships it; the others are
 * what Emacs leaves after each edit, spelled out. */
const graft = readFileSync(join(HERE, '../../../../docs/playground', FILE), 'utf8');
const HOLE = 'graft t σ = ?';
if (!graft.includes(HOLE)) throw new Error(`${FILE} no longer ends with \`${HOLE}\``);
const SPLIT = ['graft (ℊ x) σ = ?', 'graft (node f t) σ = ?'];
const REFINED = 'node f ?';
const SOURCES = {
  graft,
  bad: graft.replace(HOLE, 'graft t σ = t'),
  split: graft.replace(HOLE, SPLIT.join('\n')),
  leaf: graft.replace(HOLE, ['graft (ℊ x) σ = σ x', SPLIT[1]].join('\n')),
  refined: graft.replace(HOLE, [SPLIT[0], `graft (node f t) σ = ${REFINED}`].join('\n')),
};

/* One step is a command, or a string naming the text to write into the
 * file before the next command.  Each run is the sequence the page's plan
 * (`session.js`) sends for that request, so that a fixture is also a whole
 * run that `test_session.mjs` can replay: the refused give is followed by a
 * context query for the first load's goal, the `have` skips the goal it
 * answers, and every reload by a query for each goal it leaves. */
const RUNS = {
  'load-context': ['graft', [LOAD, CONTEXT(0)]],
  'load-error': ['bad', [LOAD]],
  'give-refused': ['graft', [LOAD, GIVE(0, 't'), CONTEXT(0)]],
  'case-split': ['graft', [LOAD, CASE(0, 't'), 'split', LOAD, CONTEXT(0), CONTEXT(1)]],
  'refine-unknown': ['graft', [LOAD, REFINE(0, ''), CONTEXT(0)]],
  'have': ['split', [LOAD, HAVE(0, 'σ x'), CONTEXT(1)]],
  'give': ['split', [LOAD, GIVE(0, 'σ x'), 'leaf', LOAD, CONTEXT(0)]],
  'refine': ['split', [LOAD, REFINE(1, 'node f'), 'refined', LOAD, CONTEXT(0), CONTEXT(1)]],
};

/* The checker as `make playground` leaves it is gzipped; as agda-wasm-dist
 * ships it, it is not.  Either will do. */
const wasm = readFileSync(wasmPath);
const agda = await WebAssembly.compile(wasm[0] === 0x1f && wasm[1] === 0x8b ? gunzipSync(wasm) : wasm);
const image = untar(new Uint8Array(gunzipSync(readFileSync(imagePath))));
const argv = new TextDecoder().decode(image.entries.get('agda.argv').data)
  .split('\n').filter(Boolean);
const enc = (t) => new TextEncoder().encode(t);

async function run(source, steps) {
  const root = cloneTree(image);
  const work = root.entries.get('work').entries;
  work.set(FILE, newFile(enc(SOURCES[source])));
  const sent = [];
  let k = 0;
  const next = () => {
    while (k < steps.length && !steps[k].startsWith('IOTCM')) {
      work.set(FILE, newFile(enc(SOURCES[steps[k]])));
      k += 1;
    }
    if (k >= steps.length) return null;
    sent.push(steps[k]);
    return enc(steps[k++] + '\n');
  };
  const wasi = new WASI({
    args: [...argv, '--interaction-json'],
    env: { PWD: '/work', HOME: '/home', Agda_datadir: '/data', AGDA_DIR: '/home/.config/agda' },
    root, next,
  });
  const status = await wasi.run(agda);
  if (status !== 0) throw new Error(`agda exited ${status}: ${wasi.text('err')}`);
  if (wasi.paceError) throw wasi.paceError;
  return { sent, out: wasi.text('out') };
}

const kindOf = (line) => { try { return JSON.parse(line).kind; } catch { return null; } };

/** Drop all but the first few HighlightingInfo lines after each prompt.  A
 * dropped line keeps its prompts, if it carries any: they say where the
 * answers to a command begin, and losing one would shift every answer after
 * it onto the wrong command. */
function trim(out) {
  let kept = 0;
  let dropped = 0;
  const lines = out.split('\n').flatMap((line) => {
    const prompts = line.match(/^(JSON> )*/)[0];
    if (prompts) kept = 0;
    if (kindOf(line.slice(prompts.length)) !== 'HighlightingInfo') return [line];
    kept += 1;
    if (kept <= KEEP_HIGHLIGHTING) return [line];
    dropped += 1;
    return prompts ? [prompts] : [];
  });
  return { text: lines.join('\n'), dropped };
}

/* What a run must have answered for its fixture to mean what its name says. */
const lines = (out) => out.split('\n').map((l) => l.replace(/^(JSON> )+/, '')).filter(Boolean)
  .map((l) => { try { return JSON.parse(l); } catch { return { kind: 'Text', text: l }; } });
const displays = (out, kind) => lines(out).filter((r) => r.kind === 'DisplayInfo' && r.info.kind === kind);
const EXPECT = {
  'load-context': (o) => displays(o, 'GoalSpecific').length === 1,
  'load-error': (o) => displays(o, 'Error').length === 1,
  'give-refused': (o) => /UnequalTerms/.test(displays(o, 'Error')[0].info.error.message)
    && !lines(o).some((r) => r.kind === 'GiveAction'),
  'case-split': (o) => lines(o).some((r) => r.kind === 'MakeCase'
    && JSON.stringify(r.clauses) === JSON.stringify(SPLIT)),
  'refine-unknown': (o) => displays(o, 'IntroConstructorUnknown').length === 1,
  'have': (o) => displays(o, 'GoalSpecific').some((r) => r.info.goalInfo.typeAux.kind === 'GoalAndHave'),
  'give': (o) => lines(o).some((r) => r.kind === 'GiveAction' && r.giveResult.str === 'σ x'),
  'refine': (o) => lines(o).some((r) => r.kind === 'GiveAction' && r.giveResult.str === REFINED),
};

writeFileSync(join(outDir, 'sources.json'), JSON.stringify({ path: PATH, ...SOURCES }, null, 2) + '\n');
for (const [name, [source, steps]] of Object.entries(RUNS)) {
  const t = performance.now();
  const { sent, out } = await run(source, steps);
  if (!EXPECT[name](out)) throw new Error(`${name}: Agda did not answer as the fixture's name says`);
  const { text, dropped } = trim(out);
  writeFileSync(join(outDir, `${name}.stdin`), sent.map((l) => l + '\n').join(''));
  writeFileSync(join(outDir, `${name}.stdout`), text);
  console.log(`${name}: ${sent.length} commands, ${text.length} bytes kept, `
    + `${dropped} HighlightingInfo lines dropped, ${Math.round(performance.now() - t)} ms`);
}
