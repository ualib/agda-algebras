// File: docs/assets/js/playground/checker.js
//
// Provenance: adapted from `docs/javascripts/playground/checker.js` of
// williamdemeo/website at commit 952e5eb (MIT, Copyright 2026 William DeMeo;
// see NOTICE).  `inflating`, `boot` and `mount` are that file's, with its
// comments; `run`, which replaces its batch `check`, is new.
//
// The worker that runs Agda.  It lives off the main thread because a run is a
// synchronous call into WebAssembly that takes from a fraction of a second to
// several seconds, depending on how much of the library the exercise imports,
// and a page that froze for that long would be a worse demonstration than no
// page.
//
// Three commands, and the page issues them in this order:
//
//   boot   fetch and compile the checker.  Once per visit; the module is
//          reused by every run afterwards.
//   mount  fetch and unpack one filesystem image.  Several exercises can
//          share an image, and a second mount of one is answered from
//          memory: the page asks only once, and this holds if it does not.
//   run    load the reader's text with `--interaction-json`, do what the
//          reader asked at a goal, if anything, and report every goal's type
//          and context.  `session.js` plans the commands; see it for the plan.
//
// A WASI *command* module exits when `main` returns, so its instance cannot
// be reused: every run builds a fresh instance over a fresh copy of the
// unpacked image.  That is why nothing a reader types outlives their run.
//
// Each image carries the argv it was built under, in `agda.argv`, and this
// worker runs that and nothing else, with `--interaction-json` added.
// Interfaces are accepted only when the options in force match the ones they
// were built under, and a mismatch is silent: the run simply re-checks the
// library from source and takes many times as long.  Reading the argv out of
// the image is what makes that impossible to get wrong from here.

import { WASI, newFile } from './wasi.js';
import { untar, cloneTree } from './tar.js';
import { session } from './session.js';

let agda = null;                        // the compiled module, fetched once
const images = new Map();               // url -> { root, argv }

// A gzip member starts `1f 8b`; a WebAssembly module starts `00 61 73 6d`.
const GZIP_MAGIC = [0x1f, 0x8b];

/** Inflate a response if it arrives gzipped, reporting progress under `label`.
 *
 * The assets are published pre-gzipped and served as `application/gzip`, so
 * the normal case is that this inflates them.  A host that decided to
 * decompress them on the way out would hand us the raw bytes instead, with
 * no `content-encoding` left to notice, so the first two bytes decide rather
 * than the file extension or a header.  Measured against both.
 *
 * A stream promises nothing about where its chunks fall, and a server that
 * flushed one byte and sent the rest 150 ms later delivered a one-byte first
 * chunk (measured, review of website#146).  Deciding on that chunk alone read
 * `1f` and stopped, and the gzip went to `compileStreaming` as if it were a
 * module: "expected magic word 00 61 73 6d, found 1f 8b".  So reads are held
 * until two bytes are in hand or the body ends, and replayed in order ahead
 * of everything after them.  Exported so a test can hand it a stream cut
 * exactly there.
 */
export async function inflating(res, label) {
  const total = Number(res.headers.get('content-length') || 0);
  let got = 0;
  const report = () => postMessage({ type: 'progress', label, got, total });

  const reader = res.body.getReader();
  const held = [];
  let seen = 0;
  let ended = false;
  while (seen < 2 && !ended) {
    const next = await reader.read();
    if (next.done) ended = true;
    else { held.push(next.value); seen += next.value.byteLength; }
  }
  const magic = new Uint8Array(2);
  for (let at = 0, i = 0; at < 2 && i < held.length; i++) {
    const take = Math.min(held[i].byteLength, 2 - at);
    magic.set(held[i].subarray(0, take), at);
    at += take;
  }
  const gzipped = seen >= 2 && magic[0] === GZIP_MAGIC[0] && magic[1] === GZIP_MAGIC[1];

  const wire = new ReadableStream({
    start(c) {
      for (const chunk of held) { got += chunk.byteLength; report(); c.enqueue(chunk); }
      if (ended) c.close();
    },
    async pull(c) {
      const next = await reader.read();
      if (next.done) return c.close();
      got += next.value.byteLength;
      report();
      c.enqueue(next.value);
    },
    cancel(reason) { return reader.cancel(reason); },
  });

  return {
    body: gzipped ? wire.pipeThrough(new DecompressionStream('gzip')) : wire,
    bytes: () => got,
  };
}

async function fetchInflating(url, label) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`${url}: HTTP ${res.status}`);
  return inflating(res, label);
}

async function boot(url) {
  const started = performance.now();
  const wire = await fetchInflating(url, 'checker');
  // Compiling from the stream rather than from a buffer: the decompressed
  // module is 31 MB, and there is no reason to hold all of it at once.
  agda = await WebAssembly.compileStreaming(
    new Response(wire.body, { headers: { 'content-type': 'application/wasm' } }));
  return { ms: performance.now() - started, bytes: wire.bytes() };
}

async function mount(url) {
  if (images.has(url)) return { ms: 0, bytes: 0 };
  const started = performance.now();
  const wire = await fetchInflating(url, 'library');
  const root = untar(new Uint8Array(await new Response(wire.body).arrayBuffer()));
  const argv = root.entries.get('agda.argv');
  if (argv === undefined) throw new Error(`${url}: the image carries no agda.argv`);
  images.set(url, {
    root,
    argv: new TextDecoder().decode(argv.data).split('\n').filter((a) => a !== ''),
  });
  return { ms: performance.now() - started, bytes: wire.bytes() };
}

// A file name the page may ask for: a module name, as the exercise files are.
const FILE = /^[A-Z][A-Za-z0-9]*\.agda$/;

/** One run over the reader's text.  `file` is the exercise's file name
 * (`Graft.agda`), `action` null or a goal command, `rewrite` the form for
 * goal types.  Returns the session's reading of the run and what it cost. */
async function run({ url, file, source, action, rewrite }) {
  const image = images.get(url);
  if (image === undefined) throw new Error(`${url}: not mounted`);
  if (agda === null) throw new Error('the checker is not loaded');
  if (!FILE.test(file)) throw new Error(`not an exercise file: ${file}`);
  const encode = (text) => new TextEncoder().encode(text);

  const root = cloneTree(image.root);
  const work = root.entries.get('work').entries;
  work.set(file, newFile(encode(source)));
  const plan = session({
    path: `/work/${file}`,
    source,
    action,
    rewrite,
    write: (text) => work.set(file, newFile(encode(text))),
  });
  const marks = [];
  const started = performance.now();
  const wasi = new WASI({
    args: [...image.argv, '--interaction-json'],
    env: {
      PWD: '/work', HOME: '/home',
      Agda_datadir: '/data', AGDA_DIR: '/home/.config/agda',
    },
    root,
    next: (output) => {
      marks.push(performance.now() - started);
      const line = plan.next(output);
      return line === null ? null : encode(line + '\n');
    },
  });
  const exit = await wasi.run(agda);
  const ms = performance.now() - started;
  // Agda writes absolute paths into its messages, and `/work/` is an
  // implementation detail of the filesystem this page invents.  The text
  // itself is left alone: a reader may write `/work/` in a comment.
  const clean = (s) => s.replace(/\/work\//g, '');
  const { source: text, ...found } = plan.result(wasi.text('out'));
  return {
    exit,
    ms,
    // When each command was sent, from the start of the run: the first is
    // the load, so the second mark is what the load cost.
    marks,
    // The instance's memory after the run, which is its peak: WebAssembly
    // memory grows and never shrinks.  Reported so that the figures in
    // ADR-011 are ones a browser gave rather than ones inferred elsewhere.
    memory: wasi.memory.buffer.byteLength,
    crossOriginIsolated: self.crossOriginIsolated === true,
    stderr: clean(wasi.text('err')),
    paceError: wasi.paceError ? String(wasi.paceError) : null,
    ...JSON.parse(clean(JSON.stringify(found))),
    source: text,
  };
}

globalThis.onmessage = async (event) => {
  const message = event.data;
  try {
    const result =
      message.cmd === 'boot' ? await boot(message.url)
      : message.cmd === 'mount' ? await mount(message.url)
      : message.cmd === 'run' ? await run(message)
      : (() => { throw new Error(`unknown command: ${message.cmd}`); })();
    postMessage({ id: message.id, type: 'ok', ...result });
  } catch (err) {
    postMessage({
      id: message.id, type: 'error',
      message: String((err && err.message) || err),
    });
  }
};
