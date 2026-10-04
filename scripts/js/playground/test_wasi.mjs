// File: scripts/js/playground/test_wasi.mjs
//
// The playground's WASI host, `docs/assets/js/playground/wasi.js`: path
// resolution, stdin from a buffer, and the paced stdin that lets one run of
// Agda answer a command before the next is chosen.
//
// The cases that predate the paced stdin follow
// `scripts/js/test_playground_wasi.mjs` of williamdemeo/website at commit
// 952e5eb (MIT; see NOTICE).
//
// The host can fail in two quiet ways.  It can answer with the wrong file:
// the first version on the site this code comes from resolved `a/b/../x` to
// the root's `x` rather than to `a/x`, and a `..` from any directory fd other
// than the root went straight to the root; both returned a real file, and the
// guest read it and carried on.  And it can ask for the next command at the
// wrong moment: Agda reads stdin on a thread of its own that reads ahead, so a
// host that decided at a read would decide before the answer it depends on
// was written, and one that decided at a poll the guest makes while it still
// has work to do would do the same.  The page would then plan its next
// command from half an answer.  Nothing reports either; the run just answers
// a different question.
//
// So this drives the import functions directly, the way the guest calls
// them, on a `WebAssembly.Memory` made here, with every structure laid out by
// hand: iovecs (pointer u32, length u32), subscriptions (48 bytes: userdata
// u64 at 0, tag u8 at 8, then the clock's id u32 at 16 and timeout u64 at 24,
// or the fd u32 at 16) and events (32 bytes: userdata u64 at 0, error u16 at
// 8, type u8 at 10, nbytes u64 at 16, flags u16 at 24).
//
// Usage:  node scripts/js/playground/test_wasi.mjs
//         make playground-test

import { WASI, newDir, newFile } from '../../../docs/assets/js/playground/wasi.js';

const OK = 0, AGAIN = 6, NOENT = 44;
const failures = [];
const expect = (got, want, what) => {
  if (got !== want) failures.push(`${what}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);
};
// A case that throws is reported as a failure of that case, and the rest
// still run.
const section = (what, body) => {
  try { body(); } catch (err) { failures.push(`${what}: threw ${JSON.stringify(String(err && err.message))}`); }
};
const enc = new TextEncoder();
const dec = new TextDecoder();

/** A host over `root` with a fresh one-page memory of its own. */
function host(opts) {
  const wasi = new WASI(opts);
  wasi.memory = new WebAssembly.Memory({ initial: 1 });
  return { wasi, call: wasi.imports().wasi_snapshot_preview1, view: () => new DataView(wasi.memory.buffer) };
}

// ---- path resolution -------------------------------------------------------

// Every file a distinct size, so a size read back names the file it came from.
const bytes = (n) => new Uint8Array(n);
const tree = newDir({
  x: newFile(bytes(1)),                                  // /x
  a: newDir({
    x: newFile(bytes(2)),                                // /a/x
    b: newDir({ x: newFile(bytes(3)), c: newDir() }),    // /a/b/x, /a/b/c
  }),
});
const NAMES = { 1: '/x', 2: '/a/x', 3: '/a/b/x' };
const fs = host({ root: tree });
const PATH = 1024, STAT = 2048, FD_OUT = 4096;

function put(path) {
  const b = enc.encode(path);
  new Uint8Array(fs.wasi.memory.buffer).set(b, PATH);
  return b.length;
}

/** What `path` names relative to directory fd `fd`, as a file name or errno. */
function stat(fd, path) {
  const errno = fs.call.path_filestat_get(fd, 0, PATH, put(path), STAT);
  if (errno !== OK) return errno;
  const size = Number(fs.view().getBigUint64(STAT + 32, true));
  return NAMES[size] ?? `a directory (${size})`;
}

/** Open a directory relative to fd 3, the root preopen, and return its fd. */
function openDir(path) {
  const errno = fs.call.path_open(3, 0, PATH, put(path), 2 /* O_DIRECTORY */, 0n, 0n, 0, FD_OUT);
  if (errno !== OK) throw new Error(`path_open ${path}: errno ${errno}`);
  return fs.view().getUint32(FD_OUT, true);
}

// From the root preopen.
expect(stat(3, 'a/x'), '/a/x', 'plain descent');
expect(stat(3, 'a/b/../x'), '/a/x', '`..` returns to the parent, not the grandparent');
expect(stat(3, 'a/b/c/../../x'), '/a/x', 'two `..` in a row');
expect(stat(3, 'a/b/../../x'), '/x', '`..` back to the root');
expect(stat(3, '/a/b/../x'), '/a/x', 'an absolute path with `..`');
expect(stat(3, '../../x'), '/x', '`..` is clamped at the root');
// POSIX would say ENOTDIR here.  The host answers every failed resolution
// with ENOENT, which the guest treats the same way; refusing is what matters.
expect(stat(3, 'a/x/../x'), NOENT, '`..` through a file is refused');
expect(stat(3, 'a/nope/../x'), NOENT, '`..` through a missing directory is refused');

// From a directory fd the guest opened itself.  A relative path resolves
// against *that* directory, and its `..` has to know its ancestors.
section('opened directories', () => {
  const b = openDir('a/b');
  expect(stat(b, 'x'), '/a/b/x', 'relative to an opened directory');
  expect(stat(b, '../x'), '/a/x', '`..` from an opened directory reaches its real parent');
  expect(stat(b, '../../x'), '/x', 'and its grandparent');
  const c = openDir('a/b/c');
  expect(stat(c, '../x'), '/a/b/x', '`..` from a directory opened three deep');
});

// ---- stdin from a buffer ---------------------------------------------------

// By default a read on fd 0 answers end-of-file at once, which is what a batch
// run sees.  Given a buffer, the host serves it in order, across reads and
// across the iovecs of one read, and then answers end-of-file for as long as
// the guest keeps asking: a host that served the buffer twice, or never
// reached end-of-file, would hang Agda's command loop.
const IOVS = 8192, BUF = 12288, GAP = 128, SENTINEL = 0xaa, NREAD = 2048;

/** One fd_read on fd 0 with one iovec per length: its errno and the text it
 * delivered.
 *
 * The iovec buffers sit GAP bytes apart in a region filled with a sentinel
 * first, and the text is reassembled from each iovec in turn, so a host that
 * ignored a later iovec's base pointer and wrote on from the first would
 * leave that iovec's buffer untouched and dirty the gap instead.  Every byte
 * past the ones an iovec received must still be the sentinel. */
function readStdin(h, lens) {
  const mem = new Uint8Array(h.wasi.memory.buffer), v = h.view();
  mem.fill(SENTINEL, BUF, BUF + lens.length * GAP);
  lens.forEach((l, i) => {
    v.setUint32(IOVS + i * 8, BUF + i * GAP, true);
    v.setUint32(IOVS + i * 8 + 4, l, true);
  });
  v.setUint32(NREAD, 0xdeadbeef, true);
  const errno = h.call.fd_read(0, IOVS, lens.length, NREAD);
  if (errno !== OK) return { errno, text: null };
  let left = v.getUint32(NREAD, true);
  const got = [];
  lens.forEach((l, i) => {
    const base = BUF + i * GAP, take = Math.min(l, left);
    left -= take;
    got.push(...mem.slice(base, base + take));
    if (mem.slice(base + take, base + GAP).some((x) => x !== SENTINEL)) {
      failures.push(`fd_read wrote past the bytes it reported in iovec ${i} (lengths ${lens.join(',')})`);
    }
  });
  return { errno, text: dec.decode(new Uint8Array(got)) };
}
const read = (h, lens) => {
  const r = readStdin(h, lens);
  return r.errno === OK ? r.text : `errno ${r.errno}`;
};

const silent = host({ root: newDir() });
expect(read(silent, [64]), '', 'no stdin option: the first read is end-of-file');

const scripted = host({ root: newDir(), stdin: enc.encode('IOTCM one\nIOTCM two\n') });
expect(read(scripted, [4, 4]), 'IOTCM on', 'a read spanning two iovecs takes the next bytes in order');
expect(read(scripted, [64]), 'e\nIOTCM two\n', 'the next read continues where the last one stopped');
expect(read(scripted, [64]), '', 'then end-of-file');
expect(read(scripted, [64]), '', 'and end-of-file again, not the buffer over');

// ---- the paced stdin -------------------------------------------------------

// `next` is asked for the next command when, and only when, the guest has
// read everything and would block: on the very first read (the first command
// depends on no answer), and after that only at a poll that waits on fd 0
// with no zero-timeout clock in it.  A read with nothing buffered answers
// EAGAIN, and a poll with a zero clock is the guest's scheduler checking in
// while some thread can still run, so neither may ask.
const SUBS = 16384, EVENTS = 20480, NEVENTS = 24576;
const CLOCK = 0, FD_READ = 1, FD_WRITE = 2, HANGUP = 1;
const REALTIME = 0, MONOTONIC = 1;

/** Lay out subscriptions and call poll_oneoff; the errno and the events.
 * Each subscription is {userdata, clock: timeout} or {userdata, read: fd} or
 * {userdata, write: fd}.  The event area is filled with 0xee first, so an
 * event the host did not write cannot pass for one it did. */
function poll(h, subs) {
  const mem = new Uint8Array(h.wasi.memory.buffer), v = h.view();
  mem.fill(0, SUBS, SUBS + subs.length * 48);
  mem.fill(0xee, EVENTS, EVENTS + subs.length * 32);
  subs.forEach((s, i) => {
    const at = SUBS + i * 48;
    v.setBigUint64(at, s.userdata, true);
    if (s.clock !== undefined) {
      v.setUint8(at + 8, CLOCK);
      v.setUint32(at + 16, s.id ?? MONOTONIC, true);
      v.setBigUint64(at + 24, s.clock, true);
      v.setBigUint64(at + 32, 0n, true);                 // precision
      v.setUint16(at + 40, 0, true);                     // relative, not absolute
    } else {
      v.setUint8(at + 8, s.read !== undefined ? FD_READ : FD_WRITE);
      v.setUint32(at + 16, s.read ?? s.write, true);
    }
  });
  const errno = h.call.poll_oneoff(SUBS, EVENTS, subs.length, NEVENTS);
  const n = v.getUint32(NEVENTS, true);
  const events = Array.from({ length: Math.min(n, subs.length) }, (_, k) => {
    const at = EVENTS + k * 32;
    return {
      userdata: v.getBigUint64(at, true),
      error: v.getUint16(at + 8, true),
      type: v.getUint8(at + 10),
      nbytes: v.getBigUint64(at + 16, true),
      flags: v.getUint16(at + 24, true),
    };
  });
  return { errno, n, events };
}
const showEvents = (r) => JSON.stringify(r.events, (_, x) => (typeof x === 'bigint' ? Number(x) : x));
/** An event as the host should write it, and a list of them as showEvents
 * prints one. */
const ev = (userdata, type, nbytes = 0, flags = 0) => ({ userdata, error: 0, type, nbytes, flags });
const events = (...es) => JSON.stringify(es);

/** Write `text` to fd `fd` through fd_write, as the guest does. */
function write(h, fd, text) {
  const b = enc.encode(text), v = h.view();
  new Uint8Array(h.wasi.memory.buffer).set(b, BUF);
  v.setUint32(IOVS, BUF, true);
  v.setUint32(IOVS + 4, b.length, true);
  const errno = h.call.fd_write(fd, IOVS, 1, NREAD);
  if (errno !== OK) throw new Error(`fd_write ${fd}: errno ${errno}`);
}

/** A paced host whose `next` hands out `script` in turn (then null), and
 * records the stdout text it was called with each time. */
function paced(script) {
  const seen = [];
  const queue = [...script];
  const h = host({
    root: newDir(),
    next: (out) => { seen.push(out); const s = queue.shift(); return s === undefined ? null : enc.encode(s); },
  });
  return { ...h, seen };
}

// One conversation, as the page has it: two commands, each planned after the
// answer to the one before is complete, then end-of-file.
section('a paced conversation', () => {
  const p = paced(['IOTCM load\n', 'IOTCM context\n']);
  write(p, 1, 'JSON> ');
  write(p, 2, 'a warning on stderr\n');

  // The first read asks, with the stdout so far and nothing from stderr.
  expect(read(p, [4]), 'IOTC', 'the first read on a paced stdin serves what next returned');
  expect(p.seen.length, 1, 'the first read asks next once');
  expect(p.seen[0], 'JSON> ', 'next is called with the stdout so far, and only stdout');
  expect(read(p, [64]), 'M load\n', 'a read with bytes still buffered serves them');
  expect(p.seen.length, 1, 'a read with bytes still buffered does not ask next');

  // Agda's reader thread reads ahead, before it has answered: EAGAIN.
  expect(read(p, [64]), `errno ${AGAIN}`, 'a read with nothing buffered after the first answers EAGAIN');
  expect(read(p, [64]), `errno ${AGAIN}`, 'and again, for as long as the guest reads');
  expect(p.seen.length, 1, 'a read with nothing buffered after the first does not ask next');

  // The scheduler checks in while a thread can still run: a zero clock.
  write(p, 1, '{"kind":"Status"}\nJSON> ');
  const busy = poll(p, [{ userdata: 11n, clock: 0n }, { userdata: 12n, read: 0 }]);
  expect(busy.errno, OK, 'poll_oneoff with a zero clock answers OK');
  expect(p.seen.length, 1, 'a poll with a zero-timeout clock does not ask next');
  expect(showEvents(busy), events(ev(11, CLOCK)),
    'a poll with a zero clock and a pending stdin reports the clock, and only the clock');

  // Every thread waits: fd 0 alone, no clock.  Now the answer is complete.
  const idle = poll(p, [{ userdata: 21n, read: 0 }]);
  expect(p.seen.length, 2, 'a poll on fd 0 with no zero clock asks next');
  expect(p.seen[1], 'JSON> {"kind":"Status"}\nJSON> ', 'and passes all the stdout written so far');
  expect(showEvents(idle), events(ev(21, FD_READ, 'IOTCM context\n'.length)),
    'that poll reports fd 0 ready, with nbytes the length of the new buffer');
  expect(read(p, [64]), 'IOTCM context\n', 'the next read serves the new buffer');
  expect(read(p, [64]), `errno ${AGAIN}`, 'and the one after it answers EAGAIN again');
  expect(p.seen.length, 2, 'without asking next');

  // next has nothing more: end-of-file, reported as a hangup.
  write(p, 1, '{"kind":"InteractionPoints"}\nJSON> ');
  const end = poll(p, [{ userdata: 31n, read: 0 }]);
  expect(p.seen.length, 3, 'the poll after the last command asks next once more');
  expect(showEvents(end), events(ev(31, FD_READ, 0, HANGUP)),
    'when next returns null the poll reports fd 0 with the hangup flag and no bytes');
  expect(read(p, [64]), '', 'and later reads answer end-of-file (0 bytes, OK)');
  expect(read(p, [64]), '', 'every later read');
  poll(p, [{ userdata: 32n, read: 0 }]);
  expect(p.seen.length, 3, 'next is not asked again once it has ended the input');
  expect(p.wasi.paceError, undefined, 'a next that returned null leaves no paceError');
});

// A clock with a timeout is a wait too: the guest would sleep until it fires
// or stdin has bytes, so with nothing buffered this poll would block, and it
// asks.  A host that took any clock for a busy scheduler would never ask a
// guest that arms a timer whenever it waits, and that guest would poll for
// ever with nothing to read.  (What the host says about the clock itself is
// not pinned: reporting a timer that has not run out as fired is a
// simplification, not a promise.)
section('a poll with a timer', () => {
  const p = paced(['IOTCM load\n', 'IOTCM context\n']);
  read(p, [64]);
  const r = poll(p, [{ userdata: 81n, clock: 1_000_000_000n }, { userdata: 82n, read: 0 }]);
  expect(p.seen.length, 2, 'a poll on fd 0 with a clock that has a timeout asks next');
  const stdin = r.events.filter((e) => e.userdata === 82n);
  expect(showEvents({ events: stdin }), events(ev(82, FD_READ, 'IOTCM context\n'.length)),
    'and reports fd 0 ready with the new buffer\'s length');
});

// Subscriptions other than the one skipped are still reported, packed from
// the first event slot, each with its own userdata.  The clock is on
// REALTIME, whose id is 0, so it has a zero exactly where a read subscription
// keeps its fd: a host that took fd 0 from it without looking at the tag
// would treat the clock as the pending stdin and drop it.
section('a mixed poll', () => {
  const p = paced(['IOTCM load\n']);
  read(p, [64]);                              // the first command, consumed
  const r = poll(p, [
    { userdata: 41n, clock: 0n, id: REALTIME },
    { userdata: 42n, read: 0 },
    { userdata: 43n, write: 1 },
  ]);
  expect(r.n, 2, 'a poll with a zero clock, a pending stdin and stdout reports two events');
  expect(showEvents(r), events(ev(41, CLOCK), ev(43, FD_WRITE)),
    'the clock and stdout, in order, in the first two slots');
  expect(p.seen.length, 1, 'and next is not asked');
});

// A next that throws ends the input rather than the guest, and the error is
// kept for the page: a read that failed would end Agda with its own, less
// useful, complaint about stdin.
section('a next that throws at the first read', () => {
  const boom = new Error('the plan could not be made');
  let calls = 0;
  const h = host({ root: newDir(), next: () => { calls++; throw boom; } });
  const first = readStdin(h, [64]);
  expect(first.errno, OK, 'a read whose next throws still answers OK');
  expect(first.text, '', 'with end-of-file');
  expect(h.wasi.paceError, boom, 'and the thrown error is kept as wasi.paceError');
  const after = poll(h, [{ userdata: 51n, read: 0 }]);
  expect(showEvents(after), events(ev(51, FD_READ, 0, HANGUP)),
    'a poll after a next that threw reports a hangup');
  expect(read(h, [64]), '', 'and a later read answers end-of-file');
  expect(calls, 1, 'a next that threw is not asked again');
});

// The same, when next first throws at a poll rather than at the first read.
section('a next that throws at a poll', () => {
  const boom = new Error('thrown at a poll');
  let calls = 0;
  const h = host({
    root: newDir(),
    next: () => { calls++; if (calls > 1) throw boom; return enc.encode('IOTCM load\n'); },
  });
  read(h, [64]);
  const r = poll(h, [{ userdata: 61n, read: 0 }]);
  expect(r.errno, OK, 'a poll whose next throws still answers OK');
  expect(showEvents(r), events(ev(61, FD_READ, 0, HANGUP)),
    'and reports a hangup on fd 0');
  expect(h.wasi.paceError, boom, 'and keeps the error');
});

// An empty answer is end-of-file too.  Taken as "nothing yet", it would leave
// stdin pending with nothing to wake the guest, and its next poll would ask
// again, for ever.
section('an empty answer', () => {
  let calls = 0;
  const h = host({
    root: newDir(),
    next: () => { calls++; return calls === 1 ? enc.encode('IOTCM load\n') : new Uint8Array(0); },
  });
  read(h, [64]);
  const r = poll(h, [{ userdata: 71n, read: 0 }]);
  expect(showEvents(r), events(ev(71, FD_READ, 0, HANGUP)),
    'an empty answer from next is reported as a hangup');
  poll(h, [{ userdata: 72n, read: 0 }]);
  expect(calls, 2, 'and next is not asked again after it');
});

console.log('playground wasi: 12 path cases through path_filestat_get and path_open, '
  + '5 stdin cases through fd_read, the paced stdin through fd_read and poll_oneoff');
if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground wasi: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground wasi: every path names the file it should, stdin is served once and in order, '
  + 'and next is asked only when the guest would block');
