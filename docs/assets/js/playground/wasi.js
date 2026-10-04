// File: docs/assets/js/playground/wasi.js
//
// Provenance: `docs/javascripts/playground/wasi.js` of williamdemeo/website at
// commit 952e5eb (MIT, Copyright 2026 William DeMeo; see NOTICE).  One thing
// is added here, the paced stdin (`next`, below); the rest of the code is
// unchanged.
//
// A WASI preview-1 host for one specific guest: the `agda` command module
// from agda-web/agda-wasm-dist, run with an in-memory filesystem.  It
// implements the 24 imports that module declares and nothing else; anything
// outside that set is not stubbed, it is absent, so a guest that needed more
// would fail to instantiate rather than misbehave.
//
// The filesystem is a tree of plain objects, built before the run and
// discarded after it.  Nothing touches the page's storage.
//
// ## A paced stdin
//
// `--interaction-json` makes Agda read one command per line from stdin and
// answer each on stdout.  A page that knows its whole command sequence in
// advance can hand it a buffer and end-of-file (`stdin`, below; measured in
// website#148).  The playground here needs more than that: whether to ask for
// a goal's context depends on whether the load succeeded and on which goals
// it found, and a give is followed by a reload of the text it produced.  The
// next command depends on the last answer.
//
// Blocking for it is not available: a read on the page's own thread cannot
// wait for anything, and waiting in a worker needs a SharedArrayBuffer and so
// cross-origin isolation.  It is not needed either, because the next command
// is computed from Agda's output alone, synchronously, in this host.  What
// has to be right is *when* it is computed, and two measurements decided it
// (2026-10-04, this guest under node 22 and in Chromium 153), as follows:
//
//   +  Agda reads stdin on a thread of its own, which reads ahead: it asked
//      for the second line before it had written a byte of the answer to the
//      first.  So a read cannot be the moment to decide.
//   +  The guest marks stdin non-blocking, and a read answered `EAGAIN`
//      blocks only the reading thread.  GHC's scheduler then polls the
//      descriptor through `poll_oneoff`: with a zero timeout (a clock
//      subscription of 0) while some thread can still run, and with no clock
//      at all once every thread is waiting.  The second kind comes only when
//      the previous command's answer is complete, and that is the moment.
//
// So with `next`, a read with nothing buffered answers `EAGAIN` (except the
// very first, which needs no answer to decide), and a `poll_oneoff` that
// would block on stdin asks `next` for more.  A load followed by one context
// query per goal then runs as one process, and a load that fails is followed
// by end-of-file rather than by queries that each repeat it (Agda re-checks
// an unloaded file for every command that needs one: measured, five loads
// for a load and four queries).

const OK = 0;
const E = {
  ACCES: 2, AGAIN: 6, BADF: 8, EXIST: 20, FAULT: 21, INVAL: 28, ISDIR: 31,
  NOENT: 44, NOSYS: 52, NOTDIR: 54, NOTEMPTY: 55, PERM: 63, SPIPE: 70,
  NOTCAPABLE: 76,
};
const FILETYPE = { DIR: 3, REG: 4, CHR: 2 };
const RIGHTS_ALL = 0xffffffffffffffffn;

export function newDir(entries = {}) {
  const d = { type: FILETYPE.DIR, entries: new Map() };
  for (const [k, v] of Object.entries(entries)) d.entries.set(k, v);
  return d;
}
export function newFile(data) {
  return { type: FILETYPE.REG, data: data instanceof Uint8Array ? data : new Uint8Array(data) };
}

// Resolve `path` against a directory, given as its *chain*: every node from
// the root down to it.  Returns the chain of the result, or null.
//
// A chain rather than a node, because `..` needs the parent and a node does
// not know its own.  The first version kept a stack of the parents it had
// descended through and read the new top after popping, which is one level
// too high: `a/b/../x` resolved to the root's `x` rather than to `a/x`, and a
// `..` from any directory fd other than the root had no stack at all and
// jumped straight to the root.  Both returned a real file, just the wrong one.
//
// `..` is clamped at the root, so the guest cannot climb out of its tree, and
// it is refused through anything that is not a directory, as POSIX refuses it.
function resolve(root, base, path) {
  const chain = path.startsWith('/') ? [root] : base.slice();
  for (const part of path.split('/')) {
    if (part === '' || part === '.') continue;
    const here = chain[chain.length - 1];
    if (here.type !== FILETYPE.DIR) return null;
    if (part === '..') { if (chain.length > 1) chain.pop(); continue; }
    const next = here.entries.get(part);
    if (next === undefined) return null;
    chain.push(next);
  }
  return chain;
}

function walk(root, base, path) {
  const chain = resolve(root, base, path);
  return chain === null ? null : chain[chain.length - 1];
}

// The parent directory of `path` plus the final component, for create,
// unlink and rename.  Returns null if the parent does not exist.
function walkParent(root, base, path) {
  const parts = path.split('/').filter((p) => p !== '' && p !== '.');
  if (parts.length === 0) return null;
  const name = parts.pop();
  if (name === '..') return null;
  const dir = walk(root, base, (path.startsWith('/') ? '/' : '') + parts.join('/'));
  if (dir === null || dir.type !== FILETYPE.DIR) return null;
  return { dir, name };
}

class Exit extends Error {
  constructor(code) { super(`exit ${code}`); this.code = code; }
}

export class WASI {
  // opts: { args, env, root, stdin, next }.  The guest's working directory is
  // not an option here: wasi-libc takes it from `PWD` in the environment.
  //
  // `stdin` is a Uint8Array the guest reads in order and then sees
  // end-of-file on.  By default it is empty, so the first read on fd 0
  // answers end-of-file, which is what a batch run sees.  A scripted
  // interaction session (`--interaction-json`) is a fixed command stream
  // followed by end-of-file.
  //
  // `next` paces stdin instead (see the header): a function called with the
  // guest's stdout so far, whenever the guest has read everything it was given
  // and is waiting for more, which returns the next bytes, or null for
  // end-of-file.  It runs inside the guest's own call into the host, so it
  // may change the filesystem before it answers, and the guest sees the
  // change on its next read of the file.
  constructor(opts) {
    // Both would make the first read past the buffer ask `next` at a read,
    // which is the moment the header says cannot be trusted.
    if (opts.stdin && opts.next) throw new Error('wasi: give stdin or next, not both');
    this.args = opts.args ?? ['agda'];
    this.env = opts.env ?? {};
    this.root = opts.root ?? newDir();
    this.stdout = [];
    this.stderr = [];
    this.exitCode = null;
    this.memory = null;
    // 0,1,2 are the standard streams; 3 is the one preopen, "/".
    this.fds = [
      {
        kind: 'stdin', node: newFile(opts.stdin ?? new Uint8Array(0)), offset: 0,
        next: opts.next ?? null, asked: false, ended: !opts.next,
      },
      { kind: 'stdout' }, { kind: 'stderr' },
      { kind: 'dir', node: this.root, chain: [this.root], path: '/', preopen: '/', offset: 0 },
    ];
  }

  get view() { return new DataView(this.memory.buffer); }
  get bytes() { return new Uint8Array(this.memory.buffer); }

  str(ptr, len) { return new TextDecoder().decode(this.bytes.subarray(ptr, ptr + len)); }

  // The chain of the directory `fd` names, which is what a relative path is
  // resolved against.
  baseFor(fd) {
    const f = this.fds[fd];
    if (!f || f.kind !== 'dir') return null;
    return f.chain;
  }

  // ---- the import object -------------------------------------------------

  imports() {
    const self = this;
    const w = (fn) => (...a) => {
      try { return fn(...a); }
      catch (err) { if (err instanceof Exit) throw err; return E.INVAL; }
    };
    return {
      wasi_snapshot_preview1: {
        args_sizes_get: w((cnt, size) => {
          const v = self.view;
          v.setUint32(cnt, self.args.length, true);
          v.setUint32(size, self.args.reduce((n, a) => n + a.length + 1, 0), true);
          return OK;
        }),
        args_get: w((ptrs, buf) => self.writeStrings(self.args, ptrs, buf)),
        environ_sizes_get: w((cnt, size) => {
          const e = self.envList();
          const v = self.view;
          v.setUint32(cnt, e.length, true);
          v.setUint32(size, e.reduce((n, a) => n + a.length + 1, 0), true);
          return OK;
        }),
        environ_get: w((ptrs, buf) => self.writeStrings(self.envList(), ptrs, buf)),

        clock_time_get: w((id, precision, out) => {
          self.view.setBigUint64(out, self.nowNs(), true);
          return OK;
        }),

        fd_close: w((fd) => {
          if (!self.fds[fd]) return E.BADF;
          if (fd > 3) self.fds[fd] = null;
          return OK;
        }),
        fd_fdstat_get: w((fd, out) => {
          const f = self.fds[fd];
          if (!f) return E.BADF;
          const type = f.kind === 'dir' ? FILETYPE.DIR
            : f.kind === 'file' ? FILETYPE.REG : FILETYPE.CHR;
          const v = self.view;
          v.setUint8(out, type);
          v.setUint16(out + 2, 0, true);
          v.setBigUint64(out + 8, RIGHTS_ALL, true);
          v.setBigUint64(out + 16, RIGHTS_ALL, true);
          return OK;
        }),
        fd_fdstat_set_flags: w(() => OK),
        fd_filestat_get: w((fd, out) => {
          const f = self.fds[fd];
          if (!f) return E.BADF;
          if (f.kind === 'dir' || f.kind === 'file') return self.writeFilestat(f.node, out);
          return self.writeFilestat({ type: FILETYPE.CHR, data: new Uint8Array(0) }, out);
        }),
        fd_filestat_set_size: w((fd, size) => {
          const f = self.fds[fd];
          if (!f || f.kind !== 'file') return E.BADF;
          const n = Number(size);
          const next = new Uint8Array(n);
          next.set(f.node.data.subarray(0, Math.min(n, f.node.data.length)));
          f.node.data = next;
          return OK;
        }),
        fd_prestat_get: w((fd, out) => {
          const f = self.fds[fd];
          if (!f || f.preopen === undefined) return E.BADF;
          const v = self.view;
          v.setUint8(out, 0);
          v.setUint32(out + 4, new TextEncoder().encode(f.preopen).length, true);
          return OK;
        }),
        fd_prestat_dir_name: w((fd, ptr, len) => {
          const f = self.fds[fd];
          if (!f || f.preopen === undefined) return E.BADF;
          const b = new TextEncoder().encode(f.preopen);
          if (b.length > len) return E.INVAL;
          self.bytes.set(b, ptr);
          return OK;
        }),
        fd_read: w((fd, iovs, n, out) => {
          const f = self.fds[fd];
          if (!f) return E.BADF;
          // stdin reads like a file: its buffer in order, then zero bytes,
          // which is end-of-file.  A paced stdin with nothing buffered asks
          // `next` on its first read, which depends on no answer, and after
          // that says "not yet" and leaves the asking to `poll_oneoff`.
          if (f.kind !== 'file' && f.kind !== 'stdin') return E.BADF;
          if (f.kind === 'stdin' && !f.ended && f.offset >= f.node.data.length) {
            if (f.asked) return E.AGAIN;
            self.ask();
          }
          let read = 0;
          const v = self.view;
          for (let i = 0; i < n; i++) {
            const p = v.getUint32(iovs + i * 8, true);
            const l = v.getUint32(iovs + i * 8 + 4, true);
            const chunk = f.node.data.subarray(f.offset, f.offset + l);
            self.bytes.set(chunk, p);
            f.offset += chunk.length;
            read += chunk.length;
            if (chunk.length < l) break;
          }
          v.setUint32(out, read, true);
          return OK;
        }),
        fd_write: w((fd, iovs, n, out) => {
          const f = self.fds[fd];
          if (!f) return E.BADF;
          let written = 0;
          const v = self.view;
          for (let i = 0; i < n; i++) {
            const p = v.getUint32(iovs + i * 8, true);
            const l = v.getUint32(iovs + i * 8 + 4, true);
            const chunk = self.bytes.slice(p, p + l);
            if (f.kind === 'stdout') self.stdout.push(chunk);
            else if (f.kind === 'stderr') self.stderr.push(chunk);
            else if (f.kind === 'file') self.writeInto(f, chunk);
            else return E.BADF;
            written += l;
          }
          v.setUint32(out, written, true);
          return OK;
        }),
        fd_seek: w((fd, offset, whence, out) => {
          const f = self.fds[fd];
          if (!f) return E.BADF;
          if (f.kind !== 'file') return E.SPIPE;
          const off = Number(offset);
          f.offset = whence === 0 ? off : whence === 1 ? f.offset + off : f.node.data.length + off;
          if (f.offset < 0) { f.offset = 0; return E.INVAL; }
          self.view.setBigUint64(out, BigInt(f.offset), true);
          return OK;
        }),
        fd_readdir: w((fd, buf, len, cookie, out) => {
          const f = self.fds[fd];
          if (!f || f.kind !== 'dir') return E.BADF;
          const names = ['.', '..', ...f.node.entries.keys()];
          const enc = new TextEncoder();
          let off = 0;
          for (let i = Number(cookie); i < names.length; i++) {
            const name = names[i];
            const nb = enc.encode(name);
            const type = name === '.' || name === '..' ? FILETYPE.DIR : f.node.entries.get(name).type;
            if (off + 24 > len) break;
            const v = self.view;
            v.setBigUint64(buf + off, BigInt(i + 1), true);
            v.setBigUint64(buf + off + 8, BigInt(i + 1), true);
            v.setUint32(buf + off + 16, nb.length, true);
            v.setUint8(buf + off + 20, type);
            v.setUint8(buf + off + 21, 0); v.setUint8(buf + off + 22, 0); v.setUint8(buf + off + 23, 0);
            off += 24;
            const room = Math.min(nb.length, len - off);
            self.bytes.set(nb.subarray(0, room), buf + off);
            off += room;
            if (room < nb.length) break;
          }
          self.view.setUint32(out, off, true);
          return OK;
        }),

        path_create_directory: w((fd, ptr, len) => {
          const base = self.baseFor(fd);
          if (!base) return E.BADF;
          const at = walkParent(self.root, base, self.str(ptr, len));
          if (!at) return E.NOENT;
          if (at.dir.entries.has(at.name)) return E.EXIST;
          at.dir.entries.set(at.name, newDir());
          return OK;
        }),
        path_filestat_get: w((fd, flags, ptr, len, out) => {
          const base = self.baseFor(fd);
          if (!base) return E.BADF;
          const node = walk(self.root, base, self.str(ptr, len));
          if (node === null) return E.NOENT;
          return self.writeFilestat(node, out);
        }),
        path_open: w((fd, dirflags, ptr, len, oflags, rb, ri, fdflags, out) => {
          const base = self.baseFor(fd);
          if (!base) return E.BADF;
          const path = self.str(ptr, len);
          const chain = resolve(self.root, base, path);
          let node = chain === null ? null : chain[chain.length - 1];
          if (node === null) {
            if (!(oflags & 1)) return E.NOENT;            // O_CREAT
            const at = walkParent(self.root, base, path);
            if (!at) return E.NOENT;
            node = newFile(new Uint8Array(0));
            at.dir.entries.set(at.name, node);
          } else if (oflags & 4) {                        // O_EXCL
            return E.EXIST;
          }
          if ((oflags & 2) && node.type !== FILETYPE.DIR) return E.NOTDIR;   // O_DIRECTORY
          if (node.type === FILETYPE.REG && (oflags & 8)) node.data = new Uint8Array(0); // O_TRUNC
          const slot = self.fds.findIndex((x) => x === null);
          const entry = node.type === FILETYPE.DIR
            ? { kind: 'dir', node, chain, path, offset: 0 }
            : { kind: 'file', node, path, offset: (fdflags & 1) ? node.data.length : 0, append: !!(fdflags & 1) };
          const n = slot === -1 ? self.fds.push(entry) - 1 : (self.fds[slot] = entry, slot);
          self.view.setUint32(out, n, true);
          return OK;
        }),
        path_readlink: w(() => E.INVAL),
        path_rename: w((fd, op, ol, nfd, np, nl) => {
          const oldBase = self.baseFor(fd), newBase = self.baseFor(nfd);
          if (!oldBase || !newBase) return E.BADF;
          const from = walkParent(self.root, oldBase, self.str(op, ol));
          const to = walkParent(self.root, newBase, self.str(np, nl));
          if (!from || !to) return E.NOENT;
          const node = from.dir.entries.get(from.name);
          if (node === undefined) return E.NOENT;
          from.dir.entries.delete(from.name);
          to.dir.entries.set(to.name, node);
          return OK;
        }),
        path_unlink_file: w((fd, ptr, len) => {
          const base = self.baseFor(fd);
          if (!base) return E.BADF;
          const at = walkParent(self.root, base, self.str(ptr, len));
          if (!at) return E.NOENT;
          const node = at.dir.entries.get(at.name);
          if (node === undefined) return E.NOENT;
          if (node.type === FILETYPE.DIR) return E.ISDIR;
          at.dir.entries.delete(at.name);
          return OK;
        }),

        // Every subscription is reported ready at once, but one: a read on
        // a paced stdin that has nothing buffered.  The guest uses this for
        // its own scheduler timers, and a batch run has no other event source
        // to wait for.  A paced stdin is the other source, and the header
        // says when it is asked for more: when the guest would block, which
        // is a poll with no zero-timeout clock in it.
        poll_oneoff: w((inPtr, outPtr, n, out) => {
          const v = self.view;
          const stdin = self.fds[0];
          const pending = () => !stdin.ended && stdin.offset >= stdin.node.data.length;
          const tagOf = (i) => v.getUint8(inPtr + i * 48 + 8);
          const fdOf = (i) => v.getUint32(inPtr + i * 48 + 16, true);
          let waits = true;
          let onStdin = false;
          for (let i = 0; i < n; i++) {
            const tag = tagOf(i);
            if (tag === 0 && v.getBigUint64(inPtr + i * 48 + 24, true) === 0n) waits = false;
            if (tag === 1 && fdOf(i) === 0) onStdin = true;
          }
          if (waits && onStdin && pending()) self.ask();
          let k = 0;
          for (let i = 0; i < n; i++) {
            const sub = inPtr + i * 48;
            const tag = tagOf(i);
            const isStdin = tag === 1 && fdOf(i) === 0;
            if (isStdin && pending()) continue;
            const ev = outPtr + k * 32;
            k++;
            v.setBigUint64(ev, v.getBigUint64(sub, true), true);
            v.setUint16(ev + 8, OK, true);
            v.setUint8(ev + 10, tag);
            v.setBigUint64(ev + 16, isStdin
              ? BigInt(stdin.node.data.length - stdin.offset) : 0n, true);
            v.setUint16(ev + 24, isStdin && stdin.ended ? 1 : 0, true);   // 1 is HANGUP
          }
          v.setUint32(out, k, true);
          return OK;
        }),

        proc_exit: (code) => { self.exitCode = code; throw new Exit(code); },
      },
    };
  }

  // ---- helpers -----------------------------------------------------------

  // Ask a paced stdin for more: its next bytes, or end-of-file.  A `next`
  // that throws ends the input rather than the guest, and the error is kept
  // for the caller: a read that failed would end Agda with its own, less
  // useful, complaint about stdin.
  ask() {
    const f = this.fds[0];
    f.asked = true;
    let more = null;
    try { more = f.next(this.text('out')); }
    catch (err) { this.paceError = err; }
    if (more && more.length > 0) {
      f.node = newFile(more);
      f.offset = 0;
    } else {
      f.ended = true;
    }
  }

  nowNs() { return BigInt(Math.round(Date.now() * 1e6)); }

  envList() { return Object.entries(this.env).map(([k, v]) => `${k}=${v}`); }

  writeStrings(list, ptrs, buf) {
    const v = this.view, enc = new TextEncoder();
    let p = buf;
    for (let i = 0; i < list.length; i++) {
      v.setUint32(ptrs + i * 4, p, true);
      const b = enc.encode(list[i]);
      this.bytes.set(b, p);
      p += b.length;
      this.bytes[p++] = 0;
    }
    return OK;
  }

  writeFilestat(node, out) {
    const v = this.view;
    const size = node.type === FILETYPE.REG ? node.data.length : 0;
    v.setBigUint64(out, 0n, true);              // dev
    v.setBigUint64(out + 8, 0n, true);          // ino
    v.setUint8(out + 16, node.type);
    v.setBigUint64(out + 24, 1n, true);         // nlink
    v.setBigUint64(out + 32, BigInt(size), true);
    v.setBigUint64(out + 40, 0n, true);         // atim
    v.setBigUint64(out + 48, 0n, true);         // mtim
    v.setBigUint64(out + 56, 0n, true);         // ctim
    return OK;
  }

  writeInto(f, chunk) {
    const end = f.offset + chunk.length;
    if (end > f.node.data.length) {
      const next = new Uint8Array(end);
      next.set(f.node.data);
      f.node.data = next;
    }
    f.node.data.set(chunk, f.offset);
    f.offset = end;
  }

  text(which) {
    const parts = which === 'out' ? this.stdout : this.stderr;
    let n = 0;
    for (const p of parts) n += p.length;
    const all = new Uint8Array(n);
    let o = 0;
    for (const p of parts) { all.set(p, o); o += p.length; }
    return new TextDecoder().decode(all);
  }

  // Run an already-compiled module to completion.  Returns the exit status;
  // a guest that returns from `_start` without calling proc_exit exits 0.
  async run(module) {
    const instance = await WebAssembly.instantiate(module, this.imports());
    this.memory = instance.exports.memory;
    // When the guest itself starts: a caller timing a run from before the
    // `await` above would count the time it waited behind another run.
    this.startedAt = performance.now();
    try { instance.exports._start(); return 0; }
    catch (err) {
      if (err instanceof Exit) return err.code;
      throw err;
    }
  }
}
