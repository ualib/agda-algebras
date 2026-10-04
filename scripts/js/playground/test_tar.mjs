// File: scripts/js/playground/test_tar.mjs
//
// The playground's tar reader, `docs/assets/js/playground/tar.js`, against
// archives built here header by header, and against the built images when
// there are any.
//
// It began as `scripts/js/test_playground_tar.mjs` of williamdemeo/website
// at commit 952e5eb (MIT; see NOTICE); the archives built by hand are new.
//
// The reader is the only thing between a filesystem image and Agda's view of
// the world, and when it puts a file in the wrong place nothing reports an
// error: Agda does not find an interface where it looks, type-checks the
// module again, and the only symptom is a slower check.  That shipped once on
// the site this code comes from (the reader ignored ustar's `prefix` field):
// one truncated path cost about 0.2 s of every check, and four cost 1.9 s.
//
// Why the archives are built here rather than taken from an image.  CI has no
// image (`make playground` builds them into a gitignored directory), and a
// case read out of an image follows the image: the smallest one here has no
// path over 100 bytes at all (its longest is 79), so a test that looked for
// one there would find nothing and pass.  The headers below are written the
// way Python's `tarfile` writes ustar, which is what
// `scripts/python/playground/build_assets.py` uses: the same split of a long
// path, the same size and checksum fields, the same padding to a 10240-byte
// record.
//
// What is pinned, each for a reason given where it is checked: a path over
// 100 bytes comes back whole; a directory entry, nested directories and an
// empty directory come back; an empty file and a file whose size is a
// multiple of 512 do not throw off the walk to the next header; anything that
// is not a plain file or a directory is refused, not skipped; and `cloneTree`
// copies down to the bytes.
//
// Usage:  node scripts/js/playground/test_tar.mjs
//         make playground-test
//
// With built images in `.playground/` (or in $PLAYGROUND_OUT), it also reads
// each one the manifest lists; without them it says so and skips that part.

import { existsSync, readFileSync } from 'node:fs';
import { resolve as resolvePath } from 'node:path';
import { fileURLToPath } from 'node:url';
import { gunzipSync } from 'node:zlib';
import { createHash } from 'node:crypto';
import { untar, cloneTree } from '../../../docs/assets/js/playground/tar.js';

const failures = [];
const check = (ok, what) => { if (!ok) failures.push(what); };
// A reader that loses its place in the archive throws (it lands in a file's
// bytes and reads them as a header), and that has to be reported as a
// failure of the case it happened in, not end the run before the rest.
const section = (what, body) => {
  try { body(); } catch (err) { failures.push(`${what}: threw ${JSON.stringify(String(err && err.message))}`); }
};
const enc = new TextEncoder();
const dec = new TextDecoder();
const BLOCK = 512;

// ---- an ustar writer -------------------------------------------------------

// The split Python's `tarfile` makes (`TarInfo._posix_split_name`): only a
// path over 100 bytes is split, and then at the *shortest* leading run of
// whole directories that leaves at most 100 bytes for `name`.  So the
// standard library's 104-byte path goes in as `lib` and a `name` of exactly
// 100 bytes, which has no NUL after it; that is how the built images carry it
// (read from their headers, 2026-10-04).
function split(path) {
  if (enc.encode(path).length <= 100) return { prefix: '', name: path };
  const parts = path.split('/');
  for (let i = 1; i < parts.length; i++) {
    const prefix = parts.slice(0, i).join('/');
    const name = parts.slice(i).join('/');
    if (enc.encode(prefix).length <= 155 && enc.encode(name).length <= 100) {
      return { prefix, name };
    }
  }
  throw new Error(`fixture: ${path} does not fit ustar`);
}

const octal = (n, digits) => `${n.toString(8).padStart(digits, '0')}\0`;

/** One 512-byte ustar header.  `type` is the typeflag character. */
function header({ path, type = '0', size = 0, linkname = '' }) {
  const h = new Uint8Array(BLOCK);
  const put = (s, at, len) => {
    const b = enc.encode(s);
    if (b.length > len) throw new Error(`fixture: ${JSON.stringify(s)} overflows its field`);
    h.set(b, at);
  };
  const { prefix, name } = split(path);
  put(name, 0, 100);
  put(octal(type === '5' ? 0o755 : 0o644, 7), 100, 8);
  put(octal(0, 7), 108, 8);                     // uid
  put(octal(0, 7), 116, 8);                     // gid
  put(octal(size, 11), 124, 12);
  put(octal(0, 11), 136, 12);                   // mtime
  h[156] = type.charCodeAt(0);
  put(linkname, 157, 100);
  put('ustar\0', 257, 6);
  put('00', 263, 2);
  put(octal(0, 7), 329, 8);                     // devmajor
  put(octal(0, 7), 337, 8);                     // devminor
  put(prefix, 345, 155);
  // The checksum is the byte sum of the header with its own field read as
  // eight spaces, written as six octal digits, a NUL and the space left over.
  h.fill(0x20, 148, 156);
  put(`${h.reduce((a, b) => a + b, 0).toString(8).padStart(6, '0')}\0`, 148, 7);
  return h;
}

/** An archive of `entries` ({path, type, data, linkname}), with the
 * end-of-archive marker and the zero padding to a whole 10240-byte record. */
function ustar(entries) {
  const blocks = [];
  for (const { path, type = '0', data = new Uint8Array(0), linkname = '' } of entries) {
    blocks.push(header({ path, type, size: data.length, linkname }));
    blocks.push(data, new Uint8Array((BLOCK - (data.length % BLOCK)) % BLOCK));
  }
  blocks.push(new Uint8Array(2 * BLOCK));
  const used = blocks.reduce((n, b) => n + b.length, 0);
  blocks.push(new Uint8Array((10240 - (used % 10240)) % 10240));
  const out = new Uint8Array(blocks.reduce((n, b) => n + b.length, 0));
  blocks.reduce((at, b) => { out.set(b, at); return at + b.length; }, 0);
  return out;
}

/** The unpacked tree as its files (path to bytes) and its directories. */
function flatten(node, prefix = '', into = { files: new Map(), dirs: new Set() }) {
  for (const [name, child] of node.entries) {
    const path = prefix === '' ? name : `${prefix}/${name}`;
    if (child.type === 3) { into.dirs.add(path); flatten(child, path, into); }
    else into.files.set(path, child.data);
  }
  return into;
}

const same = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
const show = (xs) => JSON.stringify([...xs].sort());

// ---- one archive, every shape the builder writes ---------------------------

// Named rather than derived: the point of the case is that it is over 100
// bytes, and it is the path every image reaching `Relation.Binary` carries.
const LONG = 'lib/standard-library/_build/2.8.0/agda/src/Relation/Binary/'
  + 'Indexed/Heterogeneous/Construct/Trivial.agdai';
// Exactly 100 bytes: Python writes it whole into `name`, with no prefix and
// no NUL after it.
const FULL = `work/${'n'.repeat(100 - 'work/'.length - '.agda'.length)}.agda`;

// Every file's bytes differ from every other's, so a file that came back
// under the right path with another file's bytes is caught too.
const pattern = (n, seed) => Uint8Array.from({ length: n }, (_, i) => (i * 7 + seed) % 251);
const FILES = {
  'agda.argv': enc.encode('agda\n-i\n/work\n'),
  [LONG]: pattern(300, 1),
  [FULL]: pattern(20, 2),
  'work/empty.agda': new Uint8Array(0),
  'work/two-blocks.bin': pattern(2 * BLOCK, 3),
  'work/zeros.bin': new Uint8Array(BLOCK),
  'work/after.agda': pattern(10, 4),
  'lib/agda-algebras/src/Overture/Terms/Basic.agdai': pattern(700, 5),
  'work/𝑨lgebra.agda': pattern(5, 6),
};

const archive = ustar([
  { path: 'agda.argv', data: FILES['agda.argv'] },
  // Directory entries as Python writes them, with a trailing slash, each
  // before the files in it; the directories under `lib/standard-library/`
  // have no entries, so the reader has to make them.
  { path: 'lib/', type: '5' },
  { path: 'lib/standard-library/', type: '5' },
  { path: LONG, data: FILES[LONG] },
  { path: 'home/', type: '5' },
  { path: 'home/.config/', type: '5' },
  { path: 'home/.config/agda/', type: '5' },
  { path: 'work/', type: '5' },
  { path: FULL, data: FILES[FULL] },
  // No data blocks at all: the next header follows at once.
  { path: 'work/empty.agda', data: FILES['work/empty.agda'] },
  // Exactly two blocks and no padding after them.
  { path: 'work/two-blocks.bin', data: FILES['work/two-blocks.bin'] },
  // One block of zeros right after the exact multiple: a reader that skipped
  // one block too many there would land on it, take it for the end-of-archive
  // marker, and quietly drop every entry after it.
  { path: 'work/zeros.bin', data: FILES['work/zeros.bin'] },
  { path: 'work/after.agda', data: FILES['work/after.agda'] },
  // A file whose directories no entry declares.
  { path: 'lib/agda-algebras/src/Overture/Terms/Basic.agdai',
    data: FILES['lib/agda-algebras/src/Overture/Terms/Basic.agdai'] },
  // A name that is not ASCII; the fields are UTF-8.
  { path: 'work/𝑨lgebra.agda', data: FILES['work/𝑨lgebra.agda'] },
]);

// The fixture has to be the thing it claims to be, or the cases below could
// pass without exercising the reader.  The long path's header is block 4
// (after agda.argv's header and its one data block, and two directory
// headers): it must be split, and its `name` must fill the field.
section('the fixture', () => {
  const h = archive.subarray(4 * BLOCK, 5 * BLOCK);
  check(same(h, header({ path: LONG, size: FILES[LONG].length })),
    'block 4 of the fixture is not the long path\'s header');
  const stem = dec.decode(h.subarray(0, 100));
  const prefix = dec.decode(h.subarray(345, 500)).replace(/\0+$/, '');
  check(LONG.length === 104, `the long path is ${LONG.length} bytes, not the 104 it stands for`);
  check(prefix === 'lib' && `${prefix}/${stem}` === LONG && !h.subarray(0, 100).includes(0),
    `the fixture did not split ${LONG} as Python does (prefix ${JSON.stringify(prefix)}); `
    + 'it would not exercise the prefix field');
  check(archive.length % 10240 === 0, 'the fixture is not padded to a whole record');
});

section('untar of the fixture', () => {
  const { files, dirs } = flatten(untar(archive));
  check(show(files.keys()) === show(Object.keys(FILES)),
    `the files came back as ${show(files.keys())}; a path missing here and present `
    + 'under a shorter one is a dropped ustar prefix');
  for (const [path, want] of Object.entries(FILES)) {
    const got = files.get(path);
    check(got !== undefined && same(got, want),
      `${path}: ${got === undefined ? 'missing' : `${got.length} bytes, not its own ${want.length}`}`);
  }
  // Every directory a file needs, and only those; a stray directory is where
  // a truncated path hangs.
  const DIRS = ['lib', 'lib/standard-library', 'home', 'home/.config', 'home/.config/agda',
    'work', 'lib/agda-algebras', 'lib/agda-algebras/src', 'lib/agda-algebras/src/Overture',
    'lib/agda-algebras/src/Overture/Terms',
    ...LONG.split('/').slice(2, -1).map((_, i, a) => `lib/standard-library/${a.slice(0, i + 1).join('/')}`)];
  check(show(dirs) === show(DIRS), `the directories came back as ${show(dirs)}`);
  // `home/.config/agda` holds nothing here, so only its own entry can make
  // it, and only a reader that honors directory entries passes.
  check(dirs.has('home/.config/agda'), 'an empty directory\'s entry was dropped');
});

// ---- entries the reader refuses --------------------------------------------

// The builder writes plain ustar, files and directories only, so anything
// else is a builder bug and the reader has to say so.  Skipping it would be
// worse than a crash: a symlink would leave a hole where Agda looks for a
// file, and a pax header (`x`, which Python's default format writes for any
// path over 100 bytes instead of splitting it) would leave the file it names
// unpacked under a truncated path, which is the slow failure this file is
// about.
for (const [type, what, extra] of [
  ['2', 'a symlink', { linkname: 'Trivial.agdai' }],
  ['1', 'a hard link', { linkname: 'work/after.agda' }],
  ['x', 'a pax extended header', { data: enc.encode('30 path=work/long/enough.agda\n') }],
  ['L', 'a GNU long name', { data: enc.encode('work/long/enough.agda\0') }],
]) {
  const path = type === '2' ? 'lib/link.agdai' : 'work/odd';
  const bad = ustar([{ path: 'work/after.agda', data: pattern(3, 7) }, { path, type, ...extra }]);
  let threw = null;
  try { untar(bad); } catch (err) { threw = err; }
  check(threw !== null, `${what} (type ${type}) was accepted; it must be refused`);
  check(threw === null || String(threw.message).includes(path),
    `the refusal of ${what} does not name the entry: ${threw && threw.message}`);
}

// ---- cloneTree -------------------------------------------------------------

// Each check runs on a clone of one unpacked image, so a clone has to be a
// copy down to the bytes and the maps.  The first version shared each file's
// buffer with the image, so a write into a file within its length would have
// reached every later check; no check Agda runs today does that, which is why
// it was latent.  The page's checker (`checker.js`) puts the reader's text
// into the clone's `work` directory, so a shared directory would carry one
// run's text into the image and every run after it.
section('cloneTree', () => {
  const image = untar(archive);
  const before = flatten(image);
  const clone = cloneTree(image);
  const after = flatten(clone);
  check(show(after.files.keys()) === show(before.files.keys())
    && show(after.dirs) === show(before.dirs),
    'the clone does not have the image\'s paths');
  check([...before.files].every(([p, d]) => same(after.files.get(p), d)),
    'the clone does not have the image\'s bytes');

  const original = image.entries.get('work').entries.get('after.agda').data;
  const copy = clone.entries.get('work').entries.get('after.agda').data;
  check(copy !== original && copy.buffer !== original.buffer,
    'a cloned file shares its buffer with the image');
  const first = original[0];
  copy[0] = first ^ 0xff;
  check(original[0] === first, 'writing into a cloned file changed the image');

  clone.entries.get('work').entries.set('Graft.agda', { type: 4, data: enc.encode('module Graft where') });
  check(!image.entries.get('work').entries.has('Graft.agda'),
    'adding a file to a cloned directory added it to the image');
  check(cloneTree(image).entries.get('home')?.entries.get('.config')?.entries.get('agda')?.type === 3,
    'the clone lost an empty directory');
});

// ---- the built images, when there are any ----------------------------------

// The cases above pin the reader; this pins it on the real thing.  It is
// skipped where nothing has been built (CI), and needs the manifest beside
// the images, which says what each one should contain.
const ROOT = fileURLToPath(new URL('../../../', import.meta.url));
const OUT = process.env.PLAYGROUND_OUT
  ? resolvePath(process.env.PLAYGROUND_OUT) : resolvePath(ROOT, '.playground');
let images = 0;
if (existsSync(`${OUT}/manifest.json`)) {
  const manifest = JSON.parse(readFileSync(`${OUT}/manifest.json`, 'utf8'));
  for (const [file, expected] of Object.entries(manifest.images ?? {})) {
    if (!existsSync(`${OUT}/${file}`)) continue;
    images++;
    section(file, () => {
      const raw = gunzipSync(readFileSync(`${OUT}/${file}`));
      const digest = createHash('sha256').update(raw).digest('hex');
      check(digest === expected.tar_sha256,
        `${file}: inflates to ${digest}, the manifest says ${expected.tar_sha256}`);
      const { files } = flatten(untar(new Uint8Array(raw)));

      const argv = files.get('agda.argv');
      check(argv !== undefined, `${file}: the reader did not find agda.argv`);
      if (argv !== undefined && manifest.argv) {
        const got = dec.decode(argv).split('\n').filter((a) => a !== '');
        check(JSON.stringify(got) === JSON.stringify(manifest.argv),
          `${file}: agda.argv reads ${JSON.stringify(got)}`);
      }
      check(files.has('lib/agda-algebras/agda-algebras.agda-lib'),
        `${file}: the reader did not find lib/agda-algebras/agda-algebras.agda-lib`);

      const interfaces = [...files.keys()].filter((p) => p.endsWith('.agdai')).length;
      check(interfaces === expected.interfaces,
        `${file}: ${interfaces} interfaces, the manifest says ${expected.interfaces}`);
      // A count cannot see truncation (the file is still there, at a shorter
      // path), but the longest path can, and the builder records it.
      const longest = [...files.keys()].reduce((n, p) => Math.max(n, enc.encode(p).length), 0);
      check(longest === expected.longest_path,
        `${file}: the longest path the reader produced is ${longest} bytes, `
        + `the manifest says ${expected.longest_path}`);
      const ROOTS = ['data/', 'home/', 'lib/', 'work/'];
      const stray = [...files.keys()].filter((p) => p !== 'agda.argv' && !ROOTS.some((r) => p.startsWith(r)));
      check(stray.length === 0, `${file}: ${stray.length} files outside every root: ${stray.slice(0, 3)}`);
    });
  }
}
console.log(images === 0
  ? `playground tar: no built images in ${OUT}, so only the archives built here were read`
  : `playground tar: ${images} built image(s) in ${OUT} read and compared with the manifest`);

if (failures.length) {
  for (const line of failures) console.error(`  ${line}`);
  console.error(`playground tar: ${failures.length} failure(s)`);
  process.exit(1);
}
console.log('playground tar: every path comes back whole, every other entry type is refused, '
  + 'and a clone is a copy');
