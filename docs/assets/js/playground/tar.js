// File: docs/assets/js/playground/tar.js
//
// Provenance: `docs/javascripts/playground/tar.js` of williamdemeo/website at
// commit 952e5eb (MIT, Copyright 2026 William DeMeo; see NOTICE).  The code is
// unchanged.  The comments name this repository's paths, write that
// repository's issue numbers as website#N, and say what this site's images
// carry.  The images are built by `scripts/python/playground/build_assets.py`,
// which keeps the property the comment below relies on: plain ustar, files and
// directories only.
//
// Just enough ustar to turn one of this site's own filesystem images back
// into a tree of WASI nodes.  The images are produced by
// `scripts/python/playground/build_assets.py` with `--format=ustar`, so
// there are no long-name or pax extension records to handle: a header that
// is not a plain file or a directory is a bug in the builder, not input to
// tolerate, and the reader says so.
//
// The `prefix` field is not optional and skipping it is not a small bug.
// ustar puts a path's last 100 bytes in `name` and everything before them in
// `prefix`, and the standard library's interface paths go over 100:
// `lib/standard-library/_build/2.8.0/agda/src/Relation/Binary/Indexed/Heterogeneous/Construct/Trivial.agdai`
// is 104.  A reader that takes `name` alone unpacks that file under
// `Construct/`, Agda does not find the interface where it looks, and it
// silently type-checks the module again.  Nothing reports an error; the only
// symptom is that the check is slower.  Measured, with the image, the runtime
// and the argv all correct: the obligation image shipped until website#149 had
// one such path and it cost about 0.2 s a check (1.17 to 1.42 s, against 1.08
// to 1.28 s fixed); an earlier image whose library directory was four
// characters longer had four such paths and cost 1.9 s (3.02 to 3.51 s).  The
// images this site builds have them too: every closure that reaches
// `Relation.Binary` carries the 104-byte path above (measured 2026-10-04).
// `scripts/js/playground/test_tar.mjs` holds the case, in an archive it
// builds itself.

import { newDir, newFile } from './wasi.js';

const BLOCK = 512;
const dec = new TextDecoder();

const field = (b, off, len) => {
  const s = b.subarray(off, off + len);
  const end = s.indexOf(0);
  return dec.decode(end === -1 ? s : s.subarray(0, end)).trim();
};

export function untar(bytes) {
  const root = newDir();
  for (let p = 0; p + BLOCK <= bytes.length; ) {
    const h = bytes.subarray(p, p + BLOCK);
    if (h.every((x) => x === 0)) break;                     // end-of-archive
    const prefix = field(h, 345, 155);
    const stem = field(h, 0, 100);
    const name = (prefix === '' ? stem : `${prefix}/${stem}`).replace(/^\.\//, '');
    const size = parseInt(field(h, 124, 12) || '0', 8);
    const type = String.fromCharCode(h[156]) || '0';
    p += BLOCK;
    if (name !== '') {
      if (type === '5') {
        mkdirp(root, name.replace(/\/$/, ''));
      } else if (type === '0' || type === '\0') {
        const parts = name.split('/');
        const leaf = parts.pop();
        mkdirp(root, parts.join('/')).entries.set(
          leaf, newFile(bytes.slice(p, p + size)));
      } else {
        throw new Error(`tar: unsupported entry type ${JSON.stringify(type)} for ${name}`);
      }
    }
    p += Math.ceil(size / BLOCK) * BLOCK;
  }
  return root;
}

function mkdirp(root, path) {
  let node = root;
  for (const part of path.split('/')) {
    if (part === '' || part === '.') continue;
    let next = node.entries.get(part);
    if (next === undefined) { next = newDir(); node.entries.set(part, next); }
    node = next;
  }
  return node;
}

/** A deep copy, so one unpacked image can seed many runs.
 *
 * Deep down to the bytes.  The first version copied the tree and shared each
 * file's `Uint8Array` between the clone and the image, so a write into an
 * existing file within its length would have reached the image and every
 * check after it.  No check Agda runs today does that (measured over both
 * images, correct proof and hole: no in-place write into a shared buffer, no
 * image file changed), which is why it was latent; it was still a copy that
 * was not one.  Copying cost 1.1 ms on website#146's 7.4 MB obligation image
 * against a check of over a second, so the tree is simply copied. */
export function cloneTree(node) {
  if (node.type === 3) {
    const d = newDir();
    for (const [k, v] of node.entries) d.entries.set(k, cloneTree(v));
    return d;
  }
  return newFile(node.data.slice());
}
