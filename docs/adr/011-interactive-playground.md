<!-- File: docs/adr/011-interactive-playground.md -->

# ADR-011: the playground

+  **Status**: Accepted, pending review of the pull request that adds it.
+  **Date**: 2026-10-04
+  **Tracking**: [#577][]
+  **Ancestry**: williamdemeo/website's ADR-015 measured that a browser can
   run Agda 2.8, and its ADR-016 built a batch checker page on that result and
   decided that the *interactive* environment belongs on this site; its issue
   148 measured that the plain checker answers goal queries over a scripted
   standard input.  That repository is private, so every figure this record
   relies on is restated here.  The maintenance guide is the companion note,
   [the playground section of the site guide][site-guide-playground].

---

## Summary

The documentation site gains a page, `/playground/`, where a reader opens a
definition from this library with its body removed, sees each open goal's
type and context, and fills it with Agda's own goal commands: give, refine,
case split, and the type of an expression at a goal.  The checker is Agda
2.8.0 compiled to WebAssembly by [agda-wasm-dist][], unmodified, running in a
web worker in the reader's tab.

The shape follows from three measurements.  The plain command-line `agda`,
not the Agda language server, answers every goal command through its
interaction protocol (the commands Agda's Emacs mode, *agda-mode*, sends it;
with `--interaction-json` the answers come back as JSON), so the page needs
no language server.  The protocol can be driven from inside one run, one
command at a time, by a host that decides each next command when Agda has
finished answering the last one, so a command costs one load and a failed
load costs one load, not one per question.  And none of that needs
cross-origin isolation (the two HTTP headers that make `SharedArrayBuffer`
available), so the page works on this site's host as it is, with no header
rule.

What a command costs is the size of the exercise's *closure* (the modules it
imports, transitively, with the standard library's among them), because each
command loads it again.  The page ships three images (an *image* is an
archive of a closure: each module's source and its compiled interface file),
from 370 KB, answering in under a second, to 37 MB, answering in about ten
seconds; each exercise states its download before anything is fetched.  The
images are built in the site build and never committed.  Sizes in this record
are given as the page gives them: a KB is 1,024 bytes and an MB 1,048,576.

What remains open: a session that outlives one command, which a probe
showed JavaScript Promise Integration can give without isolation, cutting the
largest image's ten seconds a command to a second and a half for a reload and
a twentieth of a second for a query; an exercise from deeper in the library,
which waits on the closure sizes recorded below; and a first check of the
page on the live site once it is deployed.

---

## The stack: the plain checker, driven through its interaction protocol

(See also [#577][], [`session.js`][session], and [`protocol.js`][protocol].)

**Decision**.  Run `agda-opt.wasm` from [agda-wasm-dist][] release
`v2.8.0-ghc9.10.3-r0` with `--interaction-json`, in a module worker, over the
WASI host adapted from williamdemeo.org's playground, and answer every goal
command from it; do not run the Agda language server.

+  A *WASI host* is the JavaScript that gives a WebAssembly program its
   operating system: arguments, a clock, standard streams, and here an
   in-memory filesystem holding the reader's file and the image.  The host is
   about 500 lines, comments included, and implements exactly the 24 imports
   the checker declares.
+  The *interaction protocol* is Agda's `IOTCM` command language and its JSON
   answers: `Cmd_load`, `Cmd_goal_type_context`, `Cmd_give`,
   `Cmd_refine_or_intro`, `Cmd_make_case` and `Cmd_goal_type_context_infer`
   are the commands the page sends.
+  The language server (`als-2.8ext.wasm`, 33 MB raw and about 10 MB
   gzipped, as plfa.isotopy.xyz ships it) is the alternative.  It keeps a
   session alive between commands, which this page does not, and it needs a
   standard input that blocks, which needs cross-origin isolation.

**Evidence**.  Measured 2026-10-04 in headless Chromium 153.0.8010.47 on
this repository's images: every command the page offers returns its answer
(the transcripts are in the browser checks of the pull request); give,
refine, case split and type-of all apply to this library's own definitions,
and the three exercises are completed through the page, start to finish,
with the hint sequences the page prints.  `crossOriginIsolated` was false in
every run.

**Status**.  Adopted.

---

## A paced standard input: each next command decided from the last answer

(See also [`wasi.js`][wasi] and [`session.js`][session].)

**Decision**.  The host feeds Agda one command at a time, deciding each when
Agda has answered the previous one: load; if the load failed, stop; if the
reader asked for something at a goal, send it; if that changed the text,
write the change into the in-memory file and load again; then ask for the
context of each goal the last load reported, by its number.

+  The decision cannot be made at a read.  Agda reads its standard input on a
   thread of its own, which reads ahead: it asked for the second line before
   it had written a byte of the answer to the first.
+  It can be made at a poll.  The guest marks its standard input
   non-blocking; a read answered `EAGAIN` ("try again") blocks only the
   reading thread, and GHC's scheduler (Agda is a Haskell program) then polls
   the descriptor through `poll_oneoff`: with a zero-timeout clock while
   another thread can run, and with no clock once every thread is waiting.
   The second kind arrives only when the previous answer is complete.
+  Nothing waits and nothing is shared between threads, so this needs no
   `SharedArrayBuffer`.

**Evidence**.  Measured under node 22 with the host's calls logged, on a
load of a two-goal variant of the first exercise: two reads before any
write; then 10,149
zero-timeout polls during the load and one blocking poll after it, where the
next command was decided.  A fixed stream of a load and four queries over a
file that does not load type-checked the file five times, because
Agda loads the file again before every command that needs it; the paced
host type-checked it once and stopped.  A fixed stream also cannot know the
goals' numbers in advance; the paced host asks for exactly the goals Agda
reported.

**Status**.  Adopted.  The host keeps its fixed-stream mode (a buffer, then
end of input) for a caller that knows its whole conversation; its tests use
it, and the page does not.  The build's interaction check needs no pacing,
since every solution it checks loads, and feeds wasmtime a fixed stream of
its own.

---

## One run per command, and a reload inside the run

(See also [`session.js`][session] and [`edits.js`][edits].)

**Decision**.  Every button on the page is one run of the checker, from its
start.  A give, a refine or a case split changes the text inside the run, the
way agda-mode changes its buffer, and the run loads the changed text again
before it reports the goals; the page then shows the new text and its goals
together.

+  The edits are agda-mode's own: a give or refine replaces the goal with
   Agda's answer, and a case split replaces the goal's line with the clauses
   (`agda2-make-case-action`, and its extended-lambda variant).
+  Agda keeps every imported module in memory between loads in one process,
   so the second load costs a fraction of the first.
+  Goal numbers are renumbered by every load, as in Emacs; the page always
   acts on the numbers its last run reported, and disables the goal commands
   while its goals describe text the reader has since changed.

**Evidence**.  Node 22, the 244-module image: 12.5 s for the first load,
1.4 s for the reload after an edit, 41 ms for a context query.  In
Chromium, a give on that image took 9.34 to 9.62 s, a check 9.71 s.

**Status**.  Adopted.  The cost of a command is therefore one cold load; the
section on what remains open says how a session that outlives a command
would remove it.

---

## Cross-origin isolation is not needed, and was not added

(See also [#577][].)

**Decision**.  No `Cross-Origin-Opener-Policy` or
`Cross-Origin-Embedder-Policy` rule, on the playground's path or anywhere.
This **supersedes** the issue's acceptance criterion "cross-origin isolation
confirmed on the live host, scoped to that page's path", which assumed that
interaction needs it.

+  Isolation is what makes `SharedArrayBuffer` available, and the language
   server's WASI shim needs that to block on its input.  The paced host never
   blocks.
+  `require-corp` makes every cross-origin subresource opt in; this site
   loads a font from a CDN, which would have to be checked for the right
   header first.  A rule that is not there cannot be scoped wrongly.

**Evidence**.  The live host, 2026-10-04: `agda-algebras.universalalgebra.org`
resolves to Cloudflare, whose nameservers serve the zone, in front of GitHub
Pages; its responses carry neither header.  So the page is expected to work
there as built: every browser check ran on a local server that sent neither
header either, and reported `crossOriginIsolated` false in every run.  The
page itself has not run on the live host, since it is not deployed until this
record's pull request merges.  The zone's Transform Rules were not inspected
(that needs access to the Cloudflare account) and nothing here depends on
them.

**Status**.  Adopted.  A persistent session is the one future change that
would bring isolation back; see what remains open.

---

## The closures, re-measured

(See also [#577][] and [the image builder][build-assets].)

**Decision**.  Record the closure tiers measured here, against the figures the
issue inherited, and choose the exercises by them.  Agda's
`--dependency-graph` writes a module's closure, and the size of an image is
one `stat` per interface in it.

**Evidence**.  Each tier populated by the shipped WebAssembly from source,
under wasmtime 43.0.1 (a command-line WebAssembly runtime, the version the
flake pins), then packed and checked again from a fresh unpacking
(each check type-checked exactly one module, the seed's).  Bytes are the
gzipped image; the issue's figures came from williamdemeo/website's issue
144, measured in September.

| Seed module                  | Modules | Image (gzipped) | Issue's figure        | Check, wasmtime |
|------------------------------|--------:|----------------:|-----------------------|----------------:|
| `Overture.Basic`             |      66 |       6,019,761 | 66, 5,928,837         |    1.9 to 2.8 s |
| `Overture.Cayley`            |     150 |      20,963,216 | 150, 20,768,154       |           5.3 s |
| `Overture`                   |     177 |      22,876,350 |                       |           6.9 s |
| `Setoid.Algebras.Basic`      |     179 |      23,297,637 |                       |    6.2 to 6.8 s |
| `Setoid.Homomorphisms.Basic` |     244 |      38,720,248 | 244, 38,386,602       |           8.6 s |
| `Setoid.Varieties.HSP`       |     313 |      54,856,127 |                       |          11.3 s |

The issue recorded 16.34 s for the `Setoid.Homomorphisms.Basic` check; it was
8.6 s here, on another machine and another wasmtime.

Native closures of the smaller modules (dependency graph; interface bytes
summed, uncompressed, builtins excluded):

| Seed module                                     | Modules | Interfaces, bytes |
|-------------------------------------------------|--------:|------------------:|
| `Overture.Signatures`                           |      15 |           278,468 |
| `Overture.Signatures` with `Overture.Terms.Basic` |    16 |           300,074 |
| `Overture.Operations`                           |      16 |           288,545 |
| `Overture.Relations`                            |      68 |         6,893,424 |
| `Overture.Signatures.Morphisms`                 |      70 |         7,015,771 |
| `Overture.Terms.Interpretation`                 |      72 |         7,122,138 |
| `Setoid.Relations`                              |     182 |        27,078,570 |

+  The standard library is most of every closure: 38.9 of the 43.0 MB of
   interfaces in the `Setoid.Homomorphisms.Basic` tier, led by
   `Data.Nat.Properties` (2.2 MB), `Data.List.Relation.Unary.All.Properties`
   (1.8 MB) and `Data.List.Properties` (1.6 MB).
+  Two imports of this library decide the sizes.  `Overture.Basic` and
   `Overture.Signatures.Morphisms` import the standard library's whole
   propositional equality, which costs about 6.4 MB of interfaces; and
   `Setoid.Algebras.Basic` imports the whole `Overture`, which brings
   `Overture.Cayley` and `Overture.Counting`, and with them the properties of
   the natural numbers, lists and finite sets.
+  This library's own signatures, operations and terms close over 16 modules
   and 290 KB.

**Status**.  Recorded.  Narrowing those two imports is the cheapest way to
make the homomorphisms tier smaller, and is left to its own issue.

---

## Three images, each behind its own consent

(See also [docs/playground.md][page] and [the image builder][build-assets].)

**Decision**.  Ship three exercises on three images, smallest first, each
saying what it would download before anything is fetched; an exercise runs on
any image whose closure contains its own.

| Exercise                    | From                               | Image             | Interfaces | Gzipped    | A command, Chromium |
|-----------------------------|------------------------------------|-------------------|-----------:|-----------:|--------------------:|
| `graft`                     | `Overture.Terms.Interpretation`    | `terms`           |         22 |    378,681 | 0.22 to 0.57 s      |
| `_✦_`                       | `Overture.Terms.Interpretation`    | `interpretations` |         75 |  6,251,569 | 1.47 to 2.40 s      |
| `⊙-is-hom`                  | `Setoid.Homomorphisms.Properties`  | `homomorphisms`   |        245 | 38,727,934 | 9.3 to 12.0 s       |

+  The checker itself is 9,703,518 bytes gzipped (31,524,760 raw), fetched
   once per visit and compiled once.
+  The times are one command each (a check, a give, a refine, a case split
   or a type query) in headless Chromium, over two sessions on one machine;
   the slower ends are from the second, while another process held a core.  `_✦_` was measured on the
   homomorphisms image, which serves it; Agda loads only what the exercise
   imports, so the image it runs on does not change the time.
+  `graft` reproduces the library's definition over the two modules it needs,
   rather than importing the module that defines it, because that module's
   other imports cost 6.5 MB: the page says so.  The other two import the
   library as the library does.
+  The issue weighed the `Overture` tier (about 6 MB, in its figures) against
   the `Setoid` tier (about 38 MB) and called the second "a different
   project".  Both are here, because the smallest closure turned out to be
   the library's own universal algebra (signatures and terms, 370 KB), and
   because a reader who chooses the 37 MB exercise is told its size and its
   pace before choosing.
+  A larger image serves a smaller exercise: the build proves each solution
   on every image that claims to serve it, and the page fetches nothing for
   an exercise one of whose images is already loaded.

**Evidence**.  Headless Chromium, the built site on a local server: no
request for the worker, the checker or an image before a button is pressed;
after loading the `⊙-is-hom` exercise and then opening the other two, the
server had served the checker and exactly one image.  Consent to first verdict
was 0.72 s for `graft` and 10.3 s for `⊙-is-hom` (local server, so without
network time).  Peak WebAssembly memory 73.5 MB on the `Overture.Basic`
tier and 343.8 MB on the homomorphisms image.

**Status**.  Adopted.

---

## Build natively, prove under the WebAssembly

(See also [the image builder][build-assets] and the measuring-agda-under-wasi
skill.)

**Decision**.  The image builder type-checks each closure with the native
Agda the flake pins, then unpacks every image fresh and checks every exercise
on it under the shipped WebAssembly, and fails unless each check
type-checked exactly one module.

+  An interface is accepted only where the reading Agda looks for it and only
   if it was built under the options in force, and a mismatch is silent: the
   module is type-checked again.  So acceptance is a count of `Checking`
   lines, unanchored (Agda indents nested ones), with exit 0.
+  The images are built in the site build (`make site-full` runs `make
   playground`) and never committed; the flake pins the release by its
   sha256, and the builder checks it and the module inside it again.
+  The builder records what each image was built from (this repository's
   commit, the standard library's store path) in a manifest the site
   publishes, and refuses to ship sources that differ from that commit unless
   told to, in which case the manifest says so.

**Evidence**.  Native interfaces swapped into a wasm-built `Overture.Basic`
image: accepted (one module checked) and loaded in 1.89 to 1.92 s against
1.90 to 1.94 s for the wasm-built ones.  Populating under the WebAssembly
took 63 s for that tier and 352 s for the homomorphisms tier; the whole
native build with its proofs takes 50 to 53 s.

**Status**.  Adopted.

---

## The component is reused, not written again

(See also the root [NOTICE][notice].)

**Decision**.  Adapt williamdemeo.org's playground component (MIT, Copyright
2026 William DeMeo): the WASI host, the tar reader and the worker's fetch
code unchanged but for the paced input; the input method with this library's
notation added; the editor's painter; the builder's pins and provenance
checks; the consent hook's shape.

**Evidence**.  The adapted files carry provenance headers naming the source
file and commit (952e5eb); the root NOTICE lists them.

**Status**.  Adopted.  Two copies now exist.  Which one is canonical, and
whether this public repository should be its home, is William's to decide.

---

## What a reader without JavaScript gets

(See also [the hook][hook].)

**Decision**.  The exercise files are the single source: the page's code
block, the editor's first text and the build's checks all read them.  The
build records Agda's highlighting and each goal's type and context, and the
page shows both with no script at all.

**Evidence**.  The built page's HTML holds each exercise as a `pre.Agda`
block with Agda's own classes, the goal display, and the consent sentence;
the scripts are added to this one page, deferred, with content hashes.

**Status**.  Adopted.

---

## Publishing one commit, not a history

(See also [the docs workflow][docs-workflow].)

**Decision**.  The docs workflow deploys with `force_orphan: true`: every
deploy replaces the published branch (`gh-pages` of
universalalgebra/agda-algebras) with one commit holding the built site.

+  The images change whenever a module in their closure does, so a branch
   that kept its history would gain tens of megabytes on most deploys and
   never lose them.
+  The cost: the published branch's existing history is discarded on the
   first deploy after this merges, and no earlier deployed site can be
   restored from it.  Every deployed site is a build of this repository's
   `master`, so any of them can be rebuilt from its commit.

**Evidence**.  The largest published file is the homomorphisms image,
38,727,934 bytes; GitHub warns about a file over 50 MB and refuses one over
100 MB, so it fits as one file, but a history of its versions would not stay
small.

**Status**.  Adopted.

---

## What remains open

+  **A session that outlives one command**.  Keeping the checker running
   between commands needs a way to wait for the reader without blocking.  A
   `SharedArrayBuffer` would do it, and needs the isolation headers.
   JavaScript Promise Integration (JSPI) does it without them: an import
   wrapped as `WebAssembly.Suspending` may answer with a promise, and the
   WebAssembly stack waits for it.  Measured once, as a probe and not as
   shipped code, 2026-10-04 in headless Chromium 153 with
   `crossOriginIsolated` false: the paced host's blocking poll suspended on a
   promise the page resolved with the reader's next command, and one Agda
   process served a load, a goal query, a three-second idle, an unchanged
   reload, an edited reload and another query, then exited 0 at end of
   input.  On the homomorphisms image the first load (with the image's
   fetch) took 12.9 s, each reload 1.45 s and each goal query 45 to 55 ms,
   against about ten seconds for every command as shipped; on the terms image, a
   reload took 140 ms and a query 10 to 19 ms.  Firefox and Safari were not
   tried, so a page built on it needs today's one-run-per-command path as
   its fallback.  That is the follow-up this record proposes.
+  **Smaller deep closures**.  The two imports named in the closures section.
+  **The live site**.  The page has run on a local server, not yet on the live
   host; the first check after the deploy is to open one exercise there and
   confirm the verdict and `crossOriginIsolated` false.
+  **Browsers other than Chromium** were not driven.

---

## Decision log

| # | Decision | Status | Evidence |
|---|----------|--------|----------|
| 1 | The plain checker through its interaction protocol, no language server | Adopted | every goal command answered in Chromium on this library's code |
| 2 | A paced standard input, decided at the blocking poll | Adopted | 10,149 zero-timeout polls and one blocking poll for one load; one load instead of five for a failed file |
| 3 | One run per command, with a reload inside the run after an edit | Adopted | 12.5 s cold load against 1.4 s reload (node) |
| 4 | No isolation headers; the issue's isolation criterion superseded | Adopted | `crossOriginIsolated` false in every run; the live host sends neither header |
| 5 | The closure tiers re-measured and recorded | Recorded | the two tables above |
| 6 | Three images, each behind its own consent; a larger image serves a smaller exercise | Adopted | 0 requests before consent; one image fetched for three exercises |
| 7 | Build natively, prove under the WebAssembly, publish from the site build | Adopted | native interfaces accepted, 1.89 to 1.92 s against 1.90 to 1.94 s |
| 8 | Reuse williamdemeo.org's component with provenance | Adopted | provenance headers and NOTICE |
| 9 | Exercise files as the single source; goals shown without JavaScript | Adopted | the built page's HTML |
| 10 | Deploy one orphan commit, discarding the published branch's history | Adopted | the largest file is 38,727,934 bytes and changes with the library |

---

## References

+  [#577][], the issue this record answers.
+  [docs/playground.md][page], the page; [the site guide's playground
   section][site-guide-playground], how to maintain it.
+  [`build_assets.py`][build-assets], the image builder, and [the
   hook][hook] that publishes and renders.
+  [`wasi.js`][wasi], [`protocol.js`][protocol], [`session.js`][session] and
   [`edits.js`][edits], the worker's modules.
+  [The docs workflow][docs-workflow], which builds and deploys the site.
+  [agda-wasm-dist][], the checker (MIT, Copyright 2024 Agda Web);
   [als-demo][] (MIT, Copyright 2026 Andy Pan); [plfa-playground][] (MIT,
   Copyright 2026 Andy Pan), the reference implementation at
   plfa.isotopy.xyz.

[#577]: https://github.com/ualib/agda-algebras/issues/577
[site-guide-playground]: ../site-guide.md#the-playground
[page]: ../playground.md
[build-assets]: ../../scripts/python/playground/build_assets.py
[hook]: ../../scripts/python/playground/mkdocs_hook.py
[wasi]: ../../docs/assets/js/playground/wasi.js
[protocol]: ../../docs/assets/js/playground/protocol.js
[session]: ../../docs/assets/js/playground/session.js
[edits]: ../../docs/assets/js/playground/edits.js
[notice]: ../../NOTICE
[docs-workflow]: ../../.github/workflows/docs.yml
[agda-wasm-dist]: https://github.com/agda-web/agda-wasm-dist
[als-demo]: https://github.com/agda-web/als-demo
[plfa-playground]: https://github.com/SeungheonOh/plfa-playground
