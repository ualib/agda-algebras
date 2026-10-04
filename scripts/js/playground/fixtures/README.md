# Recorded checker answers

These files are what the playground's checker, Agda 2.8.0 compiled to
WebAssembly, wrote when it was sent the commands the page sends.
`../test_protocol.mjs` and `../test_session.mjs` read them, so that the
page's reader (`protocol.js`) and its plan (`session.js`) are held to Agda's
own output, not to output written by hand from someone's idea of the
protocol.

## The files

Each run is one process over a fresh copy of the image, with stdin paced as
the page paces it: the next command is handed over only when Agda waits for
one.  A run is stored as the following pair of files:

+  `<run>.stdin` is every command line Agda was sent, in order.  The lines
   are spelled out in `capture.mjs`, not made by `protocol.js`, so a line
   here is one Agda parsed whatever the page's code does.
+  `<run>.stdout` is everything Agda wrote, prompts included, trimmed as
   described below.

`sources.json` holds the guest path and the texts the runs loaded: `graft`
is `docs/playground/Graft.agda` as it was at capture, and the others are
that text after an edit, written out as Emacs leaves it.  Each run sends the
sequence the page's plan sends for its request, so every run is also a
whole session that `test_session.mjs` replays.

| Run | Text | Commands | What Agda answered |
| --- | --- | --- | --- |
| `load-context` | `graft` | load, context 0 | one goal, `Term X`, and its context |
| `load-error` | `bad` | load | `UnequalTerms`, with `JumpToError` |
| `give-refused` | `graft` | load, give 0 `t`, context 0 | one `Error`, `UnequalTerms` |
| `case-split` | `graft` | load, case 0 `t`, reload of `split`, context 0, context 1 | `MakeCase`, two clauses |
| `refine-unknown` | `graft` | load, refine 0 (empty), context 0 | `IntroConstructorUnknown`: `ℊ`, `node` |
| `have` | `split` | load, have 0 `σ x`, context 1 | `GoalAndHave`, `Term X` |
| `give` | `split` | load, give 0 `σ x`, reload of `leaf`, context 0 | `GiveAction`, `{"str": "σ x"}` |
| `refine` | `split` | load, refine 1 `node f`, reload of `refined`, context 0, context 1 | `GiveAction`, `{"str": "node f ?"}` |

`capture.mjs` refuses to write a run whose answers do not say what its name
says (its `EXPECT` table), and a text it writes before a reload must match
Agda's own answer (the clauses of the split, the text of the refine).

## How they were captured

On 2026-10-04, under node 22.14.0, from the worktree root, as follows:

```bash
make playground PLAYGROUND_FLAGS=--allow-dirty
node scripts/js/playground/fixtures/capture.mjs \
  .playground/agda-opt.wasm.gz .playground/terms.tar.gz
```

+  **The checker**.  `agda-opt.wasm` from agda-web/agda-wasm-dist release
   `v2.8.0-ghc9.10.3-r0`, sha256
   `0eb63cefff55dd06de30a807440886af804716aeb6a4d7896f814ad2ae9d1f32`
   (uncompressed).
+  **The image**.  `terms.tar.gz`, sha256
   `5e9310962d8e4a097958ea8c6a6243e602fcbd84136440e156233316c59be2dd`
   (tar sha256 `edeff17dba265143ebfbc36053e3b6c78bb8caefdfea68d4aaec722f44671f11`),
   built from agda-algebras `d683c79b` with the playground's files not yet
   committed (its manifest says `"dirty": true`) and standard library 2.3.
   Every load checked exactly one module, so the image's interfaces were
   accepted.
+  **Trimming**.  Each command's answers keep the first `HighlightingInfo`
   line and drop the rest: a load of Graft writes fifteen, the first two
   about 5 KB and 8 KB each, and keeping them all puts a run with two loads
   over 60 KB.  The capture prints how many it dropped from each run (14 for
   a run with one load, 28 for two, 11 for the failed load).  Nothing else
   is touched: every other response, its order, and every prompt are as
   Agda wrote them.  So `readLoad` sees 55 highlighting payloads in a load
   of `graft`, not all of them.

Two captures from two builds of the same inputs came out byte for byte the
same, so a recapture that changes a file means something changed.

## When to capture them again

When the checker or the image builder changes, or when the page starts
sending a command these runs do not cover (add a run to `RUNS` in
`capture.mjs`, with an `EXPECT` entry).  Run the command above, then the two
tests.  A test that fails after a recapture is either Agda answering
differently, which the test's expectation should follow knowingly, or a
fault in the page's code that the old answers did not show.

## What the recordings show

These are facts about Agda's answers, not about the page, and each one is
pinned by a test, as follows:

+  **The prompts**.  The host's `next` sees nothing before the first
   command; after that, a `JSON> ` before each command's answers, and one
   more at the end, where Agda waits for the next command.
+  **Give always answers with text**.  A give or refine sent with `noRange`,
   as the page sends every one, is answered `{"str": ...}`, Agda's own
   reprinting.  Agda answers `{"paren": ...}` only for a give whose range is
   not `noRange` (`literally` in `give_gen`,
   `src/full/Agda/Interaction/InteractionTop.hs`), so no run here has one.
+  **`Direct`, not `Indirect`**.  The page sends every goal command `None
   Direct`.  Sent `None Indirect`, as it first did, a refused give was
   answered with the error and then a second `Error`, `/tmp: openTempFile:
   does not exist (No such file or directory)`: Agda tries to write the
   error's highlighting to a temporary file, and the image has no `/tmp`.
   Sent `None Direct`, the same give is answered with one `Error`; that is
   what `give-refused` records.
+  **A new goal has no range**.  A refine that creates a goal lists it with
   `"range": []`, because the text it would live in was never written.
+  **Positions are code points**.  `pos` counts code points from 1, and
   every text here has astral letters (𝑆, 𝓞, 𝓥) before its goals, so a
   position used as a UTF-16 offset lands on the wrong character.
