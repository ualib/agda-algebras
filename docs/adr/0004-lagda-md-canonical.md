# ADR-004: Markdown-literate Agda (`.lagda.md`) as the canonical literate format

## Status

Accepted — 2026-04-24.

## Context

Through the 2.x line, `agda-algebras` maintained literate sources in two places and two formats: minimal `src/X/Y/Z.agda` skeletons carrying only the `OPTIONS` pragma and the `module ... where` header, paired with LaTeX-literate `docs/lagda/X/Y/Z.lagda` files containing the actual prose and code inside `\begin{code}` / `\end{code}` blocks.  The type checker reads the skeletons; the `make html` target reads the LaTeX-literate files through `admin/generate-tex` and `admin/generate-html` and renders them into the Jekyll site at [ualib.org](https://ualib.org).

This split is a maintenance hazard: prose and proof live in two files that must be held in sync by hand, and every new module multiplies the number of such pairs.  It also directly undermines the library-as-corpus pillar: a training-corpus extractor that pairs theorem statements with their prose explanations must recover the pairing from path correspondence, with no checking that the pairing is complete or current.  (If `docs/lagda/X/Y/Z.lagda` drifts from `src/X/Y/Z.agda`, the extractor produces mismatched records and nothing in the build pipeline catches it.)

Three resolutions must be made before implementation begins:

1.  What happens to `docs/lagda/` after migration?
2.  Are there files that should remain in LaTeX-literate form?
3.  How does the Jekyll rendering pipeline change?

## Decision

**Markdown-literate Agda (`.lagda.md`) is the canonical literate format for `agda-algebras`.**  Each module is a single `src/X/Y/Z.lagda.md` file that is both type-checked by `make check` and rendered by `make html`.

The three open questions resolve as follows.

+  **`docs/lagda/` is deleted.**  Every file moves to the matching `src/X/Y/Z.lagda.md` path.  External bookmarks pointing at specific `docs/lagda/X.lagda` paths will break; this is accepted as a one-time cost, announced in the 3.0 CHANGELOG.  The ualib.org rendered site is unaffected because it serves HTML under `X.Y.Z.html` paths, not `docs/lagda` paths.
+  **No files remain in LaTeX-literate form under `src/` or `docs/lagda/`.**  Paper companions that are co-built with a LaTeX paper PDF live under `docs/papers/`, separately from the library proper; that location is out of scope for this ADR and retains its LaTeX-literate shape as long as the companion paper expects it.  The principle is that `src/` and the rendered ualib.org site have one canonical format; `docs/papers/` is a different kind of artifact and has its own conventions.
+  **The Jekyll pipeline consumes `agda --html` Markdown output directly.**  `agda --html --html-highlight=code` on a `.lagda.md` file produces Markdown with fenced code blocks that Jekyll renders natively.  `admin/generate-tex` is removed.  `admin/generate-html` is either removed or reduced to a thin wrapper that invokes `agda --html` with the library's options; the post-processing of `.tex` files goes away.

## Consequences

+  **One source of truth per module.**  Prose and proof sit in the same file; drift between them is impossible.  The `src/*.agda` skeletons disappear entirely, as does the dual-tree structure of `src/` vs `docs/lagda/`.
+  **Training-corpus extraction becomes straightforward.**  A walker over `src/**/*.lagda.md` can emit `(prose, code-block)` records without having to reconcile two paths; the proximity of prose paragraph to code block is preserved structurally.  This is the prerequisite for M8-1 (publish the (theorem, proof) corpus), and it moves that milestone substantially closer to trivial.
+  **The documentation site's URL structure is unchanged.**  `agda --html` produces `X.Y.Z.html` for both `.lagda` and `.lagda.md` inputs; external HTML links continue to resolve.
+  **External bookmarks into the repository tree that point at `docs/lagda/X/Y/Z.lagda` break.**  The cost is bounded — the file is a 3.0-era reorganization rather than a URL-scheme change — and is announced in CHANGELOG with a redirect table for the modules most likely to be linked from external sources (Preface, Demos.HSP, Setoid.Algebras.Basic).
+  **New contributors author in Markdown, not LaTeX.**  Lower onboarding friction; GitHub renders `.lagda.md` natively in the web UI; editor tooling (VSCode, Emacs) previews the Markdown cleanly.  This is a non-trivial ergonomics improvement paid for by the migration.
+  **Agda tooling for `.lagda.md` is production-quality.**  Agda 2.6+ has treated `.lagda.md` as a first-class literate format; `1Lab` is the large-scale existence proof.  No language-level risk.
+  **The `admin/generate-tex` pipeline goes away.**  That removes roughly the nontrivial portion of the current `admin/` scripting.  The fallback implication is that if we ever need to produce a LaTeX rendering of the library (for a paper, say) we would author a new small pipeline from `.lagda.md` to LaTeX; this is a modest cost that a future paper project would absorb.
+  **Paper companions under `docs/papers/` keep their current shape.**  The decision is explicit: `docs/papers/` is a separate tree whose artifacts are co-built with external LaTeX documents, and retrofitting those to Markdown-literate is out of scope.  If a future paper project prefers to author in `.lagda.md`, that decision can be made per-paper without disturbing this ADR.

## Alternatives considered

+  **Keep the dual-file `.agda` skeleton + `.lagda` content structure indefinitely.**  Rejected because it is the status quo whose costs motivated this ADR: drift-prone, corpus-hostile, and a maintenance tax on every new module.
+  **Consolidate to single-file LaTeX-literate (`.lagda`) with prose inline, keeping LaTeX as the canonical format.**  Rejected because (i) the LaTeX syntax is higher-friction for new contributors than Markdown, (ii) GitHub's native rendering of `.lagda` is poor whereas `.lagda.md` renders cleanly in the web UI, (iii) the modern Agda ecosystem (1Lab most visibly) has standardized on Markdown-literate for exactly the same reasons, (iv) the corpus-extractor argument applies identically to both formats, but the Markdown form is meaningfully easier for downstream consumers who aren't Agda-aware.
+  **Move to `.agda` with extensive comment blocks; drop literate programming entirely.**  Rejected because literate programming with rendered HTML is a central feature of the library's presentation — ualib.org is the interface most readers encounter — and the HTML rendering is materially better with fenced code blocks than with commented Agda.

## References

+  Issue M1-8 — [Consolidate literate and bare-Agda sources into .lagda.md](https://github.com/ualib/agda-algebras/issues/280).
+  [1Lab](https://github.com/plt-amy/1lab) — large-scale Agda library authored entirely in `.lagda.md`.
+  [Agda literate-programming documentation](https://agda.readthedocs.io/en/latest/tools/literate-programming.html).
+  ADR-001 — Setoid as canonical (establishes the one-canonical-form-per-concept principle this ADR extends).


