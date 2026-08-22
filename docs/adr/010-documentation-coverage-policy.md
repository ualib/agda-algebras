# ADR-010: Documentation coverage policy for public definitions

## Status

Accepted — 2026-08-22.

## Summary

This ADR settles how much prose the library owes each of its public definitions, and how that obligation is enforced.

Documentation here serves two audiences at once.  A human reading the library should find, above each definition, a sentence or two saying what it is mathematically and when to reach for it; that is what makes a library a pleasure to use rather than a puzzle.  A machine reading the library — a retrieval agent, or the training-corpus extractor of [#275][] — needs the same prose, but attached to individual definitions rather than to pages.  The two needs pull in opposite directions: per-definition attachment invites chopping each page into one definition per code block, and a page chopped that way stops being readable as prose.

The decision resolves that tension by refusing to chop the pages.  Concretely:

+  **Every code fence carries a real paragraph.**  This is the enforced bar, checked in CI, and the one the nine sub-issues of [#268][] close.  A "real" paragraph means prose about the mathematics; a heading alone, the boilerplate `This is the [X][] module of the …` sentence alone, and an empty run all fail.
+  **One definition per fence is explicitly rejected** as a repository-wide rule.  It enforces layout rather than content — 1963 paragraphs each restating a type signature would satisfy it — and it destroys the narrative reading that makes the library usable as an exposition of universal algebra.
+  **Per-definition prose is recovered by extraction, not by fragmentation.**  A prose block that *names* the definitions beneath it can be split per definition mechanically; a set of disconnected paragraphs cannot be reassembled into a narrative.  The derivation runs from the narrative to the reference, never the reverse, so the narrative is the source of truth and the extractor does the work.
+  **Two advisory measures are reported but not gated**: how many definitions their own prose *names*, and how many are *used* anywhere in the library.  The first detects prose that has drifted away from the code beneath it.  The second says where documentation effort pays off.
+  **Enforcement is a ratchet, not a wall.**  `make docstrings` fails only when the count of undocumented definitions rises above a ceiling recorded in the `Makefile`, so the rule is enforced from the day it lands and the backlog can only shrink.

Nothing mechanical can decide whether a paragraph is any *good*.  That stays a review responsibility, and the style guide's test — "a comment that only restates the type signature in English fails the 'why would I use this?' test" — remains the standard applied by human review.

The state of the corpus when this ADR was accepted, from `make docstrings`, is as follows:

| measure | value |
|---|---|
| public definitions, in 307 live modules | 3239 |
| definitions whose fence carries no real prose (the enforced bar) | 201 |
| definitions failing the rejected one-per-fence bar | 1963 |
| definitions their own prose mentions by name (advisory) | 19% |
| definitions referenced somewhere in the live trees (advisory) | 80% |
| modules opening with nothing beyond the boilerplate sentence | 50 |

## Context

`docs/STYLE_GUIDE.md` has long required that a public definition carry "a prose comment block immediately above it", and that in a `.lagda.md` module that prose be "Markdown preceding the code fence (not `-- |` comments inside it)".  The rule was never enforced, and [#268][] asked for a "`grep`-based audit" that finds zero public definitions without one.

Three things made that request impossible to satisfy as written, and forced a decision rather than a fix.

**The check cannot be a grep.**  The library holds essentially no `-- |` docstrings, so a comment-grep reports the whole corpus as undocumented; and a prose-grep cannot tell which definition a paragraph belongs to.  Worse, almost every definition in the corpus is *indented* inside an anonymous `module _ … where`, so even a structural tool that looked only at column 0 would find almost nothing.  Checking the rule requires parsing literate structure and Agda's layout rule together, which is what `scripts/python/docstring_audit.py` ([#537][]) does.

**"Immediately above" is ambiguous, and the two readings differ by an order of magnitude.**  In a literate file prose can only precede a *fence*, and a fence may hold many definitions.  Read leniently — the fence carries prose — 201 definitions are undocumented.  Read literally — the prose must sit immediately above *this* definition, so each definition needs its own fence — 1963 do.  The second reading is not merely more work; it changes what the library is, because satisfying it means breaking every multi-definition code block, including blocks indented inside a shared `module _ … where`.

**The library is also meant to read as an exposition.**  `Examples/Demos/HSP.lagda.md` is the published TYPES 2021 paper as a literate module, and much of `Setoid/` is written in the same register.  A future "universal algebra textbook" presentation is a plausible derived asset.  A rule that fragments every page into one-definition blocks forecloses that, and forecloses it in the direction that is hard to undo.

Against that stands the machine audience, which is not hypothetical.  [#275][] asks for a training corpus carrying a prose summary per definition, and formalverification/agda-native-air#120 has already published 11,666 rows extracted from this library with types and proof terms but *no prose at all*, because an Agda-internal extractor cannot see Markdown.  Prose is the thing this repository uniquely holds, and it is worth little to that consumer if it is attached only to pages.

## Decision

Enforce prose per *fence*, keep the pages narrative, and recover per-definition prose by extraction.

+  **The enforced bar.**  Every code fence in the live trees is preceded by at least one real paragraph of prose, and every module opens with prose beyond the boilerplate sentence.  `make docstrings` checks this and gates CI.
+  **The rejected bar.**  One definition per fence is not required.  A fence may introduce a family of related definitions under a single block, and should when the definitions are genuinely a family.
+  **The quality target.**  A prose block should *name* each definition beneath it.  This is reported by `make docstrings` as the `named` column and is deliberately not gated: it is a drift indicator, satisfiable by merely listing names, and no substitute for review.
+  **The extraction contract.**  `docstring_audit.py --json` emits one record per definition, keyed on `qname`, carrying the prose attached to its fence.  That is the join key with the Agda-internal corpus of [#275][], and the reason named coverage matters: the more reliably prose names its definitions, the more precisely a later extractor can attribute sentences to individual names.
+  **Enforcement is ratcheted.**  `DOCSTRING_MAX_GAPS` in the `Makefile` records the current count; `make docstrings` fails above it and prints a nudge below it.  A hard gate on a backlog of 201 would fail every unrelated pull request and be reverted within a week.
+  **What counts as a public definition** is fixed by the tool, and these are the judgement calls it embodies:
   +  A definition is public when no enclosing block hides it.  `private`, a definition's `where` body, and `let` hide it; an anonymous `module _` does not, since its contents export to the parent scope; a named submodule qualifies it instead.
   +  Record fields, record members, and data constructors are documented by their record or datatype, not separately.  They are public API, but Markdown cannot be interleaved between a record's fields, so requiring separate blocks would be unsatisfiable.
   +  Declarations inside a hidden `<!-- ```agda … ``` -->` preamble fence are reported but not counted.  Agda exports them; no rendered page shows them.  There are 49, which is itself a finding worth acting on separately.
   +  Prose carries across a hidden fence.  A preamble renders as nothing, so prose written above it sits, on the page, immediately above the next visible code block.
+  **Generated modules are out of scope.**  The 32 modules under `*/Certificates/*` are machine-emitted data, not API; they are documented once at the family level rather than per declaration.

## Consequences

+  **Positive.**  The rule becomes enforceable today rather than after a long-tail cleanup, because the ratchet separates "do not make it worse" from "make it perfect".
+  **Positive.**  Pages stay readable end to end, so the exposition register of `Setoid/` and the HSP demo survives, and a derived textbook presentation remains possible.
+  **Positive.**  The machine audience is served without changing the source: one traversal produces both the audit and the harvest, so [#268][] and [#275][] cannot drift apart into two tools that disagree at the hard cases.
+  **Negative.**  A definition sharing a fence with others may still lack a sentence of its own.  The `named` column measures exactly this residue — 19% coverage at acceptance — and closing it is ongoing work with no completion date.
+  **Negative.**  The enforced bar is weaker than the style guide's literal words.  The style guide should be reconciled with this ADR; until it is, the two texts disagree, and this ADR governs.
+  **Negative.**  Both advisory measures are proxies.  `named` is satisfied by listing names without saying anything.  `used` is textual and cannot distinguish two modules that declare the same short name; 240 names are ambiguous in that way, and the tool reports the figure rather than hiding it.
+  **Neutral.**  `used` is not a dead-code measure and must not be read as one.  In a proof library an unreferenced definition is usually a terminal result — the `roundtrip-*` faithfulness lemmas of `Classical/Bundles/` are the clearest case — an example, or an entry point for consumers outside this repository.  Of the 626 unreferenced definitions, most are of that kind.
+  **Neutral.**  The work is split into nine per-subtree sub-issues of [#268][], sized to one or two pull requests each; each lowers `DOCSTRING_MAX_GAPS` by the number it clears.

## Alternatives considered

+  **One definition per fence, repository-wide** (the literal reading of the style guide).  Rejected because it enforces layout rather than content, costs 1963 blocks against 201, and destroys the narrative reading.  It is not rejected as a *local* choice: `Setoid.Algebras.Basic` ([#538][]) meets it, and modules that are genuinely reference material may do the same.
+  **One definition per fence, with a textbook presentation derived later.**  Rejected because the derivation does not run in that direction.  Reference to narrative requires inventing connective tissue, ordering, and motivation — precisely the human-authored part.  Narrative to reference is mechanical whenever the prose names its definitions, so the narrative is the better source of truth.
+  **`-- |` docstrings inside the fences**, as most Agda and Haskell projects use.  Rejected by ADR-004 and the style guide already: the literate format exists so that prose is first-class Markdown, and in-fence comments render poorly and serve the corpus worse.
+  **A hard CI gate with no ratchet.**  Rejected because it would fail every unrelated pull request until 201 prose blocks were written, which in practice means the check is disabled instead.
+  **Gating on named coverage.**  Rejected for now as premature: at 19% it would fail everything, and the measure is too easily gamed to be a gate.  Revisit if coverage rises and the measure proves sound.

## References

+  Issue — [#268][], the docstring pass, and its nine sub-issues #539–#547.
+  Issue — [#275][], the (theorem, proof) training corpus.
+  Pull request — [#537][], the audit tool, the baseline measurements, and the CI ratchet.
+  Pull request — [#538][], `Setoid.Algebras.Basic` as the worked exemplar.
+  Issue — [#387][], the `<a id>` heading-anchor sweep, the other half of M4-2, completed separately.
+  Prior art — formalverification/agda-native-air#120, the Agda-internal corpus this repository's prose is meant to join.
+  `docs/STYLE_GUIDE.md` §§ "Every public definition has a prose comment block", "Module headers have comment blocks", "Prose belongs in Markdown".
+  `docs/audits/M4-style-audit.md` §§ 3, 3b, 4.

[#268]: https://github.com/ualib/agda-algebras/issues/268
[#275]: https://github.com/ualib/agda-algebras/issues/275
[#387]: https://github.com/ualib/agda-algebras/issues/387
[#537]: https://github.com/ualib/agda-algebras/pull/537
[#538]: https://github.com/ualib/agda-algebras/pull/538
