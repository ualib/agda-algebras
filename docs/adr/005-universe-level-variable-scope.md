<!-- File: docs/adr/005-universe-level-variable-scope.md -->

# ADR-005: Scope of the `𝓞` / `𝓥` universe-level variables

## Status

Accepted — 2026-06-06 (M4-3).

## Context

`𝓞` and `𝓥` are not generic level variables.  They are *semantically charged*: throughout the library `𝓞` denotes the universe level of a signature's *operation-symbol* type and `𝓥` the level of its *arity* type.  The convention is load-bearing — `Signature 𝓞 𝓥`, `Op`, `Term`, the `ov` shorthand, and every signature-parametrized module read against it — and the style guide already states that "using `𝓞` or `𝓥` for anything else is a bug."

They are currently declared once, as a *public* (non-`private`) `variable 𝓞 𝓥 : Level` in `Overture.Signatures`, co-located with the `Signature` type whose two levels they name, and re-exported through the `Overture` umbrella.  Signature-parametrized modules pull them in by name (`open import Overture using ( 𝓞 ; 𝓥 ; Signature )`).  Being public, they are also in scope wherever `Overture` is opened without a `using` filter — which the style guide confines to umbrella aggregators.  The convenience is real, but a public `variable` can be shadowed by a careless local declaration, and a newcomer may not immediately know where an unqualified `𝓞` came from.

A decision is forced now (M4-3) by a second, concrete problem: the handling is **not uniform**.  Although the style guide says "never re-declare them," `𝓥` is in fact re-declared as a `private variable` in `Overture.Operations` and `Setoid.Relations.Discrete` (and in several frozen `Legacy/Base/*` modules), drifting from the canonical declaration.  Issue #269 asks that `𝓞` / `𝓥` be handled uniformly and the rule recorded.  Three options were on the table:

1.  Keep `𝓞` / `𝓥` as a single public `variable` in `Overture.Signatures`; document the rule and import them by name.
2.  Make them `private` in `Overture.Signatures`; every downstream module re-declares its own `variable 𝓞 𝓥 : Level`.
3.  Move them to a dedicated `Overture.UniverseLevels` module, imported explicitly.

## Decision

Adopt **Option 1**.  `𝓞` and `𝓥` remain a single public `variable 𝓞 𝓥 : Level` declared in `Overture.Signatures`, co-located with the `Signature` type whose levels they name; downstream modules import them by name from `Overture` (or `Overture.Signatures`) and never re-declare them.  Using either name for anything other than its charged meaning remains a bug.

Applying this uniformly (issue #269's second acceptance criterion) means converting the live-tree drift sites — the `private variable … 𝓥 …` declarations in `Overture.Operations` and `Setoid.Relations.Discrete` — to import the canonical `𝓥` instead.  The frozen `Legacy/Base/*` tree is out of scope per ADR-001 and the M4 audit; its local re-declarations are left untouched.  The style-guide section "The `𝓞` / `𝓥` convention" is updated to drop the "tracked in M4-3 / interim" hedge and state the rule as settled.

## Consequences

+  **One canonical declaration, co-located with its meaning**.  A reader who lands on `Signature 𝓞 𝓥` finds the two levels, their charged semantics, and the prose explaining them in the same module — the "one canonical form per concept" principle applied to a convention rather than a definition.
+  **Lowest churn of the three options, and it ratifies the de-facto rule**.  The style guide already mandates Option 1's behavior as an interim rule, so this decision only removes the "interim" hedge and fixes the two live drift sites; no `using ( 𝓞 ; 𝓥 ; Signature )` import is touched.
+  **The common case stays a one-line import**.  Signature-parametrized modules — the majority — need `Signature` together with its two levels, so a single `open import Overture using ( 𝓞 ; 𝓥 ; Signature )` is exactly right.
+  **The public `variable` is not leak-proof** (negative).  It stays in scope under a bare `open import Overture`, so a local declaration can shadow it.  This is mitigated, not eliminated: the `using`-list discipline confines bare opens to umbrella aggregators, and the "never re-declare / off-convention-use-is-a-bug" rules become settled policy instead of an open question.
+  **A levels-only consumer acquires a `Signatures` dependency** (negative).  A module that needs `𝓥` but not `Signature` — `Overture.Operations`, whose `Op` indexes by an arity level — must import the level from `Overture.Signatures`, coupling two small foundational modules (acyclically).  Option 3 would have avoided this edge.

## Alternatives considered

+  **Option 2 — `private` in `Overture.Signatures`, re-declare downstream**.  Rejected.  It fragments a single charged convention across dozens of modules, contradicting "one canonical form per concept"; it reverses the existing "never re-declare" rule; it carries the widest blast radius (boilerplate in every signature-parametrized module, and every `using ( 𝓞 ; 𝓥 )` import removed); and it makes "off-convention use is a bug" harder to police once the names are declared locally everywhere.  Its one merit — matching stdlib's per-module `private variable` idiom — does not transfer, because stdlib's `a` / `ℓ` are generic whereas `𝓞` / `𝓥` carry fixed meaning.
+  **Option 3 — dedicated `Overture.UniverseLevels` module**.  Considered; the closest runner-up.  It keeps one source of truth, makes the import self-documenting (`open import Overture.UniverseLevels using ( 𝓞 ; 𝓥 )`), and lets a levels-only consumer avoid depending on `Overture.Signatures`.  Rejected as the primary choice because it decouples the `𝓞` / `𝓥` semantics from the `Signature` type they describe (where co-location most helps a reader); it makes the common signature-parametrized case a two-import affair rather than one; it does not actually remove the leak unless the `Overture` umbrella also stops re-exporting the new module — trading the leak for churn at every call site and a less convenient API; and a whole module for two `variable` declarations is marginal over-engineering.  It remains the natural fallback if the decoupling or full leak-elimination is later judged worth the cost.

## References

+  Issue M4-3 — [Design discussion: scope of `𝓞` and `𝓥`](https://github.com/ualib/agda-algebras/issues/269).
+  `docs/STYLE_GUIDE.md` — sections "The `𝓞` / `𝓥` convention" (the interim rule this ADR settles) and "Other level variables".
+  `src/Overture/Signatures.lagda.md` — the declaration site and the co-located semantics prose.
+  ADR-001 — Setoid as canonical tree; the `Legacy/Base/` freeze that scopes Legacy out of the uniformity sweep.
