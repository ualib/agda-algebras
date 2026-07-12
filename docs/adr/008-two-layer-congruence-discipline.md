# ADR-008: Two-layer congruence discipline for finite algebras

## Status

Accepted — 2026-07-12.

## Context

Congruences in this library are `Type`-valued compatible equivalence relations (`Con`, in `Setoid.Congruences`), which is what kernels, quotient algebras, the isomorphism theorems, subdirect representation, and the HSP theorem consume, for finite and infinite algebras alike.  Work package WP-1 of the FLRP research program (PR #462) proved that this semantic type is classically loaded even over finite carriers: `Con 𝑨` contains a *switch congruence* `Cg (λ _ _ → P)` for every proposition `P`, so any order isomorphism `Con 𝑨 ≅ 𝟚` decides between `¬ P` and `¬ ¬ P` — weak excluded middle.  Constructively `Con 𝟚` is the lattice of propositions, not the two-element lattice, so no re-encoding of `Con` avoids this (including the planned Cubical port), and banning switch congruences is not possible without losing the kernel property, since every switch congruence is the kernel of a quotient map.

At the same time, the library's finite-algebra interface (`Setoid.Subalgebras.Subdirect.Finite`) provides decidable congruences (`DecCon`) with decidable pair-membership, and isolates the classical content of "finite" in its `complete` field.  A decision was needed on which object the FLRP formalization quantifies over, and how the classical content is accounted for, before work packages WP-3 through WP-6 proceed.

## Decision

Keep the semantic congruence layer unchanged; build a first-class decidable layer for finite finitary algebras; state all computational results at the decidable layer; and cross between the layers through exactly one registered classical assumption.

+  **Layer S (semantic)**.  `Con` stays as is: the home of kernels, quotients, Noether, HSP, and impossibility results such as the WP-1 no-go theorem.
+  **Layer D (decidable)**.  Finitely presented congruences with decidable membership on finite finitary algebras; reconstruction of every decidable congruence from its list of related pairs; a constructive completeness theorem for the decidable congruences (interface `FiniteAlgebraᵈ`), obtained by enumerating Bool-valued tables; and `Representableᵈ`, over the `DecCon` poset, as the FLRP program's working notion.  The lemma stack (L1–L5) and audits are specified in `docs/notes/flrp-two-layer-congruences.md`.
+  **The bridge**.  The `complete` field of `FiniteAlgebra` — every semantic congruence is `≑`-equal to a decidable one — is the single classical assumption of the program, registered in the planned `FLRP.Assumptions` with its strength documented (between weak excluded middle and excluded middle at the working level).
+  **Terminology**.  The standard notion is called a *finite finitary algebra*: finite carrier, finitely many operation symbols, all of finite arity.  Constructively, the carrier data is a surjective enumeration plus decidable equality — jointly equivalent to Bishop-finiteness, and preferred over a bijective enumeration because surjective enumerations pass to quotients (such as coset spaces `G/H`) without choosing representatives.
+  **Naming and ordering**.  `Representable` (Layer S) and `Representableᵈ` (Layer D) coexist; the Layer-D infrastructure lands before work package WP-3, which is stated at Layer D.

## Consequences

+  **Positive.**  Certificates (WP-6) and positive representability results become constructive and computable; in particular the two-element chain, unprovably representable at Layer S under `--safe`, is representable at Layer D with no axioms.
+  **Positive.**  The classical content of "finite algebra" is auditable at a single site rather than smeared through the development, implementing the assumption-registry discipline of the FLRP roadmap.
+  **Positive.**  Layer D is arguably the faithful formalization of the informal FLRP: the finite algebras of Pálfy–Pudlák and of UACalc computations are exactly the finite finitary objects with concretely presented congruences.
+  **Negative.**  Some statements exist in both S and D forms and must be kept in sync, and the bridge lemma is a standing maintenance obligation.
+  **Negative.**  The constructive completeness proof enumerates exponentially many candidate tables; it exists to discharge the theorem, and practical congruence lists are supplied by certificates instead.
+  **Neutral.**  The WP-1 no-go theorem remains true and useful at Layer S; nothing at Layer D contradicts it.

## Alternatives considered

+  **Restrict `Con` to Bool-valued or generator-presented relations.**  Rejected: kernels of homomorphisms into arbitrary setoids would cease to be congruences, breaking quotients, the isomorphism theorems, and HSP, and infinite algebras would lose their congruence theory entirely.
+  **Adopt classical axioms globally.**  Rejected: the library is `--safe` and postulate-free by policy, and machine-checked constructive content is a stated corpus goal (M8).
+  **Work only at Layer S, parameterizing every result by classical hypotheses.**  Rejected: every computation (certificate checking, small worked examples) would then carry a classical hypothesis it does not need; Layer D keeps the computable fragment axiom-free.

## References

+  Design note — `docs/notes/flrp-two-layer-congruences.md` (lemma stack, audits, work-package impact).
+  Roadmap — `docs/notes/flrp-research-roadmap.md` (§§ 4, 6).
+  Pull request — ualib/agda-algebras#462 (WP-1: `FLRP.Problem`, the no-go theorem); issues #452 (WP-1) and #451 (tracking).
+  Prior art — `Setoid.Subalgebras.Subdirect.Finite` and `docs/notes/m6-8-finite-birkhoff.md` (the `DecCon` interface and the "classical content of finiteness" observation this ADR builds on).
