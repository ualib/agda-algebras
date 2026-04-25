# ADR-003: Cubical Agda as the canonical long-term target

## Status

Accepted — 2026-04-24.  Implementation deferred to 4.0.

## Context

The setoid-based formulation adopted in ADR-001 buys the library full constructivity at a well-understood cost: every definition carries an equivalence relation, every homomorphism proves respect for that equivalence, and the library must maintain a small discipline of never reaching for propositional equality where the setoid equivalence is the right tool.  A universal algebraist working at the whiteboard would never write any of this explicitly; the setoid machinery is type-theoretic plumbing that exists because Martin–Löf type theory, as traditionally formulated, does not provide a native account of equality that respects quotients and equivalences.

Cubical type theory (as implemented in `--cubical` mode of Agda and in the `cubical` and `1Lab` libraries) provides exactly that native account.  Equality is the path type; the structure identity principle (SIP) makes isomorphic structures propositionally equal; quotients are first-class.  For a universal-algebra development, the consequence is that the setoid-specific machinery that currently mediates between "equal" and "equivalent" would disappear, and proofs would read the way mathematicians write them: equations transport along isomorphisms by substitution, without the intervening apparatus.

Cubical Agda is not yet the canonical target.  Two considerations hold it back.  First, the ecosystem is still young: stdlib's `Algebra.Bundles`, on which the Classical layer's interop depends, is not cubical-compatible; neither is a substantial fraction of imports shared with the rest of the Agda community.  Second, the primary audience of `agda-algebras` — universal algebraists and formal-methods engineers — is still overwhelmingly working in MLTT-with-setoids or propositional-equality settings; a cubical-only library would underserve them.

The 3.0 cycle does not ship a cubical canonical tree, but it commits to a design discipline that makes the 4.0 port mechanical rather than a second redevelopment.

## Decision

Cubical Agda is the canonical long-term target for `agda-algebras`.  The specific commitments:

+  **Version 4.0 promotes `src/Cubical/` to canonical status**; `src/Setoid/` at that point assumes a role analogous to `src/Legacy/Base/` today — frozen, type-checked, not receiving new development.  The specific promotion criteria are listed under "Promotion criteria" below.
+  **The 3.0 development is authored with cubical portability in mind.**  Equations are stated in terms of `Algebra.Domain`'s equivalence, never reaching for setoid-specific machinery where a cubical analog does not exist.  This discipline is enforced by the style guide and by code review; its correctness is validated by M5-1, which ports a single classical structure (Monoid) to cubical and verifies the port is substantive mechanical.
+  **M5-1 is the proof-of-concept:**  `Cubical/Algebras/Basic.agda`, `Cubical/Algebras/SIP.agda`, and a `Cubical/Classical/Monoid.agda` obtained by substitutional derivation from its Setoid analog.  Once M5-1 lands, the design discipline is validated; if it fails, the portability discipline is revised and the failure is documented in a follow-on ADR.

## Promotion criteria

4.0 may promote `src/Cubical/` to canonical status once all of the following hold:

1.  `Cubical/Algebras/Basic.agda` and `Cubical/Algebras/SIP.agda` are stable and exercised by at least the content of `Setoid/Algebras/`.
2.  A non-trivial classical structure (Monoid or beyond) has been ported from `Classical/Structures/X.agda` to `Cubical/Classical/X.agda` by substantively mechanical substitution, without reformulating any equation.
3.  Agda's cubical mode has reached a maturity level where the `--safe --cubical` combination is robust across the library's use cases.  The criterion for "robust" is that the CI pipeline runs the cubical track without reproducible bugs in the language implementation for a two-month steady-state period.
4.  Stdlib (or a recognized cubical companion library such as `cubical` or `1Lab`) provides the interop surface area that `Classical/Bundles/` currently relies on.

Not all four need hold in the same quarter; the promotion is triggered when the last one flips.  The follow-up ADR at promotion time will record which specific versions and libraries satisfied each criterion.

## Consequences

+  **The 3.0 development is not "set theoretic" in the sense it would have to be abandoned at 4.0.**  The setoid formulation is the path of record for the current cycle; it is preserved in `Legacy/Setoid/` at 4.0 and remains type-checking.
+  **A portability discipline constrains what new contributions may assume.**  Theorems in `Setoid/` and `Classical/Structures/` that would require setoid-specific machinery without a cubical analog must either find a cubical-portable alternative or be marked as non-portable in the module header.  The constraint is real but modest; most universal-algebra theorems are portable because they are stated about the algebra's equivalence, not about the specific representation of that equivalence.
+  **M5-1 is a genuine validation, not a formality.**  A substantive failure of the Monoid port would surface in M5-1, and the response would be to relax the commitment or to redefine the discipline, not to paper over the failure.  ADR-003 is appropriately tentative on the implementation side.
+  **The library has a forward-looking story for the next decade.**  Cubical Agda is the direction the Agda ecosystem as a whole is moving (1Lab is the most visible exemplar); committing to it publicly aligns `agda-algebras` with that trajectory and makes the case that its setoid-era proofs remain useful — as first-class training data, if nothing else — after the foundations shift.

## Alternatives considered

+  **Keep Setoid canonical indefinitely; never promote to cubical.**  Rejected because the cubical trajectory is the mathematically natural substrate for universal algebra (isomorphism *is* equality, quotients are first-class, equations transport substitutionally), and because the cost of maintaining the setoid-specific plumbing compounds as the library grows.  A library committed to the long term should choose the foundation its successors will thank it for.
+  **Start cubical immediately; skip the setoid cycle.**  Rejected because (i) the stdlib bundle interop that `Classical/` depends on is not cubical-ready, (ii) the user base is not cubical-ready, and (iii) the library has a working Setoid-based HSP proof that would be thrown away and re-developed with no compensating mathematical gain.  The setoid cycle is not a detour; it is the shipping vehicle for a decade of prior work, and the portability discipline it trains contributors in is a precondition for the cubical cycle succeeding.
+  **Commit to cubical aspirationally but without the portability discipline.**  Rejected because this is how the library ends up with two incompatible trees at 4.0 — a setoid one that works and a cubical one that doesn't, with no mechanical migration path.  The discipline is the asset; without it the commitment is empty.

## References

+  Issue M5-1 — [Cubical/Algebras/Basic with SIP and Monoid port](https://github.com/ualib/agda-algebras/issues/XX).
+  ADR-001 — Setoid as canonical development tree for 3.0.
+  ADR-002 — Classical layer design (which makes the portability discipline concrete).
+  Vezzosi, Mörtberg, and Abel (2019), *Cubical Agda: A Dependently Typed Programming Language with Univalence and Higher Inductive Types*, JFP.
+  The `1Lab` project — [https://1lab.dev](https://1lab.dev).
+  The Agda `cubical` library — [https://github.com/agda/cubical](https://github.com/agda/cubical).


