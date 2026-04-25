# ADR-002: Classical structures as Σ-typed cores with record-typed bundle views

## Status

Accepted — 2026-04-24.

## Context

The 3.0 reconstruction adds a `src/Classical/` tree holding specific algebraic theories — semigroups, monoids, groups, lattices, rings — built on the universal-algebra foundation established in `src/Setoid/`.  Every classical structure `X` must answer three questions about its representation:

1.  What is the type-theoretic shape of `X`?  A record with named projections, or a Σ-type pairing an algebra with a proof it satisfies the `X`-theory?
2.  How does `X` interoperate with the Agda standard library's `Algebra.Bundles`?  Stdlib provides `Algebra.Bundles.Semigroup`, `Monoid`, and so on as records; anyone interoperating with stdlib-typed code must convert.
3.  How is `X` kept portable to the eventual cubical Agda formulation (ADR-003), where the equivalence underlying the algebra becomes a path type?

These three questions interact.  A record-typed core is easier to read at use sites (named projections, instance arguments) but commits the library to a specific projection vocabulary that fights the stdlib-shaped bundle idiom when we want bidirectional conversion.  A Σ-typed core matches the mathematical reading "`X` *is* an algebra equipped with a proof it satisfies the `X`-theory" and is also the formulation most robust to changes in the underlying equivalence — crucial for the cubical port.

A related question: what does "classical" mean in this subtree?  It does not mean "classical logic" — the library stays constructive throughout.  `Classical/` names the *tradition* of concrete algebraic structures (groups, rings, lattices) as distinct from the universal-algebraic treatment of algebras-over-a-signature that lives in `Setoid/`.  An alternative name considered was `Concrete/`; `Classical/` was retained because "classical algebraic structures" is standard terminology in the universal-algebra literature (Burris and Sankappanavar use it throughout).

## Decision

Each classical structure `X` is represented in two parallel forms:

+  **Core (Σ-typed)** at `Classical/Structures/X.agda`:

    ```agda
    X : (α ρ : Level) → Type _
    X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Eₓ
    ```

    where `𝑆ₓ` is the signature of `X` (in `Classical/Signatures/X.agda`) and `Eₓ` is the set of defining equations (in `Classical/Theories/X.agda`).
+  **Bundle view (record-typed)** at `Classical/Bundles/X.agda`, matching the stdlib shape `Algebra.Bundles.X`, with bidirectional conversion functions to and from the Σ-typed core.

The core is the canonical form for library-internal definitions and theorems.  The bundle view exists solely for stdlib interoperability.

Equations in the Σ-typed core are stated purely in terms of the `Algebra.Domain` equivalence (the setoid's `_≈_`), never in terms of propositional equality or any other setoid-specific feature.  This is the portability discipline that makes the eventual cubical port (ADR-003) mechanical.

A helper `fromPropEq : (A : Type α) → ... → X α α` lets users construct classical structures from propositional-equality-based definitions without writing explicit setoid wrapping.

Each classical structure ships as a quintuple: `Classical/Signatures/X.agda`, `Classical/Theories/X.agda`, `Classical/Structures/X.agda`, `Classical/Bundles/X.agda`, and a level-fixed veneer `Classical/Small/Structures/X.agda` specialized to the common `ℓ₀`–`ℓ₀` case.

## Consequences

+  **Definitions read the way a universal algebraist thinks.**  "A monoid is a magma satisfying the monoid equations" is exactly what `Σ[ 𝑨 ∈ Algebra 𝑆ₘ α ρ ] 𝑨 ⊨ Eₘ` types.  This is pedagogically valuable for the library-as-training-corpus role.
+  **Stdlib interop has a fixed cost paid once per structure.**  Every `Classical/Bundles/X.agda` is a small, mechanical file: one record definition, two conversion functions, a round-trip proof.  The cost is predictable and the pattern is copy-paste.
+  **Cubical portability is a property of the code, not a retrofit.**  Since no theorem in `Classical/Structures/X.agda` may reach for setoid-specific machinery, the 4.0 port (ADR-003) is substitutional — replace the setoid equivalence with the path type, rerun the type-checker, fix any fallout — rather than a second rewrite.  Enforcing this discipline is a design cost paid up front.
+  **Use-site ergonomics are slightly worse than with a record-typed core.**  A proof that works against a Σ-typed monoid projects with `proj₁` and `proj₂` rather than named fields.  This is annoying in short proofs; we offset it with named convenience accessors (`Domain`, `Signature`, `equations`) defined next to each structure.
+  **The core `Algebra` type stays a record.**  This is not inconsistent with the Σ-for-classical-structures choice: `Algebra` has multiple meaningful named projections (`Domain`, `Interp`, …) and is inhabited many times across the library; `Semigroup` naturally decomposes as "algebra + proof," which a Σ expresses directly.  The rule for future decisions is in `docs/STYLE_GUIDE.md` — record when there are three or more meaningful named projections or when stdlib interop demands it, Σ when the structure has a "bundled-together" mathematical reading.
+  **A parallel record implementation of any classical structure is a bug.**  The `Base/Structures/Basic` vs `Base/Structures/Sigma` dual is exactly the mistake this ADR codifies against; see the STYLE_GUIDE for the explicit rule.

## Alternatives considered

+  **Record-typed core, no Σ-typed variant**.  Rejected because (i) the stdlib bundle idiom already exists and we would effectively be re-deriving it with our vocabulary, (ii) the mathematical reading is weaker, (iii) the record-typed core is more fragile under the cubical port since record projection definitions mention the underlying equivalence more intrusively than Σ projection does.
+  **Two record variants in parallel (one library-internal, one stdlib-shaped)**.  Rejected for the same reason the `Base/Structures/Basic` + `Base/Structures/Sigma` split in the legacy tree is a maintenance hazard: two type-level representations of the same mathematical object doubles every theorem's cost.  The Σ + bundle split is not two representations of the same object; it is a canonical core with a narrow interop view.
+  **`Classical/` built directly on `Base/` instead of `Setoid/`**.  Rejected because (i) `Base/` is frozen (ADR-001), (ii) `Base/` postulates extensionality, breaking the constructivity commitment, and (iii) `Base/`'s propositional-equality setting is not cubical-portable without further rework.

## References

+  Issue M3-1 — [Introduce the Classical/ tree](https://github.com/ualib/agda-algebras/issues/XX).
+  Issue M3-2 — `Classical.Structures.Semigroup` as the pattern-setting first structure.
+  Issue M3-3 — Stdlib bundle bridges.
+  `docs/STYLE_GUIDE.md` — section on record vs Σ.
+  Agda standard library, `Algebra.Bundles`.
+  Burris and Sankappanavar, *A Course in Universal Algebra*, chapter II.


