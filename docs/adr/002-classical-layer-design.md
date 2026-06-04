<!-- File: docs/adr/002-classical-layer-design.md -->

# ADR-002: Classical structures over the universal-algebra foundation

## Status

Accepted — 2026-04-24.
Revised v2 — 2026-05-17, following the M3-2 (Semigroup) load test.
Amended v2.1 — 2026-05-28, adds §10 on `Classical/Properties/` following the M3-7 (Lattice) order-theoretic equivalence work.
Amended v2.2 — 2026-06-04, records the M4-1 Σ-projection migration (#267 / #367): the bracket projections `∣_∣` / `∥_∥` are replaced by `proj₁` / `proj₂` across the live trees, revising the "no mass rename of Σ-projections" stance in §1, §7, and *Alternatives considered*.  The long-form `OperationSymbolsOf` / `ArityOf` remain canonical for signature components and are defined via `proj₁` / `proj₂` once #367 lands.  The caret (§7) and long-form-naming policies are unaffected.

---

## Context

The 3.0 reconstruction adds a `src/Classical/` tree holding specific algebraic theories — magmas, semigroups, monoids, groups, lattices, rings — built on the universal-algebra foundation in `src/Setoid/`.  This ADR records the architectural decisions that determine how each classical structure is represented, how it interoperates with the Agda standard library's `Algebra.Bundles`, how it stays portable to the eventual cubical Agda formulation (ADR-003), and — equally importantly — what set of *user-facing* affordances each structure exposes so that working with classical structures in `agda-algebras` is at least as ergonomic as working with `Algebra.Bundles` directly.

Eight interacting questions get answered below:

+  How is an operation symbol's interpretation represented — as a tuple-indexed function `(I → A) → A` or in curried form `A → A → A`?  The universal-algebra meta-theory requires the former for arity-uniform recursion (Birkhoff, HSP, varieties); the user-facing syntax working algebraists use is the latter (`x ∙ y`, not `pair x y`).
+  How are the variables in an equation represented at the term level?  A per-structure named-enum carrier is locally readable but proliferates across structures and leaks into bundle bridges.
+  How are equational identities represented?  A per-structure copy of associativity, identity laws, etc. is what stdlib's `Algebra.Definitions` provides at the *evaluated* level; we need an analogous library at the *syntactic* (term-pair) level so the meta-theory's `Modᵗ` can consume them.
+  How is each concrete structure related to weaker structures in the hierarchy?  Mathematically a monoid is a semigroup with an identity; type-theoretically the signature changes between levels, so direct Σ-over-predecessor nesting does not work.
+  What is the type-theoretic shape of a structure `X`?  A record with named projections or a Σ-type pairing an algebra with a proof it satisfies the `X`-theory?
+  How does `X` interoperate with `Algebra.Bundles`?  Stdlib provides `Semigroup`, `Monoid`, etc. as records; anyone interoperating with stdlib-typed code must convert.
+  What does "round trip" mean for the bundle bridge under setoid semantics?  Propositional `≡` on the Σ-type is naive — it loses to Fin n η under `--cubical-compatible`; pointwise agreement is what's mathematically meant by "the same semigroup."
+  How are distinguished elements (identity of a monoid, zero of a ring, basepoints of pointed structures) represented?

A related question: what does "classical" mean in this subtree?  It does not mean "classical logic" — the library stays constructive throughout.  `Classical/` names the *tradition* of concrete algebraic structures (groups, rings, lattices) as distinct from the universal-algebraic treatment of algebras-over-a-signature that lives in `Setoid/`.  `Classical/` was chosen over `Concrete/` because the term is standard in the universal-algebra literature (Burris and Sankappanavar use it throughout).

---

## Decision

### 1.  Operation representation: tuple-indexed at the foundation, curried at the user interface

The foundational layer — `Overture.Operations`, `Setoid.Algebras`, `Overture.Terms`, and everything downstream that participates in the universal-algebra meta-theory — uses the tuple-indexed form `(I → A) → A`.  This is non-negotiable: variety closure operators, the term algebra as a W-type, Birkhoff's HSP theorem, and the equational-logic substrate (`Modᵗ`) all recurse on arity and require operations in this form.

The user-facing layer — every accessor exported from `Classical/Structures/X` and `Classical/Bundles/X` — exposes operations in *curried* form: a binary operation as `A → A → A`, a nullary operation as `A`, a unary operation as `A → A`.  The wrappers between the two forms are provided once, generically, by `Curry`/`Uncurry` helpers in a shared `Classical.Operations` module, one helper per arity.  Per-structure files do not redefine these helpers and do not write `pair`-style wrappers inline.

The bare type-class formulation of curried operations (à la Haskell's `Num` hierarchy via Agda instance arguments) is *not* introduced in 3.0.  Instance arguments in Agda are heavier than type classes in Lean or Haskell, and the use sites we care about are served well by `open Magma 𝑴 using (_∙_)`-style named-accessor opens.  If a future revision finds that pattern too verbose, instance arguments can layer on top of the named-accessor API without re-architecting.

The arity-first ordering `Op : Type 𝓥 → Type α → Type (𝓥 ⊔ α)` with `Op I A = (I → A) → A` is preferred over the carrier-first alternative — `Op (Fin 2)` partially applies as "binary operation," independent of any carrier.

**Self-documenting projections for signatures**.  The Σ-type encoding of `Signature 𝓞 𝓥 = Σ (Type 𝓞) (λ Op → Op → Type 𝓥)` is mathematically clean but reads opaquely at use sites — `f : ∣ 𝑆 ∣` and `∥ 𝑆 ∥ f` do not telegraph their meaning to a reader without the encoding cached.  The `Overture.Signatures` module exposes long-form aliases:

```agda
OperationSymbolsOf : Signature 𝓞 𝓥 → Type 𝓞
OperationSymbolsOf 𝑆 = proj₁ 𝑆

ArityOf : (𝑆 : Signature 𝓞 𝓥) → OperationSymbolsOf 𝑆 → Type 𝓥
ArityOf 𝑆 f = proj₂ 𝑆 f
```

These are definitionally identical to `proj₁` / `proj₂`.  M4-1 makes the long forms the canonical names for signature components throughout the library and migrates generic Σ-projections in the live trees to `proj₁` / `proj₂` (#367); that change also adds a `WARNING_ON_USAGE` to the bracket definitions `∣_∣` / `∥_∥` in `Overture.Basic` and retains them only so `Legacy/` keeps compiling.

### 2.  Variable carrier for equations: `Fin n`, not per-structure named enums

The variable carrier for equations in `Th-X` is `Fin n`, with `n` the number of distinct variables the equations require — `Fin 2` for commutativity, `Fin 3` for associativity, and so on.  No per-structure `<Structure>Var` enums are introduced.  Readable patterns at use sites come from `Data.Fin.Patterns` (`0F`, `1F`, `2F`); where additional readability is wanted, per-equation locally bound names inside `Theories/X` files are encouraged.

The original M3-2 design (per-structure `SemigroupVar` with constructors `x`, `y`, `z`) was rejected on load-test grounds.  The per-structure enum leaked from `Classical/Theories/Semigroup` into the bundle bridge's variable-assignment machinery and into the worked-example's variable plumbing, and would have re-leaked at every subsequent structure.  Generic `Fin n` confines structure-specific naming to projections of carrier elements, where it belongs.

### 3.  Equation builders: generic, parametric in signature and operation symbol

A subtree `Classical/Equations/` (sibling of `Signatures/`, `Theories/`, `Structures/`, `Bundles/`, `Small/`) houses generic equation builders parametric in a signature `𝑆` and operation symbols within it.  Examples:

```text
Associative     : (f : OperationSymbolsOf 𝑆) → ArityOf f ≡ Fin 2
                → ∀ {X} → X → X → X → Term X × Term X

Commutative     : (f : OperationSymbolsOf 𝑆) → ArityOf f ≡ Fin 2
                → ∀ {X} → X → X → Term X × Term X

LeftIdentity    : (f : OperationSymbolsOf 𝑆) → ArityOf f ≡ Fin 2
                → (e : OperationSymbolsOf 𝑆) → ArityOf e ≡ Fin 0
                → ∀ {X} → X → Term X × Term X

DistributesOverˡ : (· : OperationSymbolsOf 𝑆) → ArityOf · ≡ Fin 2
                 → (+ : OperationSymbolsOf 𝑆) → ArityOf + ≡ Fin 2
                 → ∀ {X} → X → X → X → Term X × Term X
```

Each per-structure `Classical/Theories/X.lagda.md` file composes these builders with `X`'s operation symbols; it does not redefine the underlying equation shapes.  `Classical.Equations` is the *syntactic dual* of stdlib's `Algebra.Definitions`, which provides the same inventory at the evaluated (carrier-quantified) level.  Having both views is genuinely additive: `Algebra.Definitions` is what `IsSemigroup.assoc` returns and what users prove for concrete algebras; `Classical.Equations` is what feeds `Modᵗ` and the variety machinery.  Neither subsumes the other.

This module is the concrete answer — beyond pedagogy and corpus quality — to "why does `Classical/` exist as a parallel hierarchy rather than as a stdlib shim?"

### 4.  Theory index: `Eq-X` indexes equations, not variables

Each `Classical/Theories/X.lagda.md` file defines `Th-X : Eq-X → Term (Fin n) × Term (Fin n)`, where `Eq-X` is a small named enum whose constructors name the equations of `X`'s theory — `assoc`, `id-l`, `id-r`, `inv-l`, `inv-r`, `dist-l`, `dist-r`, etc.  For single-equation theories (semigroup: associativity only) the index degenerates to `⊤` rather than introducing a redundant one-constructor enum.

### 5.  Structure encoding: self-contained over the structure's own signature, with forgetful projections for inheritance

Each classical structure `X` is fully characterized by the pair `(Sig-X , Th-X)` — its own signature and its own complete equational theory in that signature — and is encoded as

```text
X α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-X
```

inside an `open Setoid.Algebras {𝑆 = Sig-X}` block that fixes the signature parameter.  The degenerate case `Magma α ρ = Algebra α ρ` covers the empty-theory base — no Σ wrapping a trivial `⊤`-typed proof obligation.

The mathematical inheritance relationships between structures — "a monoid is a semigroup," "a group is a monoid," "a ring is an abelian group with extra structure" — are *not* encoded by Σ-nesting one structure's definition inside another.  Σ-over-predecessor was considered and rejected because each level carries a different signature: monoid adds a nullary identity symbol, group adds a unary inverse symbol, ring adds an entire second operation cluster.  Nesting would require signature-extension functors woven through every structure's definition, which is exactly the cumbersome scaffolding the user-facing layer is meant to avoid.

Inheritance instead manifests as *forgetful-functor projections* defined alongside each structure: `monoid→semigroup : Monoid α ρ → Semigroup α ρ`, `group→monoid : Group α ρ → Monoid α ρ`, `ring→abelianGroup : Ring α ρ → AbelianGroup α ρ`.  Each forgetful is a small theorem: drop the operations the weaker structure does not have, and re-extract the weaker theory's equations from the stronger structure's `Th-X`.  Forgetful projections compose, so chains like `group→semigroup` are derived rather than primitive.

The benefit of self-contained encoding: "what equations does a group satisfy?" has a single-location answer, `Th-Group`.  No walking up an inheritance chain to collect equations.  Trade-off: a theorem proved for semigroups applied to a group requires an explicit `theorem (group→semigroup 𝑮)` rather than `theorem (proj₁ 𝑮)`.  This is the same trade `Algebra.Bundles` makes in the standard library, on the same grounds: it keeps each structure cleanly self-describing.

### 6.  Bundle bridge: pointwise equivalence, not propositional Σ-equality

The bidirectional conversion functions `⟨_⟩ˣ` (Σ-core → stdlib bundle) and `⟪_⟫ˣ` (stdlib bundle → Σ-core) form a *pointwise inverse pair*: the round-tripped algebra has the same underlying setoid as the original and interprets each operation symbol identically on every input.  The round-trip is *not* claimed as an inhabitant of `_≡_` on the Σ-type — under `--cubical-compatible`, the lack of η on `Fin n`-pattern lambdas makes the operation-tuple-vs-curried repackaging propositionally but not definitionally equal, and demanding `≡` on the Σ-type forces a funext appeal that the `--safe` regime forbids.

Pointwise agreement is the mathematically correct notion of "same semigroup" under setoid semantics: two semigroups are the same exactly when their underlying setoids coincide and their operations agree on every input.  Each bundle bridge module exports a `roundtrip-X` lemma stating this pointwise agreement; nothing stronger is claimed.

### 7.  Notation policy

**Operation-symbol interpretation**: `f ^ 𝑨` replaces `f ̂ 𝑨`.  The caret combining character is unicode-Tetris that breaks grep, sed, and shell-pipeline tooling; ASCII `^` survives every text-processing tool.  The two notations coexist for one minor version under a `WARNING_ON_USAGE` pragma on `̂`, then `̂` is removed.

**Unicode usage across the library**: three categories, with three different policies.

+  *Standard mathematical notation* — `≈`, `⊨`, `⊧`, `⊫`, `≅`, `≤`, `⨅`, `≡`, the bold-italic letters denoting algebraic structures (`𝑨` for an algebra, `𝑴` for a magma, `𝑮` for a group), the script letters for level variables (`𝓞`, `𝓥`), the blackboard letters for forgetful accessors (`𝔻[_]` for `Domain`, `𝕌[_]` for `Carrier`).  These mirror conventions in McKenzie–McNulty–Taylor and Burris–Sankappanavar; algebraists recognize them on sight, and the bold-italic/Roman distinction between an algebra `𝑨` and its universe `A` is mathematically load-bearing, not decorative.  Keep.

+  *Subscripted Latin used to name structure-specific entities* — `𝑆ₓ`, `Thₓ`, `Eqₓ` in the original draft.  Replaced by hyphen-separated long forms: `Sig-X`, `Th-X`, `Eq-X`.  Hyphen-separated forms grep cleanly, display in any monospaced font, read aloud sensibly, and don't require an Agda-input-mode dance per occurrence.  New `Classical/` code uses the long forms exclusively.

+  *Bracket notation for Σ-projections* — `∣ 𝑆 ∣`, `∥ 𝑆 ∥ f`.  **Migrated** to `proj₁` / `proj₂` (and the `OperationSymbolsOf` / `ArityOf` long-forms for signature components) across the live trees by M4-1 (#367), which adds a `WARNING_ON_USAGE` to the definitions in `Overture.Basic` and retains them for `Legacy/`.  The blackboard accessor notation `𝔻[ 𝑨 ]` (Domain) and `𝕌[ 𝑨 ]` (Carrier) is category-1 standard notation and is **kept** everywhere.

The original v2 policy performed no mass rename; M4-1 (amendment v2.2) revised this for the `∣_∣` / `∥_∥` Σ-projections specifically, which are now `proj₁` / `proj₂` library-wide.  The remaining policy stands: new `Classical/` code adopts the long-form conventions, and the subscript / blackboard notation in `Setoid/` is retained as well-established reference material.

### 8.  First concrete structure: Magma

The pattern-setting first concrete structure under `Classical/` is `Magma`, not `Semigroup`.  Magma has an empty equational theory, which separates the *signature mechanics* (operation-symbol naming, arity convention, signature assembly) from the *equation mechanics* (term-level equations, model-of-theory predicate, generic equation builders).  Establishing signature mechanics first, in isolation, prevents the conflation that drove the original M3-2 attempt's diagnostic burden.

### 9.  Distinguished elements and pointed expansions

Distinguished elements of an algebra — the identity of a monoid, zero of a ring, top/bottom of a bounded lattice, basepoints of pointed structures — are represented as **nullary operation symbols** of the structure's signature.  The user-facing layer surfaces them as constants of carrier type via the `Curry₀` helper.  Equations involving distinguished elements (the monoid identity laws, the ring annihilation law) are standard term-level equations whose terms contain the nullary symbol as a leaf, via the same `Classical.Equations` builders that handle higher-arity operation symbols.

This choice is mandated by the equational-logic substrate: the variety machinery (`Modᵗ`, `Th`, the closure operators) characterizes a variety as algebras satisfying a set of identities *over the signature*.  A monoid's identity element must appear in identities involving the operation `∙` (specifically, `ε ∙ x ≈ x` and `x ∙ ε ≈ x`), hence must be a syntactic symbol of the signature.  Encoding the identity as a distinguished carrier element of an algebra (rather than a signature symbol) would make those identity equations inexpressible in the variety framework.

A "pointed" variant of an algebraic structure is a signature extension by an additional nullary symbol denoting the basepoint.  Concretely, a pointed group has signature

```agda
data Op-PointedGroup : Type where
  ∙-Op ε-Op ⁻¹-Op p-Op : Op-PointedGroup
ar-PointedGroup ∙-Op  = Fin 2
ar-PointedGroup ε-Op  = Fin 0
ar-PointedGroup ⁻¹-Op = Fin 1
ar-PointedGroup p-Op  = Fin 0
```

with the basepoint `p` interpreted via `p-Op ^ 𝑮`.  The equational theory `Th-PointedGroup` includes the group axioms unchanged plus whatever equations specify the basepoint's behavior; the variety of pointed groups is, in general, *not* the same variety as ungroup-pointed groups, and known results (Bryant, *The laws of finite pointed groups*, Bull. LMS 14 (1982), 119–123; in light of Oates–Powell's finite-basis theorem for finite groups) show pointed expansions can change decidability and finite-axiomatizability properties.  The encoding accommodates the distinction without architectural change.

The naming convention for nullary operation symbols mirrors the binary case: `<symbol>-Op` (`∙-Op`, `ε-Op`, `0-Op`, `1-Op`, `⊤-Op`, `⊥-Op`).  Hyphenation reads aloud the way an algebraist pronounces these — "dot-op," "epsilon-op," "zero-op" — and greps cleanly.

### 10.  `Classical/Properties/` for derived results

A sixth subtree `Classical/Properties/` (sibling of `Signatures/`, `Theories/`, `Structures/`, `Bundles/`, `Small/`) houses *derived* results about classical structures — theorems that are properties of a fixed inhabitant of one of the structures defined in `Classical/Structures/`, rather than part of the structure's definition.  Each per-structure file `Classical/Properties/X.lagda.md` consumes `X-Op`'s curried accessors and proves further facts about a parameterized `(𝑿 : X α ρ)`.

The inaugural inhabitant is `Classical.Properties.Lattice`, which proves the meet-join / order-theoretic equivalence: the partial order `x ≤ y := x ∧ y ≈ x` induced by the algebraic data, with the partial-order witnesses and the proof that `_∧_` and `_∨_` are the binary meet and join with respect to it.  Future inhabitants of this subtree include, for example, uniqueness of inverses in `Classical.Properties.Group`, `0 · x ≈ 0` in `Classical.Properties.Ring`, and the order-induced semilattice on a `Semilattice`.

Unlike the five quintuple subtrees, `Classical/Properties/` is *sparse*: per-structure files are added only as concrete derived results accrue, not maintained as a uniform one-file-per-structure shape.  An umbrella aggregator `Classical.Properties` re-exports each per-structure file as it lands.

The decision to organize by *concern* (a top-level `Classical/Properties/` directory housing per-structure files) rather than by *structure* (per-structure subdirectories such as `Classical/Lattice/Properties.lagda.md`) was made for consistency with the existing tree's organization: every other file in `Classical/` lives under a concern-named directory, with the structure as the leaf name.  Per-structure subdirectories for properties alone would mix two organizing axes and create an asymmetry a reader would have to memorize.  The choice also mirrors stdlib's `Algebra.Lattice.Properties.Lattice` layout.

---

## Empirical revision history

The original ADR-002 (2026-04-24) was authored ahead of any implementation.  The M3-2 (Semigroup) load test in 2026-05 surfaced five issues with the original design:

+  The per-structure `SemigroupVar` enum was conceptually load-bearing but practically leaked from `Classical/Theories/` into the bundle bridge's variable-assignment machinery, foreshadowing analogous leaks at every subsequent structure.  Generic `Fin n` resolves this (revised §2).
+  The `Fin 2` η-failure under `--cubical-compatible` forced the bundle bridge's `assoc` proof into a four-step setoid-reasoning sandwich with `cong (Interp 𝑨)` calls at two levels of nesting, even on the simplest associativity equation.  The root cause is that operation arguments enter as a tuple `(Fin 2 → A)` on one side and as curried `A → A → A` on the other; generic `Curry`/`Uncurry` helpers contain the η-bridge to one location instead of forcing it into every per-structure proof (revised §1).
+  The propositional-equality round-trip lemma did not hold even on the concrete `ℕ-semigroup`: the bundle's `_∙_` was built by partial application of `(Interp 𝑨) ⟨$⟩ (∙-Op , …)`, and the round-trip re-interpreted operation arguments through a fresh `λ {0F → … ; 1F → …}` repackaging, with no η to collapse the two.  Pointwise equivalence (revised §6) is what is mathematically meant by "same semigroup" under setoid semantics.
+  Starting the concrete-structures pipeline at Semigroup rather than Magma forced the first implementation to handle signature mechanics and equation mechanics simultaneously, with diagnostic burden distinguishing which class an error belonged to.  Magma-first (revised §8) cleanly isolates the two.
+  The original ADR did not address the representation of distinguished elements at all, leaving Monoid's identity and Ring's zero as undefined design questions.  Resolved as nullary operation symbols of the signature (new §9), with pointed-expansion semantics following the same pattern.

The revisions above are the response to these findings.  No part of the original ADR's higher-level architecture (Σ-typed cores, bundle views for stdlib interop, level-fixed veneers in `Small/`, the cubical-portability discipline) is overturned.

---

## Consequences

+  **Definitions read the way a universal algebraist thinks**.  "A semigroup is a magma satisfying associativity" is exactly what `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semigroup` types, with `Th-Semigroup _ = Associative ∙-Op refl 0F 1F 2F`.  The generic-builder layer makes each per-structure theory file a short composition, not a re-derivation.

+  **The library uniquely answers what stdlib does not**.  Generic equation builders that compose to populate `Th-X` for any `X` form the syntactic dual of `Algebra.Definitions` and feed the meta-theory's `Modᵗ` in a way that stdlib's evaluated-form predicates cannot.  This is the concrete justification — beyond pedagogy and corpus quality — for `Classical/` existing as a parallel hierarchy rather than a stdlib shim.

+  **Curried user-facing operations match working-algebraist syntax**.  `_∙_ : A → A → A` is what `x ∙ y` expects.  Tuple-indexed operations live below the user interface, surfaced only when interfacing with the universal-algebra meta-theory.

+  **`fromOp`-family constructors bridge bare-type definitions to the Σ-typed core**.  Users construct a magma from `(A : Type α) → (_·_ : A → A → A)`, a semigroup additionally from `(·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))`, a monoid additionally from `(ε : A)` and the identity laws, and so on.  The return type collapses to `X α α` because propositional equality at carrier `A : Type α` lives in `Type α`; consumers needing `α ≠ ρ` work directly with the underlying setoid.

+  **Stdlib bundle interop is a fixed, per-structure cost**.  Each `Classical/Bundles/X.lagda.md` is one record definition, two conversion functions, a pointwise round-trip lemma — uniformly small thanks to the generic `Curry`/`Uncurry` helpers absorbing the Fin n η-bridge once.

+  **Cubical portability remains substitutional**.  No theorem in `Classical/Structures/X.lagda.md` reaches for setoid-specific machinery; the 4.0 cubical port replaces the setoid equivalence with the path type and reruns the type-checker.  Pointwise equivalence at the bundle bridge survives this port unchanged.

+  **Use-site ergonomics are comparable to stdlib's**.  One `proj₁` to reach the underlying algebra, then named accessors (`Domain`, `Carrier`, `_∙_`, `ε`, `_⁻¹`) of the algebra.  Same projection depth as stdlib's `Group.semigroup.magma.Carrier`-style chains.

+  **The core `Algebra` type stays a record**.  Σ-for-classical-structures is not inconsistent: `Algebra` has multiple meaningful named projections and many inhabitants; `Semigroup` decomposes as "algebra + proof of theory" which a Σ types directly.  See `docs/STYLE_GUIDE.md` for the general record-vs-Σ rule.

+  **A parallel record implementation of any classical structure is a bug**.  The `Base/Structures/Basic` vs `Base/Structures/Sigma` duplication in the legacy tree is exactly the mistake this ADR codifies against.

---

## Alternatives considered

+  **Record-typed core, no Σ-typed variant**.  Rejected because stdlib's bundle idiom already exists and we would be re-deriving it; the mathematical reading is weaker; record-typed cores are more fragile under the cubical port since record projections mention the underlying equivalence more intrusively than Σ projection does.

+  **Two record variants in parallel (one library-internal, one stdlib-shaped)**.  Rejected: same maintenance hazard as the legacy `Base/Structures/Basic` + `Base/Structures/Sigma` split.  The Σ + bundle split is not two representations of the same object; it is a canonical core with a narrow interop view.

+  **`Classical/` built directly on `Base/` instead of `Setoid/`**.  Rejected because `Base/` is frozen (ADR-001), postulates extensionality (breaking the constructivity commitment), and is not cubical-portable without further rework.

+  **Σ-over-predecessor inheritance** (`Monoid α ρ = Σ[ 𝑺 ∈ Semigroup α ρ ] … extras`).  Considered as a way to enforce the mathematical "a monoid is a semigroup" reading at the type level.  Rejected because each level of the hierarchy carries a different signature; Σ-over-predecessor cannot smoothly accommodate signature extension.  Encoding it would require signature-extension functors woven through every structure's definition — the opposite of the user-facing-simplicity goal.  Self-contained encoding (revised §5) keeps each structure cleanly characterized by `(Sig-X , Th-X)` and expresses inheritance via forgetful projections that compose downward.

+  **Per-structure named-enum variable carriers** (e.g., `data SemigroupVar : Type where x y z : SemigroupVar`).  Considered for local-readability reasons.  Rejected because per-structure enums leak from `Classical/Theories/X` into bundle bridges and worked-example plumbing, and proliferate across structures.  Generic `Fin n` with `Data.Fin.Patterns`-style readability resolves the leak without sacrificing readability.

+  **Propositional `≡` on the Σ-type as the bundle-bridge round-trip statement**.  Considered as the natural-looking statement.  Rejected because under `--cubical-compatible` the lack of η on `Fin n`-pattern lambdas makes the operation-tuple-vs-curried repackaging propositionally but not definitionally equal, and demanding `≡` forces a funext appeal that `--safe` forbids.  Pointwise equivalence is the mathematically correct statement and types in `--safe`.

+  **Distinguished elements as algebra-level distinguished carrier elements rather than nullary operation symbols**.  Considered for the apparent simplicity of "a pointed group is a group with a chosen basepoint."  Rejected because the equational-logic substrate (`Modᵗ`, the variety machinery) characterizes a variety as algebras satisfying identities *over the signature*: if a distinguished element does not appear as a signature symbol, no identity can mention it, and the structure's theory cannot constrain it.  Nullary-symbol encoding (revised §9) is what makes the variety of monoids a proper variety and what makes pointed-group expansions a meaningful distinct variety.

+  **Mass rename of unicode in the existing `Setoid/` tree**.  Considered for consistency with the long-form-name convention adopted for new `Classical/` code.  Rejected as churn for no architectural benefit: `Setoid/` is well-established reference material, the unicode there is mostly category-1 (standard mathematical notation) anyway, and a rename would invalidate existing tutorials, papers, and external references to specific identifiers.  Policy is per-tree: new `Classical/` long-form, existing `Setoid/` retained.  (Amended v2.2: the one narrow exception is the `∣_∣` / `∥_∥` Σ-projections, migrated to `proj₁` / `proj₂` in M4-1 (#267 / #367) — there the readability and grep-tooling arguments outweighed the churn; the category-1 mathematical notation, subscripts, and blackboard accessors are still retained.)

+  **Per-structure `Classical/<X>/Properties.lagda.md` subdirectories** (e.g. `Classical/Lattice/Properties.lagda.md`).  Considered as a layout option for derived results when M3-7's lattice order-theoretic equivalence motivated the first Properties module.  Rejected for organizational uniformity: the existing tree organizes strictly by concern (one axis = concern as directory, leaf = structure), and per-structure subdirectories for properties alone would mix two organizing axes (concern-as-directory for everything else, structure-as-directory only for properties).  By-concern (§10) keeps the existing pattern uniform and mirrors stdlib's layout.


---

## References

+  Issue M3-1 — [Introduce the Classical/ tree](https://github.com/ualib/agda-algebras/issues/260).
+  Issue M3-1a — [Scaffold the Classical/ tree](https://github.com/ualib/agda-algebras/issues/326).
+  Issue M3-2 — [Classical.Operations and Classical.Equations infrastructure](https://github.com/ualib/agda-algebras/issues/330).
+  Issue M3-3 — [Classical.Magma](https://github.com/ualib/agda-algebras/issues/330).
+  Issue M3-4 — [Classical.Semigroup](https://github.com/ualib/agda-algebras/issues/261) (reformulated; supersedes original body).
+  Issue M3-5 — Stdlib bundle bridges (continued).
+  Issue M3-7 — [Classical.Semilattice and Classical.Lattice](https://github.com/ualib/agda-algebras/issues/264) (the order-theoretic equivalence motivating §10).
+  ADR-001 — `Setoid/` as canonical development tree (the foundation `Classical/` builds on).
+  ADR-003 — Cubical Agda as the canonical long-term target (the discipline `Classical/` enforces).
+  `docs/STYLE_GUIDE.md` — sections on record vs Σ, on unicode usage, on long-form vs bracket projection names.
+  Agda standard library, `Algebra.Bundles` and `Algebra.Definitions`.
+  Burris and Sankappanavar, *A Course in Universal Algebra*, chapter II.
+  R. Bryant, *The laws of finite pointed groups*, Bull. London Math. Soc. **14** (1982), 119–123 — for §9 on pointed expansions and the connection to Oates–Powell's finite-basis theorem.
