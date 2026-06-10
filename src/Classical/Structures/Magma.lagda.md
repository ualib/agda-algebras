---
layout: default
file: "src/Classical/Structures/Magma.lagda.md"
title: "Classical.Structures.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Magmas — the empty-theory base case

This is the [Classical.Structures.Magma][] module of the [Agda Universal Algebra Library][].

A magma is a set equipped with a single binary operation, with no further axioms
imposed.  Mathematically a magma is just an inhabitant of the type
`Algebra Sig-Magma α ρ`: an `Sig-Magma`-algebra in the sense of universal
algebra, with no theory to satisfy.  This is the degenerate case of the general
classical-structure encoding `X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Th-X`; the
Σ-wrapping vanishes when `Th-X` is empty (per
[ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md)) and the
representation collapses to a type alias.

This is also the first concrete classical structure to land in Milestone 3 (of the
[agda-algebras 3.0 upgrade][ROADMAP]) and, as such, this module's prose is
normative for the signature-mechanics conventions every subsequent structure
consumes.

Specifically: hyphen-separated `<symbol>-Op`
constructor naming (in the corresponding `Signatures/X` file), `ar-<Structure>`
arity-function naming, `Sig-<Structure>` signature-value naming, ASCII `^` for
operation-symbol interpretation, a named `<Structure>-Op` module housing the
curried user-facing accessors so that downstream code can `open <Structure>-Op 𝑿`
once and use the binary operation in infix form `a ∙ b` (mirroring the
`open Magma M`-and-then-`a ∙ b` idiom of `Algebra.Bundles`), the curried-accessor
body `_∙_ = Curry₂ (∙-Op ^ _)`, and the `opsTo<family>` constructor pattern.

Semigroup, Monoid, Group, Lattice, and Ring all follow this template.
(Deviations require an ADR.)

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations                   using ( Curry₂ ; pair )
open import Classical.Signatures.Magma             using ( Op-Magma ; ∙-Op ; Sig-Magma )
open import Classical.Structures.Interpret         using ( interp-cong )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] ; ⟨_⟩ )
open import Setoid.Homomorphisms.Basic {𝑆 = Sig-Magma}  using ( hom ; IsHom )

private variable α ρ : Level
```

#### The type of magmas

`Magma α ρ` is the type of `Sig-Magma`-algebras whose carrier sits at level `α`
and whose underlying setoid equivalence sits at level `ρ`.  Empty theory means
no Σ-wrapping; the alias makes use sites read `Magma α ρ` rather than
`Algebra {𝑆 = Sig-Magma} α ρ`.

```agda
Magma : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Magma α ρ = Algebra α ρ
```

(If it's not obvious why `Algebra α ρ` yields a magma here, note that the
`Setoid.Algebras.Basic` module is imported above with the signature parameter set to
`𝑆 = Sig-Magma`.)


#### The `Magma-Op` module: named accessors for a fixed magma

`Domain`, `Carrier`, and `_∙_` are exposed inside a named parametric module
`Magma-Op`.  Users `open Magma-Op 𝑴` at a use site to bring all three into
scope; the binary operation is then expressed using infix notation `a ∙ b`, matching
the experience of using `open Magma M` with the standard library's
`Algebra.Bundles.Magma` module.

The name `Magma-Op` follows the hyphen-separated long-form convention established by
`Sig-Magma`, `ar-Magma`, and `∙-Op`.  It is *normative*: every subsequent classical
structure ships an analogously named module (`Semigroup-Op`, `Monoid-Op`, `Group-Op`,
`Lattice-Op`, `Ring-Op`).  Each later module additively re-exports the underlying
weaker structure's operations through the forgetful projection; `Group-Op` exposes
`_∙_`, `ε`, and `_⁻¹`; `Ring-Op` exposes `_+_`, `0`, `-_`, `_·_`, and `1`.  The
"open the operations module once, use infix thereafter" idiom is uniform across the
hierarchy.

The function `_∙_` interprets the syntactic operation symbol `∙-Op` in the algebra
`𝑴` and then curries the resulting `(Fin 2 → 𝕌[ 𝑴 ]) → 𝕌[ 𝑴 ]` into the
user-facing `𝕌[ 𝑴 ] → 𝕌[ 𝑴 ] → 𝕌[ 𝑴 ]`.  The arity-tuple-vs-curried bridging is
delegated to `Curry₂` from [`Classical.Operations`][]; the per-structure file never
constructs `pair`-style argument tuples inline.  This is what
[ADR-002](../../docs/adr/002-classical-layer-design.md) §1 requires: the `Fin n`
η-bridge is contained inside one module library-wide.

When two magmas appear in the same expression — for example, both sides of a
round-trip lemma in [`Classical.Bundles.Magma`][] — the standard Agda idiom is

    open Magma-Op 𝑴
    open Magma-Op 𝑵 renaming (_∙_ to _∙'_)

```agda
module Magma-Op {α ρ : Level} (𝑴 : Magma α ρ) where
  infixl 7 _∙_
  _∙_ : 𝕌[ 𝑴 ] → 𝕌[ 𝑴 ] → 𝕌[ 𝑴 ]
  _∙_ = Curry₂ (∙-Op ^ 𝑴)
```

#### From a bare type and a binary operation

The single most common use case for downstream consumers is constructing a magma
from a bare type `A : Type α` and a binary operation `_·_ : A → A → A`.
The `opsToMagma` function performs the construction.  The underlying setoid is
the propositional-equality setoid `≡.setoid A`, and the interpretation of `∙-Op`
uncurries `_·_` back into the tuple-indexed form the algebra demands.

For structures with non-empty theory, the analogous constructor takes one additional
argument per equation in the theory — `eqsToSemigroup` takes an associativity
proof, `eqsToMonoid` takes associativity plus the two identity laws, and so on.
Magma's empty theory means `opsToMagma` takes no equation arguments.  This is the
empty-theory edge case of the `opsTo<family>` constructor pattern.

```agda
opsToMagma : (A : Type α) (_·_ : A → A → A) → Magma α α
opsToMagma A _·_ = record { Domain = ≡.setoid A ; Interp = interp }
  where
  interp : Func (⟨ Sig-Magma ⟩ _) _
  interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
  cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , args≡) = ≡.cong₂ _·_ (args≡ 0F) (args≡ 1F)
```

#### A note on morphisms

A magma morphism is, by [ADR-002][] §5, definitionally a homomorphism of the
underlying `Sig-Magma`-algebras.  No per-structure morphism record is introduced; we
inherit [`Setoid.Homomorphisms`][] wholesale, instantiated at `𝑆 = Sig-Magma`.  This
is uniformly the policy across the classical hierarchy: each structure inherits
homomorphisms, isomorphisms, and substructure machinery from `Setoid/`
instantiated at its own signature.  Per-structure morphism *invariants* — for
example, "monoid homomorphisms preserve the identity element" — are theorems
about the inherited homomorphism, not new record fields.

The first such invariant is the inherited homomorphism's compatibility with `∙-Op`
restated in *curried* form: `h (x ∙ y) ≈ h x ∙ h y`.  The `compatible` field of
`IsHom` states this against argument tuples (`h ((∙-Op ^ 𝑨) a) ≈ (∙-Op ^ 𝑩) (h ∘ a)`);
`hom-preserves-∙` instantiates the tuple at `pair x y` and pays the `Fin 2` η-bridge
once, via [`interp-cong`][Classical.Structures.Interpret], so downstream consumers
(e.g. the free-expansion functor of M4-5d) get the curried law as a one-liner.

```agda
module _ {α β ρᵃ ρᵇ : Level} {𝑨 : Magma α ρᵃ} {𝑩 : Magma β ρᵇ} where
  open Magma-Op 𝑨 using ( _∙_ )
  open Magma-Op 𝑩 using () renaming ( _∙_ to _∙ᵇ_ )
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; refl to ≈ᵇ-refl ; trans to ≈ᵇ-trans )

  -- Magma homomorphisms preserve the binary operation, in curried form.
  hom-preserves-∙ : (h : hom 𝑨 𝑩) (x y : 𝕌[ 𝑨 ])
    → proj₁ h ⟨$⟩ (x ∙ y) ≈ᵇ (proj₁ h ⟨$⟩ x) ∙ᵇ (proj₁ h ⟨$⟩ y)
  hom-preserves-∙ h x y =
    ≈ᵇ-trans  (IsHom.compatible (proj₂ h) {∙-Op} {pair x y})
              (interp-cong 𝑩 ∙-Op (λ { 0F → ≈ᵇ-refl ; 1F → ≈ᵇ-refl }))
```

--------------------------------------

<span style="float:left;">[← Classical.Structures](Classical.Structures.html)</span>
<span style="float:right;">[Classical.Bundles.Magma →](Classical.Bundles.Magma.html)</span>

{% include UALib.Links.md %}
