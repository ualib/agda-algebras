---
layout: default
file: "src/Classical/Structures/Magma.lagda.md"
title: "Classical.Structures.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### <a id="classical-structures-magma">Magmas — the empty-theory base case</a>

This is the [Classical.Structures.Magma][] module of the [Agda Universal Algebra Library][].

A magma is a set equipped with a single binary operation, with no further axioms
imposed.  Mathematically a magma is just an inhabitant of the type
`Algebra Sig-Magma α ρ`: an `Sig-Magma`-algebra in the sense of universal
algebra, with no theory to satisfy.  This is the degenerate case of the general
classical-structure encoding `X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Th-X`; the
Σ-wrapping vanishes when `Th-X` is empty (per
[ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md)) and the
representation collapses to a type alias.

This is also the first concrete classical structure to land under M3, and as such
this module's *prose is normative* for the signature-mechanics conventions every
subsequent structure consumes.  Specifically: hyphen-separated `<symbol>-Op`
constructor naming (in the corresponding `Signatures/X` file), `ar-<Structure>`
arity-function naming, `Sig-<Structure>` signature-value naming, ASCII `^` for
operation-symbol interpretation, the curried-user-facing-accessor pattern
`_∙_ = Curry₂ (∙-Op ^ _)`, and the `fromOp`-family constructor pattern.
Semigroup (M3-4), Monoid (M3-6), Group (M3-6), Lattice (M3-7), and Ring (M3-8)
each follow this template; deviations need their own ADR.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Product                           using ( _,_ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong₂ ; isEquivalence ; setoid)

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations                   using ( Curry₂ ; pair )
open import Classical.Signatures.Magma             using ( Op-Magma ; ∙-Op ; Sig-Magma )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] ; ⟨_⟩ )

private variable α ρ : Level
```

#### <a id="the-type">The type of magmas</a>

`Magma α ρ` is the type of `Sig-Magma`-algebras whose carrier sits at level `α`
and whose underlying setoid equivalence sits at level `ρ`.  Empty theory means
no Σ-wrapping; the alias makes use sites read `Magma α ρ` rather than
`Algebra Sig-Magma α ρ`.

```agda
Magma : (α ρ : Level) → Type _
Magma α ρ = Algebra α ρ
```

#### <a id="named-accessors">Named accessors</a>

`Domain`, `Carrier`, and `_∙_` are exposed as top-level functions whose first
explicit argument is the magma.  Defining them inside an unnamed parametric
module — `module _ (𝑴 : Magma α ρ)` — gives each name the shape
`(𝑴 : Magma α ρ) → …` at use sites while keeping the bodies readable; inside the
module the names read as if `𝑴` were a record being projected, which is the
ergonomic intent.

`_∙_` interprets the syntactic operation symbol `∙-Op` in the algebra `𝑴` and
then curries the resulting `(Fin 2 → 𝕌[ 𝑴 ]) → 𝕌[ 𝑴 ]` into the user-facing
`𝕌[ 𝑴 ] → 𝕌[ 𝑴 ] → 𝕌[ 𝑴 ]`.  The arity-tuple-vs-curried bridging is delegated
to `Curry₂` from [`Classical.Operations`][]; the per-structure file never
constructs `pair`-style argument tuples inline.  This is what
[ADR-002 v2 §1](../../docs/adr/002-classical-layer-design.md) requires: the
Fin n η-bridge is contained inside one module library-wide.

```agda
module Magma-Op {α ρ : Level} (𝑴 : Magma α ρ) where

  Domain : Setoid α ρ
  Domain = 𝔻[ 𝑴 ]

  Carrier : Type α
  Carrier = 𝕌[ 𝑴 ]

  infixl 7 _∙_
  _∙_ : Carrier → Carrier → Carrier
  _∙_ = Curry₂ (∙-Op ^ 𝑴)
```

#### <a id="fromOp">From a bare type and a binary operation</a>

The single most common use case for downstream consumers is constructing a magma
from a bare type `A : Type α` and a binary operation `_·_ : A → A → A`.
`fromOp` performs the construction: the underlying setoid is the propositional-
equality setoid `≡.setoid A`, and the interpretation of `∙-Op` uncurries `_·_`
back into the tuple-indexed form the algebra demands.

For structures with non-empty theory, the analogous constructor takes one
additional argument per equation in the theory — `Semigroup`'s `fromPropEq` takes
an associativity proof, `Monoid`'s takes associativity plus the two identity
laws, and so on.  Magma's empty theory means `fromOp` takes no equation
arguments.  This is the empty-theory edge case of the `fromOp`-family
constructor pattern; M3-4 onward generalizes it.

```agda
fromOp : ∀{α} → (A : Type α) → (A → A → A) → Magma α α
fromOp {α} A _·_ = record { Domain = M ; Interp = interp }
  where
  M : Setoid α α
  M = setoid A

  interp : Func (⟨ Sig-Magma ⟩ M) M
  interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
  cong interp { ∙-Op , _ } { .∙-Op , _ } (refl , args≡) = cong₂ _·_ (args≡ 0F) (args≡ 1F)
```

#### <a id="morphisms">A note on morphisms</a>

A magma morphism is, by [ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md),
definitionally a homomorphism of the underlying `Sig-Magma`-algebras.  No
per-structure morphism record is introduced; M3-3 inherits
[`Setoid.Homomorphisms`][] wholesale, instantiated at `𝑆 = Sig-Magma`.  This is
uniformly the policy across the classical hierarchy: each structure inherits
homomorphisms, isomorphisms, and substructure machinery from `Setoid/`
instantiated at its own signature.  Per-structure morphism *invariants* — for
example, "monoid homomorphisms preserve the identity element" — are theorems
about the inherited homomorphism, not new record fields.

--------------------------------------

<span style="float:left;">[← Classical.Structures](Classical.Structures.html)</span>
<span style="float:right;">[Classical.Bundles.Magma →](Classical.Bundles.Magma.html)</span>

{% include UALib.Links.md %}
