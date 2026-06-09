---
layout: default
file: "src/Classical/Categories/Reduct.lagda.md"
title: "Classical.Categories.Reduct module"
date: "2026-06-09"
author: "the agda-algebras development team"
---

### Reduct as a functor on algebras

This is the [Classical.Categories.Reduct][] module of the [Agda Universal Algebra Library][].

A signature morphism `φ : SigMorphism 𝑆₁ 𝑆₂` induces a covariant functor
`reductF φ : Alg 𝑆₂ ⟶ Alg 𝑆₁` between the [algebra categories][Setoid.Categories.Algebra].
On objects it is [`reduct`][Classical.Structures.Reduct]`φ`; on a homomorphism it keeps the
*same* underlying setoid map and transfers the `𝑆₂`-homomorphism condition to `𝑆₁` by the
`κ`-reindex — `compatible` at the `𝑆₁`-symbol `o` is `f`'s `𝑆₂`-`compatible` at `ι φ o`,
definitionally on the nose, because `(o ^ reduct φ 𝑨) = (ι φ o ^ 𝑨) ∘ (_∘ κ φ o)`.

The functor laws are immediate: `F-resp-≈` is the identity (the underlying maps are
unchanged, and the hom-equality is pointwise on them), and `identity` / `homomorphism` hold
by the codomain's `refl` (the underlying maps of both sides are the same — `𝒾𝒹` and `⊙-hom`
are the identity map and function composition).

This functor lives in the `Classical` tree, not `Setoid.Categories`, because its object map
`reduct` is in `Classical.Structures.Reduct` (ADR-006), which is above `Setoid`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Classical.Categories.Reduct where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using ()             renaming ( Set to Type )
open import Data.Product    using ( _,_ ; proj₁ ; proj₂ )
open import Function        using ( Func ; _∘_ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ )
open import Setoid.Categories.Functor      using ( Functor )
open import Classical.Structures.Reduct    using ( reduct )

import Setoid.Categories.Algebra   as AlgCat
import Setoid.Homomorphisms.Basic  as HomMod
import Setoid.Algebras.Basic       as AlgMod

open Func renaming ( to to _⟨$⟩_ )

private variable
  α ρ : Level

module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) where

  private
    module A₁ = AlgCat  {𝑆 = 𝑆₁}   -- the category Alg 𝑆₁
    module A₂ = AlgCat  {𝑆 = 𝑆₂}   -- the category Alg 𝑆₂
    module H₂ = HomMod  {𝑆 = 𝑆₂}   -- 𝑆₂-homomorphisms (the source homs)
    module M₁ = AlgMod  {𝑆 = 𝑆₁}   -- 𝑆₁-algebras (for the reduct's domain setoid)

  reductF : Functor (A₂.Alg α ρ) (A₁.Alg α ρ)
  reductF = record
    { F₀           = reduct φ
    ; F₁           = λ f → proj₁ f , record
                       { compatible = λ {o} {a} →
                           H₂.IsHom.compatible (proj₂ f) {ι φ o} {a ∘ κ φ o} }
    ; F-resp-≈     = λ f≋g → f≋g
    ; identity     = λ {𝑨} _ → Setoid.refl M₁.𝔻[ reduct φ 𝑨 ]
    ; homomorphism = λ {_} {_} {E} _ → Setoid.refl M₁.𝔻[ reduct φ E ]
    }
```

--------------------------------------

{% include UALib.Links.md %}
