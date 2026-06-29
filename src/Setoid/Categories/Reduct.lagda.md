---
layout: default
file: "src/Setoid/Categories/Reduct.lagda.md"
title: "Setoid.Categories.Reduct module"
date: "2026-06-09"
author: "the agda-algebras development team"
---

### Reduct as a functor on algebras

This is the [Setoid.Categories.Reduct][] module of the [Agda Universal Algebra Library][].

A signature morphism `φ : SigMorphism 𝑆₁ 𝑆₂` induces a covariant functor
`reductF φ : Alg 𝑆₂ ⟶ Alg 𝑆₁` between the [algebra categories][Setoid.Categories.Algebra].
On objects it is [`reduct`][Setoid.Algebras.Reduct]`φ`; on a homomorphism it keeps the
*same* underlying setoid map and transfers the `𝑆₂`-homomorphism condition to `𝑆₁` by the
`κ`-reindex — `compatible` at the `𝑆₁`-symbol `o` is `f`'s `𝑆₂`-`compatible` at `ι φ o`,
definitionally on the nose, because `(o ^ reduct φ 𝑨) = (ι φ o ^ 𝑨) ∘ (_∘ κ φ o)`.

The functor laws are immediate: `F-resp-≈` is the identity (the underlying maps are
unchanged, and the hom-equality is pointwise on them), and `identity` / `homomorphism` hold
by the codomain's `refl` (the underlying maps of both sides are the same — `𝒾𝒹` and `⊙-hom`
are the identity map and function composition).

This functor lives in `Setoid.Categories`, alongside the rest of the category vocabulary; its
object map `reduct` is [`Setoid.Algebras.Reduct`][Setoid.Algebras.Reduct], also a `Setoid/`
construction.  (Both were relocated from `Classical/` by
[ADR-006](../../docs/adr/006-signature-morphism-category.md), M4-16: reduct is universal
algebra, not classical, and depends on nothing in `Classical/`.)

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Categories.Reduct where


-- Imports from the Agda Standard Library ----------------------------
open import Data.Product                   using ( _,_ ; proj₁ ; proj₂ )
open import Function                       using ( Func ; _∘_ ; id)
open import Level                          using ( Level ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary                using ( Setoid )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Reduct         using ( reduct )
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ )
open import Setoid.Algebras.Basic          using (𝔻[_])
open import Setoid.Categories.Algebra      using (Alg)
open import Setoid.Categories.Category     using (Category)
open import Setoid.Categories.Functor      using ( Functor )
open import Setoid.Homomorphisms.Basic     using (IsHom; mkIsHom)

open Func renaming ( to to _⟨$⟩_ )

module _ {α ρ : Level} {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) where
  𝓐₁ 𝓐₂ : Category (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) (α ⊔ ρ)
  𝓐₁ = Alg {𝑆 = 𝑆₁} α ρ
  𝓐₂ = Alg {𝑆 = 𝑆₂} α ρ
  open IsHom {𝑆 = 𝑆₂} renaming ( compatible to comp₂ )

  reductF : Functor 𝓐₂ 𝓐₁
  reductF =
    record
      { F₀            = reduct φ
      ; F₁            = λ f → proj₁ f
                             , mkIsHom (λ{o a} → comp₂ (proj₂ f) {ι φ o} {a ∘ κ φ o})
      ; F-resp-≈      = id
      ; identity      = λ {𝑨} _ → Setoid.refl 𝔻[ reduct φ 𝑨 ]
      ; homomorphism  = λ {_} {_} {E} _ → Setoid.refl 𝔻[ reduct φ E ]
      }
```
