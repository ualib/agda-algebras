---
layout: default
title : "Setoid.Subalgebras.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-18"
author: "agda-algebras development team"
---

#### Properties of the subalgebra relation for setoid algebras

This is the [Setoid.Subalgebras.Properties][] module of the [Agda Universal Algebra Library][].

This module establishes the order-theoretic facts about the subalgebra relation
`_≤_`{.AgdaFunction} that the rest of the library relies on: that it is a
preorder, that isomorphism refines it in either direction, that it survives
universe lifting, and that it is preserved by products.

The preorder is stated with respect to isomorphism rather than equality
(`≤-preorder`{.AgdaFunction}), which is the only sensible choice, since mutual
embeddings do not make two algebras equal.  The universe-lifting group is the
part used most often, for the reason recorded in [Setoid.Algebras.Basic][]:
Agda's universes are not cumulative, so a `≤` established at one level has to be
transported explicitly before it can be used at another.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Subalgebras.Properties where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------------
open import Data.Product              using ( _,_ )
open import Function                  using ( _∘_ )  renaming ( Func to _⟶_ )
open import Level                     using ( Level ; _⊔_ )
open import Relation.Binary           using ( Setoid )
open import Relation.Unary            using ( Pred ; _⊆_ )
import Relation.Binary.Structures as RelStructs

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------------
open import Overture                  using  ( proj₁ ; proj₂ ; 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open import Setoid.Algebras           using  ( Algebra ; Lift-Algˡ ; Lift-Algʳ
                                             ; Lift-Alg ; ov ; ⨅ ; 𝔻[_] )
open import Setoid.Functions          using  ( id-is-injective ; IsInjective ; ⊙-injective )
open import Setoid.Homomorphisms      using  ( hom ; IsHom ; 𝒾𝒹 ; ⊙-hom ; _≅_
                                             ; ≅toInjective ; ≅fromInjective ; mkiso
                                             ; ≅-sym ; ≅-refl ; ≅-trans
                                             ; Lift-≅ˡ ; Lift-≅ ; Lift-≅ʳ)
open import Setoid.Subalgebras.Basic  using  ( _≤_ ; _≥_ ; _≤c_ )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level
```
-->

The subalgebra relation is a *preorder*, i.e., a reflexive, transitive binary relation.

```agda
open _≅_

≅→≤ : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≅→≤ φ = (to φ) , ≅toInjective φ

≅→≥ : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≅→≥ φ = (from φ) , ≅fromInjective φ

≤-refl : {𝑨 𝑩 : Algebra {𝑆 = 𝑆} α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≤-refl = ≅→≤

≥-refl : {𝑨 𝑩 : Algebra {𝑆 = 𝑆} α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≥-refl = ≅→≤ ∘ ≅-sym

≤-reflexive : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id-is-injective {𝑨 = 𝔻[ 𝑨 ]}

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}{𝑪 : Algebra {𝑆 = 𝑆} γ ρᶜ} where
  ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
  ≤-trans ( f , finj ) ( g , ginj ) = (⊙-hom f g) , ⊙-injective (proj₁ f) (proj₁ g) finj ginj

  ≤-trans-≅ : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
  ≤-trans-≅ (h , hinj) B≅C =
    ⊙-hom h (to B≅C) , ⊙-injective (proj₁ h) (proj₁ (to B≅C)) hinj (≅toInjective B≅C)

  ≅-trans-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
  ≅-trans-≤ A≅B (h , hinj) =
    ⊙-hom (to A≅B) h , ⊙-injective (proj₁ (to A≅B)) (proj₁ h) (≅toInjective A≅B) hinj

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}{𝑪 : Algebra {𝑆 = 𝑆} γ ρᶜ} where
  ≥-trans : 𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
  ≥-trans A≥B B≥C = ≤-trans B≥C A≥B

≤→≤c→≤c : {𝑨 : Algebra {𝑆 = 𝑆} α α}{𝑩 : Algebra {𝑆 = 𝑆} α α}{𝒦 : Pred(Algebra {𝑆 = 𝑆} α α) (ov {𝑆 = 𝑆} α)}
  → 𝑨 ≤ 𝑩 → 𝑩 ≤c 𝒦 → 𝑨 ≤c 𝒦
≤→≤c→≤c A≤B sB = (proj₁ sB) , (proj₁ (proj₂ sB) , ≤-trans A≤B (proj₂ (proj₂ sB)))

module _ {𝑆 : Signature 𝓞 𝓥} {α ρᵃ ρ : Level} where

  open RelStructs {a = ov {𝑆 = 𝑆} (α ⊔ ρᵃ)} {ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ} (_≅_ {α = α}{ρᵃ = ρᵃ}{𝑆 = 𝑆})
  open IsPreorder

  ≤-preorder : IsPreorder _≤_
  isEquivalence  ≤-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
  reflexive      ≤-preorder = ≤-refl
  trans          ≤-preorder A≤B B≤C = ≤-trans A≤B B≤C

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}{𝑪 : Algebra {𝑆 = 𝑆} γ ρᶜ} where
  A≥B×B≅C→A≥C : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
  A≥B×B≅C→A≥C A≥B B≅C  = ≥-trans A≥B (≅→≥ B≅C)

  A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
  A≤B×B≅C→A≤C A≤B B≅C = ≤-trans  A≤B (≅→≤ B≅C)

  A≅B×B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
  A≅B×B≥C→A≥C A≅B B≥C = ≥-trans (≅→≥ A≅B) B≥C

  A≅B×B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
  A≅B×B≤C→A≤C A≅B B≤C = ≤-trans (≅→≤ A≅B) B≤C

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

iso→injective : (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ) {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}
  (φ : 𝑨 ≅ 𝑩) → IsInjective (proj₁ (to φ))
iso→injective 𝑨 (mkiso f g f∼g g∼f) {x} {y} fxfy =
  begin
  x                            ≈˘⟨ g∼f x ⟩
  proj₁ g ⟨$⟩ (proj₁ f ⟨$⟩ x)  ≈⟨ cong (proj₁ g) fxfy ⟩
  proj₁ g ⟨$⟩ (proj₁ f ⟨$⟩ y)  ≈⟨ g∼f y ⟩
  y                            ∎
  where open SetoidReasoning 𝔻[ 𝑨 ]

≤-mono : {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}{𝒦 𝒦' : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) γ}
  → 𝒦 ⊆ 𝒦' → 𝑩 ≤c 𝒦 → 𝑩 ≤c 𝒦'
≤-mono KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)
```

#### Lifts of subalgebras of setoid algebras

Ten lemmas of one shape: transport a `≤` or a `≥` across the isomorphism between
an algebra and its lift.  Each is a single application of one of the mixed
transitivity lemmas above to one of the `Lift-≅`{.AgdaFunction} isomorphisms of
[Setoid.Homomorphisms.Isomorphisms][], which is the concrete sense in which
universe lifting costs nothing here.

The suffix says which level moves, following `Lift-Algˡ`{.AgdaFunction},
`Lift-Algʳ`{.AgdaFunction} and `Lift-Alg`{.AgdaFunction} of
[Setoid.Algebras.Basic][]: `ˡ` raises the level of the carrier, `ʳ` the level of
the equality, and the unadorned name raises both.

+  `≤-Liftˡ`{.AgdaFunction}, `≤-Liftʳ`{.AgdaFunction} and
   `≤-Lift`{.AgdaFunction} lift the algebra on the right of `≤`, the larger one;
+  `≥-Liftˡ`{.AgdaFunction}, `≥-Liftʳ`{.AgdaFunction} and
   `≥-Lift`{.AgdaFunction} do the same for `≥`, which lifts the smaller one;
+  `Lift-≤-Liftˡ`{.AgdaFunction}, `Lift-≤-Liftʳ`{.AgdaFunction} and
   `Lift-≤-Lift`{.AgdaFunction} lift both algebras at once, and are literally the
   composition of the two groups above;
+  `Lift-is-sub`{.AgdaFunction} is the class-relative version: lifting an algebra
   does not disturb its being a subalgebra of some member of `𝒦`.

```agda
Lift-is-sub :
  {𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ)(ov {𝑆 = 𝑆} α)}
  {𝑩 : Algebra β ρᵇ} {ℓ : Level}
  → 𝑩 ≤c 𝒦 → (Lift-Algˡ 𝑩 ℓ) ≤c 𝒦
Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B×B≅C→A≥C B≤A Lift-≅ˡ)

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  ≤-Liftˡ : {ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Algˡ 𝑩 ℓ
  ≤-Liftˡ A≤B = A≤B×B≅C→A≤C A≤B Lift-≅ˡ

  ≤-Liftʳ : {ρ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Algʳ 𝑩 ρ
  ≤-Liftʳ A≤B = A≤B×B≅C→A≤C A≤B Lift-≅ʳ

  ≤-Lift : {ℓ ρ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Alg 𝑩 ℓ ρ
  ≤-Lift A≤B = A≤B×B≅C→A≤C  A≤B Lift-≅

  ≥-Liftˡ : {ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Algˡ 𝑩 ℓ
  ≥-Liftˡ A≥B = A≥B×B≅C→A≥C A≥B Lift-≅ˡ

  ≥-Liftʳ : {ρ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Algʳ 𝑩 ρ
  ≥-Liftʳ A≥B = A≥B×B≅C→A≥C A≥B Lift-≅ʳ

  ≥-Lift : {ℓ ρ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Alg 𝑩 ℓ ρ
  ≥-Lift A≥B = A≥B×B≅C→A≥C A≥B Lift-≅

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  Lift-≤-Liftˡ : {ℓᵃ ℓᵇ : Level} → 𝑨 ≤ 𝑩 → Lift-Algˡ 𝑨 ℓᵃ ≤ Lift-Algˡ 𝑩 ℓᵇ
  Lift-≤-Liftˡ A≤B = ≥-Liftˡ (≤-Liftˡ A≤B)

  Lift-≤-Liftʳ : {rᵃ rᵇ : Level} → 𝑨 ≤ 𝑩 → Lift-Algʳ 𝑨 rᵃ ≤ Lift-Algʳ 𝑩 rᵇ
  Lift-≤-Liftʳ A≤B = ≥-Liftʳ (≤-Liftʳ A≤B)

  Lift-≤-Lift : {a rᵃ b rᵇ : Level}
    → 𝑨 ≤ 𝑩 → Lift-Alg 𝑨 a rᵃ ≤ Lift-Alg 𝑩 b rᵇ
  Lift-≤-Lift A≤B = ≥-Lift (≤-Lift A≤B)
```

#### Products of subalgebras

`⨅-≤`{.AgdaFunction} is the compatibility of the subalgebra relation with
products: if `ℬ i ≤ 𝒜 i` for every index `i`, then `⨅ ℬ ≤ ⨅ 𝒜`.  The embedding is
assembled coordinatewise from the given ones, and injectivity is coordinatewise
too, because two elements of a product are equal exactly when they agree in every
coordinate.

Small as it is, this is the load-bearing step of `PS⊆SP`{.AgdaFunction} in
[Setoid.Varieties.Preservation][], where a product of subalgebras has to be
recognised as a subalgebra of a product so that `S`{.AgdaFunction} and
`P`{.AgdaFunction} can be interchanged.

```agda
module _
  {I : Type ι}
  {𝒜 : I → Algebra {𝑆 = 𝑆} α ρᵃ}
  {ℬ : I → Algebra {𝑆 = 𝑆} β ρᵇ}
  where
  open IsHom

  ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
  ⨅-≤ B≤A = h , hM
    where
    h : hom (⨅ ℬ) (⨅ 𝒜)
    h = hfunc , hhom
      where
      homAt : ∀ i → hom (ℬ i) (𝒜 i)
      homAt = λ i → proj₁ (B≤A i)

      hmapAt : ∀ i → 𝔻[ ℬ i ] ⟶ 𝔻[ 𝒜 i ]
      hmapAt = proj₁ ∘ homAt

      hfunc : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
      hfunc ⟨$⟩ x = λ i → (hmapAt i) ⟨$⟩ (x i)
      hfunc .cong = λ xy i → cong (hmapAt i) (xy i)

      hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
      hhom .compatible = λ i → compatible (proj₂ (homAt i))

    hM : IsInjective (proj₁ h)
    hM = λ xy i → (proj₂ (B≤A i)) (xy i)
```
