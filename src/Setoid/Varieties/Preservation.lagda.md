---
layout: default
title : "Setoid.Varieties.Preservation (The Agda Universal Algebra Library)"
date : "2021-09-24"
author: "agda-algebras development team"
---

### Equation preservation for setoid algebras

This is the [Setoid.Varieties.Preservation][] module of the [Agda Universal Algebra Library][] where we show
that the classes \af H `𝒦`{.AgdaBound}, \af S `𝒦`{.AgdaBound}, \af P `𝒦`{.AgdaBound}, and \af V `𝒦`{.AgdaBound} all satisfy the
same identities.


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Varieties.Preservation {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------
open import Data.Product           using ( _,_ )
open import Data.Unit.Polymorphic  using ( ⊤ )
open import Function               using ()  renaming ( Func to _⟶_ )
open import Level                  using ( Level ; _⊔_ )
open import Relation.Binary        using ( Setoid )
open import Relation.Unary         using ( Pred ; _⊆_ ; _∈_ )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture                                    using  ( proj₁ ; proj₂ )

open import Overture.Terms                     {𝑆 = 𝑆}  using  ( Term )
open import Setoid.Algebras                    {𝑆 = 𝑆}  using  ( Algebra ; ov ; ⨅ )
open import Setoid.Homomorphisms               {𝑆 = 𝑆}  using  ( ≅⨅⁺-refl ; ≅-refl
                                                               ; IdHomImage ; ≅-sym )
open import Setoid.Subalgebras                 {𝑆 = 𝑆}  using  ( _≤_ ; ⨅-≤ ; ≅-trans-≤
                                                               ; ≤-reflexive )
open import Setoid.Terms                       {𝑆 = 𝑆}  using  ( module Environment)
open import Setoid.Varieties.Closure           {𝑆 = 𝑆}  using  ( H ; S ; P ; S-expa
                                                               ; H-expa ; V ; P-expa
                                                               ; V-expa ;Level-closure )
open import Setoid.Varieties.Properties        {𝑆 = 𝑆}  using  ( ⊧-H-invar ; ⊧-S-invar
                                                               ; ⊧-P-invar ; ⊧-I-invar )
open import Setoid.Varieties.SoundAndComplete  {𝑆 = 𝑆}  using  ( _⊧_ ; _⊫_ ; ⊫-proof
                                                               ; _≈̇_ ; _⊢_▹_≈_ ; Th)
open _⟶_      using () renaming ( to to _⟨$⟩_ )
open Algebra  using ( Domain )
```
-->

#### Closure properties

The types defined above represent operators with useful closure properties. We now
prove a handful of such properties that we need later.

```agda
module _  {α ρᵃ ℓ : Level}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
  private
    a = α ⊔ ρᵃ
    oaℓ = ov (a ⊔ ℓ)

  S⊆SP : ∀{ι} → S ℓ 𝒦 ⊆ S {β = α}{ρᵃ} (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ} ℓ ι 𝒦)
  S⊆SP {ι} (𝑨 , (kA , B≤A )) = 𝑨 , (pA , B≤A)
    where
    pA : 𝑨 ∈ P ℓ ι 𝒦
    pA = ⊤ , (λ _ → 𝑨) , (λ _ → kA) , ≅⨅⁺-refl

  P⊆SP : ∀{ι} → P ℓ ι 𝒦 ⊆ S (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ}ℓ ι 𝒦)
  P⊆SP {ι} x = S-expa{ℓ = a ⊔ ℓ ⊔ ι} x


  P⊆HSP : ∀{ι} →  P {β = α}{ρᵃ} ℓ ι 𝒦 ⊆ H (a ⊔ ℓ ⊔ ι) (S (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))
  P⊆HSP {ι} x = H-expa{ℓ = a ⊔ ℓ ⊔ ι}  (S-expa{ℓ = a ⊔ ℓ ⊔ ι} x)

  P⊆V : ∀{ι} → P ℓ ι 𝒦 ⊆ V ℓ ι 𝒦
  P⊆V = P⊆HSP

  SP⊆V : ∀{ι} → S{β = α}{ρᵇ = ρᵃ} (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ} ℓ ι 𝒦) ⊆ V ℓ ι 𝒦
  SP⊆V {ι} x = H-expa{ℓ = a ⊔ ℓ ⊔ ι} x
```

Finally, we are in a position to prove that a product of subalgebras of algebras
in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

```agda
  PS⊆SP : P (a ⊔ ℓ) oaℓ (S{β = α}{ρᵃ} ℓ 𝒦) ⊆ S oaℓ (P ℓ oaℓ 𝒦)
  PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
    where
    ℬ : I → Algebra α ρᵃ
    ℬ i = sA i .proj₁

    kB : (i : I) → ℬ i ∈ 𝒦
    kB i =  sA i .proj₂ .proj₁

    ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
    ⨅A≤⨅B = ⨅-≤ λ i → proj₂ (proj₂ (sA i))
    Goal : 𝑩 ∈ S{β = oaℓ}{oaℓ}oaℓ (P {β = oaℓ}{oaℓ} ℓ oaℓ 𝒦)
    Goal = ⨅ ℬ , (I , (ℬ , (kB , ≅-refl))) , (≅-trans-≤ B≅⨅A ⨅A≤⨅B)
```

#### H preserves identities

First we prove that the closure operator H is compatible with identities that hold in the given class.

```agda
module _   {α ρᵃ ℓ χ : Level}
            {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}
            {X : Type χ}
            {p q : Term X}
            where

  H-id1 : 𝒦 ⊫ (p ≈̇ q) → H {β = α}{ρᵃ}ℓ 𝒦 ⊫ (p ≈̇ q)
  H-id1 σ .⊫-proof 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ .⊫-proof 𝑨 kA) BimgA
```

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

```agda
  H-id2 : H ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
  H-id2 Hpq .⊫-proof 𝑨 kA = Hpq .⊫-proof 𝑨 (𝑨 , (kA , IdHomImage))
```

#### S preserves identities

```agda
  S-id1 : 𝒦 ⊫ (p ≈̇ q) → (S {β = α}{ρᵃ} ℓ 𝒦) ⊫ (p ≈̇ q)
  S-id1 σ .⊫-proof 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ .⊫-proof 𝑨 kA) B≤A

  S-id2 : S ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
  S-id2 Spq .⊫-proof 𝑨 kA = Spq .⊫-proof 𝑨 (𝑨 , (kA , ≤-reflexive))
```

#### P preserves identities

```agda
  P-id1 : ∀{ι} → 𝒦 ⊫ (p ≈̇ q) → P {β = α}{ρᵃ}ℓ ι 𝒦 ⊫ (p ≈̇ q)
  P-id1 σ .⊫-proof 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
    where
    ih : ∀ i → 𝒜 i ⊧ (p ≈̇ q)
    ih i = σ .⊫-proof (𝒜 i) (kA i)
    IH : ⨅ 𝒜 ⊧ (p ≈̇ q)
    IH = ⊧-P-invar {p = p}{q} 𝒜 ih

  P-id2 : ∀{ι} → P ℓ ι 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
  P-id2{ι} PKpq .⊫-proof 𝑨 kA = PKpq .⊫-proof 𝑨 (P-expa {ℓ = ℓ}{ι} kA)
```

#### V preserves identities

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

```agda
module _
  {α ρᵃ ℓ ι χ : Level}
  {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}
  {X : Type χ}
  {p q : Term X}
  where

  private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

  V-id1 : 𝒦 ⊫ (p ≈̇ q) → V ℓ ι 𝒦 ⊫ (p ≈̇ q)
  V-id1 σ .⊫-proof 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
    H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)} spK⊧pq .⊫-proof 𝑩 (𝑨 , (spA , BimgA))
      where
      spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
      spA = ⨅A , (p⨅A , A≤⨅A)
      spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ (p ≈̇ q)
      spK⊧pq = S-id1{ℓ = aℓι} (P-id1{ℓ = ℓ} {𝒦 = 𝒦} σ)

  V-id2 : V ℓ ι 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
  V-id2 Vpq .⊫-proof 𝑨 kA = Vpq .⊫-proof 𝑨 (V-expa ℓ ι kA)

  Lift-id1 : ∀{β ρᵇ} → 𝒦 ⊫ (p ≈̇ q) → Level-closure{α}{ρᵃ}{β}{ρᵇ} ℓ 𝒦 ⊫ (p ≈̇ q)
  Lift-id1 pKq .⊫-proof 𝑨 (𝑩 , kB , B≅A) ρ = Goal
    where
    open Environment 𝑨
    open Setoid (Domain 𝑨) using (_≈_)
    Goal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
    Goal = ⊧-I-invar 𝑨 p q (pKq .⊫-proof 𝑩 kB) B≅A ρ
```

#### Class identities

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities
modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all
structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities
modeled by `𝒦`.   We formalize this observation as follows.

```agda
  classIds-⊆-VIds : 𝒦 ⊫ (p ≈̇ q)  → (p , q) ∈ Th (V ℓ ι 𝒦)
  classIds-⊆-VIds pKq = V-id1 pKq

  VIds-⊆-classIds : (p , q) ∈ Th (V ℓ ι 𝒦) → 𝒦 ⊫ (p ≈̇ q)
  VIds-⊆-classIds Thpq = V-id2 Thpq
```
