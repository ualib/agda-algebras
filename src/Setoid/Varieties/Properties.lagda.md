---
layout: default
title : "Setoid.Varieties.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-24"
author: "agda-algebras development team"
---

### Properties of the models relation for setoid algebras

We prove some closure and invariance properties of the relation `⊧`.  In particular, we prove the following facts (which are needed, for example, in the proof the Birkhoff HSP Theorem).

* [Algebraic invariance](#algebraic-invariance). `⊧` is an *algebraic invariant* (stable under isomorphism).

* [Subalgebraic invariance](#subalgebraic-invariance). Identities modeled by a class of algebras are also modeled by all subalgebras of algebras in the class.

* [Product invariance](#product-invariance). Identities modeled by a class of algebras are also modeled by all products of algebras in the class.



<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Properties where

-- Imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; proj₁ ; proj₂ )
open import Function         using ( _∘_ ; Func ; _$_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open  import Overture                           using  ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open  import Overture.Terms                     using  ( Term ; ℊ )
open  import Setoid.Algebras                    using  ( Algebra ; Lift-Algˡ ; ov
                                                       ; 𝕌[_] ; 𝔻[_] ; ⨅ )
open  import Setoid.Functions                   using  ( InvIsInverseʳ ; SurjInv )
open  import Setoid.Homomorphisms               using  ( hom ; _≅_ ; mkiso ; Lift-≅ˡ
                                                       ; ≅-sym ; _IsHomImageOf_ )
open  import Setoid.Subalgebras                 using  ( _≤_ ; SubalgebrasOfClass )
open  import Setoid.Terms                       using  ( 𝑻 ; module Environment
                                                       ; comm-hom-term ; interp-prod
                                                       ; term-agreement )
open  import Setoid.Varieties.SoundAndComplete  using  ( _⊧_ ; _⊫_ ; ⊫-proof ; _≈̇_
                                                       ; _⊢_▹_≈_ )

private variable α ρᵃ β ρᵇ χ ℓ : Level

open Func     using ( cong ) renaming ( to to _⟨$⟩_ )
open Algebra  using ( Domain )
```
-->



#### Algebraic invariance of ⊧ {#algebraic-invariance}

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism).


```agda
module _ {X : Type χ}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}(𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ)(p q : Term {𝑆 = 𝑆} X) where
  open Environment 𝑨      using () renaming ( ⟦_⟧   to ⟦_⟧₁ )
  open Environment 𝑩      using () renaming ( ⟦_⟧   to ⟦_⟧₂ )
  open Setoid (Domain 𝑩)  using ( _≈_ ; sym ; trans )
  open SetoidReasoning (Domain 𝑩)

  ⊧-I-invar : 𝑨 ⊧ (p ≈̇ q)  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ (p ≈̇ q)
  ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ = trans i $ trans ii $ trans iii $ trans iv v
    where
    -- TODO: refactor this proof using new relational reasoning syntax/style
    f = _⟨$⟩_ (proj₁ fh) ; g = _⟨$⟩_ (proj₁ gh)

    i : ⟦ p ⟧₂ ⟨$⟩ ρ ≈ ⟦ p ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ))
    i = sym $ cong ⟦ p ⟧₂ (f∼g ∘ ρ)

    ii : ⟦ p ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ)) ≈ f (⟦ p ⟧₁ ⟨$⟩ (g ∘ ρ))
    ii = sym $ comm-hom-term fh p (g ∘ ρ)

    iii : f (⟦ p ⟧₁ ⟨$⟩ (g ∘ ρ)) ≈ f (⟦ q ⟧₁ ⟨$⟩ (g ∘ ρ))
    iii = cong (proj₁ fh) $ Apq (g ∘ ρ)

    iv : f (⟦ q ⟧₁ ⟨$⟩ (g ∘ ρ)) ≈ ⟦ q ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ))
    iv = comm-hom-term fh q (g ∘ ρ)

    v : ⟦ q ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ)) ≈ ⟦ q ⟧₂ ⟨$⟩ ρ
    v = cong ⟦ q ⟧₂ (f∼g ∘ ρ)
```


As the proof makes clear, we show `𝑩 ⊧ p ≈ q` by showing that `𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧`
holds *extensionally*, that is, `∀ x, 𝑩 ⟦ p ⟧ x ≡ 𝑩 ⟦q ⟧ x`.

#### Lift-invariance of ⊧ {#lift-invariance}
The ⊧ relation is also invariant under the algebraic lift and lower operations.


```agda
module _ {X : Type χ}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} where

  ⊧-Lift-invar : (p q : Term {𝑆 = 𝑆} X) → 𝑨 ⊧ (p ≈̇ q) → Lift-Algˡ 𝑨 β ⊧ (p ≈̇ q)
  ⊧-Lift-invar p q Apq = ⊧-I-invar (Lift-Algˡ 𝑨 _) p q Apq Lift-≅ˡ

  ⊧-lower-invar : (p q : Term {𝑆 = 𝑆} X) → Lift-Algˡ 𝑨 β ⊧ (p ≈̇ q)  →  𝑨 ⊧ (p ≈̇ q)
  ⊧-lower-invar p q lApq = ⊧-I-invar 𝑨 p q lApq (≅-sym Lift-≅ˡ)
```


#### Homomorphic invariance of ⊧
Identities modeled by an algebra `𝑨` are also modeled by every homomorphic image
of `𝑨`, which fact can be formalized as follows.


```agda
module _ {X : Type χ}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}{p q : Term {𝑆 = 𝑆} X} where

  ⊧-H-invar : 𝑨 ⊧ (p ≈̇ q) → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ (p ≈̇ q)
  ⊧-H-invar Apq (φh , φE) ρ =
   begin
        ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
        ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
    φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong (proj₁ φh) (Apq (φ⁻¹ ∘ ρ))         ⟩
    φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
        ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
        ⟦ q ⟧   ⟨$⟩               ρ    ∎
    where
    φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    φ⁻¹ = SurjInv (proj₁ φh) φE
    φ = (_⟨$⟩_ (proj₁ φh))
    open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
    open Environment 𝑩  using ( ⟦_⟧ )
    open SetoidReasoning 𝔻[ 𝑩 ]
```



#### Subalgebraic invariance of ⊧ {#subalgebraic-invariance}
Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`, which fact can be formalized as follows.


```agda
module _ {X : Type χ}{p q : Term {𝑆 = 𝑆} X}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  open Environment 𝑨      using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment 𝑩      using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open Setoid (Domain 𝑨)  using ( _≈_ )
  open Setoid (Domain 𝑩)  using () renaming ( _≈_ to _≈₂_ )
  open SetoidReasoning (Domain 𝑨)

  ⊧-S-invar : 𝑨 ⊧ (p ≈̇ q) →  𝑩 ≤ 𝑨  →  𝑩 ⊧ (p ≈̇ q)
  ⊧-S-invar Apq B≤A b = goal
    where
    hh : hom 𝑩 𝑨
    hh = (proj₁ B≤A)
    h = _⟨$⟩_ (proj₁ hh)
    ξ : ∀ b → h (⟦ p ⟧₂ ⟨$⟩ b) ≈ h (⟦ q ⟧₂ ⟨$⟩ b)
    ξ b = begin
           h (⟦ p ⟧₂ ⟨$⟩ b)    ≈⟨ comm-hom-term hh p b ⟩
           ⟦ p ⟧₁ ⟨$⟩ (h ∘ b)  ≈⟨ Apq (h ∘ b) ⟩
           ⟦ q ⟧₁ ⟨$⟩ (h ∘ b)  ≈˘⟨ comm-hom-term hh q b ⟩
           h (⟦ q ⟧₂ ⟨$⟩ b)    ∎

    goal : ⟦ p ⟧₂ ⟨$⟩ b ≈₂ ⟦ q ⟧₂ ⟨$⟩ b
    goal = (proj₂ B≤A) (ξ b)
```


Next, identities modeled by a class of algebras is also modeled by all subalgebras
of the class.  In other terms, every term equation `(p ≈̇ q)` that is satisfied by
all `𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of `𝒦`.


```agda
module _ {X : Type χ}{p q : Term {𝑆 = 𝑆} X} where

  ⊧-S-class-invar :  {𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ}
   →                 (𝒦 ⊫ (p ≈̇ q)) → ((𝑩 , _) : SubalgebrasOfClass 𝒦 {β}{ρᵇ})
   →                 𝑩 ⊧ (p ≈̇ q)
  ⊧-S-class-invar Kpq (𝑩 , 𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (Kpq .⊫-proof 𝑨 kA) B≤A
```



#### Product invariance of ⊧ {#product-invariance}

An identity satisfied by all algebras in an indexed collection is also satisfied
by the product of algebras in that collection.


```agda
module _ {X : Type χ}{p q : Term {𝑆 = 𝑆} X}{I : Type ℓ}(𝒜 : I → Algebra {𝑆 = 𝑆} α ρᵃ) where

  ⊧-P-invar : (∀ i → 𝒜 i ⊧ (p ≈̇ q)) → ⨅ 𝒜 ⊧ (p ≈̇ q)
  ⊧-P-invar 𝒜pq a = goal
    where
    open Algebra (⨅ 𝒜)      using () renaming ( Domain to ⨅A )
    open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
    open Environment        using ( ⟦_⟧ )
    open Setoid ⨅A          using ( _≈_ )
    open SetoidReasoning ⨅A

    ξ : (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i)) ≈ (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i))
    ξ = λ i → 𝒜pq i (λ x → (a x) i)
    goal : ⟦ p ⟧₁ ⟨$⟩ a ≈ ⟦ q ⟧₁ ⟨$⟩ a
    goal = begin
            ⟦ p ⟧₁ ⟨$⟩ a                             ≈⟨ interp-prod 𝒜 p a ⟩
            (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i))  ≈⟨ ξ ⟩
            (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i))  ≈˘⟨ interp-prod 𝒜 q a ⟩
            ⟦ q ⟧₁ ⟨$⟩ a                             ∎
```


An identity satisfied by all algebras in a class is also satisfied by the product
of algebras in the class.


```agda
  ⊧-P-class-invar :  (𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ)(ov {𝑆 = 𝑆} α))
   →                 𝒦 ⊫ (p ≈̇ q) → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ (p ≈̇ q)

  ⊧-P-class-invar 𝒦 σ K𝒜 = ⊧-P-invar (λ i ρ → σ .⊫-proof (𝒜 i) (K𝒜 i) ρ)
```


Another fact that will turn out to be useful is that a product of a collection of
algebras models (p ≈̇ q) if the lift of each algebra in the collection models
(p ≈̇ q).


```agda
  ⊧-P-lift-invar : (∀ i → Lift-Algˡ (𝒜 i) β ⊧ (p ≈̇ q))  →  ⨅ 𝒜 ⊧ (p ≈̇ q)
  ⊧-P-lift-invar α = ⊧-P-invar Aipq
    where
    Aipq : ∀ i → (𝒜 i) ⊧ (p ≈̇ q)
    Aipq i = ⊧-lower-invar{𝑨 = (𝒜 i)} p q (α i)
```



#### Modeled identities and homomorphism kernels

If an algebra 𝑨 models an identity (p ≈̇ q), then the pair (p , q) belongs to the
kernel of every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is,
every homomorphism from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.

 
```agda
module _ {𝑆 : Signature 𝓞 𝓥}{X : Type χ}{p q : Term {𝑆 = 𝑆} X}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}(φh : hom (𝑻 X) 𝑨) where
  open Setoid (Domain 𝑨) using ( _≈_ )
  private φ = _⟨$⟩_ (proj₁ φh)

  ⊧-H-ker : 𝑨 ⊧ (p ≈̇ q) → φ p ≈ φ q
  ⊧-H-ker β =
   begin
    φ p                 ≈⟨ cong (proj₁ φh) (term-agreement p)⟩
    φ (⟦ p ⟧ ⟨$⟩ ℊ)     ≈⟨ comm-hom-term φh p ℊ ⟩
    ⟦ p ⟧₂ ⟨$⟩ (φ ∘ ℊ)  ≈⟨ β (φ ∘ ℊ) ⟩
    ⟦ q ⟧₂ ⟨$⟩ (φ ∘ ℊ)  ≈˘⟨ comm-hom-term φh q ℊ ⟩
    φ (⟦ q ⟧ ⟨$⟩ ℊ)     ≈˘⟨ cong (proj₁ φh) (term-agreement q)⟩
    φ q                 ∎

    where
    open SetoidReasoning (Domain 𝑨)
    open Environment 𝑨      using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
    open Environment (𝑻 X)  using ( ⟦_⟧ )
```
