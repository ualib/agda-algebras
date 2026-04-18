---
layout: default
title : "Base.Structures.Isos module (The Agda Universal Algebra Library)"
date : "2021-07-23"
author: "agda-algebras development team"
---

### <a id="isomorphisms">Isomorphisms</a>

This is the [Base.Structures.Isos][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Isos where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Axiom.Extensionality.Propositional
                            using () renaming (Extensionality to funext)
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ )
open import Level           using ( _⊔_ ; Level ; Lift )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( module ≡-Reasoning ; cong-app )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower )

open import Base.Structures.Basic  using ( signature ; structure ; Lift-Strucˡ )
                                   using ( Lift-Strucʳ ; Lift-Struc ; sigl )
                                   using ( siglˡ ; siglʳ )
open import Base.Structures.Homs   using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; 𝓁𝒾𝒻𝓉ˡ )
                                   using ( 𝓁ℴ𝓌ℯ𝓇ˡ ; 𝓁𝒾𝒻𝓉ʳ ; 𝓁ℴ𝓌ℯ𝓇ʳ ; is-hom )
open import Base.Structures.Products
                                   using ( ⨅ ; ℓp ; ℑ ; class-product )
private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ α ρᵃ β ρᵇ γ ρᶜ ρ ℓ ι : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
\end{code}


#### <a id="definition-of-isomorphism">Definition of Isomorphism</a>

Recall, `f ≈ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`.
We use this notion of equality of functions in the following definition of *isomorphism*.

\begin{code}

record _≅_  (𝑨 : structure  𝐹 𝑅 {α}{ρᵃ})
            (𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}) : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
            where

 constructor mkiso
 field
  to       : hom 𝑨 𝑩
  from     : hom 𝑩 𝑨
  to∼from  : ∣ to ∣ ∘ ∣ from ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑩} ∣
  from∼to  : ∣ from ∣ ∘ ∣ to ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑨} ∣

open _≅_ public

\end{code}

That is, two structures are isomorphic provided there are homomorphisms going back and forth between them which compose to the identity map.


#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

module _ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} where

 ≅-refl : 𝑨 ≅ 𝑨
 ≅-refl = mkiso 𝒾𝒹 𝒾𝒹 (λ _ → ≡.refl) (λ _ → ≡.refl)

 module _ {𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}} where
  ≅-sym : 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
  ≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

  module _ {𝑪 : structure 𝐹 𝑅 {γ}{ρᶜ}} where
   ≅-trans : 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪
   ≅-trans φab φbc = mkiso f g τ ν
    where
    f : hom 𝑨 𝑪
    f = ∘-hom {𝑨 = 𝑨}{𝑩}{𝑪} (to φab) (to φbc)
    g : hom 𝑪 𝑨
    g = ∘-hom {𝑨 = 𝑪}{𝑩}{𝑨} (from φbc) (from φab)

    τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑪} ∣
    τ x = ( ≡.cong ∣ to φbc ∣ (to∼from φab (∣ from φbc ∣ x)) ) ∙ (to∼from φbc) x

    ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑨} ∣
    ν x = ( ≡.cong ∣ from φab ∣ (from∼to φbc (∣ to φab ∣ x)) ) ∙ (from∼to φab) x
\end{code}


#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in the [Base.Overture][] module.

\begin{code}

open Level

module _ {𝑨 : structure 𝐹 𝑅{α}{ρᵃ}} where

 Lift-≅ˡ : 𝑨 ≅ (Lift-Strucˡ ℓ 𝑨)
 Lift-≅ˡ = record  { to = 𝓁𝒾𝒻𝓉ˡ
                   ; from = 𝓁ℴ𝓌ℯ𝓇ˡ {𝑨 = 𝑨}
                   ; to∼from = cong-app lift∼lower
                   ; from∼to = cong-app (lower∼lift{α}{ρᵃ})
                   }

 Lift-≅ʳ : 𝑨 ≅ (Lift-Strucʳ ℓ 𝑨)
 Lift-≅ʳ  = record  { to = 𝓁𝒾𝒻𝓉ʳ
                    ; from = 𝓁ℴ𝓌ℯ𝓇ʳ
                    ; to∼from = cong-app ≡.refl
                    ; from∼to = cong-app ≡.refl
                    }

 Lift-≅ : 𝑨 ≅ (Lift-Struc ℓ ρ 𝑨)
 Lift-≅  = record  { to = 𝓁𝒾𝒻𝓉
                   ; from = 𝓁ℴ𝓌ℯ𝓇 {𝑨 = 𝑨}
                   ; to∼from = cong-app lift∼lower
                   ; from∼to = cong-app (lower∼lift{α}{ρᵃ})
                   }

module _ {𝑨 : structure 𝐹 𝑅{α}{ρᵃ}} {𝑩 : structure 𝐹 𝑅{β}{ρᵇ}} where

 Lift-Strucˡ-iso : (ℓ ℓ' : Level) → 𝑨 ≅ 𝑩 → Lift-Strucˡ ℓ 𝑨 ≅ Lift-Strucˡ ℓ' 𝑩
 Lift-Strucˡ-iso ℓ ℓ' A≅B = ≅-trans ( ≅-trans (≅-sym Lift-≅ˡ) A≅B ) Lift-≅ˡ


 Lift-Struc-iso :  (ℓ ρ ℓ' ρ' : Level) → 𝑨 ≅ 𝑩
  →                Lift-Struc ℓ ρ 𝑨 ≅ Lift-Struc ℓ' ρ' 𝑩

 Lift-Struc-iso ℓ ρ ℓ' ρ' A≅B = ≅-trans ( ≅-trans (≅-sym Lift-≅) A≅B ) Lift-≅
\end{code}


#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.

\begin{code}

module _ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ} } where

 Lift-Struc-assocˡ :  {ℓ ℓ' : Level}
  →                   Lift-Strucˡ (ℓ ⊔ ℓ') 𝑨 ≅ (Lift-Strucˡ ℓ (Lift-Strucˡ ℓ' 𝑨))

 Lift-Struc-assocˡ {ℓ}{ℓ'} = ≅-trans (≅-trans Goal Lift-≅ˡ) Lift-≅ˡ
  where
  Goal : Lift-Strucˡ (ℓ ⊔ ℓ') 𝑨 ≅ 𝑨
  Goal = ≅-sym Lift-≅ˡ

 Lift-Struc-assocʳ :  {ρ ρ' : Level}
  →                   Lift-Strucʳ (ρ ⊔ ρ') 𝑨 ≅ (Lift-Strucʳ ρ (Lift-Strucʳ ρ' 𝑨))

 Lift-Struc-assocʳ {ρ}{ρ'} = ≅-trans (≅-trans Goal Lift-≅ʳ) Lift-≅ʳ
  where
  Goal : Lift-Strucʳ (ρ ⊔ ρ') 𝑨 ≅ 𝑨
  Goal = ≅-sym Lift-≅ʳ

 Lift-Struc-assoc :  {ℓ ℓ' ρ ρ' : Level}
  →                  Lift-Struc (ℓ ⊔ ℓ') (ρ ⊔ ρ') 𝑨 ≅ (Lift-Struc ℓ ρ (Lift-Struc ℓ' ρ' 𝑨))
 Lift-Struc-assoc {ℓ}{ℓ'}{ρ}{ρ'} = ≅-trans (≅-trans Goal Lift-≅ ) Lift-≅
  where
  Goal : Lift-Struc (ℓ ⊔ ℓ') (ρ ⊔ ρ') 𝑨 ≅ 𝑨
  Goal = ≅-sym Lift-≅
\end{code}


#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic.
The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

module _  {I : Type ι}
          {𝒜 : I → structure 𝐹 𝑅{α}{ρᵃ}}
          {ℬ : I → structure 𝐹 𝑅{β}{ρᵇ}} where
 open structure
 open ≡-Reasoning

 ⨅≅ : funext ι α → funext ι β → (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

 ⨅≅ fiu fiw AB = record  { to       = ϕ , ϕhom
                         ; from     = ψ , ψhom
                         ; to∼from  = ϕ~ψ
                         ; from∼to  = ψ~ϕ
                         }
  where
  ϕ : carrier (⨅ 𝒜) → carrier (⨅ ℬ)
  ϕ a i = ∣ to (AB i) ∣ (a i)

  ϕhom : is-hom (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom =  ( λ r a x 𝔦 → fst ∥ to (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦))
          , λ f a → fiw (λ i → snd ∥ to (AB i) ∥ f λ z → a z i)
  ψ : carrier (⨅ ℬ) → carrier (⨅ 𝒜)
  ψ b i = ∣ from (AB i) ∣ (b i)

  ψhom : is-hom (⨅ ℬ) (⨅ 𝒜) ψ
  ψhom =  ( λ r a x 𝔦 → fst ∥ from (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦))
          , λ f a → fiu (λ i → snd ∥ from (AB i) ∥ f λ z → a z i)

  ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 {𝑨 = ⨅ ℬ} ∣
  ϕ~ψ 𝒃 = fiw λ i → (to∼from (AB i)) (𝒃 i)

  ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 {𝑨 = ⨅ 𝒜} ∣
  ψ~ϕ a = fiu λ i → (from∼to (AB i)) (a i)

\end{code}

A nearly identical proof goes through for isomorphisms of lifted products (though,
just for fun, we use the universal quantifier syntax here to express the dependent
function type in the statement of the lemma, instead of the Pi notation we used in
the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of
`Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

module _  {I : Type ι}
          {𝒜 : I → structure 𝐹 𝑅 {α}{ρᵃ}}
          {ℬ : (Lift γ I) → structure 𝐹 𝑅 {β}{ρᵇ}} where

 open structure

 Lift-Struc-⨅≅ :  funext (ι ⊔ γ) β → funext ι α
  →               (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Strucˡ γ (⨅ 𝒜) ≅ ⨅ ℬ

 Lift-Struc-⨅≅ fizw fiu AB = Goal
  where
   ϕ : carrier (⨅ 𝒜) →  carrier (⨅ ℬ)
   ϕ a i = ∣ to (AB (lower i)) ∣ (a (lower i))

   ϕhom : is-hom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom =  ( λ r a x i → fst ∥ to (AB (lower i)) ∥ r (λ x₁ → a x₁ (lower i)) (x (lower i)))
           , λ f a → fizw (λ i → snd ∥ to (AB (lower i)) ∥ f λ x → a x (lower i))

   ψ : carrier (⨅ ℬ) → carrier (⨅ 𝒜)
   ψ b i = ∣ from (AB i) ∣ (b (lift i))

   ψhom : is-hom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom =  ( λ r a x i → fst ∥ from (AB i) ∥ r (λ x₁ → a x₁ (lift i)) (x (lift i)))
           , λ f a → fiu (λ i → snd ∥ from (AB i) ∥ f λ x → a x (lift i))

   ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 {𝑨 = (⨅ ℬ)} ∣
   ϕ~ψ b = fizw λ i → to∼from (AB (lower i)) (b i)

   ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 {𝑨 = (⨅ 𝒜)} ∣
   ψ~ϕ a = fiu λ i → from∼to (AB i) (a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ~ψ ψ~ϕ

   Goal : Lift-Strucˡ γ (⨅ 𝒜) ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅ˡ) A≅B
\end{code}

--------------------------------

<span style="float:left;">[← Base.Structures.Homs](Base.Structures.Homs.html)</span>
<span style="float:right;">[Base.Structures.Terms →](Base.Structures.Terms.html)</span>

{% include UALib.Links.md %}
