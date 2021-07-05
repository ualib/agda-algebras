---
layout: default
title : Homomorphisms.Setoid module (Agda Universal Algebra Library)
date : 2021-07-03
author: [agda-algebras development team][]
---

### Homomorphisms of Algebras over Setoids

This is the [Homomorphisms.Setoid][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality  using    ( _≡_    ;  refl     )
open import Agda.Primitive         using    ( _⊔_    ;  lsuc     )
                                   renaming ( Set    to Type     )
open import Data.Product           using    ( _,_    ;  Σ-syntax
                                            ; Σ      ;  _×_      )
                                   renaming ( proj₁  to  fst
                                            ; proj₂  to  snd     )
open import Function               using    ( _∘_    ;  id       )
open import Level                  using    ( Level  ;  Lift     )
open import Relation.Binary                       using    ( IsEquivalence  )
open import Relation.Unary                        using    ( _⊆_ )
import Relation.Binary.PropositionalEquality as PE

-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries     using ( ∣_∣ ; ∥_∥ ; _⁻¹ ; _≈_)
open import Overture.Inverses          using ( IsInjective ; IsSurjective )
open import Overture.Inverses          using ( SurjInv )
open import Relations.Discrete         using ( ker ; kernel )
open import Relations.Truncation       using ( is-set ; blk-uip ; is-embedding
                                             ; monic-is-embedding|Set )
open import Relations.Extensionality   using ( swelldef ; block-ext|uip ; pred-ext
                                             ; SurjInvIsRightInv ; epic-factor )
open import Algebras.Setoid   {𝑆 = 𝑆}  using ( 𝕌[_] ; SetoidAlgebra ; _̂_ ; Lift-SetoidAlg )
open import Congruences.Setoid {𝑆 = 𝑆} using ( _∣≈_ ; Con ; IsCongruence ; _╱_)
\end{code}

### Homomorphisms for setoid algebras

\begin{code}

module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
         where
 private
  A = 𝕌[ 𝑨 ] -- (𝕌 = forgetful functor)
  B = 𝕌[ 𝑩 ]

 compatible-op-map : ∣ 𝑆 ∣ → (A → B) → Type _
 compatible-op-map 𝑓 h = ∀ a → h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)

 -- The property of being a homomorphism.
 is-homomorphism : (A → B) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 is-homomorphism h = ∀ 𝑓  →  compatible-op-map 𝑓 h

 -- The type of homomorphisms from `𝑨` to `𝑩`.
 hom : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 hom = Σ (A → B) is-homomorphism

open PE.≡-Reasoning
open PE renaming (cong to ≡-cong)

module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)  -- (explicit 𝑨)
         {β ρᵇ : Level} {𝑩 : SetoidAlgebra β ρᵇ}  -- (implicit 𝑩)
         {γ ρᶜ : Level} (𝑪 : SetoidAlgebra γ ρᶜ)  -- (explicit 𝑪)
         where
 private
  A = 𝕌[ 𝑨 ]  -- carrier of domain of 𝑨
  B = 𝕌[ 𝑩 ]
  C = 𝕌[ 𝑪 ]

 -- The composition of homomorphisms is again a homomorphism.
 ∘-is-hom : {g : A → B}{h : B → C}
  →         is-homomorphism 𝑨 𝑩 g → is-homomorphism 𝑩 𝑪 h
            -------------------------------------------------
  →         is-homomorphism 𝑨 𝑪 (h ∘ g)

 ∘-is-hom {g} {h} ghom hhom 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a) ≡⟨ ≡-cong h ( ghom 𝑓 a ) ⟩
                                  h ((𝑓 ̂ 𝑩)(g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
                                  (𝑓 ̂ 𝑪)(h ∘ g ∘ a) ∎

 ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
 ∘-hom (g , ghom) (h , hhom) = h ∘ g , ∘-is-hom {g}{h} ghom hhom 


private variable
 α ρ : Level
 𝑨 : SetoidAlgebra α ρ

-- the identity homs
𝒾𝒹 : hom 𝑨 𝑨
𝒾𝒹 = id , λ 𝑓 a → refl

open Level
-- the lift hom
𝓁𝒾𝒻𝓉 : {β : Level} → hom 𝑨 (Lift-SetoidAlg 𝑨 β)
𝓁𝒾𝒻𝓉 = lift , (λ 𝑓 a → refl)

-- the lower hom
𝓁ℴ𝓌ℯ𝓇 : {β : Level} → hom (Lift-SetoidAlg 𝑨 β) 𝑨
𝓁ℴ𝓌ℯ𝓇 = (lower , λ 𝑓 a → refl)

module LiftSetoidHom {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
                     (ℓᵃ : Level)
                     {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
                     (ℓᵇ : Level)
                     where
 open Level

 Lift-hom : hom 𝑨 𝑩  →  hom (Lift-SetoidAlg 𝑨 ℓᵃ) (Lift-SetoidAlg 𝑩 ℓᵇ)

 Lift-hom (f , fhom) = lift ∘ f ∘ lower , Goal
  where
  lA lB : SetoidAlgebra _ _
  lA = Lift-SetoidAlg 𝑨 ℓᵃ
  lB = Lift-SetoidAlg 𝑩 ℓᵇ

  lABh : is-homomorphism lA 𝑩 (f ∘ lower)
  lABh = ∘-is-hom lA {𝑩 = 𝑨}  𝑩 {lower}{f} (λ _ _ → refl) fhom

  Goal : is-homomorphism lA lB (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom lA {𝑩 = 𝑩} lB {f ∘ lower}{lift} lABh λ _ _ → refl


-- Monomorphisms and epimorphisms
module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
         where

 private
  A = 𝕌[ 𝑨 ]  -- carrier of domain of 𝑨
  B = 𝕌[ 𝑩 ]

 is-monomorphism : (A → B) → Type _
 is-monomorphism g = is-homomorphism 𝑨 𝑩 g × IsInjective g

 is-epimorphism : (A → B) → Type _
 is-epimorphism g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

record mon {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
           {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β) where
 field
  map : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
  is-mon : is-monomorphism 𝑨 𝑩 map

 mon-to-hom : mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom _ = map , ∣ is-mon ∣


record epi {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
           {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β) where
 field
  map : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
  is-epi : is-epimorphism 𝑨 𝑩 map

 epi-to-hom : epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom _ = map , ∣ is-epi ∣


\end{code}



#### Kernels of homomorphisms for SetoidAlgebras

\begin{code}


module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
         where
 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]


 homker-comp : swelldef 𝓥 β → (h : hom 𝑨 𝑩) → 𝑨 ∣≈ (ker ∣ h ∣)
 homker-comp wd h f {u}{v} kuv = ∣ h ∣((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
                                 (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
                                 (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
                                 ∣ h ∣((f ̂ 𝑨) v)   ∎

-- NOT WORKING YET
--  kercon : swelldef 𝓥 β → hom 𝑨 𝑩 → Con 𝑨 -- {α}{β}
--  kercon wd h = ker ∣ h ∣ , {!!} -- mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

--  kerquo : swelldef 𝓥 β → hom 𝑨 𝑩 → SetoidAlgebra _ _ -- (α ⊔ lsuc β) _
--  kerquo wd h = 𝑨 ╱ (kercon wd h)


-- ker[_⇒_]_↾_ : {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
--               {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
--  →            hom 𝑨 𝑩 → swelldef 𝓥 β → SetoidAlgebra _ _ --  (α ⊔ lsuc β) _
-- ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo 𝑨 𝑩 wd h

\end{code}






#### Homomorphism Decomposition for SetoidAlgebras


If `τ : hom 𝑨 𝑩`, `ν : hom 𝑨 𝑪`, `ν` is surjective, and `ker ν ⊆ ker τ`, then there exists `φ : hom 𝑪 𝑩` such that `τ = φ ∘ ν` so the following diagram commutes:

```
𝑨 --- ν ->> 𝑪
 \         .
  \       .
   τ     φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {α ρᵃ : Level} {𝑨 : SetoidAlgebra α ρᵃ}
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
         {γ ρᶜ : Level} {𝑪 : SetoidAlgebra γ ρᶜ} where

 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]
  C = 𝕌[ 𝑪 ]

 open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)

 HomFactor : swelldef 𝓥 γ
  →          (τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
             --------------------------------------------------
  →          Σ[ φ ∈ (hom 𝑪 𝑩)] (∣ τ ∣ ≈ ∣ φ ∣ ∘ ∣ ν ∣)

 HomFactor wd τ ν Kντ νE = (φ , φIsHomCB)  , τφν
  where
  νInv : C → A
  νInv = SurjInv ∣ ν ∣ νE

  η : ∀ c → c ≡ ∣ ν ∣ (νInv c)
  η c = sym (SurjInvIsRightInv ∣ ν ∣ νE c)

  φ : C → B
  φ = ∣ τ ∣ ∘ νInv

  ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
  ξ a = η (∣ ν ∣ a)

  τφν : ∣ τ ∣ ≈ φ ∘ ∣ ν ∣
  τφν x = Kντ (ξ x)

  φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
  φIsHomCB 𝑓 c =
   φ ((𝑓 ̂ 𝑪) c)                    ≡⟨ ≡-cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) λ i → η ((c i)))⟩
   φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ ≡-cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
   φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ sym (τφν ((𝑓 ̂ 𝑨)(νInv ∘ c))) ⟩
   ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
   (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}

If, in addition to the hypotheses of the last theorem, we assume τ is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext β β`.)

\begin{code}

 open epi
 HomFactorEpi : swelldef 𝓥 γ
  →             (τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
  →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                ---------------------------------------------
  →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ τ ∣ ≈ (φ .map) ∘ ∣ ν ∣

 HomFactorEpi wd τ ν kerincl νe τe = record { map = fst ∣ φF ∣
                                            ; is-epi = (snd ∣ φF ∣) , φE
                                            } , ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ τ ∣ ≈ ∣ φ ∣ ∘ ∣ ν ∣
   φF = HomFactor wd τ ν kerincl νe

   φ : C → B
   φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

   φE : IsSurjective φ
   φE = epic-factor  ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

\end{code}

--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

