---
layout: default
title : "Varieties.Func.HSP module (Agda Universal Algebra Library)"
date : "2021-10-16"
author: "agda-algebras development team"
---

#### <a id="the-hsp-theorem">The HSP Theorem</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.HSP {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type ) --  _⊔_ ; lsuc ); lzero to ℓ₀ )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
-- open import Function using ( id ; _∘_ )
open import Function.Bundles using ( Func )
open import Level
open import Relation.Binary  using ( Setoid ) -- ; Decidable ; _Preserves_⟶_ )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ ) -- ; Π )
open import Relations.Func.Discrete                 using ( fkerPred )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; 𝕌[_] ; Lift-Alg )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( hom ; mon ; IsMon ; IsHom ; epi→ontohom )
open import Homomorphisms.Func.Products     {𝑆 = 𝑆} using ( ⨅-hom-co )
open import Homomorphisms.Func.Factor       {𝑆 = 𝑆} using ( HomFactor )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( ℓ⨅≅⨅ℓ )
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; mon→≤ )
open import Subalgebras.Func.Properties     {𝑆 = 𝑆} using ( ≤-Lift )
open import Terms.Basic                     {𝑆 = 𝑆} using ( Term ; ℊ ; node )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( module Environment ; 𝑻 )
open import Terms.Func.Properties           {𝑆 = 𝑆} using ( free-lift ; lift-hom )
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( free-lift-interp )
open import Varieties.Func.SoundAndComplete {𝑆 = 𝑆} using ( module FreeAlgebra ; _⊢_▹_≈_ ; ModPred ; ThPred ; _⊫_ ; _≈̇_ )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( S ; V ; P ; Lift-class ; Lift-class-lemma
                                                          ; S-Lift-lemma ; S-idem )
open import Varieties.Func.Preservation     {𝑆 = 𝑆} using ( PS⊆SP ; S-id2 )
open import Varieties.Func.FreeAlgebras {𝑆 = 𝑆} using ( module FreeHom ; 𝔽-ModTh-epi-lift )

open Func using ( cong ) renaming ( f to _⟨$⟩_ )
open SetoidAlgebra using ( Domain )

private variable
 χ : Level


module _ {α : Level}{X : Type (α ⊔ χ)}(𝒦 : Pred (SetoidAlgebra α α) (ov α))
 where
 private
  oα = ov α
  oαχ = ov (α ⊔ χ)
  ooα = ov oα
  ooαχ = ov oαχ

 open FreeHom (α ⊔ χ) 𝒦
 open FreeAlgebra {ι = oαχ}{I = ℐ} ℰ using ( 𝔽[_] )

-- We want to pair each `(𝑨 , p)` in `ℑ` with an environment `ρ : X → ∣ 𝑨 ∣` so that we can quantify
-- over all algebras *and* all assignments of values in the domain `∣ 𝑨 ∣` to variables in `X`.

 ℑ⁺ : Type _
 ℑ⁺ = Σ[ 𝑨 ∈ (SetoidAlgebra α α) ] (𝑨 ∈ S 𝒦) × (Setoid.Carrier (Environment.Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → SetoidAlgebra α α
 𝔄⁺ i = ∣ i ∣

 ℭ : SetoidAlgebra (χ ⊔ oα) (χ ⊔ oα)
 ℭ = ⨅ 𝔄⁺

---------------------------------------------------------------------------

 module _ {i : ℑ⁺} where
  open Setoid (Domain ℭ) using () renaming ( _≈_ to _≈C≈_ ; trans to ctrans; sym to csym)
  open Environment ℭ using () renaming ( ⟦_⟧ to c⟦_⟧ ; Env to cEnv )

  open SetoidAlgebra (𝔄⁺ i) using ( Interp ) renaming ( Domain to A )
  open Setoid A using ( _≈_ ; refl ; sym ; trans )
  open Environment (𝔄⁺ i) using () renaming ( ⟦_⟧ to a⟦_⟧ )

  lemma0 : ∀ ρ s → a⟦_⟧{X = X} s ⟨$⟩ (λ x → ρ x i) ≈ (c⟦ s ⟧ ⟨$⟩ ρ) i
  lemma0 ρ (ℊ x) = refl
  lemma0 ρ (node f t) = goal
   where
   goal : a⟦ node f t ⟧ ⟨$⟩ (λ x → ρ x i) ≈ (c⟦ node f t ⟧ ⟨$⟩ ρ) i
   goal = cong Interp (≡.refl , (λ i₁ → lemma0 ρ (t i₁)))


  lemma1 : ∀ ρ → ∀ {p q} → (c⟦_⟧{X = X} p ⟨$⟩ ρ) ≈C≈ (c⟦ q ⟧ ⟨$⟩ ρ)
   →       a⟦ p ⟧ ⟨$⟩ (λ x → ρ x i) ≈ a⟦ q ⟧ ⟨$⟩ (λ x → ρ x i)
  lemma1 ρ {p} {q} pCq = trans (lemma0 ρ p) (trans (pCq i) (sym (lemma0 ρ q)))


  fl-lemma0 : ∀ ρ s → (free-lift{X = X}{𝑨 = 𝔄⁺ i} (λ x → ρ x i) s) ≈ (free-lift{𝑨 = ℭ} ρ s i)
  fl-lemma0 ρ (ℊ x) = refl
  fl-lemma0 ρ (node f t) = goal
   where
   goal : free-lift{X = X}{𝑨 = 𝔄⁺ i} (λ x → ρ x i) (node f t) ≈ free-lift{𝑨 = ℭ} ρ (node f t) i
   goal = cong Interp (≡.refl , (λ i₁ → fl-lemma0 ρ (t i₁)))


  skEqual : (p q : Term X) → Type α
  skEqual p q = a⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ a⟦ q ⟧ ⟨$⟩ snd ∥ i ∥

 AllEqual⊆ker𝔽 : {p q : Term X}
  →              (∀ i → skEqual{i = i} p q) → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 AllEqual⊆ker𝔽 {p} {q} x = Goal
  where
  open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )
  S𝒦⊫pq : S 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈F≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{p = p}{q} S𝒦⊫pq)


--------------------------------------------------------------------------

 ℓℭ : SetoidAlgebra oαχ oαχ
 ℓℭ = Lift-Alg ℭ oαχ oαχ

 PℓSℓℭ : ℓℭ ∈ P (S (Lift-class 𝒦))
 PℓSℓℭ = (Lift oαχ ℑ⁺) , ((λ x → Lift-Alg (𝔄⁺ (lower x)) oαχ oαχ) , (ξ , ℓ⨅≅⨅ℓ))
  where
  ξ : (i : Lift oαχ ℑ⁺) → Lift-Alg (𝔄⁺ (lower i)) oαχ oαχ ∈ S (Lift-class 𝒦)
  ξ i = S-Lift-lemma (Lift-class-lemma (fst ∥ lower i ∥))

 SPℓℭ : ℓℭ ∈ S (P (Lift-class 𝒦))
 SPℓℭ = PS⊆SP PℓSℓℭ

 open SetoidAlgebra ℭ using ( Interp ) renaming (Domain to C)
 open Setoid C using ( trans ; sym ; refl ) renaming ( Carrier to ∣C∣ ; _≈_ to _≈C≈_ )

 open Environment ℭ using () renaming (⟦_⟧ to c⟦_⟧ ; Env to cEnv)
 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)

 open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
 open Setoid F using () renaming (refl to reflF ; _≈_ to _≈F≈_ ; Carrier to ∣F∣)


 ker𝔽⊆kerℭ : fkerPred ∣ hom𝔽[ X ] ∣ ⊆ fkerPred ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈ₐ_ ; trans to transₐ ; sym to symₐ )
  open Environment 𝑨
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ₐ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t
  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ₐ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ₐ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = transₐ (symₐ (fl p)) (transₐ subgoal (fl q))


 hom𝔽ℭ : hom 𝔽[ X ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic ∣

 open Environment ℭ
 kerℭlemma : ∀{p q} → (p , q) ∈ fkerPred ∣ homℭ ∣ → ∀ τ → free-lift{𝑨 = ℭ} τ p ≈C≈ free-lift{𝑨 = ℭ} τ q
 kerℭlemma {p} {q} pKq τ (𝑨 , sA , ρ) = Goal
  where
  i : ℑ⁺
  i = (𝑨 , sA , ρ)
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈ₐ_ ; trans to transₐ ; sym to symₐ )
  open Environment 𝑨
  have : (free-lift{𝑨 = 𝑨} (λ x → τ x i) p) ≈ₐ (free-lift{𝑨 = 𝑨} (λ x → τ x i) q)
  have = pKq (𝑨 , sA , (λ x → τ x i))
  Goal : (free-lift{𝑨 = ℭ} τ p i) ≈ₐ (free-lift{𝑨 = ℭ} τ q i)
  Goal = transₐ (symₐ (fl-lemma0{i = i} τ p)) (transₐ have (fl-lemma0{i = i} τ q))


 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ fkerPred ∣ homℭ ∣ → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual{i = i} p q
  pqEqual i = goal
   where
   open Environment (𝔄⁺ i) using () renaming ( ⟦_⟧ to ⟦_⟧i )
   open Setoid (Domain (𝔄⁺ i)) using () renaming ( trans to transi ; sym to symi ; _≈_ to _≈ᵢ_ )
   goal : ⟦ p ⟧i ⟨$⟩ snd ∥ i ∥ ≈ᵢ ⟦ q ⟧i ⟨$⟩ snd ∥ i ∥
   goal = transi (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
                  (transi (pKq i)(symi (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))
  E⊢pq : ℰ ⊢ X ▹ p ≈ q
  E⊢pq = AllEqual⊆ker𝔽 pqEqual


 mon𝔽ℭ : mon 𝔽[ X ] ℭ
 mon𝔽ℭ = ∣ hom𝔽ℭ ∣ , isMon
  where
  open IsMon
  open Term
  open IsHom
  isMon : IsMon 𝔽[ X ] ℭ ∣ hom𝔽ℭ ∣
  isHom isMon = ∥ hom𝔽ℭ ∥
  isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq

 𝔽≤ℓℭ : 𝔽[ X ] ≤ (Lift-Alg ℭ oαχ oαχ)
 𝔽≤ℓℭ = ≤-Lift (mon→≤ mon𝔽ℭ)

 SP𝔽 : 𝔽[ X ] ∈ S (P (Lift-class 𝒦))
 SP𝔽 = S-idem (ℓℭ , SPℓℭ , 𝔽≤ℓℭ)

module _ {α : Level}(𝒦 : Pred (SetoidAlgebra α α) (ov α))
         (𝑨 : SetoidAlgebra α α) where
 private
  oα = ov α
  ooα = ov oα

 open FreeHom α 𝒦
 open FreeAlgebra {ι = oα}{I = ℐ} ℰ using ( 𝔽[_] )

 open SetoidAlgebra 𝑨 using( Interp ) renaming (Domain to A)
 open Setoid A using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )


 Birkhoff : 𝑨 ∈ ModPred{X = ∣A∣} (ThPred{X = ∣A∣} (V 𝒦))
  →         Lift-Alg 𝑨 oα oα ∈ V (Lift-class 𝒦)

 Birkhoff A∈ModThK = 𝔽[ ∣A∣ ] , SP𝔽{χ = α} 𝒦
                   , epi→ontohom 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 oα oα)
                        (𝔽-ModTh-epi-lift 𝑨 𝒦 (λ {p q} → A∈ModThK{p = p}{q}))

\end{code}

--------------------------------

<span style="float:left;">[← Varieties.Func.FreeAlgebras](Varieties.Func.FreeAlgebras.html)</span>
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}

