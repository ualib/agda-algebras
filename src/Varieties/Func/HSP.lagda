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
open import Agda.Primitive   using ( lsuc ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
                             renaming ( proj₁ to fst ; proj₂ to snd ; _×_  to _∧_ )
open import Function.Bundles using ( Func )
open import Level
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

-- -- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Relations.Func.Discrete                 using ( fkerPred )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; Lift-Alg )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( hom ; mon ; IsMon ; IsHom ; epi ; epi→ontohom )
open import Homomorphisms.Func.Products     {𝑆 = 𝑆} using ( ⨅-hom-co )
open import Homomorphisms.Func.Factor       {𝑆 = 𝑆} using ( HomFactor )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( ≅-refl )
open import Homomorphisms.Func.HomomorphicImages {𝑆 = 𝑆} using ( _IsHomImageOf_ )
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; mon→≤ )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( module Environment ; 𝑻 )
open import Terms.Func.Properties           {𝑆 = 𝑆} using ( lift-hom ; free-lift )
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( free-lift-interp )
open import Varieties.Func.SoundAndComplete {𝑆 = 𝑆} using ( module FreeAlgebra ; _⊫_ ; _≈̇_
                                                          ; _⊢_▹_≈_ ; Mod ; Th )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( S ; V ; P ; S-idem ; V-≅-lc )
open import Varieties.Func.Preservation     {𝑆 = 𝑆} using ( S-id2 ; PS⊆SP )
open import Varieties.Func.FreeAlgebras     {𝑆 = 𝑆} using ( module FreeHom ; 𝔽-ModTh-epi-lift )

open Func using ( cong ) renaming ( f to _⟨$⟩_ )
open SetoidAlgebra using ( Domain )

module _ {α ρᵃ ℓ : Level}
         (𝒦 : Pred(SetoidAlgebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
         {X : Type (α ⊔ ρᵃ ⊔ ℓ)} where

 private
  a = α ⊔ ρᵃ
  ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (a ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

-- We want to pair each `(𝑨 , p)` in `ℑ` with an environment `ρ : X → ∣ 𝑨 ∣` so that we can quantify
-- over all algebras *and* all assignments of values in the domain `∣ 𝑨 ∣` to variables in `X`.

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (SetoidAlgebra α ρᵃ) ] (𝑨 ∈ S{β = α}{ρᵃ}ℓ 𝒦) ∧ (Setoid.Carrier (Environment.Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → SetoidAlgebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 ℭ : SetoidAlgebra ι ι
 ℭ = ⨅ 𝔄⁺

\end{code}

Next we define a useful type, `skEqual`, which we use to represent a term identity `p ≈ q`
for any given `i = (𝑨 , sA , ρ)` (where `𝑨` is an algebra, `sA : 𝑨 ∈ S 𝒦` is a proof that
`𝑨` belongs to `S 𝒦`, and `ρ` is a mapping from `X` to the domain of `𝑨`). Then we prove
`AllEqual⊆ker𝔽` which asserts that if the identity `p ≈ q` holds in all `𝑨 ∈ S 𝒦` (for
all environments), then `p ≈ q` holds in the relatively free algebra `𝔽[ X ]`; equivalently,
the pair `(p , q)` belongs to the kernel of the natural homomorphism from `𝑻 X` onto `𝔽[ X ]`.
We will use this fact below to prove that there is a monomorphism from `𝔽[ X ]` into `ℭ`,
and thus `𝔽[ X ]` is a subalgebra of ℭ, so belongs to `S (P 𝒦)`.

\begin{code}

 skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where
  open Setoid (Domain (𝔄⁺ i)) using ( _≈_ )
  open Environment (𝔄⁺ i) using ( ⟦_⟧ )

 AllEqual⊆ker𝔽 : ∀ {p q}
  →              (∀ i → skEqual i {p}{q}) → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 AllEqual⊆ker𝔽 {p} {q} x = Goal
  where
  open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )
  S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈F≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ}{p = p}{q} S𝒦⊫pq)


--------------------------------------------------------------------------

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

 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ fkerPred ∣ homℭ ∣ → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual i {p}{q}
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
  open IsHom
  isMon : IsMon 𝔽[ X ] ℭ ∣ hom𝔽ℭ ∣
  isHom isMon = ∥ hom𝔽ℭ ∥
  isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq

\end{code}

Now that we have proved the existence of a monomorphism from `𝔽[ X ]` to `ℭ` we are in a position
to prove that `𝔽[ X ]` is a subalgebra of ℭ, so belongs to `S (P 𝒦)`.  In fact, we will show
that `𝔽[ X ]` is a subalgebra of the *lift* of `ℭ`, denoted `ℓℭ`.

\begin{code}

 𝔽≤ℭ : 𝔽[ X ] ≤ ℭ
 𝔽≤ℭ = mon→≤ mon𝔽ℭ

 SP𝔽 : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SP𝔽 = S-idem SSP𝔽
  where
  PSℭ : ℭ ∈ P (a ⊔ ℓ) ι (S ℓ 𝒦)
  PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))

  SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
  SPℭ = PS⊆SP {ℓ = ℓ} PSℭ

  SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
  SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)


module _ {α ρᵃ ℓ : Level}
         {𝒦 : Pred(SetoidAlgebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}
         {𝑨 : SetoidAlgebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} where

 private
  ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
 open Setoid (Domain 𝑨) using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )


 Birkhoff-lemma : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
  →               Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦

 Birkhoff-lemma A∈ModThK = 𝔽[ ∣A∣ ] , goal1 , goal2
  where
  goal1 : 𝔽[ ∣A∣ ] ∈ S{ι} ι (P ℓ ι 𝒦)
  goal1 = SP𝔽{ℓ = ℓ} 𝒦

  η : epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
  η = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → A∈ModThK{p = p}{q})

  goal2 : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ ∣A∣ ]
  goal2 = epi→ontohom 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι) η


 Birkhoff : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
  →         𝑨 ∈ V ℓ ι 𝒦

 Birkhoff A∈ModThK = V-≅-lc{α}{ρᵃ}{ℓ} 𝒦 𝑨 subgoal
  where
  subgoal : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
  subgoal = Birkhoff-lemma (λ {p q} → A∈ModThK{p = p}{q})


\end{code}

--------------------------------

<span style="float:left;">[← Varieties.Func.FreeAlgebras](Varieties.Func.FreeAlgebras.html)</span>
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}

