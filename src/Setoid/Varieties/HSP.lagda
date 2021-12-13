---
layout: default
title : "Setoid.Varieties.HSP module (Agda Universal Algebra Library)"
date : "2021-10-16"
author: "agda-algebras development team"
---

#### <a id="the-hsp-theorem">The HSP Theorem</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.HSP {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive    using ( lsuc )            renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax )  renaming ( proj₁ to fst ; proj₂ to snd ; _×_  to _∧_ )
open import Function.Bundles  using ()                  renaming ( Func to _⟶_ )
open import Level
open import Relation.Binary   using ( Setoid )
open import Relation.Unary    using ( Pred ; _∈_ ; _⊆_ )

-- -- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Base.Overture.Preliminaries                     using ( ∣_∣ ; ∥_∥ )
open import Setoid.Relations.Discrete                       using ( fkerPred )
open import Setoid.Algebras.Basic                   {𝑆 = 𝑆} using ( Algebra ; ov ; Lift-Alg )
open import Setoid.Algebras.Products                {𝑆 = 𝑆} using ( ⨅ )
open import Setoid.Homomorphisms.Basic              {𝑆 = 𝑆} using ( hom ; mon ; IsMon ; IsHom )
                                                            using ( epi ; epi→ontohom )
open import Setoid.Homomorphisms.Products           {𝑆 = 𝑆} using ( ⨅-hom-co )
open import Setoid.Homomorphisms.Factor             {𝑆 = 𝑆} using ( HomFactor )
open import Setoid.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} using ( ≅-refl )
open import Setoid.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} using ( _IsHomImageOf_ )
open import Setoid.Subalgebras.Subalgebras          {𝑆 = 𝑆} using ( _≤_ ; mon→≤ )
open import Setoid.Terms.Basic                      {𝑆 = 𝑆} using ( module Environment ; 𝑻 )
open import Setoid.Terms.Properties                 {𝑆 = 𝑆} using ( lift-hom ; free-lift )
open import Setoid.Terms.Operations                 {𝑆 = 𝑆} using ( free-lift-interp )
open import Setoid.Varieties.SoundAndComplete       {𝑆 = 𝑆} using ( module FreeAlgebra ; _⊫_ ; _≈̇_ )
                                                            using ( _⊢_▹_≈_ ; Mod ; Th )
open import Setoid.Varieties.Closure                {𝑆 = 𝑆} using ( S ; V ; P ; S-idem ; V-≅-lc )
open import Setoid.Varieties.Preservation           {𝑆 = 𝑆} using ( S-id2 ; PS⊆SP )
open import Setoid.Varieties.FreeAlgebras           {𝑆 = 𝑆} using ( module FreeHom ; 𝔽-ModTh-epi-lift )

open _⟶_          using () renaming ( f to _⟨$⟩_ )
open Setoid       using ( Carrier )
open Algebra      using ( Domain )
open Environment  using ( Env )

module _ {α ρᵃ ℓ : Level}
         (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
         {X : Type (α ⊔ ρᵃ ⊔ ℓ)} where

 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

\end{code}

We want to pair each `(𝑨 , p)` (where p : 𝑨 ∈ S 𝒦) with an environment
`ρ : X → ∣ 𝑨 ∣` so that we can quantify over all algebras *and* all
assignments of values in the domain `∣ 𝑨 ∣` to variables in `X`.

\begin{code}

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) ∧ (Carrier (Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → Algebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 ℭ : Algebra ι ι
 ℭ = ⨅ 𝔄⁺

\end{code}

Next we define a useful type, `skEqual`, which we use to represent a term identity `p ≈ q` for any
given `i = (𝑨 , sA , ρ)` (where `𝑨` is an algebra, `sA : 𝑨 ∈ S 𝒦` is a proof that `𝑨` belongs
to `S 𝒦`, and `ρ` is a mapping from `X` to the domain of `𝑨`). Then we prove `AllEqual⊆ker𝔽` which
asserts that if the identity `p ≈ q` holds in all `𝑨 ∈ S 𝒦` (for all environments), then `p ≈ q`
holds in the relatively free algebra `𝔽[ X ]`; equivalently, the pair `(p , q)` belongs to the
kernel of the natural homomorphism from `𝑻 X` onto `𝔽[ X ]`. We will use this fact below to prove
that there is a monomorphism from `𝔽[ X ]` into `ℭ`, and thus `𝔽[ X ]` is a subalgebra of ℭ,
so belongs to `S (P 𝒦)`.

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
  open Algebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )
  S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈F≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ}{p = p}{q} S𝒦⊫pq)

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)

 open Algebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
 open Setoid F using () renaming (refl to reflF ; _≈_ to _≈F≈_ ; Carrier to ∣F∣)


 ker𝔽⊆kerℭ : fkerPred ∣ hom𝔽[ X ] ∣ ⊆ fkerPred ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid (Domain 𝑨) using ( _≈_ ; sym ; trans )
  open Environment 𝑨 using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t
  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))


 hom𝔽ℭ : hom 𝔽[ X ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic ∣

 open Environment ℭ

 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ fkerPred ∣ homℭ ∣ → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄⁺ i) using () renaming ( ⟦_⟧ to ⟦_⟧ᵢ )
   open Setoid (Domain (𝔄⁺ i)) using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ᵢ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ᵢ ⟨$⟩ snd ∥ i ∥
   goal = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
                 (trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))
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
  PSℭ : ℭ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))

  SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
  SPℭ = PS⊆SP {ℓ = ℓ} PSℭ

  SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
  SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)

\end{code}

#### <a id="proof-of-the-hsp-theorem">Proof of the HSP theorem</a>

Finally, we are in a position to prove Birkhoff's celebrated variety theorem.

\begin{code}

module _ {α ρᵃ ℓ : Level}
         {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private
  ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

 Birkhoff : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Birkhoff 𝑨 ModThA = V-≅-lc{α}{ρᵃ}{ℓ} 𝒦 𝑨 VlA
  where
  open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )
  sp𝔽A : 𝔽[ ∣A∣ ] ∈ S{ι} ι (P ℓ ι 𝒦)
  sp𝔽A = SP𝔽{ℓ = ℓ} 𝒦

  epi𝔽lA : epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
  epi𝔽lA = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})

  lAimg𝔽A : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ ∣A∣ ]
  lAimg𝔽A = epi→ontohom 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι) epi𝔽lA

  VlA : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
  VlA = 𝔽[ ∣A∣ ] , sp𝔽A , lAimg𝔽A

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

\begin{code}

 module _ {𝑨 : Algebra α ρᵃ} where
  open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )

  Birkhoff-converse : 𝑨 ∈ V{α}{ρᵃ}{α}{ρᵃ}{α}{ρᵃ} ℓ ι 𝒦 → 𝑨 ∈ Mod{X = ∣A∣} (Th (V ℓ ι 𝒦))
  Birkhoff-converse vA pThq = pThq 𝑨 vA

\end{code}

We have thus proved that every variety is an equational class.

Readers familiar with the classical formulation of the Birkhoff HSP theorem as an
"if and only if" assertion might worry that the proof is still incomplete. However,
recall that in the [Setoid.Varieties.Preservation][] module we proved the following
identity preservation lemma:

`V-id1 : 𝒦 ⊫ p ≈̇ q → V 𝒦 ⊫ p ≈̇ q`

Thus, if `𝒦` is an equational class---that is, if 𝒦 is the class of algebras
satisfying all identities in some set---then `V 𝒦` ⊆ 𝒦`.  On the other hand, we
proved that `V` is expansive in the [Setoid.Varieties.Closure][] module:

`V-expa : 𝒦 ⊆ V 𝒦`

so `𝒦` (= `V 𝒦` = `HSP 𝒦`) is a variety.

Taken together, `V-id1` and `V-expa` constitute formal proof that every equational
class is a variety.

This completes the formal proof of Birkhoff's variety theorem.

--------------------------------

<span style="float:left;">[← Setoid.Varieties.FreeAlgebras](Setoid.Varieties.FreeAlgebras.html)</span>
<span style="float:right;">[Top ↑](index.html)</span>

{% include UALib.Links.md %}

