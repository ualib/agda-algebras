n---
layout: default
title : "Varieties.Func.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### <a id="free-setoid-algebras">Free setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ) -- ; lzero to ℓ₀ )
open import Data.Product     using ( _,_ ; Σ-syntax ) renaming ( proj₂ to snd )  -- ; _×_ ) 
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid ; Decidable )
open import Relation.Unary   using ( Pred ; _⊆_ ; _∈_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                   using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries              using ( _⟶_ )
open import Overture.Inverses                   using () renaming ( Image_∋_ to img_∋_ )
open import Overture.Func.Inverses                   using ( Image_∋_ ) -- ; eq )
open import Overture.Surjective                 using ( proj ; projIsOnto ) renaming ( IsSurjective to onto ) --  update ; ; projIsOnto )
open import Overture.Func.Surjective                 using ( IsSurjective )
open import Algebras.Func.Basic              {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; 𝕌[_] ; Lift-Alg )
open import Algebras.Func.Products           {𝑆 = 𝑆} using ( 𝔄 ; ℑ ; ⨅ )
open import Homomorphisms.Func.Basic         {𝑆 = 𝑆} using ( hom ; epi ; IsEpi ; IsHom ; epi-to-hom )
open import Homomorphisms.Func.Products      {𝑆 = 𝑆} using ( ⨅-hom-co )
open import Homomorphisms.Func.Kernels       {𝑆 = 𝑆} using ( kerquo )
open import Homomorphisms.Func.Isomorphisms  {𝑆 = 𝑆} using ( ⨅≅ ; ≅-sym ; Lift-≅ )
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; FirstHomCorollary )
open import Subalgebras.Func.Properties      {𝑆 = 𝑆} using ( Lift-≤-Lift )
open import Terms.Basic                      {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic                 {𝑆 = 𝑆} using ( 𝑻 ; _≐_ )
open import Terms.Func.Properties    {𝑆 = 𝑆} using ( lift-hom )
open import Varieties.Func.EquationalLogic  {𝑆 = 𝑆}  using ( _⊫_≈_ )
open import Varieties.Func.SoundAndComplete {𝑆 = 𝑆}  using ( module FreeAlgebra ; Eq ; Mod ; Th )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( S ; P ; V )

module _ {α : Level} {𝒦 : Pred (SetoidAlgebra α α) (ov α) }
         {𝔄I : ∀ i → 𝕌[ 𝔄{𝒦 = 𝒦} i ] }  -- assume all algebras in 𝒦 are nonempty
         {_≟_ : Decidable{A = ℑ{𝒦 = 𝒦}} _≡_}
         where

 -- X is the "arbitrary" collection of variables; it suffices to take X to be the
 -- cardinality of the largest algebra in 𝒦, but since we don't have the luxury of
 -- knowing that cardinality, we simply let X be the product of all algebras in 𝒦.
 open SetoidAlgebra using (Domain)
 open Setoid using (Carrier)
 open img_∋_
 open Eq

 𝕏 : Type (ov α)
 𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = 𝒦})) )
 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type (ov (ov α))
 ℐ = Σ[ eq ∈ Eq{ov α} ] 𝒦 ⊫ (lhs eq) ≈ (rhs eq)
 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 hsurj : {𝑨 : SetoidAlgebra α α} → 𝑨 ∈ 𝒦 → Σ[ h ∈ (𝕏 → 𝕌[ 𝑨 ]) ] onto h
 hsurj {𝑨 = 𝑨} KA = proj _≟_ 𝔄I (𝑨 , KA) , projIsOnto _≟_ 𝔄I

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

\begin{code}
 open _≐_
 open FreeAlgebra {X = 𝕏}{ι = ov(ov α)}{I = ℐ} ℰ

 open SetoidAlgebra 𝔽[ 𝕏 ] using ( Interp ) renaming ( Domain to FF )
 open Setoid FF using ( _≈_ ; reflexive ) renaming ( refl to reflF ; Carrier to F )
 -- open Environment 𝔽[ 𝕏 ]
 -- open Setoid (Env 𝕏) using () renaming ( Carrier to 𝕏→F )
 -- open Environment (𝑻 𝕏)
 -- open Setoid (Env 𝕏) using () renaming ( Carrier to 𝕏⇒T )
 open Setoid using (Carrier)
 open SetoidAlgebra (𝑻 𝕏) using () renaming (Domain to 𝕋)
 open Setoid 𝕋 using () renaming ( _≈_ to _≃_ ; refl to reflT )
 open Func using ( cong ) renaming ( f to _⟨$⟩_ )
 open Term

\end{code}

We begin by constructing `ℭ`, using the techniques described in the section on <a href="https://ualib.gitlab.io/Varieties.Varieties.html#products-of-classes">products of classes</a>.

\begin{code}

  -- ℭ is the product of all subalgebras of algebras in 𝒦.
 ℭ : SetoidAlgebra (ov α)(ov α)
 ℭ = ⨅ (𝔄{ρ = α}{𝒦 = 𝒦})

\end{code}

Observe that the inhabitants of `ℭ` are maps from `ℑ` to `{𝔄 i : i ∈ ℑ}`.  A homomorphism from `𝑻 𝕏` to `ℭ` is obtained as follows.

\begin{code}
 homℭ : hom (𝑻 𝕏) ℭ
 homℭ = ⨅-hom-co 𝔄 h
  where
  h : ∀ i → hom (𝑻 𝕏) (𝔄 i)
  h i = lift-hom ∣ hsurj ∥ i ∥ ∣

 epi𝔽 : epi (𝑻 𝕏) 𝔽[ 𝕏 ]
 epi𝔽 = h , hepi
  where
  c : ∀ {x y} → x ≃ y → x ≈ y
  c (_≐_.refl {x} {y} ≡.refl) = reflF
  c (genl {f}{s}{t} x) = cong Interp (≡.refl , (λ i → c (x i)))

  h : 𝕋 ⟶ FF
  h ⟨$⟩ t = t
  cong h = c

  open IsEpi
  open IsHom
  hepi : IsEpi (𝑻 𝕏) 𝔽[ 𝕏 ] h
  compatible (isHom hepi) {f}{a} = cong Interp (≡.refl , (λ i → reflF))
  preserves≈ (isHom hepi) = c
  isSurjective hepi {y} = Image_∋_.eq y reflF


 hom𝔽 : hom (𝑻 𝕏) 𝔽[ 𝕏 ]
 hom𝔽 = epi-to-hom (𝑻 𝕏) 𝔽[ 𝕏 ] epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = IsEpi.isSurjective (snd (epi𝔽))



 open V
 open S
 open P

 𝔽≤ℭ : (kerquo homℭ) ≤ ℭ
 𝔽≤ℭ = FirstHomCorollary homℭ

 ℓ : Level
 ℓ = (ov (𝓞 ⊔ 𝓥 ⊔ ov α))

 ℓℭ : SetoidAlgebra ℓ ℓ
 ℓℭ = Lift-Alg ℭ ℓ ℓ

 𝔽 : SetoidAlgebra ℓ (ov α)
 𝔽 = kerquo homℭ

 -- 𝕏↠_[_] : (𝑨 : SetoidAlgebra (ov α)(ov α)) → 𝑨 ∈ Mod' (Th'{X = 𝕏}(V{α}{ov α} 𝒦))
 --  →       Σ[ h ∈ (𝕏 → 𝕌[ 𝑨 ]) ] onto h
 -- 𝕏↠ 𝑨 [ A∈ModK ] = {!!}

 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra (ov α) (ov α)) → 𝑨 ∈ Mod' (Th'{X = X}(V{α}{ov α} 𝒦)) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = goal
 --  where
 --  η : X → 𝕌[ 𝑨 ]
 --  η = {!!}
 --  φ = lift-hom{𝑨 = 𝑨} η
 --  φE : IsSurjective ∣ φ ∣
 --  φE = {!!} -- lift-of-epi-is-epi ? -- ηE
 --  -- pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
 --  -- pqlem2 p q z = λ x → AinMTV p q (kernel-in-theory z) x

 --  -- kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ φ ∣
 --  -- kerincl {p , q} x = ∣ φ ∣ p      ≡⟨ (free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η p)⁻¹ ⟩
 --  --                     (𝑨 ⟦ p ⟧) η  ≡⟨ pqlem2 p q x η ⟩
 --  --                     (𝑨 ⟦ q ⟧) η  ≡⟨ free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η q ⟩
 --  --                     ∣ φ ∣ q      ∎
 --  goal : epi 𝔽 𝑨
 --  goal = {!!} -- ∣ HomFactorEpi 𝑨 φ hom𝔽 kerincl hom𝔽-is-epic φE)

 ℓ𝔽 : SetoidAlgebra ℓ ℓ
 ℓ𝔽 = Lift-Alg 𝔽 ℓ ℓ

 Pℭ : ℭ ∈ P{α}{ov α} 𝒦
 Pℭ = piso (pprod ((λ i → pbase ∥ i ∥))) (⨅≅ (λ i → ≅-sym Lift-≅))

 SPℭ : ℭ ∈ S{ov α}{ov α} (P 𝒦)
 SPℭ = siso (sbase Pℭ) (≅-sym Lift-≅)

 SPℓℭ : ℓℭ ∈ S{ov α}{ℓ} (P 𝒦)
 SPℓℭ = sbase Pℭ

 ℓ𝔽∈SP : ℓ𝔽 ∈ S{ov α}{ℓ} (P{α}{ov α} 𝒦)
 ℓ𝔽∈SP = Goal
  where
  ℓ𝔽≤ℓC : ℓ𝔽 ≤ ℓℭ
  ℓ𝔽≤ℓC = Lift-≤-Lift 𝔽≤ℭ

  Goal : ℓ𝔽 ∈ S (P 𝒦)
  Goal = ssub SPℓℭ ℓ𝔽≤ℓC

 -- SP⊆V : (S{ov α}{ℓ} (P 𝒦)) ⊆ V 𝒦
 -- SP⊆V (sbase{𝑨} x) = {!!}
 -- SP⊆V (ssub x y) = vssub (SP⊆V x) y
 -- SP⊆V (siso x y) = viso (SP⊆V x) y

 -- ℓ𝔽∈V : ℓ𝔽 ∈ V 𝒦
 -- ℓ𝔽∈V = SP⊆V ℓ𝔽∈SP

\end{code}


#### The HSP Theorem
Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove Birkhoff's HSP theorem. (Note that since the proof enlists
the help of the `𝔽-ModTh-epi` theorem, we must assume an environment exists,
which is manifested in the premise `∀ 𝑨 → X ↠ 𝑨`.

\begin{code}

 -- Birkhoff : Mod{X = X}{𝒦 = 𝒦} (Th{α = ov α} (V{α}{ℓ} 𝒦)) ⊆ V{α}{ℓ} 𝒦
 -- Birkhoff {𝑨} AMod = vhimg {!ℓ𝔽∈V!} {!!} -- vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi-to-hom 𝑨 φE , snd ∥ φE ∥)
 --   where
 --   φE : epi 𝔽 𝑨
 --   φE = 𝔽-ModTh-epi 𝑨 AMod

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

begin{code}

 -- Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
 -- Birkhoff-converse α p q pThq = pThq α

\end{code}

To be continued...

(TODO: complete this module)


--------------------------------

<span style="float:left;">[← Varieties.Func.Closure](Varieties.Func.Closure.html)</span>
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}














<!-- 



 -- 𝔽∈SP : (Lift-Alg 𝔽[ X ] (ov (ov (α ⊔ ρ)))) ∈ (S{ov (α ⊔ ρ)}{ov (α ⊔ ρ)} (P{α}{ov (α ⊔ ρ)} 𝒦))
 -- 𝔽∈SP = {!!} -- ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

 -- 𝕍𝒦 : Pred (SetoidAlgebra _ _) _
 -- 𝕍𝒦 = V 𝒦
 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra _ _) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = ?
\end{code}

#### The HSP Theorem
Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove Birkhoff's HSP theorem. (Note that since the proof enlists
the help of the `𝔽-ModTh-epi` theorem, we must assume an environment exists,
which is manifested in the premise `∀ 𝑨 → X ↠ 𝑨`.

begin{code}

 -- Birkhoff : Mod (Th (V 𝒦)) ⊆ V 𝒦
 -- Birkhoff {𝑨} AMod = vhimg {!!} {!!} -- vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi-to-hom 𝑨 φE , snd ∥ φE ∥)
   -- where
   -- φE : epi 𝔽 𝑨
   -- φE = 𝔽-ModTh-epi 𝑨 (𝕏 𝑨) α

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

begin{code}

 -- Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
 -- Birkhoff-converse α p q pThq = pThq α

\end{code}

We have thus proved that every variety is an equational class.  Readers familiar
with the classical formulation of the Birkhoff HSP theorem, as an "if and only
if" result, might worry that we haven't completed the proof.  But recall that
in the [Varieties.Preservation][] module we proved the following identity
preservation lemmas:

* `𝒦 ⊫ p ≈ q → H 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → S 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → P 𝒦 ⊫ p ≈ q`

From these it follows that every equational class is a variety. Thus, our formal
proof of Birkhoff's theorem is complete.







 -- recall, 𝔽[ X ] : SetoidAlgebra (ov α) (ov α)
 -- 𝔽∈SP : 𝔽[ X ] ∈ S{ov(ov α)}{ov(ov α)} (P{α}{ov(ov α)} 𝒦)
 -- 𝔽∈SP = ssub {!SPℭ!} {!!}
 𝔽[X]∈SP : 𝔽[ X ] ∈ S (P 𝒦)
 𝔽[X]∈SP = Goal -- ssub {!SPℭ!} {!!}
  where
  lC : SetoidAlgebra _ _
  lC = Lift-Alg ℭ (ov α) (ov α)
  SPlC : lC ∈ S (P 𝒦)
  SPlC = sk→lsk SPℭ
   -- A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
  C≤lC : ℭ ≤ lC
  C≤lC = {!!}
  𝔽≤lC : 𝔽[ X ] ≤ lC
  𝔽≤lC = ≤-trans 𝔽[ X ]{𝑩 = ℭ} lC {!𝔽≤ℭ!} C≤lC -- A≤B×B≅C→A≤C {!𝔽≤ℭ!} {!!}
  Goal : 𝔽[ X ] ∈ S (P 𝒦)
  Goal = ssub {!SPℭ!} {!!}

 𝔽[X]∈V : 𝔽[ X ] ∈ V 𝒦
 𝔽[X]∈V = {!!}




-->
