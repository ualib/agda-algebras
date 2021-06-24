---
layout: default
title : Varieties.Preservation (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

### <a id="Equation preservation">Equation preservation</a>

This section presents the [Varieties.Preservation][] module of the [Agda Universal Algebra Library][]. In this module we show that identities are preserved by closure operators H, S, and P.  This will establish the easy direction of Birkhoff's HSP Theorem.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level renaming ( suc to lsuc )
open import Algebras.Basic

module Varieties.Preservation {α : Level} {𝑆 : Signature 𝓞 𝓥} where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Data.Sum.Base           using    ( _⊎_ )
open import Function.Base           using    ( _∘_ )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ｛_｝ ; _∪_ )



-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries             using ( _⁻¹ ; ∣_∣ ; ∥_∥ ; 𝑖𝑑 )
open import Overture.Inverses                  using ( Inv ; InvIsInv )
open import Relations.Extensionality           using (DFunExt; SwellDef)
open import Algebras.Products          {𝑆 = 𝑆} using (ov)
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using (_≅_; ≅-refl)
open import Terms.Basic                {𝑆 = 𝑆} using (Term ; 𝑻 ; lift-hom)
open import Terms.Operations           {𝑆 = 𝑆} using (_⟦_⟧; comm-hom-term)
open import Subalgebras.Subalgebras         using    ( SubalgebraOfClass )
 
open import Varieties.Basic            {𝑆 = 𝑆} using ( _⊫_≈_ ; _⊧_≈_ ; ⊧-Lift-invar
                                                     ; ⊧-lower-invar ; ⊧-S-class-invar
                                                     ; ⊧-I-invar ; ⊧-P-lift-invar
                                                     ; ⊧-P-invar ; ⊧-S-invar ; Th)

open import Varieties.EquationalLogic {𝑆 = 𝑆} using (H; S; P; V)

private variable β γ 𝓧 : Level

open H
open S
open P
open V
open Term
open _⊎_

𝓕 𝓕⁺ : Level
𝓕 = ov α
𝓕⁺ = lsuc (ov α)    -- (this will be the level of the relatively free algebra)

\end{code}



#### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator H is compatible with identities that hold in the given class.

\begin{code}

open ≡-Reasoning

module _ (wd : SwellDef){X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 H-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → H{β = α} 𝒦 ⊫ p ≈ q
 H-id1 p q σ (hbase x) = ⊧-Lift-invar wd p q (σ x)
 H-id1 p q σ (hhimg{𝑨}{𝑪} HA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = (H-id1 p q σ) HA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInv φ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd 𝓧 α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
      (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
      φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
      φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
      (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd 𝓧 α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
      (𝑩 ⟦ q ⟧) b          ∎

\end{code}

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

\begin{code}

 H-id2 : ∀ {β} → (p q : Term X) → H{β = β} 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q

 H-id2 p q Hpq KA = ⊧-lower-invar wd p q (Hpq (hbase KA))

\end{code}


#### <a id="s-preserves-identities">S preserves identities</a>

\begin{code}

 S-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → S{β = α} 𝒦 ⊫ p ≈ q

 S-id1 p q σ (sbase x) = ⊧-Lift-invar wd p q (σ x)
 S-id1 p q σ (slift x) = ⊧-Lift-invar wd p q ((S-id1 p q σ) x)

 S-id1 p q σ (ssub{𝑨}{𝑩} sA B≤A) = ⊧-S-class-invar wd p q goal ν
  where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
  τ : 𝑨 ⊧ p ≈ q
  τ = S-id1 p q σ sA

  Apq : ｛ 𝑨 ｝ ⊫ p ≈ q
  Apq refl = τ

  goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊫ p ≈ q
  goal {𝑩} (inj₁ x) = σ x
  goal {𝑩} (inj₂ y) = Apq y

  ν : SubalgebraOfClass (λ z → (𝒦 ∪ ｛ 𝑨 ｝) (Data.Product.proj₁ z , Data.Product.proj₂ z))
  ν = (𝑩 , 𝑨 , (𝑩 , B≤A) , _⊎_.inj₂ refl , ≅-refl)

 S-id1 p q σ (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar wd 𝑩 p q (S-id1 p q σ x) x₁

\end{code}

Again, the obvious converse is barely worth the bits needed to formalize it.

\begin{code}

 S-id2 : ∀{β}(p q : Term X) → S{β = β}𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q

 S-id2 p q Spq {𝑨} KA = ⊧-lower-invar wd p q (Spq (sbase KA))

\end{code}





#### <a id="p-preserves-identities">P preserves identities</a>

\begin{code}

module _ (fe : DFunExt) (wd : SwellDef){X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 P-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → P{β = α} 𝒦 ⊫ p ≈ q

 P-id1 p q σ (pbase x) = ⊧-Lift-invar wd p q (σ x)
 P-id1 p q σ (pliftu x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)
 P-id1 p q σ (pliftw x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)

 P-id1 p q σ (produ{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
  where
  IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
  IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (prodw{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
  where
  IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
  IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (pisow{𝑨}{𝑩} x y) = ⊧-I-invar wd 𝑩 p q (P-id1 p q σ x) y

\end{code}

...and conversely...

\begin{code}

module _  (wd : SwellDef){X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 P-id2 : ∀ {β}(p q : Term X) → P{β = β} 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 P-id2 p q PKpq KA = ⊧-lower-invar wd p q (PKpq (pbase KA))

\end{code}


#### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

module Vid (fe : DFunExt)(wd : SwellDef){𝓧 : Level} {X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 V-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → V{β = α} 𝒦 ⊫ p ≈ q
 V-id1 p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
 V-id1 p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
 V-id1 p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)

 V-id1 p q σ (vhimg{𝑨}{𝑪}VA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1 p q σ VA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInv φ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd 𝓧 α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
      (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
      φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
      φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
      (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd 𝓧 α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
      (𝑩 ⟦ q ⟧) b          ∎

 V-id1 p q σ ( vssubw {𝑨}{𝑩} VA B≤A ) =
  ⊧-S-class-invar wd p q goal (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q σ VA

   Asinglepq : ｛ 𝑨 ｝ ⊫ p ≈ q
   Asinglepq refl = IH

   goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊫ p ≈ q
   goal {𝑩} (inj₁ x) = σ x
   goal {𝑩} (inj₂ y) = Asinglepq y

 V-id1 p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1 p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B

module Vid' (fe : DFunExt)(wd : SwellDef){𝓧 : Level} {X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 open Vid fe wd {𝓧}{X}{𝒦} public
 V-id1' : (p q : Term X) → 𝒦 ⊫ p ≈ q → V{β = β} 𝒦 ⊫ p ≈ q
 V-id1' p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
 V-id1' p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
 V-id1' p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1' p q σ) x)
 V-id1' p q σ (vhimg{𝑨}{𝑪} VA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1' p q σ VA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInv φ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd 𝓧 _ (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
      (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) p preim)⁻¹ ⟩
      φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
      φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) q preim ⟩
      (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd 𝓧 _ (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
      (𝑩 ⟦ q ⟧) b          ∎

 V-id1' p q σ (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar wd 𝑩 {p}{q}(V-id1' p q σ VA) B≤A
 V-id1' p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1' p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1' p q σ (V𝒜 i)
 V-id1' p q σ (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1' p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1' p q σ VA)A≅B

\end{code}


#### <a id="class-identities">Class identities</a>

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities modeled by `𝒦`.   We formalize this observation as follows.

\begin{code}

module _ (fe : DFunExt)(wd : SwellDef){𝓧 : Level} {X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 ovu lovu : Level
 ovu = ov α
 lovu = lsuc (ov α)
 𝕍 : Pred (Algebra lovu 𝑆) (lsuc lovu)
 𝕍 = V{α}{lovu} 𝒦
 𝒱 : Pred (Algebra ovu 𝑆) lovu
 𝒱 = V{β = ovu} 𝒦

 open Vid' fe wd {𝓧}{X}{𝒦} public
 class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊫ p ≈ q  →  (p , q) ∈ Th 𝒱
 class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA

 class-ids : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊫ p ≈ q  →  (p , q) ∈ Th 𝕍
 class-ids p q pKq VCloA = V-id1' p q pKq VCloA


 class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊫ p ≈ q
 class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar wd p q (Thpq (vbase KA))


\end{code}


Once again, and for the last time, completeness dictates that we formalize the coverse of `V-id1`, however obvious it may be.

\begin{code}

module _ (wd : SwellDef){X : Type 𝓧}{𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 V-id2 : (p q : Term X) → (V{β = β} 𝒦 ⊫ p ≈ q) → (𝒦 ⊫ p ≈ q)
 V-id2 p q Vpq {𝑨} KA = ⊧-lower-invar wd p q (Vpq (vbase KA))

\end{code}


----------------------------

[← Varieties.Varieties](Varieties.Varieties.html)
<span style="float:right;">[FreeAlgebras →](Varieties.FreeAlgebras.html)</span>

{% include UALib.Links.md %}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team








