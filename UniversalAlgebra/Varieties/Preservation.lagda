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

module Varieties.Preservation {α 𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where


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
open import Overture.Preliminaries       using ( _⁻¹ ; ∣_∣ ; ∥_∥ ; 𝑖𝑑 )
open import Overture.Inverses            using ( Inv ; InvIsInv )
open import Algebras.Products          𝑆 using (ov)
open import Homomorphisms.Isomorphisms 𝑆 using (_≅_; ≅-refl)
open import Terms.Basic                𝑆 using (Term ; 𝑻 ; lift-hom)
open import Terms.Operations           𝑆 using (_⟦_⟧; comm-hom-term)
open import Varieties.Basic            𝑆 using ( _⊧_≋_ ; _⊧_≈_ ; ⊧-Lift-invar
                                               ; ⊧-lower-invar ; ⊧-S-class-invar
                                               ; ⊧-I-invar ; ⊧-P-lift-invar
                                               ; ⊧-P-invar ; ⊧-S-invar ; Th)

open import Varieties.EquationalLogic 𝑆 using (H; S; P; V)

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

module _ {fe : (∀ a b → funext a b)}{X : Type 𝓧} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 open ≡-Reasoning

 H-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → H{β = α} 𝒦 ⊧ p ≋ q
 H-id1 p q σ (hbase x) = ⊧-Lift-invar fe p q (σ x)

 H-id1 p q σ (hhimg{𝑨}{𝑪} HA (𝑩 , ((φ , φhom) , φE))) = Goal
  where
  ν : 𝑨 ⊧ p ≈ q
  ν = (H-id1 p q σ) HA

  preim : ∀ 𝒃 x → ∣ 𝑨 ∣
  preim 𝒃 x = Inv φ (φE (𝒃 x))

  ζ : ∀ 𝒃 → φ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = (fe 𝓧 α) λ x → InvIsInv φ (φE (𝒃 x))

  Goal : 𝑩 ⟦ p ⟧  ≡ 𝑩 ⟦ q ⟧
  Goal = (fe (α ⊔ 𝓧) α) λ 𝒃
   →  (𝑩 ⟦ p ⟧) 𝒃             ≡⟨ (cong (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
      (𝑩 ⟦ p ⟧)(φ ∘(preim 𝒃)) ≡⟨(comm-hom-term (fe 𝓥 α) 𝑩(φ , φhom) p(preim 𝒃))⁻¹ ⟩
      φ((𝑨 ⟦ p ⟧)(preim 𝒃))   ≡⟨ cong φ (cong-app ν (preim 𝒃)) ⟩
      φ((𝑨 ⟦ q ⟧)(preim 𝒃))   ≡⟨ comm-hom-term (fe 𝓥 α) 𝑩 (φ , φhom) q (preim 𝒃) ⟩
      (𝑩 ⟦ q ⟧)(φ ∘(preim 𝒃)) ≡⟨ cong (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
      (𝑩 ⟦ q ⟧) 𝒃             ∎

\end{code}

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

\begin{code}

 H-id2 : ∀ {β} → (p q : Term X) → H{β = β} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

 H-id2 p q Hpq KA = ⊧-lower-invar fe p q (Hpq (hbase KA))

\end{code}


#### <a id="s-preserves-identities">S preserves identities</a>

\begin{code}

 S-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → S{β = α} 𝒦 ⊧ p ≋ q

 S-id1 p q σ (sbase x) = ⊧-Lift-invar fe p q (σ x)
 S-id1 p q σ (slift x) = ⊧-Lift-invar fe p q ((S-id1 p q σ) x)

 S-id1 p q σ (ssub{𝑨}{𝑩} sA B≤A) =
  ⊧-S-class-invar fe p q pq (𝑩 , 𝑨 , (𝑩 , B≤A) , _⊎_.inj₂ refl , ≅-refl)
   where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
   ν : 𝑨 ⊧ p ≈ q
   ν = S-id1 p q σ sA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq refl = ν

   pq : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   pq {𝑩} (inj₁ x) = σ x
   pq {𝑩} (inj₂ y) = Apq y

 S-id1 p q σ (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (S-id1 p q σ x) x₁

\end{code}

Again, the obvious converse is barely worth the bits needed to formalize it.

\begin{code}

 S-id2 : ∀{β}(p q : Term X) → S{β = β}𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

 S-id2 p q Spq {𝑨} KA = ⊧-lower-invar fe p q (Spq (sbase KA))

\end{code}


#### <a id="p-preserves-identities">P preserves identities</a>

\begin{code}

 P-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → P{β = α} 𝒦 ⊧ p ≋ q

 P-id1 p q σ (pbase x) = ⊧-Lift-invar fe p q (σ x)
 P-id1 p q σ (pliftu x) = ⊧-Lift-invar fe p q ((P-id1 p q σ) x)
 P-id1 p q σ (pliftw x) = ⊧-Lift-invar fe p q ((P-id1 p q σ) x)

 P-id1 p q σ (produ{I}{𝒜} x) = ⊧-P-lift-invar 𝒜  fe {p}{q} IH
  where
  IH : ∀ i → (Lift-Alg (𝒜 i) α) ⟦ p ⟧ ≡ (Lift-Alg (𝒜 i) α) ⟦ q ⟧
  IH i = ⊧-Lift-invar fe p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (prodw{I}{𝒜} x) = ⊧-P-lift-invar 𝒜 fe {p}{q}IH
  where
  IH : ∀ i → Lift-Alg (𝒜 i) α ⟦ p ⟧ ≡ Lift-Alg (𝒜 i) α ⟦ q ⟧
  IH i = ⊧-Lift-invar fe p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (pisow{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (P-id1 p q σ x) x₁

\end{code}

...and conversely...

\begin{code}

 P-id2 : ∀ {β}(p q : Term X) → P{β = β} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q
 P-id2 p q PKpq KA = ⊧-lower-invar fe p q (PKpq (pbase KA))

\end{code}


#### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

 V-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{β = α} 𝒦 ⊧ p ≋ q
 V-id1 p q σ (vbase x) = ⊧-Lift-invar fe p q (σ x)
 V-id1 p q σ (vlift{𝑨} x) = ⊧-Lift-invar  fe p q ((V-id1 p q σ) x)
 V-id1 p q σ (vliftw{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1 p q σ) x)

 V-id1 p q σ (vhimg{𝑨}{𝑪}VA (𝑩 , ((φ , φh) , φE))) = Goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1 p q σ VA

  preim : ∀ 𝒃 (x : X) → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv φ (φE (𝒃 x)))

  ζ : ∀ 𝒃 → φ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = (fe 𝓧 α) λ x → InvIsInv φ (φE (𝒃 x))

  Goal : (𝑩 ⟦ p ⟧) ≡ (𝑩 ⟦ q ⟧)
  Goal = (fe (α ⊔ 𝓧) α) λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃      ≡⟨ (cong (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                (𝑩 ⟦ p ⟧)(φ ∘(preim 𝒃)) ≡⟨(comm-hom-term (fe 𝓥 α) 𝑩(φ , φh) p(preim 𝒃))⁻¹ ⟩
                φ ((𝑨 ⟦ p ⟧)(preim 𝒃))  ≡⟨ cong φ (cong-app IH (preim 𝒃)) ⟩
                φ ((𝑨 ⟦ q ⟧)(preim 𝒃))  ≡⟨ comm-hom-term (fe 𝓥 α) 𝑩 (φ , φh) q (preim 𝒃) ⟩
                (𝑩 ⟦ q ⟧)(φ ∘(preim 𝒃)) ≡⟨ cong (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
                (𝑩 ⟦ q ⟧) 𝒃             ∎

 V-id1 p q σ ( vssubw {𝑨}{𝑩} VA B≤A ) =
  ⊧-S-class-invar fe p q pq (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q σ VA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq refl = IH

   pq : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   pq {𝑩} (inj₁ x) = σ x
   pq {𝑩} (inj₂ y) = Asinglepq y

 V-id1 p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar 𝒜 fe {p}{q} λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar 𝒜 fe {p}{q} λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1 p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q σ VA) A≅B


 V-id1' : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{β = 𝓕⁺} 𝒦 ⊧ p ≋ q
 V-id1' p q σ (vbase x) = ⊧-Lift-invar fe p q (σ x)
 V-id1' p q σ (vlift{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1 p q σ) x)
 V-id1' p q σ (vliftw{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1' p q σ) x)
 V-id1' p q σ (vhimg{𝑨}{𝑪} VA (𝑩 , ((φ , φh) , φE))) = Goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1' p q σ VA

  preim : ∀ 𝒃 x → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv φ (φE (𝒃 x)))

  ζ : ∀ 𝒃 → φ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = (fe 𝓧 𝓕⁺) λ x → InvIsInv φ (φE (𝒃 x))

  Goal : 𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧
  Goal = (fe (𝓧 ⊔ 𝓕⁺) 𝓕⁺) λ 𝒃
   →     (𝑩 ⟦ p ⟧) 𝒃               ≡⟨ (cong (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹  ⟩
         (𝑩 ⟦ p ⟧) (φ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term (fe 𝓥 𝓕⁺) 𝑩 (φ , φh) p (preim 𝒃))⁻¹ ⟩
         φ((𝑨 ⟦ p ⟧) (preim 𝒃))    ≡⟨ cong φ (cong-app IH (preim 𝒃))⟩
         φ((𝑨 ⟦ q ⟧) (preim 𝒃))    ≡⟨ comm-hom-term (fe 𝓥 𝓕⁺) 𝑩 (φ , φh) q (preim 𝒃)⟩
         (𝑩 ⟦ q ⟧) (φ ∘ (preim 𝒃)) ≡⟨ cong (𝑩 ⟦ q ⟧) (ζ 𝒃)⟩
         (𝑩 ⟦ q ⟧) 𝒃               ∎

 V-id1' p q σ (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar fe 𝑩 {p}{q}(V-id1' p q σ VA) B≤A
 V-id1' p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar 𝒜 fe {p}{q} λ i → V-id1 p q σ (V𝒜 i)
 V-id1' p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar 𝒜 fe {p}{q} λ i → V-id1' p q σ (V𝒜 i)
 V-id1' p q σ (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1' p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1' p q σ VA)A≅B

\end{code}


#### <a id="class-identities">Class identities</a>

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities modeled by `𝒦`.   We formalize this observation as follows.

\begin{code}

 𝒱 : Pred (Algebra (𝓕⁺) 𝑆) (lsuc 𝓕⁺)
 𝒱 = V{β = 𝓕⁺} 𝒦

 class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  →  (p , q) ∈ Th 𝒱
 class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA


 class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊧ p ≋ q
 class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar fe p q (Thpq (vbase KA))

\end{code}


Once again, and for the last time, completeness dictates that we formalize the coverse of `V-id1`, however obvious it may be.

\begin{code}

module _ {β : Level}{X : Type 𝓧}{𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 V-id2 : (∀ a b → funext a b) → (p q : Term X) → (V{β = β} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 V-id2 fe p q Vpq {𝑨} KA = ⊧-lower-invar fe p q (Vpq (vbase KA))

\end{code}


----------------------------

[← Varieties.Varieties](Varieties.Varieties.html)
<span style="float:right;">[FreeAlgebras →](Varieties.FreeAlgebras.html)</span>

{% include UALib.Links.md %}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team








