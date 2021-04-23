---
layout: default
title : Varieties.Preservation (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="Equation preservation">Equation preservation</a>

This section presents the [Varieties.Preservation][] module of the [Agda Universal Algebra Library][]. In this module we show that identities are preserved by closure operators H, S, and P.  This will establish the easy direction of Birkhoff's HSP Theorem.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Varieties.Preservation  where

open import Varieties.Varieties public

module preservation {𝑆 : Signature 𝓞 𝓥} {𝓤 𝓧 : Level }{X : Type 𝓧} where
 open varieties {𝑆 = 𝑆}{X = X} public

 𝓕 𝓕⁺ 𝓾𝔁 : Level
 𝓕 = ov 𝓤
 𝓕⁺ = lsuc (ov 𝓤)    -- (this will be the level of the relatively free algebra)
 𝓾𝔁 = 𝓤 ⊔ 𝓧

\end{code}



#### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator H is compatible with identities that hold in the given class.

 \begin{code}

 module _ {fe : DFunExt} {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

  H-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → H{𝓤}{𝓤} 𝒦 ⊧ p ≋ q
  H-id1 p q α (hbase x) = ⊧-Lift-invar fe p q (α x)
  H-id1 p q α (hlift{𝑨} x) = ⊧-Lift-invar fe p q (H-id1 p q α x)

  H-id1 p q α (hhimg{𝑨}{𝑪} HA((𝑩 , ϕ , (ϕhom , ϕsur)), B≅C)) = ⊧-I-invar fe 𝑪 p q γ B≅C
   where
   β : 𝑨 ⊧ p ≈ q
   β = (H-id1 p q α) HA

   preim : ∀ 𝒃 x → ∣ 𝑨 ∣
   preim 𝒃 x = Inv ϕ (ϕsur (𝒃 x))

   ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = (fe 𝓧 𝓤) λ x → InvIsInv ϕ (ϕsur (𝒃 x))

   γ : 𝑩 ⟦ p ⟧  ≡ 𝑩 ⟦ q ⟧
   γ = (fe 𝓾𝔁 𝓤) λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃             ≡⟨ (ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                 (𝑩 ⟦ p ⟧)(ϕ ∘(preim 𝒃)) ≡⟨(comm-hom-term (fe 𝓥 𝓤) 𝑩(ϕ , ϕhom) p(preim 𝒃))⁻¹ ⟩
                 ϕ((𝑨 ⟦ p ⟧)(preim 𝒃))   ≡⟨ ap ϕ (happly β (preim 𝒃)) ⟩
                 ϕ((𝑨 ⟦ q ⟧)(preim 𝒃))   ≡⟨ comm-hom-term (fe 𝓥 𝓤) 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
                 (𝑩 ⟦ q ⟧)(ϕ ∘(preim 𝒃)) ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
                 (𝑩 ⟦ q ⟧) 𝒃             ∎

  H-id1 p q α (hiso{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (H-id1 p q α x) x₁

 \end{code}

 The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

 \begin{code}

  H-id2 : ∀ {𝓦} → (p q : Term X) → H{𝓤}{𝓦} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

  H-id2 p q Hpq KA = ⊧-lower-invar fe p q (Hpq (hbase KA))

 \end{code}


 #### <a id="s-preserves-identities">S preserves identities</a>

 \begin{code}

  S-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → S{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

  S-id1 p q α (sbase x) = ⊧-Lift-invar fe p q (α x)
  S-id1 p q α (slift x) = ⊧-Lift-invar fe p q ((S-id1 p q α) x)

  S-id1 p q α (ssub{𝑨}{𝑩} sA B≤A) =
   ⊧-S-class-invar fe p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
    where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
    β : 𝑨 ⊧ p ≈ q
    β = S-id1 p q α sA

    Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Apq refl = β

    γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    γ {𝑩} (inj₁ x) = α x
    γ {𝑩} (inj₂ y) = Apq y

  S-id1 p q α (ssubw{𝑨}{𝑩} sA B≤A) =
   ⊧-S-class-invar fe p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
    where  --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
    β : 𝑨 ⊧ p ≈ q
    β = S-id1 p q α sA

    Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Apq refl = β

    γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    γ {𝑩} (inj₁ x) = α x
    γ {𝑩} (inj₂ y) = Apq y

  S-id1 p q α (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (S-id1 p q α x) x₁

 \end{code}

 Again, the obvious converse is barely worth the bits needed to formalize it.

 \begin{code}

  S-id2 : ∀{𝓦}(p q : Term X) → S{𝓤}{𝓦}𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

  S-id2 p q Spq {𝑨} KA = ⊧-lower-invar fe p q (Spq (sbase KA))

 \end{code}


 #### <a id="p-preserves-identities">P preserves identities</a>

 \begin{code}

  P-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → P{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

  P-id1 p q α (pbase x) = ⊧-Lift-invar fe p q (α x)
  P-id1 p q α (pliftu x) = ⊧-Lift-invar fe p q ((P-id1 p q α) x)
  P-id1 p q α (pliftw x) = ⊧-Lift-invar fe p q ((P-id1 p q α) x)

  P-id1 p q α (produ{I}{𝒜} x) = ⊧-P-lift-invar I 𝒜  fe {p}{q} IH
   where
   IH : ∀ i → (Lift-alg (𝒜 i) 𝓤) ⟦ p ⟧ ≡ (Lift-alg (𝒜 i) 𝓤) ⟦ q ⟧
   IH i = ⊧-Lift-invar fe p q ((P-id1 p q α) (x i))

  P-id1 p q α (prodw{I}{𝒜} x) = ⊧-P-lift-invar I 𝒜 fe {p}{q}IH
   where
   IH : ∀ i → Lift-alg (𝒜 i) 𝓤 ⟦ p ⟧ ≡ Lift-alg (𝒜 i) 𝓤 ⟦ q ⟧
   IH i = ⊧-Lift-invar fe p q ((P-id1 p q α) (x i))

  P-id1 p q α (pisou{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (P-id1 p q α x) x₁
  P-id1 p q α (pisow{𝑨}{𝑩} x x₁) = ⊧-I-invar fe 𝑩 p q (P-id1 p q α x) x₁

 \end{code}

 ...and conversely...

 \begin{code}

  P-id2 : ∀ {𝓦}(p q : Term X) → P{𝓤}{𝓦} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q
  P-id2 p q PKpq KA = ⊧-lower-invar fe p q (PKpq (pbase KA))

 \end{code}


 #### <a id="v-preserves-identities">V preserves identities</a>

 Finally, we prove the analogous preservation lemmas for the closure operator `V`.

 \begin{code}

  V-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{𝓤}{𝓤} 𝒦 ⊧ p ≋ q
  V-id1 p q α (vbase x) = ⊧-Lift-invar fe p q (α x)
  V-id1 p q α (vlift{𝑨} x) = ⊧-Lift-invar  fe p q ((V-id1 p q α) x)
  V-id1 p q α (vliftw{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1 p q α) x)

  V-id1 p q α (vhimg{𝑨}{𝑪}VA((𝑩 , ϕ , (ϕh , ϕE)) , B≅C)) = ⊧-I-invar fe 𝑪 p q γ B≅C
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q α VA

   preim : ∀ 𝒃 (x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (ϕE (𝒃 x)))

   ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = (fe 𝓧 𝓤) λ x → InvIsInv ϕ (ϕE (𝒃 x))

   γ : (𝑩 ⟦ p ⟧) ≡ (𝑩 ⟦ q ⟧)
   γ = (fe 𝓾𝔁 𝓤) λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃      ≡⟨ (ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                 (𝑩 ⟦ p ⟧)(ϕ ∘(preim 𝒃)) ≡⟨(comm-hom-term (fe 𝓥 𝓤) 𝑩(ϕ , ϕh) p(preim 𝒃))⁻¹ ⟩
                 ϕ ((𝑨 ⟦ p ⟧)(preim 𝒃))  ≡⟨ ap ϕ (happly IH (preim 𝒃)) ⟩
                 ϕ ((𝑨 ⟦ q ⟧)(preim 𝒃))  ≡⟨ comm-hom-term (fe 𝓥 𝓤) 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
                 (𝑩 ⟦ q ⟧)(ϕ ∘(preim 𝒃)) ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
                 (𝑩 ⟦ q ⟧) 𝒃             ∎

  V-id1 p q α (vssub {𝑨}{𝑩} VA B≤A) = ⊧-S-class-invar fe p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
    where
    IH : 𝑨 ⊧ p ≈ q
    IH = V-id1 p q α VA

    Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Asinglepq refl = IH

    γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    γ {𝑩} (inj₁ x) = α x
    γ {𝑩} (inj₂ y) = Asinglepq y

  V-id1 p q α ( vssubw {𝑨}{𝑩} VA B≤A ) =
   ⊧-S-class-invar fe p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
    where
    IH : 𝑨 ⊧ p ≈ q
    IH = V-id1 p q α VA

    Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Asinglepq refl = IH

    γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    γ {𝑩} (inj₁ x) = α x
    γ {𝑩} (inj₂ y) = Asinglepq y

  V-id1 p q α (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 fe {p}{q} λ i → V-id1 p q α (V𝒜 i)
  V-id1 p q α (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 fe {p}{q} λ i → V-id1 p q α (V𝒜 i)
  V-id1 p q α (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q α VA) A≅B
  V-id1 p q α (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q α VA) A≅B


  V-id1' : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{𝓤}{𝓕⁺} 𝒦 ⊧ p ≋ q
  V-id1' p q α (vbase x) = ⊧-Lift-invar fe p q (α x)
  V-id1' p q α (vlift{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1 p q α) x)
  V-id1' p q α (vliftw{𝑨} x) = ⊧-Lift-invar fe p q ((V-id1' p q α) x)
  V-id1' p q α (vhimg{𝑨}{𝑪} VA ((𝑩 , ϕ , (ϕh , ϕE)) , B≅C)) =
   ⊧-I-invar fe 𝑪 p q γ B≅C
    where
    IH : 𝑨 ⊧ p ≈ q
    IH = V-id1' p q α VA

    preim : ∀ 𝒃 x → ∣ 𝑨 ∣
    preim 𝒃 x = (Inv ϕ (ϕE (𝒃 x)))

    ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
    ζ 𝒃 = (fe 𝓧 𝓕⁺) λ x → InvIsInv ϕ (ϕE (𝒃 x))

    γ : 𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧
    γ = (fe (𝓧 ⊔ 𝓕⁺) 𝓕⁺) λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃  ≡⟨ (ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹  ⟩
                  (𝑩 ⟦ p ⟧) (ϕ ∘ (preim 𝒃)) ≡⟨(comm-hom-term (fe 𝓥 𝓕⁺) 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
                  ϕ((𝑨 ⟦ p ⟧)(preim 𝒃))     ≡⟨ ap ϕ (happly IH (preim 𝒃))⟩
                  ϕ((𝑨 ⟦ q ⟧)(preim 𝒃))     ≡⟨ comm-hom-term (fe 𝓥 𝓕⁺) 𝑩 (ϕ , ϕh) q (preim 𝒃)⟩
                  (𝑩 ⟦ q ⟧)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃)⟩
                  (𝑩 ⟦ q ⟧) 𝒃               ∎

  V-id1' p q α (vssub{𝑨}{𝑩} VA B≤A) = ⊧-S-invar fe 𝑩 {p}{q}(V-id1 p q α VA) B≤A
  V-id1' p q α (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar fe 𝑩 {p}{q}(V-id1' p q α VA) B≤A
  V-id1' p q α (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 fe {p}{q} λ i → V-id1 p q α (V𝒜 i)
  V-id1' p q α (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 fe {p}{q} λ i → V-id1' p q α (V𝒜 i) -- {fwu = (fe 𝓕⁺ 𝓕⁺)}{(fe 𝓥 𝓕⁺)}{(fe 𝓕⁺ 𝓕⁺)}
  V-id1' p q α (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1 p q α VA) A≅B
  V-id1' p q α (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar fe 𝑩 p q (V-id1' p q α VA)A≅B

 \end{code}


 #### <a id="class-identities">Class identities</a>

 From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities modeled by `𝒦`.   We formalize this observation as follows.

 \begin{code}

  𝒱 : Pred (Algebra (𝓕⁺) 𝑆) (lsuc 𝓕⁺)
  𝒱 = V{𝓤}{𝓕⁺} 𝒦

  class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  →  (p , q) ∈ Th 𝒱
  class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA


  class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊧ p ≋ q
  class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar fe p q (Thpq (vbase KA))


  class-identities : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th 𝒱)
  class-identities p q = class-ids-⇒ p q , class-ids-⇐ p q

 \end{code}


 Once again, and for the last time, completeness dictates that we formalize the coverse of `V-id1`, however obvious it may be.

 \begin{code}

 module _ {𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

  V-id2 : DFunExt → (p q : Term X) → (V{𝓤}{𝓦} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
  V-id2 fe p q Vpq {𝑨} KA = ⊧-lower-invar fe p q (Vpq (vbase KA))

 \end{code}


----------------------------

[← Varieties.Varieties](Varieties.Varieties.html)
<span style="float:right;">[FreeAlgebras →](Varieties.FreeAlgebras.html)</span>

{% include UALib.Links.md %}

