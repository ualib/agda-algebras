\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 23 Dec 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂; Π)

module closure-exp-new-new
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import homomorphisms {𝑆 = 𝑆} public
open import subuniverses {𝑆 = 𝑆}{𝕏 = 𝕏}{fe = gfe} public
open import terms {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = gfe} renaming (generator to ℊ) public

_⊧_≈_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Algebra 𝓤 𝑆 → Term{𝓧}{X} → Term → 𝓤 ⊔ 𝓧 ̇
𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →      Term{𝓧}{X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇
_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

lemma-⊧-≅ : {𝓠 𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
           (p q : Term{𝓧}{X}) → (𝑨 ⊧ p ≈ q) → (𝑨 ≅ 𝑩) → 𝑩 ⊧ p ≈ q
lemma-⊧-≅ {𝓠}{𝓤}{𝓧}{X}{𝑨}{𝑩} p q Apq (f , g , f∼g , g∼f) = γ
 where
  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ x →
      (p ̇ 𝑩) x ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (p ̇ 𝑩) (∣ 𝒾𝒹 𝑩 ∣ ∘ x) ≡⟨ ap (λ - → (p ̇ 𝑩) -) (gfe λ i → ((f∼g)(x i))⁻¹)  ⟩
      (p ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘ x) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
      ∣ f ∣ ((p ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ ap (λ - → ∣ f ∣ (- (∣ g ∣ ∘ x))) Apq ⟩
      ∣ f ∣ ((q ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ comm-hom-term gfe 𝑨 𝑩 f q (∣ g ∣ ∘ x) ⟩
      (q ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ ap (λ - → (q ̇ 𝑩) -) (gfe λ i → (f∼g) (x i)) ⟩
      (q ̇ 𝑩) x ∎

⊧-≅ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
      (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(p q : Term{𝓧}{X})
 →    𝑨 ⊧ p ≈ q → 𝑨 ≅ 𝑩 → 𝑩 ⊧ p ≈ q
⊧-≅ 𝑨 𝑩 p q Apq (fh , gh , f∼g , g∼f) = γ
 where
  f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
  f = ∣ fh ∣
  g : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  g = ∣ gh ∣
  fgid : (b : ∣ 𝑩 ∣) → b ≡ f (g b)
  fgid b = b           ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
           (∣ 𝒾𝒹 𝑩 ∣) b ≡⟨ (f∼g b)⁻¹ ⟩
           (f ∘ g) b ∎

  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ x
   →  (p ̇ 𝑩) x ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (p ̇ 𝑩) (λ i → x i) ≡⟨ ap (p ̇ 𝑩) (gfe λ i → (f∼g (x i))⁻¹) ⟩
      (p ̇ 𝑩) (λ i → f (g (x i))) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 fh p (g ∘ x))⁻¹  ⟩
      f ((p ̇ 𝑨) (g ∘ x)) ≡⟨ ap f (intensionality Apq (g ∘ x)) ⟩
      f ((q ̇ 𝑨) (g ∘ x)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 fh q (g ∘ x))  ⟩
      (q ̇ 𝑩) (λ i → f (g (x i))) ≡⟨ ap (q ̇ 𝑩) (gfe λ i → (f∼g (x i))) ⟩
      (q ̇ 𝑩) x ∎

lift-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
      (𝑨 : Algebra 𝓤 𝑆)(p q : Term{𝓧}{X})
 →    𝑨 ⊧ p ≈ q → (lift-alg 𝑨 𝓦) ⊧ p ≈ q
lift-alg-⊧ 𝑨 p q Apq = ⊧-≅ 𝑨 (lift-alg 𝑨 _) p q Apq lift-alg-≅


------------------------------------------------------------------------
-- Equational theories and classes
Th : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →   Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

Mod : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

--Closure wrt H
data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  himg  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦
  hiso  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦

--Closure wrt S
data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  sub   : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦

--Closure wrt P
data P {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  plift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  prod  : {I : 𝓦 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P{𝓤}{𝓦} 𝒦
  piso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P{𝓤}{𝓦} 𝒦

data V {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ V{𝓤}{𝓦} 𝒦
  vhimg : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦
  vsub  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦
  vprod : {I : 𝓦 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ V{𝓤}{𝓦} 𝒦
  viso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦

--alternatives---
data H' {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra 𝓤 𝑆)(OV 𝓤) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ H' 𝒦
  himg  : {𝑨 𝑩 : Algebra 𝓤 𝑆} → 𝑨 ∈ H' 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H' 𝒦
  hiso  : {𝑨 𝑩 : Algebra 𝓤 𝑆} → 𝑨 ∈ H' 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H' 𝒦
data S' {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S'{𝓤}{𝓦} 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S'{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S'{𝓤}{𝓦} 𝒦
  sub   : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S'{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S'{𝓤}{𝓦} 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S'{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S'{𝓤}{𝓦} 𝒦
-- data S' {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra 𝓤 𝑆) (OV 𝓤) where
--   sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ S' 𝒦
--   sub   : {𝑨 𝑩 : Algebra 𝓤 𝑆} → 𝑨 ∈ S' 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S' 𝒦
--   siso  : {𝑨 𝑩 : Algebra 𝓤 𝑆} → 𝑨 ∈ S' 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S' 𝒦
data P' {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P'{𝓤}{𝓦} 𝒦
  pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P'{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P'{𝓤}{𝓦} 𝒦
  pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P'{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P'{𝓤}{𝓦} 𝒦
  produ  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P'{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P'{𝓤}{𝓦} 𝒦
  prodw  : {I : 𝓦 ̇ }{𝒜 : I → Algebra (𝓤 ⊔ 𝓦) 𝑆} → (∀ i → (𝒜 i) ∈ P'{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P'{𝓤}{𝓦} 𝒦
  pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P'{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P'{𝓤}{𝓦} 𝒦
  pisow  : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P'{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P'{𝓤}{𝓦} 𝒦



lift-alg-assoc : {𝓤 𝓦 𝓘 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
lift-alg-assoc {𝓤} {𝓦} {𝓘} {𝑨} = TRANS-≅ (TRANS-≅ ζ lift-alg-≅) lift-alg-≅
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅

-- lift-class : Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦))
-- lift-class 𝒦 = λ
lower-class : {𝓤 𝓦 : Universe} → Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) → Pred (Algebra 𝓤 𝑆)(OV (𝓤 ⊔ 𝓦))
lower-class {𝓤}{𝓦}𝒦 = λ (𝑨 : Algebra 𝓤 𝑆) → lift-alg 𝑨 𝓦 ∈ 𝒦


-- --P is a closure operator ----------------------------------------
-- --In particular, it's expansive...
P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ P{𝓤}{𝓤} 𝒦
P-expa{𝓤}{𝒦} {𝑨} KA = piso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

P-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦) ⊆ P{𝓤}{𝓦} 𝒦
P-idemp {𝓤} {𝓦} {𝒦} (pbase x) = plift x
P-idemp {𝓤} {𝓦} {𝒦} (plift x) = plift (P-idemp x)
P-idemp {𝓤} {𝓦} {𝒦} (prod x) = prod (λ i → P-idemp (x i))
P-idemp {𝓤} {𝓦} {𝒦} (piso x x₁) = piso (P-idemp x) x₁

P'-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ P'{𝓤}{𝓤} 𝒦
P'-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

P'-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P'{𝓤}{𝓦} (P'{𝓤}{𝓤} 𝒦) ⊆ P'{𝓤}{𝓦} 𝒦

P'-idemp {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (pbase{𝑨} x) = pliftu x
P'-idemp {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (pliftu{𝑨} x) = pliftu (P'-idemp{𝓤}{𝓤} x)
P'-idemp {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 (𝓤 ⊔ 𝓦))} (pliftw{𝑨} x) = pliftw (P'-idemp x)
P'-idemp {𝓤} {𝓦} {𝒦} (produ x) = produ (λ i → P'-idemp{𝓤}{𝓤} (x i))
P'-idemp {𝓤} {𝓦} {𝒦} (prodw x) = prodw (λ i → P'-idemp (x i))
P'-idemp {𝓤} {𝓦} {𝒦} {𝑨} (pisou x x₁) = pisou (P'-idemp{𝓤}{𝓤} x) x₁
P'-idemp {𝓤} {𝓦} {𝒦} {𝑨} (pisow x x₁) = pisow (P'-idemp x) x₁


P'-idemp' : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P'{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P'-idemp' (pbase x) = pliftw x
P'-idemp' {𝓤} {𝓦} {𝒦} (pliftu x) = pliftw (P'-idemp' {𝓤}{𝓦} x)
P'-idemp' {𝓤} {𝓦} {𝒦}  (pliftw x) = pliftw (P'-idemp' {𝓤}{𝓦} x)
P'-idemp' {𝓤} {𝓦} {𝒦}  (produ x) = prodw (λ i → P'-idemp' {𝓤}{𝓦} (x i))
P'-idemp' {𝓤} {𝓦} {𝒦}  (prodw x) = prodw (λ i → P'-idemp' {𝓤}{𝓦} (x i))
P'-idemp' {𝓤} {𝓦} {𝒦}  (pisou x x₁) = pisow (P'-idemp' {𝓤}{𝓦} x) x₁
P'-idemp' {𝓤} {𝓦} {𝒦}  (pisow x x₁) = pisow (P'-idemp' {𝓤}{𝓦} x) x₁


-- this is only needed for old PS⊆SP (so we can eventually remove it)
P-idemp' : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P-idemp' {𝑨} x = {!!} -- (pbase x) = pliftw x

lift-alg-P : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝑨 : Algebra 𝓤 𝑆}

 →                 𝑨 ∈ (P{𝓤}{𝓤} 𝒦)
             ---------------------------------
 →             lift-alg 𝑨 𝓦 ∈  P{𝓤}{𝓦} 𝒦

lift-alg-P pA =  P-idemp (pbase pA)

lift-alg-subP' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝑩 : Algebra 𝓤 𝑆}

 →                𝑩 IsSubalgebraOfClass (P'{𝓤}{𝓤} 𝒦)
            ---------------------------------------------------
 →           (lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)

lift-alg-subP' {𝓤} {𝓦} {𝒦} {𝑩} (𝑨 , (𝑪 , C≤A) , pA , B≅C ) = γ
 where
  lA lB lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  lB = lift-alg 𝑩 𝓦
  lC = lift-alg 𝑪 𝓦

  lC≤lA : lC ≤ lA
  lC≤lA = lift-alg-lift-≤-lift 𝑪 {𝑨} C≤A
  plA : lA ∈ P'{𝓤}{𝓦} 𝒦
  plA = pliftu pA

  γ : lB IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
  γ = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 𝑪 B≅C)


lift-alg-subP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝑩 : Algebra 𝓤 𝑆}

 →                𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
            ---------------------------------------------------
 →           (lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lift-alg-subP {𝓤} {𝓦} {𝒦} {𝑩} (𝑨 , (𝑪 , C≤A) , pA , B≅C ) = γ
 where
  lA lB lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  lB = lift-alg 𝑩 𝓦
  lC = lift-alg 𝑪 𝓦

  lC≤lA : lC ≤ lA
  lC≤lA = lift-alg-lift-≤-lift 𝑪 {𝑨} C≤A
  plA : lA ∈ P{𝓤}{𝓦} 𝒦
  plA = lift-alg-P pA

  γ : lB IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  γ = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 𝑪 B≅C)


--S is a closure operator -------------------------------------------
--In particular, it's monotone.
S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'
S-mono ante (sbase x) = sbase (ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S-mono{𝓤}{𝓤} ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (sub{𝑨}{𝑩} sA B≤A) = sub (S-mono ante sA) B≤A
S-mono {𝒦} {𝒦'} ante (siso x x₁) = siso (S-mono ante x) x₁

S'-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S'{𝓤}{𝓦} 𝒦 ⊆ S'{𝓤}{𝓦} 𝒦'
S'-mono ante (sbase x) = sbase (ante x)
S'-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S'-mono{𝓤}{𝓤} ante x)
S'-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (sub{𝑨}{𝑩} sA B≤A) = sub (S'-mono ante sA) B≤A
S'-mono {𝒦} {𝒦'} ante (siso x x₁) = siso (S'-mono ante x) x₁

-- S'-mono : {𝓤 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →       𝒦 ⊆ 𝒦'  →  S' 𝒦 ⊆ S' 𝒦'
-- S'-mono ante (sbase x) = sbase (ante x)
-- S'-mono ante (sub x x₁) = sub (S'-mono ante x) x₁
-- S'-mono ante (siso x x₁) = siso (S'-mono ante x) x₁

subalgebra→S : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
             ----------------------------------------------------------
 →                  𝑪 ∈ S{𝓤}{𝓦} 𝒦

subalgebra→S {𝓤}{𝓦}{𝒦}{𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = sub sA C≤A
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  slAu : lift-alg 𝑨 𝓤 ∈ S{𝓤}{𝓤} 𝒦
  slAu = sbase KA

  sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
  sA = siso slAu (sym-≅ lift-alg-≅)

subalgebra→S' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
             ----------------------------------------------------------
 →                  𝑪 ∈ S'{𝓤}{𝓦} 𝒦

subalgebra→S' {𝓤}{𝓦}{𝒦}{𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = sub sA C≤A
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  slAu : lift-alg 𝑨 𝓤 ∈ S'{𝓤}{𝓤} 𝒦
  slAu = sbase KA

  sA : 𝑨 ∈ S'{𝓤}{𝓤} 𝒦
  sA = siso slAu (sym-≅ lift-alg-≅)


S→subalgebra : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦
              --------------------------------------------------
 →                𝑩 IsSubalgebraOfClass 𝒦

S→subalgebra {𝓤} {𝒦} {.(lift-alg 𝑩 𝓤)} (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
S→subalgebra {𝓤} {𝒦} {.(lift-alg 𝑩 𝓤)} (slift{𝑩} x) = 𝑨 , SA , KA , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
 where
  BS : 𝑩 IsSubalgebraOfClass 𝒦
  BS = S→subalgebra x
  𝑨 : Algebra 𝓤 𝑆
  𝑨 = ∣ BS ∣
  SA : SUBALGEBRA 𝑨
  SA = fst ∥ BS ∥
  KA : 𝑨 ∈ 𝒦
  KA = ∣ snd ∥ BS ∥ ∣
  B≅SA : 𝑩 ≅ ∣ SA ∣
  B≅SA = ∥ snd ∥ BS ∥ ∥

S→subalgebra {𝓤} {𝒦} {𝑩} (sub{𝑨} sA B≤A) = γ
 where
  AS : 𝑨 IsSubalgebraOfClass 𝒦
  AS = S→subalgebra sA
  𝑨' : Algebra 𝓤 𝑆
  𝑨' = ∣ AS ∣
  SA : SUBALGEBRA 𝑨'
  SA = fst ∥ AS ∥
  KA : 𝑨' ∈ 𝒦
  KA = ∣ snd ∥ AS ∥ ∣
  A≅SA : 𝑨 ≅ ∣ SA ∣
  A≅SA = ∥ snd ∥ AS ∥ ∥
  B≤SA : 𝑩 ≤ ∣ SA ∣
  B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A A≅SA
  B≤A' : 𝑩 ≤ 𝑨'
  B≤A' = transitivity-≤ 𝑩{∣ SA ∣}{𝑨'} B≤SA ∥ SA ∥
  γ : 𝑩 IsSubalgebraOfClass 𝒦
  γ = 𝑨' , (𝑩 , B≤A') , KA , refl-≅
S→subalgebra {𝓤} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = S→subalgebra sA
  𝔸 : Algebra _ 𝑆
  𝔸 = ∣ IH ∣
  SA : SUBALGEBRA 𝔸
  SA = fst ∥ IH ∥
  𝔸∈𝒦 : 𝔸 ∈ 𝒦
  𝔸∈𝒦 = fst ∥ snd IH ∥
  A≅SA : 𝑨 ≅ ∣ SA ∣
  A≅SA = snd ∥ snd IH ∥
  B≅sa : 𝑩 ≅ ∣ SA ∣
  B≅sa = TRANS-≅ (sym-≅ A≅B) A≅SA
  γ : 𝑩 IsSubalgebraOfClass 𝒦
  γ = 𝔸 , SA , 𝔸∈𝒦 , B≅sa

module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} where

 S'→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S'{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦
 S'→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
 S'→subalgebra {.(lift-alg 𝑩 𝓤)} (slift{𝑩} x) = 𝑨 , SA , KA , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S'→subalgebra x
   𝑨 : Algebra 𝓤 𝑆
   𝑨 = ∣ BS ∣
   SA : SUBALGEBRA 𝑨
   SA = fst ∥ BS ∥
   KA : 𝑨 ∈ 𝒦
   KA = ∣ snd ∥ BS ∥ ∣
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥
 S'→subalgebra {𝑩} (sub{𝑨} sA B≤A) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S'→subalgebra sA
   𝑨' : Algebra 𝓤 𝑆
   𝑨' = ∣ AS ∣
   SA : SUBALGEBRA 𝑨'
   SA = fst ∥ AS ∥
   KA : 𝑨' ∈ 𝒦
   KA = ∣ snd ∥ AS ∥ ∣
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = ∥ snd ∥ AS ∥ ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A A≅SA
   B≤A' : 𝑩 ≤ 𝑨'
   B≤A' = transitivity-≤ 𝑩{∣ SA ∣}{𝑨'} B≤SA ∥ SA ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ = 𝑨' , (𝑩 , B≤A') , KA , refl-≅
 S'→subalgebra {𝑩} (siso{𝑨} sA A≅B) = γ
  where
   IH : 𝑨 IsSubalgebraOfClass 𝒦
   IH = S'→subalgebra sA
   𝔸 : Algebra _ 𝑆
   𝔸 = ∣ IH ∣
   SA : SUBALGEBRA 𝔸
   SA = fst ∥ IH ∥
   𝔸∈𝒦 : 𝔸 ∈ 𝒦
   𝔸∈𝒦 = fst ∥ snd IH ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd IH ∥
   B≅sa : 𝑩 ≅ ∣ SA ∣
   B≅sa = TRANS-≅ (sym-≅ A≅B) A≅SA
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ = 𝔸 , SA , 𝔸∈𝒦 , B≅sa



S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦)
S⊆SP{𝓤}{𝓦}{𝒦} = S-mono{𝒦 = 𝒦}{𝒦' = (P{𝓤}{𝓤} 𝒦)} P-expa

-- S'⊆S'P' : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →     S' 𝒦 ⊆ S' (P'{𝓤}{𝓤} 𝒦)
-- S'⊆S'P'{𝓤}{𝒦} = S'-mono {𝒦 = 𝒦}{𝒦' = (P'{𝓤}{𝓤} 𝒦)} P'-expa


S⊆SP' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
S⊆SP' {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (sbase{𝑨} x) = γ
 where
  lA llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  llA = lift-alg lA (𝓤 ⊔ 𝓦)

  spllA : llA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  spllA = sbase{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = (𝓤 ⊔ 𝓦)} (pbase x)

  γ : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = siso spllA (sym-≅ lift-alg-≅)

  -- splA : (lift-alg 𝑨 (𝓤 ⊔ 𝓦)) ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  -- splA = S⊆SP'{𝓤}{𝓤 ⊔ 𝓦}{𝒦u} slA

S⊆SP' {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} x
  Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
  Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP Asc

  γ : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

S⊆SP' {𝓤} {𝓦} {𝒦} {𝑩} (sub{𝑨} sA B≤A) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA
  Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
  Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP Asc

  lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  γ : 𝑩 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = sub{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp (lift-alg-sub-lift 𝑨 B≤A)

S⊆SP' {𝓤} {𝓦} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA
  Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
  Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP Asc

  lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B
  γ : 𝑩 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B


S⊆SP'' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S'{𝓤}{𝓦} 𝒦 ⊆ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
S⊆SP'' {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (sbase{𝑨} x) = γ
 where
  lA llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  llA = lift-alg lA (𝓤 ⊔ 𝓦)

  spllA : llA ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  spllA = sbase{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = (𝓤 ⊔ 𝓦)} (pbase x)

  γ : lA ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  γ = siso spllA (sym-≅ lift-alg-≅)

S⊆SP'' {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S'{𝓤}{𝓤} (P'{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP''{𝓤}{𝓤} x
  Asc : 𝑨 IsSubalgebraOfClass (P'{𝓤}{𝓤} 𝒦)
  Asc = S'→subalgebra{𝓤}{P'{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP' Asc
  γ : lA ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  γ = subalgebra→S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P'{𝓤}{𝓦} 𝒦}{lA} lAsc
-- -- S'→subalgebra : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
-- --                {𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑩 ∈ S'{𝓤}{𝓦} 𝒦
-- --               --------------------------------------------------
-- --  →                𝑩 IsSubalgebraOfClass 𝒦

-- S'→subalgebra {𝓤} {𝓦}{𝒦} {𝑩} x = {!!}


S⊆SP'' {𝓤} {𝓦} {𝒦} {𝑩} (sub{𝑨} sA B≤A) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S'{𝓤}{𝓤} (P'{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP''{𝓤}{𝓤} sA
  Asc : 𝑨 IsSubalgebraOfClass (P'{𝓤}{𝓤} 𝒦)
  Asc = S'→subalgebra{𝓤}{P'{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP' Asc

  lAsp : lA ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P'{𝓤}{𝓦} 𝒦}{lA} lAsc

  γ : 𝑩 ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  γ = sub{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp (lift-alg-sub-lift 𝑨 B≤A)

S⊆SP'' {𝓤} {𝓦} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S'{𝓤}{𝓤} (P'{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP''{𝓤}{𝓤} sA
  Asc : 𝑨 IsSubalgebraOfClass (P'{𝓤}{𝓤} 𝒦)
  Asc = S'→subalgebra{𝓤}{P'{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP' Asc

  lAsp : lA ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P'{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B
  γ : 𝑩 ∈ S'{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P'{𝓤}{𝓦} 𝒦)
  γ = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B


lemPS⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →        {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →        ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lemPS⊆SP {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K =
 ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤}{𝓦}{I = I}{𝒜 = 𝒜} (λ i → P-expa (KA i))) , γ
 where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra 𝓤 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  KA : ∀ i → 𝒜 i ∈ 𝒦
  KA = λ i → ∣ snd ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥
  pA : ∀ i → lift-alg (𝒜 i) 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  pA = λ i → pbase (KA i)

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → ∣ SA≤𝒜 i ∣

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift{𝓠 = 𝓤}{𝓤 = 𝓤}{𝓘 = 𝓦} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe B≅SA


lemPS⊆SP' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →        {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →        ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)

lemPS⊆SP' {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K =
 ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (produ{𝓤}{𝓦}{I = I}{𝒜 = 𝒜} (λ i → P'-expa (KA i)) ) , γ
 where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra 𝓤 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  KA : ∀ i → 𝒜 i ∈ 𝒦
  KA = λ i → ∣ snd ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥
  pA : ∀ i → lift-alg (𝒜 i) 𝓦 ∈ P'{𝓤}{𝓦} 𝒦
  pA = λ i → pbase (KA i)

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → ∣ SA≤𝒜 i ∣

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift{𝓠 = 𝓤}{𝓤 = 𝓤}{𝓘 = 𝓦} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe B≅SA

module _ {𝓤 : Universe}{𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} {hfe : hfunext (OV 𝓤)(OV 𝓤)} where

 PS⊆SP'' : (P'{OV 𝓤}{OV 𝓤} (S'{𝓤}{OV 𝓤} 𝒦u)) ⊆ (S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u))
 PS⊆SP'' (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP'' (pbase (slift{𝑨} x)) = γ
  where
   slA : (lift-alg 𝑨 (OV 𝓤)) ∈ S'{𝓤}{OV 𝓤} 𝒦u
   slA = slift x

   splA : (lift-alg 𝑨 (OV 𝓤)) ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   splA = S⊆SP''{𝓤}{OV 𝓤}{𝒦u} slA
   γ : lift-alg (lift-alg 𝑨 (OV 𝓤)) (OV 𝓤) ∈ S'{OV 𝓤}{(OV 𝓤)} (P'{𝓤}{(OV 𝓤)} 𝒦u)
   γ = slift splA

 PS⊆SP'' (pbase {𝑩} (sub{𝑨} sA B≤A)) = γ
  where
   lA lB : Algebra (OV 𝓤) 𝑆
   lA = lift-alg 𝑨 (OV 𝓤)
   lB = lift-alg 𝑩 (OV 𝓤)
   ζ : lB ≤ lA
   ζ = lift-alg-lift-≤-lift 𝑩{𝑨} B≤A
   spA : lA ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   spA = S⊆SP''{𝓤}{OV 𝓤}{𝒦u} (slift sA)
   γ' : (lift-alg 𝑩 (OV 𝓤)) ∈ (S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u))
   γ' = sub{𝓤 = (OV 𝓤)} spA ζ
   γ : lift-alg 𝑩 (OV 𝓤) ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   γ = siso γ' refl-≅


 PS⊆SP'' (pbase (siso{𝑨}{𝑩} x A≅B)) = γ
  where
   lA lB : Algebra (OV 𝓤) 𝑆
   lA = lift-alg 𝑨 (OV 𝓤)
   lB = lift-alg 𝑩 (OV 𝓤)
   ζ : lA ≅ lB
   ζ = lift-alg-iso 𝓤 (OV 𝓤) 𝑨 𝑩 A≅B

   slA : lA ∈ S'{𝓤}{OV 𝓤} 𝒦u
   slA = slift x

   splA : lA ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   splA = S⊆SP'' slA

   γ : (lift-alg 𝑩 (OV 𝓤)) ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   γ = siso splA ζ
 PS⊆SP'' (pliftu x) = slift (PS⊆SP'' x)
 PS⊆SP'' (pliftw x) = slift (PS⊆SP'' x)
 PS⊆SP'' (produ{I}{𝒜} x) = γ
  where
   uw : Universe
   uw = OV 𝓤

   spA : (i : I) → (𝒜 i) ∈ S'{uw}{uw} (P'{𝓤}{uw} 𝒦u)
   spA i = PS⊆SP'' (x i)

   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P'{𝓤}{uw} 𝒦u)
   ξ i = S'→subalgebra{𝒦 = (P'{𝓤}{uw} 𝒦u)} (spA i)

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))
   η' = lemPS⊆SP'{𝓤 = (uw)}{uw}{𝒦 = (P'{𝓤}{uw} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S'{uw}{uw} (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))
   η = subalgebra→S'{𝓤 = (uw)}{𝓦 = uw}{𝒦 = (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S'{uw}{uw} (P'{𝓤}{uw} 𝒦u)
   γ = (S'-mono{𝓤 = (uw)}{𝒦 = (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))}{𝒦' = (P'{𝓤}{uw} 𝒦u)} (P'-idemp')) η

 PS⊆SP'' (prodw{I}{𝒜} x) = γ
  where
   uw : Universe
   uw = OV 𝓤

   spA : (i : I) → (𝒜 i) ∈ S'{uw}{uw} (P'{𝓤}{uw} 𝒦u)
   spA i = PS⊆SP'' (x i)

   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P'{𝓤}{uw} 𝒦u)
   ξ i = S'→subalgebra{𝒦 = (P'{𝓤}{uw} 𝒦u)} (spA i)

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))
   η' = lemPS⊆SP'{𝓤 = (uw)}{uw}{𝒦 = (P'{𝓤}{uw} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S'{uw}{uw} (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))
   η = subalgebra→S'{𝓤 = (uw)}{𝓦 = uw}{𝒦 = (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S'{uw}{uw} (P'{𝓤}{uw} 𝒦u)
   γ = (S'-mono{𝓤 = (uw)}{𝒦 = (P'{uw}{uw} (P'{𝓤}{uw} 𝒦u))}{𝒦' = (P'{𝓤}{uw} 𝒦u)} (P'-idemp')) η
 PS⊆SP'' (pisou{𝑨}{𝑩} pA A≅B) = γ
  where
   spA : 𝑨 ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   spA = PS⊆SP'' pA

   γ : 𝑩 ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   γ = siso{OV 𝓤}{OV 𝓤}{P'{𝓤}{OV 𝓤} 𝒦u}{𝑨}{𝑩} spA A≅B
 PS⊆SP'' (pisow{𝑨}{𝑩} pA A≅B) = γ
  where
   spA : 𝑨 ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   spA = PS⊆SP'' pA

   γ : 𝑩 ∈ S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u)
   γ = siso{OV 𝓤}{OV 𝓤}{P'{𝓤}{OV 𝓤} 𝒦u}{𝑨}{𝑩} spA A≅B



-- The NEW version of PS⊆SP is PS⊆SP''
PS⊆SP' : {𝓤 𝓦 : Universe} {𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
        (hfe : hfunext (𝓤 ⊔ 𝓦)(𝓤 ⊔ 𝓦))
 →      P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (S{𝓤}{𝓤 ⊔ 𝓦} 𝒦u) ⊆ (S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u))

PS⊆SP' {𝓤} {𝓦} {𝒦u} _ (pbase (sbase x)) = sbase (pbase x)
PS⊆SP' {𝓤} {𝓦} {𝒦u} _ (pbase (slift{𝑨} x)) = γ
 where
  slA : (lift-alg 𝑨 (𝓤 ⊔ 𝓦)) ∈ S{𝓤}{𝓤 ⊔ 𝓦} 𝒦u
  slA = slift x

  splA : (lift-alg 𝑨 (𝓤 ⊔ 𝓦)) ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  splA = S⊆SP'{𝓤}{𝓤 ⊔ 𝓦}{𝒦u} slA
  γ : lift-alg (lift-alg 𝑨 (𝓤 ⊔ 𝓦)) (𝓤 ⊔ 𝓦) ∈ S{𝓤 ⊔ 𝓦}{(𝓤 ⊔ 𝓦)} (P{𝓤}{(𝓤 ⊔ 𝓦)} 𝒦u)
  γ = slift splA

PS⊆SP' {𝓤} {𝓦} {𝒦u} _ (pbase {𝑩} (sub{𝑨} sA B≤A)) = γ
 where
  lA lB : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 (𝓤 ⊔ 𝓦)
  lB = lift-alg 𝑩 (𝓤 ⊔ 𝓦)
  ζ : lB ≤ lA
  ζ = lift-alg-lift-≤-lift 𝑩{𝑨} B≤A
  spA : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  spA = S⊆SP'{𝓤}{𝓤 ⊔ 𝓦}{𝒦u} (slift sA)
  γ' : (lift-alg 𝑩 (𝓤 ⊔ 𝓦)) ∈ (S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u))
  γ' = sub{𝓤 = (𝓤 ⊔ 𝓦)} spA ζ
  γ : lift-alg 𝑩 (𝓤 ⊔ 𝓦) ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  γ = siso γ' refl-≅

PS⊆SP' {𝓤} {𝓦} {𝒦u} _ (pbase (siso{𝑨}{𝑩} x A≅B)) = γ -- siso (S⊆SP' (slift x)) (TRANS-≅ ζ lift-alg-≅)
 where
  lA lB : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 (𝓤 ⊔ 𝓦)
  lB = lift-alg 𝑩 (𝓤 ⊔ 𝓦)
  ζ : lA ≅ lB
  ζ = lift-alg-iso 𝓤 (𝓤 ⊔ 𝓦) 𝑨 𝑩 A≅B

  slA : lA ∈ S{𝓤}{𝓤 ⊔ 𝓦} 𝒦u
  slA = slift x

  splA : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  splA = S⊆SP' slA

  γ : (lift-alg 𝑩 (𝓤 ⊔ 𝓦)) ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  γ = siso splA ζ

PS⊆SP' {𝓤} {𝓦} {𝒦u} hfe (plift{𝑨} x) = slift (PS⊆SP'{𝓤}{𝓦}{𝒦u} hfe x)

PS⊆SP' {𝓤} {𝓦} {𝒦u} hfe (prod{I}{𝒜} x) = γ
 where
  uw : Universe
  uw = 𝓤 ⊔ 𝓦
  psA : (i : I) → (𝒜 i) ∈ P{uw}{uw} (S{𝓤}{uw} 𝒦u)
  psA i = x i
  spA : (i : I) → (𝒜 i) ∈ S{uw}{uw} (P{𝓤}{uw} 𝒦u)
  spA i = PS⊆SP'{𝓤}{𝓦}{𝒦u} hfe (psA i)

  ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{uw} 𝒦u)
  ξ i = S→subalgebra{𝒦 = (P{𝓤}{uw} 𝒦u)} (spA i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
  η' = lemPS⊆SP{𝓤 = (uw)}{uw}{𝒦 = (P{𝓤}{uw} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

  η : ⨅ 𝒜 ∈ S{uw}{uw} (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
  η = subalgebra→S{𝓤 = (uw)}{𝓦 = uw}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

  γ : ⨅ 𝒜 ∈ S{uw}{uw} (P{𝓤}{uw} 𝒦u)
  γ = (S-mono{𝓤 = (uw)}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝒦' = (P{𝓤}{uw} 𝒦u)} (P-idemp'{𝓦 = 𝓦})) η

PS⊆SP' {𝓤} {𝓦} {𝒦u} hfe (piso{𝑨}{𝑩} pA A≅B) = γ
 where
  spA : 𝑨 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  spA = PS⊆SP' {𝓤} {𝓦 = (𝓤 ⊔ 𝓦)} {𝒦u} hfe pA

  γ : 𝑩 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u)
  γ = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓤 ⊔ 𝓦} 𝒦u}{𝑨}{𝑩} spA A≅B


module _
 {𝓤 𝓦 : Universe}
 {𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 {hfe' : hfunext 𝓤 𝓤}
 {hfe'' : hfunext (OV 𝓤) 𝓤}
 {hfe : hfunext (OV 𝓤) (OV 𝓤)} where

 ℑs : (OV 𝓤) ̇
 ℑs = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ (S{𝓤}{𝓤} 𝒦u)

 ℑ→A : (i : ℑs) → Algebra 𝓤 𝑆
 ℑ→A i = ∣ i ∣

 class-product : Algebra (OV 𝓤) 𝑆
 class-product = ⨅ ℑ→A

 class-prod-s : Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-prod-s 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ S{𝓤}{𝓤} 𝒦))) → ∣ i ∣))


 class-prod-s-∈-ps : class-prod-s 𝒦u ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦u))
 class-prod-s-∈-ps = γ
  where
   I : (OV 𝓤) ̇
   I = ℑs
   𝒜 : I → Algebra 𝓤 𝑆
   𝒜 = ℑ→A
   sA : (i : I) → (𝒜 i) ∈ (S{𝓤}{𝓤} 𝒦u)
   sA i = ∥ i ∥

   lA llA : I → Algebra (OV 𝓤) 𝑆
   lA i =  lift-alg (𝒜 i) (OV 𝓤)
   llA i = lift-alg (lA i) (OV 𝓤)

   slA : (i : I) → (lA i) ∈ (S{𝓤}{(OV 𝓤)} 𝒦u)
   slA i = siso (sA i) lift-alg-≅

   psllA : (i : I) → (llA i) ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{(OV 𝓤)} 𝒦u))
   psllA i = pbase{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} (slA i)

   ps⨅llA : ⨅ llA ∈ P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦u)
   ps⨅llA = prod{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} psllA

   llA≅A : (i : I) → (llA i) ≅ (𝒜 i)
   llA≅A i = Trans-≅ (llA i) (𝒜 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

   ⨅llA≅cpK : ⨅ llA ≅ class-prod-s 𝒦u
   ⨅llA≅cpK = ⨅≅ gfe llA≅A

   γ : class-prod-s 𝒦u ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦u))
   γ = piso{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} ps⨅llA ⨅llA≅cpK

 class-prod-s-∈-sp : class-prod-s 𝒦u ∈ (S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u))
 class-prod-s-∈-sp = PS⊆SP'{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝒦u} hfe class-prod-s-∈-ps

--------------- new ------------------

 ℑs' : (OV 𝓤) ̇
 ℑs' = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ (S'{𝓤}{𝓤} 𝒦u)

 ℑ→A' : (i : ℑs') → Algebra 𝓤 𝑆
 ℑ→A' i = ∣ i ∣

 class-product' : Algebra (OV 𝓤) 𝑆
 class-product' = ⨅ ℑ→A'

 class-prod-s' : Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-prod-s' 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ S'{𝓤}{𝓤} 𝒦))) → ∣ i ∣))

 class-prod-s-∈-ps' : class-prod-s' 𝒦u ∈ (P'{OV 𝓤}{OV 𝓤} (S'{𝓤}{OV 𝓤} 𝒦u))
 class-prod-s-∈-ps' = γ
  where
   I : (OV 𝓤) ̇
   I = ℑs'
   𝒜 : I → Algebra 𝓤 𝑆
   𝒜 = ℑ→A'
   sA : (i : I) → (𝒜 i) ∈ (S'{𝓤}{𝓤} 𝒦u)
   sA i = ∥ i ∥

   lA llA : I → Algebra (OV 𝓤) 𝑆
   lA i =  lift-alg (𝒜 i) (OV 𝓤)
   llA i = lift-alg (lA i) (OV 𝓤)

   slA : (i : I) → (lA i) ∈ (S'{𝓤}{(OV 𝓤)} 𝒦u)
   slA i = siso (sA i) lift-alg-≅

   psllA : (i : I) → (llA i) ∈ (P'{OV 𝓤}{OV 𝓤} (S'{𝓤}{(OV 𝓤)} 𝒦u))
   psllA i = pbase{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} (slA i)

   ps⨅llA : ⨅ llA ∈ P'{OV 𝓤}{OV 𝓤} (S'{𝓤}{OV 𝓤} 𝒦u)
   ps⨅llA = produ{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} psllA

   llA≅A : (i : I) → (llA i) ≅ (𝒜 i)
   llA≅A i = Trans-≅ (llA i) (𝒜 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

   ⨅llA≅cpK : ⨅ llA ≅ class-prod-s' 𝒦u
   ⨅llA≅cpK = ⨅≅ gfe llA≅A

   γ : class-prod-s' 𝒦u ∈ (P'{OV 𝓤}{OV 𝓤} (S'{𝓤}{OV 𝓤} 𝒦u))
   γ = pisou{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} ps⨅llA ⨅llA≅cpK

 class-prod-s-∈-sp' : class-prod-s' 𝒦u ∈ (S'{OV 𝓤}{OV 𝓤} (P'{𝓤}{OV 𝓤} 𝒦u))
 class-prod-s-∈-sp' = PS⊆SP''{hfe = hfe} class-prod-s-∈-ps'


-- ----------------------------------------------------------------------------------------------------
-- --------------------------------------- NEW
-- ------------------------------------------------------------

-- -- S-iso : {𝓤 𝓧 𝓨 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
-- --         {𝑨 : Algebra (𝓤 ⊔ 𝓧) 𝑆} {𝑩 : Algebra (𝓤 ⊔ 𝓨) 𝑆}
-- --  →       𝑨 ∈ S{𝓤}{𝓧} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (sbase{𝑨} x) lAx≅B = siso (sbase x) lA≅B
-- --  where
-- --   lA : Algebra 𝓤 𝑆
-- --   lA = lift-alg 𝑨 𝓤
-- --   lAx : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- --   lAx = lift-alg 𝑨 𝓧
-- --   lA≅lAx : lA ≅ lAx
-- --   lA≅lAx = Trans-≅ lA lAx (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- --   lA≅B : lA ≅ 𝑩
-- --   lA≅B = Trans-≅ lA 𝑩 lA≅lAx lAx≅B
-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (slift{𝑨} x) lAx≅B = siso x A≅B
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 (lift-alg-≅{𝑨 = 𝑨}) lAx≅B

-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (sub{𝑨} x sa≤A) sa≅B = γ
-- --  where
-- --   B≤A : 𝑩 ≤ 𝑨
-- --   B≤A = Iso-≤ 𝑨 𝑩 sa≤A (sym-≅ sa≅B)

-- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- --   γ = sub x B≤A

-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (siso{𝑨} sA A≅sa) sa≅B = γ
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 A≅sa sa≅B

-- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- --   γ = siso sA A≅B
-- -- P-iso : {𝓤 𝓦 𝓧 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
-- --         {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} {𝑩 : Algebra (𝓤 ⊔ 𝓧) 𝑆}
-- --  →       𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P{𝓤}{𝓧} 𝒦
-- -- P-iso {𝓤} {𝓦} {𝓧} {𝒦} {.(lift-alg 𝑨 𝓦)} {𝑩} (pbase{𝑨} x) lAw≅B = γ
-- --  where
-- --   lAx : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- --   lAx = lift-alg 𝑨 𝓧
-- --   lAw : Algebra (𝓤 ⊔ 𝓦) 𝑆
-- --   lAw = lift-alg 𝑨 𝓦
-- --   plAx : lAx ∈ P{𝓤}{𝓧} 𝒦
-- --   plAx = pbase x

-- --   lAx≅lAw : lAx ≅ lAw
-- --   lAx≅lAw = Trans-≅ lAx lAw (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- --   lAx≅B : lAx ≅ 𝑩
-- --   lAx≅B = Trans-≅ lAx 𝑩 lAx≅lAw lAw≅B
-- --   γ : 𝑩 ∈ P{𝓤}{𝓧} 𝒦
-- --   γ = piso plAx lAx≅B

-- -- P-iso {𝓤} {𝓦} {𝓧} {𝒦} {.(lift-alg 𝑨 𝓦)} {𝑩} (plift{𝑨} x) lAw≅B = γ
-- --  where
-- --   lAx : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- --   lAx = lift-alg 𝑨 𝓧
-- --   lAw : Algebra (𝓤 ⊔ 𝓦) 𝑆
-- --   lAw = lift-alg 𝑨 𝓦
-- --   plAx : lAx ∈ P{𝓤}{𝓧} 𝒦
-- --   plAx = plift x

-- --   lAx≅lAw : lAx ≅ lAw
-- --   lAx≅lAw = Trans-≅ lAx lAw (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- --   lAx≅B : lAx ≅ 𝑩
-- --   lAx≅B = Trans-≅ lAx 𝑩 lAx≅lAw lAw≅B

-- --   γ : 𝑩 ∈ P{𝓤}{𝓧} 𝒦
-- --   γ = piso plAx lAx≅B

-- -- P-iso {𝓤} {𝓦} {𝓧} {𝒦} {.((∀ i → fst (𝒜 i)) , (λ f 𝒂 i → snd (𝒜 i) f (λ x₁ → 𝒂 x₁ i)))} {𝑩}(prod{I}{𝒜} x) A≅B = γ
-- --  where
-- --   γ : 𝑩 ∈ P{𝓤}{𝓧} 𝒦
-- --   γ = {!!} -- piso plAx lAx≅B

-- -- P-iso {𝓤} {𝓦} {𝓧} {𝒦} {sa} {𝑩} (piso{𝑨} x x₁) A≅B = γ
-- --  where
-- --   γ : 𝑩 ∈ P{𝓤}{𝓧} 𝒦
-- --   γ = {!!} -- piso plAx lAx≅B










-- -- {.(lift-alg 𝑨 𝓧)} {𝑩} (pbase{𝑨} x) lAx≅B = γ
-- --  where
-- --   lAuw : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- --   lAuw = lift-alg 𝑨 (𝓤 ⊔ 𝓧)
-- --   plAuw : lAuw ∈ P{𝓤}{𝓤 ⊔ 𝓧} 𝒦
-- --   plAuw = pbase x

-- --   lA≅lAx : lA ≅ lAx
-- --   lA≅lAx = Trans-≅ lA lAx (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- --   lAuw≅B : lA ≅ 𝑩
-- --   lAuw≅B = Trans-≅ lA 𝑩 lA≅lAx lAx≅B
-- --   γ : 𝑩 ∈ P{𝓤}{𝓨} 𝒦
-- --   γ = {!!} -- piso plA lA≅B

-- -- P-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (plift{𝑨} x) lAx≅B = {!!} -- piso x A≅B
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 (lift-alg-≅{𝑨 = 𝑨}) lAx≅B

-- -- P-iso {𝓤} {𝓧} {𝓨} {𝒦}
-- --  {.((∀ i → fst (𝒜 i)) , (λ f 𝒂 i → snd (𝒜 i) f (λ x₁ → 𝒂 x₁ i)))}
-- --  {𝑩}(prod{I}{𝒜} x) A≅B = γ
-- --   where
-- -- -- P-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
-- -- --  →        P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦) ⊆ P{𝓤}{𝓦} 𝒦


-- --    lA llA : I → Algebra (𝓤 ⊔ 𝓨) 𝑆
-- --    lA i = lift-alg (𝒜 i) 𝓨
-- --    llA i = lift-alg (lA i) (𝓤 ⊔ 𝓨)

-- --    plA : (i : I) → (lA i) ∈ (P{𝓤}{𝓨} 𝒦)
-- --    plA i = plift (x i)

-- --    ppllA : (i : I) → lift-alg (lA i) (𝓤 ⊔ 𝓨) ∈ P{𝓤 ⊔ 𝓨}{𝓤 ⊔ 𝓨}(P{𝓤}{𝓨} 𝒦)
-- --    ppllA i = pbase (plA i)

-- --    pp⨅llA : ⨅ llA ∈ P{𝓤 ⊔ 𝓨}{𝓧} (P{𝓤}{𝓨} 𝒦)
-- --    pp⨅llA = prod ppllA

-- --    l⨅A : Algebra (𝓤 ⊔ 𝓧 ⊔ 𝓨) 𝑆
-- --    l⨅A = lift-alg (⨅ 𝒜) (𝓤 ⊔ 𝓨)

-- --    -- plA i = plift (x i)
-- --    -- ppllA : (i : I) → (llA i) ∈ P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}(P{𝓤}{𝓤 ⊔ 𝓦} 𝒦)
-- --    -- ppllA i = pbase{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{𝒦 = (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦)} (plA i)
-- --    γ : 𝑩 ∈ P{𝓤}{𝓨} 𝒦
-- --    γ = {!!} -- sub x B≤A

-- -- --     Aiso : (i : I) → (llA i) ≅ (𝒜 i)
-- -- --     Aiso i = Trans-≅ (llA i) (𝒜 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

-- -- --     ⨅llA≅⨅A : ⨅ llA ≅ ⨅ 𝒜
-- -- --     ⨅llA≅⨅A = ⨅≅ gfe Aiso

-- -- --     ⨅llA≅l⨅A : ⨅ llA ≅ l⨅A
-- -- --     ⨅llA≅l⨅A = Trans-≅ (⨅ llA) l⨅A ⨅llA≅⨅A lift-alg-≅

-- -- --     pp⨅llA : (⨅ llA) ∈ P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦)
-- -- --     pp⨅llA = prod ppllA

-- -- --     ppl⨅A : l⨅A ∈ P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦)
-- -- --     ppl⨅A = piso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{𝒦 = (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦)} pp⨅llA ⨅llA≅l⨅A

-- -- --     γ : l⨅A ∈ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦
-- -- --     γ = {!!} -- P-idemp'{𝓦 = 𝓦} ppl⨅A


-- -- P-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (piso{𝑨} pA A≅sa) sa≅B = {!!}
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 A≅sa sa≅B

-- --   γ : 𝑩 ∈ P{𝓤}{𝓨} 𝒦
-- --   γ = {!!} -- piso pA A≅B

-- -- S-iso : {𝓤 𝓧 𝓨 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
-- --         {𝑨 : Algebra (𝓤 ⊔ 𝓧) 𝑆} {𝑩 : Algebra (𝓤 ⊔ 𝓨) 𝑆}
-- --  →       𝑨 ∈ S{𝓤}{𝓧} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (sbase{𝑨} x) lAx≅B = siso (sbase x) lA≅B
-- --  where
-- --   lA : Algebra 𝓤 𝑆
-- --   lA = lift-alg 𝑨 𝓤
-- --   lAx : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- --   lAx = lift-alg 𝑨 𝓧
-- --   lA≅lAx : lA ≅ lAx
-- --   lA≅lAx = Trans-≅ lA lAx (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- --   lA≅B : lA ≅ 𝑩
-- --   lA≅B = Trans-≅ lA 𝑩 lA≅lAx lAx≅B
-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (slift{𝑨} x) lAx≅B = siso x A≅B
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 (lift-alg-≅{𝑨 = 𝑨}) lAx≅B

-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (sub{𝑨} x sa≤A) sa≅B = γ
-- --  where
-- --   B≤A : 𝑩 ≤ 𝑨
-- --   B≤A = Iso-≤ 𝑨 𝑩 sa≤A (sym-≅ sa≅B)

-- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- --   γ = sub x B≤A

-- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (siso{𝑨} sA A≅sa) sa≅B = γ
-- --  where
-- --   A≅B : 𝑨 ≅ 𝑩
-- --   A≅B = Trans-≅ 𝑨 𝑩 A≅sa sa≅B

-- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- --   γ = siso sA A≅B

-- -- --  where
-- -- --   lA : Algebra 𝓤 𝑆
-- -- --   lA = lift-alg 𝑨 𝓤
-- -- --   lAx : Algebra (𝓤 ⊔ 𝓧) 𝑆
-- -- --   lAx = lift-alg 𝑨 𝓧
-- -- --   lA≅lAx : lA ≅ lAx
-- -- --   lA≅lAx = Trans-≅ lA lAx (sym-≅ (lift-alg-≅{𝑨 = 𝑨})) (lift-alg-≅{𝑨 = 𝑨})
-- -- --   lA≅B : lA ≅ 𝑩
-- -- --   lA≅B = Trans-≅ lA 𝑩 lA≅lAx lAx≅B
-- -- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {.(lift-alg 𝑨 𝓧)} {𝑩} (slift{𝑨} x) lAx≅B = siso x A≅B
-- -- --  where
-- -- --   A≅B : 𝑨 ≅ 𝑩
-- -- --   A≅B = Trans-≅ 𝑨 𝑩 (lift-alg-≅{𝑨 = 𝑨}) lAx≅B

-- -- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (sub{𝑨} x sa≤A) sa≅B = γ
-- -- --  where
-- -- --   B≤A : 𝑩 ≤ 𝑨
-- -- --   B≤A = Iso-≤ 𝑨 𝑩 sa≤A (sym-≅ sa≅B)

-- -- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- -- --   γ = sub x B≤A

-- -- -- S-iso {𝓤} {𝓧} {𝓨} {𝒦} {sa} {𝑩} (siso{𝑨} sA A≅sa) sa≅B = γ
-- -- --  where
-- -- --   A≅B : 𝑨 ≅ 𝑩
-- -- --   A≅B = Trans-≅ 𝑨 𝑩 A≅sa sa≅B

-- -- --   γ : 𝑩 ∈ S{𝓤}{𝓨} 𝒦
-- -- --   γ = siso sA A≅B


