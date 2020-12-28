\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 23 Dec 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂; Π)

module closure-exp-new
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
data hclo {𝓤 𝓦 𝓘 : Universe}(𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) :
 Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ hclo 𝒦
  hlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ hclo{𝓤}{𝓦}{𝓘} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ hclo 𝒦
  himg  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ hclo{𝓤}{𝓦}{𝓘} 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ hclo 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ hclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ hclo 𝒦

--Closure wrt S
data sclo {𝓤 𝓦 𝓘 : Universe}(𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) :
 Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ sclo 𝒦
  slift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
  sub   : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → (sa : SUBALGEBRA 𝑨) → ∣ sa ∣ ∈ sclo 𝒦
  siso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ sclo 𝒦

--Closure wrt P
data pclo {𝓤 𝓦 𝓘 : Universe} (𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆) (OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) :
 Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆) (OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
  pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ pclo 𝒦
  plift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦 → (lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘)) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦
  prod  : {I : 𝓘 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i →  (𝒜 i) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦) → ⨅ 𝒜 ∈ pclo 𝒦
  piso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ pclo 𝒦

data vclo {𝓤 𝓦 𝓘 : Universe}(𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) :
 Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
  vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ vclo 𝒦
  vlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦 → (lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘)) ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦
  vhimg : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ vclo 𝒦
  vsub  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦 → (sa : Subalgebra 𝑨) → ∣ sa ∣ ∈ vclo 𝒦
  vprod : {I : 𝓘 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦) → ⨅ 𝒜 ∈ vclo 𝒦
  viso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ vclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ vclo 𝒦



--Closure wrt H
data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  hlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  himg  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦

--Closure wrt S
data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  slift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  sub   : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦
  siso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦

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

--Closure wrt H
data H' {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H'{𝓤}{𝓦} 𝒦
  hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H'{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H'{𝓤}{𝓦} 𝒦
  himg  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ H'{𝓤}{𝓤} 𝒦 → 𝑩 is-hom-image-of 𝑨 → lift-alg 𝑩 𝓤 ∈ H'{𝓤}{𝓦} 𝒦
  hiso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ H'{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 𝓤 ∈ H'{𝓤}{𝓦} 𝒦

--Closure wrt S
data S' {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S'{𝓤}{𝓦} 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S'{𝓤}{𝓦} 𝒦
  sub   : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → lift-alg 𝑩 𝓤 ∈ S'{𝓤}{𝓦} 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 𝓤  ∈ S'{𝓤}{𝓦} 𝒦

--Closure wrt P
data P' {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P'{𝓤}{𝓦} 𝒦
  plift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P'{𝓤}{𝓦} 𝒦
  prod  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P'{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P'{𝓤}{𝓦} 𝒦
  piso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P'{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P'{𝓤}{𝓦} 𝒦



------------------------
-- data HCLO {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra 𝓤 𝑆) (OV 𝓤) where
--  HBASE : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HCLO 𝒦
--  HIMG : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ HCLO 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HCLO 𝒦

-- --Closure wrt S
-- data SCLO (𝓤 𝓦 : Universe){𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝒦' : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦))} : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
--  SBASE : {𝑨 :  Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ SCLO 𝓤 𝓦
--  SBASE' : {𝑨 :  Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ 𝒦' → 𝑨 ∈ SCLO 𝓤 𝓦
--  SUB : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆}{𝑩 : Algebra 𝓦 𝑆} → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ SCLO 𝓤 𝓦{𝒦}{𝒦'} → 𝑩 ≤ 𝑨 → lift-alg 𝑩 (𝓤 ⊔ 𝓦) ∈ SCLO 𝓤 𝓦

-- data P {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
--  Pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
--  Plift : {𝑨 : Algebra 𝓤 𝑆} → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
--  Pprod : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → lift-alg (𝒜 i) (𝓤 ⊔ 𝓦) ∈ P 𝒦) → ⨅ 𝒜 ∈ P 𝒦

lift-alg-idemp : {𝓤 𝓦 𝓘 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
lift-alg-idemp {𝓤} {𝓦} {𝓘} {𝑨} = TRANS-≅ (TRANS-≅ ζ lift-alg-≅) lift-alg-≅
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅


--P is a closure operator ----------------------------------------
--In particular, it's expansive...
P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ P{𝓤}{𝓤} 𝒦
P-expa{𝓤}{𝒦} {𝑨} KA = piso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

-- ...and idempotent.
P'-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P'{𝓤}{𝓦} (P'{𝓤}{𝓤} 𝒦) ⊆ P'{𝓤}{𝓦} 𝒦
P'-idemp {𝓤} {𝓦} {𝒦} x = {!!}


P-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦) ⊆ P{𝓤}{𝓦} 𝒦
P-idemp {𝓤} {𝓦} {𝒦} (pbase x) = plift x
P-idemp {𝓤} {𝓦} {𝒦} (plift x) = plift (P-idemp x)
P-idemp {𝓤} {𝓦} {𝒦} (prod x) = prod (λ i → P-idemp (x i))
P-idemp {𝓤} {𝓦} {𝒦} (piso x x₁) = piso (P-idemp x) x₁


--S is a closure operator -------------------------------------------
--In particular, it's monotone.
S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'
S-mono ante (sbase x) = sbase (ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S-mono{𝓤}{𝓤} ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (sub{𝑨}{𝑩} sA B≤A) = sub (S-mono ante sA) B≤A
S-mono {𝒦} {𝒦'} ante (siso x x₁) = siso (S-mono ante x) x₁

S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦)
S⊆SP{𝓤}{𝓦}{𝒦} = S-mono{𝒦 = 𝒦}{𝒦' = (P{𝓤}{𝓤} 𝒦)} P-expa


subalgebra→S' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
             ----------------------------------------------------------
 →                  𝑪 ∈ S'{𝓤}{𝓦} 𝒦

subalgebra→S' {𝓤}{𝓦}{𝒦}{𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = {!!}

-- For a given algebra 𝑨, and class 𝒦 of algebras, we will find the following fact useful
-- (e.g., in proof of Birkhoff's HSP theorem):  𝑨 ∈ S 𝒦  ⇔  𝑨 IsSubalgebraOfClass 𝒦
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




S→subalgebra' : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S'{𝓤}{𝓤} 𝒦
              --------------------------------------------------
 →                𝑩 IsSubalgebraOfClass 𝒦
S→subalgebra' {𝓤} {𝒦}{𝑩} x = {!!}


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

lemPS⊆SP' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →        {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →        ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
lemPS⊆SP'{𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K = {!!}

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















--alternatives-----------------------------
module _
 {𝓤 𝓦 𝓘 : Universe}
 {𝒦 𝒦' : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

 --sclo is a closure operator
 --In particular, it's monotone.
 sclo-mono : 𝒦 ⊆ 𝒦' → sclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ sclo{𝓤}{𝓦}{𝓘} 𝒦'
 sclo-mono ant (sbase x) = sbase (ant x)
 sclo-mono ant (slift x) = slift (sclo-mono ant x)
 sclo-mono ant (sub x sa) = sub (sclo-mono ant x) sa
 sclo-mono ant (siso x x₁) = siso (sclo-mono ant x) x₁




module _ {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

 --pclo is a closure operator
 --In particular, it's idempotent and expansive.
 pclo-idemp : pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
 pclo-idemp (pbase x) = x
 pclo-idemp (plift x) = plift (pclo-idemp x)
 pclo-idemp (prod x) = prod (λ i → pclo-idemp (x i))
 pclo-idemp (piso x x₁) = piso (pclo-idemp x) x₁

 pclo-expa : 𝒦 ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
 pclo-expa x = pbase x

 --By monotonicity of sclo and expansivity of pclo, S ⊆ SP.
 s⊆sp : sclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
 s⊆sp = sclo-mono{𝒦 = 𝒦}{𝒦' = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} pclo-expa

 pclo⊆vclo : pclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ vclo{𝓤}{𝓦}{𝓘} 𝒦
 pclo⊆vclo (pbase x) = vbase x
 pclo⊆vclo (plift x) = vlift (pclo⊆vclo x)
 pclo⊆vclo (prod x) = vprod (λ i → pclo⊆vclo (x i))
 pclo⊆vclo (piso x x₁) = viso (pclo⊆vclo x) x₁

 sclo⊆vclo : sclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ vclo{𝓤}{𝓦}{𝓘} 𝒦
 sclo⊆vclo (sbase x) = vbase x
 sclo⊆vclo (slift x) = vlift (sclo⊆vclo x)
 sclo⊆vclo (sub x sa) = vsub (sclo⊆vclo x) sa
 sclo⊆vclo (siso x x₁) = viso (sclo⊆vclo x) x₁

 sp⊆v : sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ vclo{𝓤}{𝓦}{𝓘} 𝒦
 sp⊆v (sbase (pbase x)) = vbase x
 sp⊆v (sbase (plift{𝑨} x)) = pclo⊆vclo (plift x)
 sp⊆v (sbase (prod x)) = pclo⊆vclo (prod x)
 sp⊆v (sbase (piso x x₁)) = pclo⊆vclo (piso x x₁)
 sp⊆v (slift x) = vlift (sp⊆v x)
 sp⊆v (sub x sa) = vsub (sp⊆v x) sa
 sp⊆v (siso x x₁) = viso (sp⊆v x) x₁








-- module _ {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

--  --NOTATION: use 𝔞 to denote for universe 𝓤 ⊔ 𝓦 ⊔ 𝓘
--  𝔞 : Universe
--  𝔞 = 𝓤 ⊔ 𝓦 ⊔ 𝓘

--  -- For a given algebra 𝑨, and class 𝒦 of algebras, we will find the following fact useful
--  -- (e.g., in proof of Birkhoff's HSP theorem):  𝑨 ∈ SClo 𝒦  ⇔  𝑨 IsSubalgebraOfClass 𝒦
--  subalgebra→sclo : {𝑪 : Algebra 𝔞 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
--                    ----------------------------------------------------------
--   →                         𝑪 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦

--  subalgebra→sclo {𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = sub (sbase KA) (𝑪 , Iso-≤ 𝑨 𝑪 B≤A C≅B)
--   where
--    C≤A : 𝑪 ≤ 𝑨
--    C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

--    CsubA : SUBALGEBRA 𝑨
--    CsubA = 𝑪 , C≤A

--    scloA : 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
--    scloA = sbase KA

--    γ : 𝑪 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
--    γ = sub scloA CsubA

--  sclo→subalgebra : {𝑩 : Algebra 𝔞 𝑆} → 𝑩 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
--                    -------------------------------------------------------
--   →                          𝑩 IsSubalgebraOfClass 𝒦

--  sclo→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , refl-≅
--  sclo→subalgebra (slift{𝑩} x) = 𝑨 , SA , KA , trans-≅ lB 𝑩 ∣ SA ∣ (sym-≅ lift-alg-≅) B≅SA
--   where
--    lB : Algebra 𝔞 𝑆
--    lB = lift-alg 𝑩 𝔞
--    BsubK : 𝑩 IsSubalgebraOfClass 𝒦
--    BsubK = sclo→subalgebra x
--    𝑨 : Algebra 𝔞 𝑆
--    𝑨 = ∣ BsubK ∣
--    SA : SUBALGEBRA 𝑨
--    SA = fst ∥ BsubK ∥
--    KA : 𝑨 ∈ 𝒦
--    KA = ∣ snd ∥ BsubK ∥ ∣
--    B≅SA : 𝑩 ≅ ∣ SA ∣
--    B≅SA = ∥ snd ∥ BsubK ∥ ∥

--  sclo→subalgebra (sub{𝑩} x sa) = γ
--   where
--    BsubK : 𝑩 IsSubalgebraOfClass 𝒦
--    BsubK = sclo→subalgebra x
--    𝑨 : Algebra 𝔞 𝑆
--    𝑨 = ∣ BsubK ∣
--    KA : 𝑨 ∈ 𝒦
--    KA = ∣ snd ∥ BsubK ∥ ∣
--    SA : SUBALGEBRA 𝑨
--    SA = fst ∥ BsubK ∥
--    B≅SA : 𝑩 ≅ ∣ SA ∣
--    B≅SA = ∥ snd ∥ BsubK ∥ ∥
--    B≤A : 𝑩 ≤ 𝑨
--    B≤A = Iso-≤ 𝑨 𝑩 ∥ SA ∥ B≅SA
--    saa : SUBALGEBRA 𝑨
--    saa = ∣ sa ∣ , Trans-≤ 𝑨 ∣ sa ∣ B≤A ∥ sa ∥
--    γ : ∣ sa ∣ IsSubalgebraOfClass 𝒦
--    γ = 𝑨 , saa , KA , refl-≅

--  sclo→subalgebra (siso{𝑨}{𝑩} sA A≅B) = γ
--   where
--    lB : Algebra _ 𝑆
--    lB = lift-alg 𝑩 𝔞
--    IH : 𝑨 IsSubalgebraOfClass 𝒦
--    IH = sclo→subalgebra sA
--    𝔸 : Algebra _ 𝑆
--    𝔸 = ∣ IH ∣
--    SA : SUBALGEBRA 𝔸
--    SA = fst ∥ IH ∥
--    𝔸∈𝒦 : 𝔸 ∈ 𝒦
--    𝔸∈𝒦 = fst ∥ snd IH ∥
--    A≅SA : 𝑨 ≅ ∣ SA ∣
--    A≅SA = snd ∥ snd IH ∥
--    lB≅sa : lift-alg 𝑩 𝔞 ≅ ∣ SA ∣
--    lB≅sa = TRANS-≅ (TRANS-≅ (sym-≅ lift-alg-≅) (sym-≅ A≅B)) A≅SA
--    γ : lift-alg 𝑩 𝔞 IsSubalgebraOfClass 𝒦
--    γ = 𝔸 , SA , 𝔸∈𝒦 , lB≅sa

--  lemps⊆sp : hfunext 𝓘 𝔞
--   →         {I : 𝓘 ̇}{ℬ : I → Algebra 𝔞 𝑆}
--   →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
--            ----------------------------------------------------
--   →         ⨅ ℬ IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)

--  lemps⊆sp hfe {I}{ℬ} ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤}{𝓦}{𝓘}{I = I}{𝒜 = 𝒜} pclo𝒜) , γ
--   where
--    𝒜 : I → Algebra 𝔞 𝑆
--    𝒜 = λ i → ∣ ℬ≤𝒦 i ∣

--    SA : I → Algebra 𝔞 𝑆
--    SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣

--    𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
--    𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣

--    ℬ≅SA : ∀ i → ℬ i ≅ SA i
--    ℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥
--    pclo𝒜 : ∀ i → (𝒜 i) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦
--    pclo𝒜 = λ i → pbase (𝒦𝒜 i)

--    SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
--    SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣

--    h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
--    h = λ i → ∣ SA≤𝒜 i ∣

--    ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
--    ⨅SA≤⨅𝒜 = i , ii , iii
--     where
--      i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
--      i = λ x i → (h i) (x i)
--      ii : is-embedding i
--      ii = embedding-lift{𝓠 = 𝔞}{𝓤 = 𝔞}{𝓘 = 𝓘} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
--      iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
--      iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
--    γ : ⨅ ℬ ≅ ⨅ SA
--    γ = ⨅≅ gfe ℬ≅SA

-- module _ {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

--  --NOTATION: use 𝔞 to denote for universe 𝓤 ⊔ 𝓦 ⊔ 𝓘
--  𝔄 : Universe
--  𝔄 = 𝓤 ⊔ 𝓦 ⊔ 𝓘

--  ps⊆sp : hfunext 𝓘 𝔄
--   →      pclo{𝓤}{𝓦}{𝓘} (sclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)

--  ps⊆sp _ (pbase {𝑨} (sbase x)) = sbase (pbase x)
--  ps⊆sp _ (pbase {.(lift-alg 𝑨 𝔄)} (slift{𝑨} x)) = slift (s⊆sp x)
--  ps⊆sp _ (pbase {.(𝑩)} (sub{𝑨} x (𝑩 , B≤A))) = sub (s⊆sp x) (𝑩 , B≤A)
--  ps⊆sp _ (pbase {.(lift-alg 𝑩 𝔄)} (siso{𝑨}{𝑩} x A≅B)) = siso (s⊆sp x) A≅B
--  ps⊆sp hfe (plift x) = slift (ps⊆sp hfe x)
--  ps⊆sp hfe  (prod{I = I}{𝒜 = 𝒜} x) = γ
--   where
--    ⨅A : Algebra 𝔄 𝑆
--    ⨅A = ⨅ 𝒜

--    ζ : (i : I) → (𝒜 i) ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
--    ζ i = ps⊆sp hfe (x i)

--    ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
--    ξ i = sclo→subalgebra{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} (ζ i)

--    η' : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦))
--    η' = lemps⊆sp{𝓤}{𝓦}{𝓘}{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} hfe {I = I}{ℬ = 𝒜} ξ

--    pci : pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
--    pci = pclo-idemp

--    η : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
--    η = mono-≤ (⨅ 𝒜) pci η'

--    γ : ⨅ 𝒜 ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
--    γ = subalgebra→sclo{𝓤}{𝓦}{𝓘}{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)}{𝑪 = ⨅ 𝒜} η

--  ps⊆sp hfe (piso x x₁) = siso (ps⊆sp hfe x) x₁



module _ {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} {𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} where

 subalgebra-of-class-idem : 𝑩 IsSubalgebraOfClass (P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦))
  →                         𝑩 IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
 subalgebra-of-class-idem x = mono-≤ 𝑩 P-idemp x

 subalgebra-of-class-drop : 𝑩 IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  →                         𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
 subalgebra-of-class-drop (𝑨 , SA , x , B≅SA) = {!!}

 subalgebra-of-class-idemdrop : 𝑩 IsSubalgebraOfClass (P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦))
  →                             𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
 subalgebra-of-class-idemdrop = subalgebra-of-class-drop ∘ subalgebra-of-class-idem

  -- η' : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u))
  -- η' = lemPS⊆SP{𝓤}{𝓦}{𝒦 = (P{𝓤}{𝓤} 𝒦u)}{hfe'}{I = I}{ℬ = 𝒜} ξ

  -- η : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦u)
  -- η = subalgebra-of-class-idemdrop η' -- mono-≤ (⨅ 𝒜) pci η'
 -- (.(lift-alg 𝑨 𝓦) , SA , pbase{𝑨} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (.(lift-alg 𝑨 𝓦) , SA , plift{𝑨} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (.(⨅ 𝒜) , SA , prod{I}{𝒜} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (𝑨 , SA , piso x x₁ , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (.(lift-alg 𝑨 𝓦) , SA , pbase{𝑨} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (.(lift-alg 𝑨 𝓦) , SA , plift{𝑨} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (.(⨅ 𝒜) , SA , prod{I}{𝒜} x , B≅SA) = {!!}
 -- subalgebra-of-class-idemdrop (𝑨 , SA , piso x x₁ , B≅SA) = {!!}




  -- η' : ⨅ 𝒜 
  -- η' = lemPS⊆SP{𝓤}{𝓦}{𝒦 = (P{𝓤}{𝓤} 𝒦u)}{hfe'}{I = I}{ℬ = 𝒜} ξ

  -- pci : P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u) ⊆ P{𝓤}{𝓦} 𝒦u
  -- pci = P-idemp

  -- η : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦u)
  -- η = {!!} -- mono-≤ (⨅ 𝒜) pci η'

 -- PS⊆SP'' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 --           (hfe : hfunext 𝓤 𝓤)(hfe' : hfunext 𝓦 𝓤)
 --  →        (P'{𝓤}{𝓦} (S'{𝓤}{𝓤} 𝒦u)) ⊆ (S'{𝓤}{𝓦} (P'{𝓤}{𝓤} 𝒦u))
 -- PS⊆SP'' = ?


PS⊆SP' : {𝓤 𝓦 : Universe} {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
        (hfe : hfunext 𝓤 𝓤) (hfe' : hfunext 𝓦 𝓤)
 →      (P'{𝓤}{𝓦}(S'{𝓤}{𝓤} 𝒦)) ⊆ (S'{𝓤}{𝓦} (P'{𝓤}{𝓤} 𝒦))
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (pbase {.(lift-alg 𝑨 𝓤)} (sbase{𝑨} x)) = sbase (pbase x)
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (pbase {.(lift-alg 𝑨 𝓤)} (slift{𝑨} x)) = {!γ!}
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (pbase {.(lift-alg 𝑩 𝓤)} (sub{𝑨}{𝑩} x x₁)) = {!!}
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (pbase {.(lift-alg 𝑩 𝓤)} (siso{𝑨}{𝑩} x x₁)) = {!!}
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (plift{𝑨} x) = {!!}
PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (prod{I}{𝒜} x) = {!γ!}
 where
  ⨅A : Algebra (𝓤 ⊔ 𝓦) 𝑆
  ⨅A = ⨅ 𝒜

  ζ : (i : I) → 𝒜 i ∈ S'{𝓤}{𝓤} (P'{𝓤}{𝓤} 𝒦)
  ζ i = PS⊆SP' hfe hfe (x i)

  ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P'{𝓤}{𝓤} 𝒦)
  ξ i = S→subalgebra'{𝒦 = (P'{𝓤}{𝓤} 𝒦)} (ζ i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (P'{𝓤}{𝓦} (P'{𝓤}{𝓤} 𝒦))
  η' = lemPS⊆SP'{𝓤}{𝓦}{𝒦 = (P'{𝓤}{𝓤} 𝒦)}{hfe'}{I = I}{ℬ = 𝒜} ξ

  -- η : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
  -- η = subalgebra-of-class-idemdrop η'
  η : ⨅ 𝒜 IsSubalgebraOfClass (P'{𝓤}{𝓦} 𝒦)
  η = mono-≤ (⨅ 𝒜) P'-idemp η'

  -- I'm very surprised this satisfies the goal... 
  γ : ⨅ 𝒜 ∈ S'{𝓤 ⊔ 𝓦}{𝓦} (P'{𝓤}{𝓦} 𝒦)
  γ = subalgebra→S'{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦}{𝒦 = (P'{𝓤}{𝓦} 𝒦)}{𝑪 = ⨅ 𝒜} η
  -- ...but it does type-check; indeed, it's the only way I can get the whole
  -- program to work (i.e., type-check)
  -- (...and I've tried many, many alternative approaches)

PS⊆SP' {𝓤} {𝓦} {𝒦} hfe hfe' (piso x x₁) = {!!}






PS⊆SP : {𝓤 𝓦 : Universe} {𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
        (hfe : hfunext 𝓤 𝓤) (hfe' : hfunext 𝓦 𝓤)
 →      (P{𝓤}{𝓦}(S{𝓤}{𝓤} 𝒦u)) ⊆ (S{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u))
PS⊆SP _ _ (pbase (sbase x)) = sbase (pbase x)
PS⊆SP {𝓤}{𝓦}{𝒦u} _ _ (pbase (slift{𝑨} x)) = γ
 where
  spA : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦u)
  spA = S⊆SP{𝓤}{𝓤}{𝒦u} x
  A≅llA : 𝑨 ≅ lift-alg (lift-alg 𝑨 𝓤) 𝓦
  A≅llA = TRANS-≅ lift-alg-≅ lift-alg-≅
  γ : (lift-alg (lift-alg 𝑨 𝓤) 𝓦) ∈ S{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u)
  γ = siso spA A≅llA

PS⊆SP {𝓤}{𝓦}{𝒦u} _ _ (pbase{𝑩} (sub{𝑨} sA B≤A)) = sub spA lB≤A
 where
  lB : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lB = lift-alg 𝑩 𝓦
  lB≤A : lB ≤ 𝑨
  lB≤A = trans-≤-≅ 𝑩 {𝑨} lB B≤A lift-alg-≅
  spA : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦u)
  spA = S-mono {𝒦 = 𝒦u}{𝒦' = (P{𝓤}{𝓤} 𝒦u)} P-expa sA

PS⊆SP _ _ (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP x) (TRANS-≅ A≅B lift-alg-≅)
PS⊆SP {𝓤}{𝓦}{𝒦u} hfe  hfe' (plift{𝑨} x) = siso spA lift-alg-≅
 where
  spA : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦u)
  spA = PS⊆SP hfe hfe x
PS⊆SP {𝓤}{𝓦}{𝒦u} hfe hfe' (prod{I}{𝒜} x) = γ
 where

  ⨅A : Algebra (𝓤 ⊔ 𝓦) 𝑆
  ⨅A = ⨅ 𝒜

  ζ : (i : I) → 𝒜 i ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦u)
  ζ i = PS⊆SP hfe hfe (x i)

  ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦u)
  ξ i = S→subalgebra{𝒦 = (P{𝓤}{𝓤} 𝒦u)} (ζ i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u))
  η' = lemPS⊆SP{𝓤}{𝓦}{𝒦 = (P{𝓤}{𝓤} 𝒦u)}{hfe'}{I = I}{ℬ = 𝒜} ξ

  η : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦u)
  η = subalgebra-of-class-idemdrop η'
  -- η : ⨅ 𝒜 IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦u)
  -- η = mono-≤ (⨅ 𝒜) P-idemp η'

  γ : ⨅ 𝒜 ∈ S{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦u)
  γ = subalgebra→S{𝓤}{𝓦}{𝒦 = (P{𝓤}{𝓤} 𝒦u)}{𝑪 = ⨅ 𝒜} η

PS⊆SP {𝓤}{𝓦}{𝒦u} hfe hfe' (piso{𝑨}{𝑩} psA A≅B) = siso{𝒦 = (P{𝓤}{𝓤} 𝒦u)}{𝑨 = 𝑨}{𝑩 = 𝑩} spA A≅B
 where
  spA : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦u)
  spA = PS⊆SP{𝓤}{𝓤}{𝒦u} hfe hfe psA
 -- PS⊆SP (pbase{lA} (sbase{𝑨} x)) = sbase (pbase x)
 -- PS⊆SP (pbase (sub{𝑨} x (𝑩 , B≤A))) = {!!} -- sub (S⊆SP x) (𝑩 , B≤A) -- (pbase (sub x x₁)) = 
 -- PS⊆SP (pbase (siso x x₁)) = {!!}
 -- PS⊆SP (prod x) = {!!}
 -- PS⊆SP (piso x x₁) = {!!}

 -- ps⊆sp _ (pbase {𝑨} (sbase x)) = sbase (pbase x)
 -- ps⊆sp _ (pbase {.(lift-alg 𝑨 𝔄)} (slift{𝑨} x)) = slift (s⊆sp x)
 -- ps⊆sp _ (pbase {.(𝑩)} (sub{𝑨} x (𝑩 , B≤A))) = sub (s⊆sp x) (𝑩 , B≤A)
 -- ps⊆sp _ (pbase {.(lift-alg 𝑩 𝔄)} (siso{𝑨}{𝑩} x A≅B)) = siso (s⊆sp x) A≅B
 -- ps⊆sp hfe (plift x) = slift (ps⊆sp hfe x)
 -- ps⊆sp hfe  (prod{I = I}{𝒜 = 𝒜} x) = γ
 --  where
 --   ⨅A : Algebra 𝔄 𝑆
 --   ⨅A = ⨅ 𝒜

 --   ζ : (i : I) → (𝒜 i) ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
 --   ζ i = ps⊆sp hfe (x i)

 --   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
 --   ξ i = sclo→subalgebra{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} (ζ i)

 --   η' : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦))
 --   η' = lemps⊆sp{𝓤}{𝓦}{𝓘}{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} hfe {I = I}{ℬ = 𝒜} ξ

 --   pci : pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
 --   pci = pclo-idemp

 --   η : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
 --   η = mono-≤ (⨅ 𝒜) pci η'

 --   γ : ⨅ 𝒜 ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
 --   γ = subalgebra→sclo{𝓤}{𝓦}{𝓘}{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)}{𝑪 = ⨅ 𝒜} η

 -- ps⊆sp hfe (piso x x₁) = siso (ps⊆sp hfe x) x₁

module _
 {𝓤 𝓦 : Universe}
 {𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 {hfe : hfunext 𝓤 𝓤}
 {hfe' : hfunext (OV 𝓤) 𝓤} where

 ℑs : (OV 𝓤) ̇
 ℑs = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ (S{𝓤}{𝓤} 𝒦u)

 ℑ→A : (i : ℑs) → Algebra 𝓤 𝑆
 ℑ→A i = ∣ i ∣

 class-product : Algebra (OV 𝓤) 𝑆
 class-product = ⨅ ℑ→A

 class-prod-s : Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-prod-s 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ S{𝓤}{𝓤} 𝒦))) → ∣ i ∣))

 transport-class : {𝓘 : Universe}(𝓙 : Universe) → Pred (Algebra 𝓘 𝑆)(OV 𝓘) → Pred (Algebra 𝓙 𝑆) ((OV 𝓘) ⊔ 𝓙)
 transport-class {𝓘} 𝓙 𝒦 = λ (𝑨' : Algebra 𝓙 𝑆) → Σ 𝑨 ꞉ (Algebra 𝓘 𝑆) , (𝑨 ∈ 𝒦) × ((lift-alg 𝑨 (𝓘 ⊔ 𝓙)) ≅ (lift-alg 𝑨' (𝓘 ⊔ 𝓙)))

 class-prod-s-∈-ps : class-prod-s 𝒦u ∈ (P{𝓤}{OV 𝓤} (S{𝓤}{𝓤} 𝒦u))
 class-prod-s-∈-ps = prod{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝒦 = (S{𝓤}{𝓤} 𝒦u)}{I = I}{𝒜 = 𝒜} psA
  where
   I : (OV 𝓤) ̇
   I = ℑs
   𝒜 : I → Algebra 𝓤 𝑆
   𝒜 = ℑ→A
   sA : (i : I) → (𝒜 i) ∈ (S{𝓤}{𝓤} 𝒦u)
   sA i = ∥ i ∥
   pslA : (i : I) → lift-alg (𝒜 i) 𝓤 ∈ (P{𝓤}{𝓤} (S{𝓤}{𝓤} 𝒦u))
   pslA i = pbase (sA i)
   psA : (i : I) → (𝒜 i) ∈ (P{𝓤}{𝓤} (S{𝓤}{𝓤} 𝒦u))
   psA i = piso (pslA i) (sym-≅ lift-alg-≅)

 class-prod-s-∈-sp : class-prod-s 𝒦u ∈ (S{𝓤}{OV 𝓤} (P{𝓤}{𝓤} 𝒦u))
 class-prod-s-∈-sp = PS⊆SP{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝒦u} hfe hfe' class-prod-s-∈-ps

 ℑs' : (OV 𝓤) ̇
 ℑs' = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ (S'{𝓤}{𝓤} 𝒦u)

 ℑ→A' : (i : ℑs') → Algebra 𝓤 𝑆
 ℑ→A' i = ∣ i ∣

 class-prod-s' : Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-prod-s' 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ S'{𝓤}{𝓤} 𝒦))) → ∣ i ∣))

 class-prod-s-∈-ps' : class-prod-s' 𝒦u ∈ (P'{𝓤}{OV 𝓤} (S'{𝓤}{𝓤} 𝒦u))
 class-prod-s-∈-ps' = prod{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝒦 = (S'{𝓤}{𝓤} 𝒦u)}{I = I}{𝒜 = 𝒜} psA
  where
   I : (OV 𝓤) ̇
   I = ℑs'
   𝒜 lA : I → Algebra 𝓤 𝑆
   𝒜 = ℑ→A'
   lA i = lift-alg (𝒜 i) 𝓤
   sA : (i : I) → (𝒜 i) ∈ (S'{𝓤}{𝓤} 𝒦u)
   sA i = ∥ i ∥
   pslA : (i : I) → (lA i) ∈ (P'{𝓤}{𝓤} (S'{𝓤}{𝓤} 𝒦u))
   pslA i = pbase{𝓤 = 𝓤}{𝓦 = 𝓤} (sA i)
   psA : (i : I) → (𝒜 i) ∈ (P'{𝓤}{𝓤} (S'{𝓤}{𝓤} 𝒦u))
   psA i = piso{𝓤 = 𝓤}{𝓦 = 𝓤}{𝑨 = (lA i)}{𝑩 = (𝒜 i)} (pslA i) (sym-≅ lift-alg-≅)

 class-prod-s-∈-sp' : class-prod-s' 𝒦u ∈ (S'{𝓤}{OV 𝓤} (P'{𝓤}{𝓤} 𝒦u))
 class-prod-s-∈-sp' = PS⊆SP'{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝒦u} hfe hfe' class-prod-s-∈-ps'





----------------------------------------------------------------------------
----------------        RECENT EXPERIMENTAL STUFF       ---------------------
----------------------------------------------------------------------------

 -- {𝒦+ : Pred (Algebra (OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}
 -- {𝒦all : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}  where
 -- cps : Algebra ((OV 𝓤)⁺) 𝑆
 -- cps = cp (S''{𝓤}{𝓤} 𝒦₀)

 -- 𝓐 𝓤' 𝓦' 𝓘' 𝓐' 𝓞' 𝓥' : Universe
 -- 𝓐 = 𝓤 ⊔ 𝓦 ⊔ 𝓘
 -- -- NOTATION OV 𝓐 = 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓘 ⁺)
 -- 𝓤' = OV 𝓤
 -- 𝓦' = OV 𝓦
 -- 𝓘' = OV 𝓘
 -- 𝓞' = 𝓞 ⁺
 -- 𝓥' = 𝓥 ⁺
 -- 𝓐' = (𝓤' ⊔ 𝓦' ⊔ 𝓘')

 -- cpK₀ : Algebra (OV 𝓐) 𝑆
 -- cpK₀ = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆) , 𝑨 ∈ 𝒦all)) → ∣ i ∣))


 -- cp'' : Pred (Algebra (OV 𝓤) 𝑆)((OV 𝓤)⁺) → Algebra ((OV 𝓤)⁺) 𝑆
 -- cp'' 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , lift-alg 𝑨 (OV 𝓤) ∈ 𝒦)) → ∣ i ∣))

 -- cp'' : Pred (Algebra (OV 𝓤) 𝑆)((OV 𝓤)⁺) → Algebra ((OV 𝓤)⁺) 𝑆
 -- cp'' 𝒦 = (⨅ (λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , lift-alg 𝑨 (OV 𝓤) ∈ 𝒦)) → ∣ i ∣))

 -- 𝒦' : Pred (Algebra (OV 𝓐) 𝑆) (OV 𝓐)
 -- 𝒦' = λ (𝑨' : Algebra 𝓐' 𝑆) → Σ 𝑨 ꞉ Algebra 𝓐 𝑆 , (𝑨 ∈ 𝒦all) × ((lift-alg 𝑨 𝓐') ≅ 𝑨')
--   l𝒜 : I → Algebra (OV 𝓤) 𝑆
--   l𝒜 i = lift-alg (𝒜 i) (OV 𝓤)

--   SA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
--   SA i = ∥ i ∥

--   SlA : (i : I) → l𝒜 i ∈ (SClo{𝓤}{OV 𝓤} 𝒦)
--   SlA i = lift-alg-SClo (SA i)
--   PSllA : (i : I) → lift-alg (l𝒜 i) (OV 𝓤) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSllA i = pbase (SlA i)
--   γ' : ⨅ l𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ' = prod{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)}{I = I}{𝒜 = l𝒜} PSllA

--   lid : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ≅ lift-alg (lift-alg (𝒜 i) (OV 𝓤)) (OV 𝓤)
--   lid i = lift-alg-idemp{𝓤}{OV 𝓤}{OV 𝓤}{𝒜 i}

--   PSlA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSlA i = piso (PSllA i) (sym-≅ (lid i))

--   lAi≅Ai : (i : I) → (lift-alg (𝒜 i) (OV 𝓤) ≅ 𝒜 i)
--   lAi≅Ai = λ i → (sym-≅ lift-alg-≅)

--   lA≅A : ⨅ l𝒜 ≅ ⨅ 𝒜
--   lA≅A = ⨅≅ gfe lAi≅Ai

--   γ : ⨅ 𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ = piso γ' lA≅A

   -- 𝑨 : Algebra 𝓤 𝑆
   -- 𝑨 = {!!}
   -- α : 𝑨 ∈ P{𝓤}{𝓤} (S{𝓤}{𝓤} 𝒦u)
   -- α = {!!}
   -- β : lift-alg 𝑨 (OV 𝓤) ≅ lift-alg (class-prod-s 𝒦u) (OV 𝓤)
   -- β = {!!}
 -- class-product-s-∈-ps : cps ∈ lift-class (pclo{𝓤}{𝓦}{𝓘} (sclo{𝓤}{𝓦}{𝓘} 𝒦₀))
 -- class-product-s-∈-ps = {!!} , {!!}
 -- class-product-s-∈-ps :
 --  (class-product{𝓤'}{𝓦'}{𝓘'}{𝒦}) ∈ pclo{𝓤}{𝓦}{𝓘} (sclo{𝓤}{𝓦}{𝓘} 𝒦₀)
 -- class-product-s-∈-ps = {!!}
--  where
--   I : (OV 𝓤) ̇
--   I = ℑ{𝓤} (SClo{𝓤}{𝓤} 𝒦)
--   𝒜 : I → Algebra 𝓤 𝑆
--   𝒜 = ℑ→A{𝓤} (SClo 𝒦)
--   l𝒜 : I → Algebra (OV 𝓤) 𝑆
--   l𝒜 i = lift-alg (𝒜 i) (OV 𝓤)

--   SA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
--   SA i = ∥ i ∥

--   SlA : (i : I) → l𝒜 i ∈ (SClo{𝓤}{OV 𝓤} 𝒦)
--   SlA i = lift-alg-SClo (SA i)
--   PSllA : (i : I) → lift-alg (l𝒜 i) (OV 𝓤) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSllA i = pbase (SlA i)
--   γ' : ⨅ l𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ' = prod{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)}{I = I}{𝒜 = l𝒜} PSllA

--   lid : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ≅ lift-alg (lift-alg (𝒜 i) (OV 𝓤)) (OV 𝓤)
--   lid i = lift-alg-idemp{𝓤}{OV 𝓤}{OV 𝓤}{𝒜 i}

--   PSlA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSlA i = piso (PSllA i) (sym-≅ (lid i))

--   lAi≅Ai : (i : I) → (lift-alg (𝒜 i) (OV 𝓤) ≅ 𝒜 i)
--   lAi≅Ai = λ i → (sym-≅ lift-alg-≅)

--   lA≅A : ⨅ l𝒜 ≅ ⨅ 𝒜
--   lA≅A = ⨅≅ gfe lAi≅Ai

--   γ : ⨅ 𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ = piso γ' lA≅A

-- class-prod-S-∈-SP : {𝓤 : Universe} → hfunext (OV 𝓤) (OV 𝓤)
--  →                  {𝑲 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--                     --------------------------------------------------
--  →                  (class-product (SClo{𝓤}{𝓤} 𝑲)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)

-- class-prod-S-∈-SP {𝓤} hfe {𝑲} = γ
--  where
--   ξ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝑲)
--   ξ = class-product-S-∈-PS {𝓤}{𝑲}

--   γ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)
--   γ = {!!} -- ps⊆sp {𝓤} ? ξ

-- class-product-S-∈-PS : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →       class-product (SClo{𝓤}{𝓤} 𝒦) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
-- class-product-S-∈-PS {𝓤}{𝒦} = γ
--  where
--   I : (OV 𝓤) ̇
--   I = ℑ{𝓤} (SClo{𝓤}{𝓤} 𝒦)
--   𝒜 : I → Algebra 𝓤 𝑆
--   𝒜 = ℑ→A{𝓤} (SClo 𝒦)
--   l𝒜 : I → Algebra (OV 𝓤) 𝑆
--   l𝒜 i = lift-alg (𝒜 i) (OV 𝓤)

--   SA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
--   SA i = ∥ i ∥

--   SlA : (i : I) → l𝒜 i ∈ (SClo{𝓤}{OV 𝓤} 𝒦)
--   SlA i = lift-alg-SClo (SA i)
--   PSllA : (i : I) → lift-alg (l𝒜 i) (OV 𝓤) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSllA i = pbase (SlA i)
--   γ' : ⨅ l𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ' = prod{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)}{I = I}{𝒜 = l𝒜} PSllA

--   lid : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ≅ lift-alg (lift-alg (𝒜 i) (OV 𝓤)) (OV 𝓤)
--   lid i = lift-alg-idemp{𝓤}{OV 𝓤}{OV 𝓤}{𝒜 i}

--   PSlA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
--   PSlA i = piso (PSllA i) (sym-≅ (lid i))

--   lAi≅Ai : (i : I) → (lift-alg (𝒜 i) (OV 𝓤) ≅ 𝒜 i)
--   lAi≅Ai = λ i → (sym-≅ lift-alg-≅)

--   lA≅A : ⨅ l𝒜 ≅ ⨅ 𝒜
--   lA≅A = ⨅≅ gfe lAi≅Ai

--   γ : ⨅ 𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
--   γ = piso γ' lA≅A








-- -----------=====================================================================================


----------------------------------------------------------------------------
----------------        OLDER EXPERIMENTAL STUFF       ---------------------
----------------------------------------------------------------------------

-- SClo-mono : {𝓤 𝓦 : Universe}{𝒦₁ 𝒦₂ : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →          𝒦₁ ⊆ 𝒦₂ → SClo{𝓤}{𝓦} 𝒦₁ ⊆ SClo{𝓤}{𝓦} 𝒦₂
-- SClo-mono h₀ (sbase x) = sbase (h₀ x)
-- SClo-mono h₀ (sub x sa) = sub (SClo-mono h₀ x) sa
-- SClo-mono h₀ (siso x x₁) = siso (SClo-mono h₀ x) x₁

-- PClo-idem : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →          PClo{𝓤}{𝓤} (PClo{𝓤}{𝓤} 𝒦) ⊆ PClo{𝓤}{𝓤} 𝒦
-- PClo-idem {𝓤} {𝒦} (pbase x) = piso x lift-alg-≅
-- PClo-idem {𝓤} {𝒦} (prod{I}{𝒜} x) = prod{𝓤}{I = I}{𝒜 = 𝒜} λ i → PClo-idem{𝓤}{𝒦} (x i)
-- PClo-idem (piso x x₁) = piso (PClo-idem x) x₁



-- PClo-idem' : {𝓤 𝓦 𝓩 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →           PClo {𝓤 ⊔ 𝓦}{𝓩} (PClo{𝓤}{𝓦} 𝒦) ⊆ PClo {𝓤}{𝓦 ⊔ 𝓩} 𝒦
-- PClo-idem' {𝓤} {𝓦} {𝓩} {𝒦} (pbase{lA} (pbase{𝑨} x)) = γ
--  where
--   ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓩)
--   ζ = lift-alg-idemp{𝑨 = 𝑨}
--   ξ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ∈ PClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
--   ξ = pbase{𝓤 = 𝓤}{𝓦 = (𝓦 ⊔ 𝓩)} x
--   γ : (lift-alg (lift-alg 𝑨 𝓦) 𝓩) ∈ PClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
--   γ = piso ξ ζ
-- PClo-idem' {𝓤} {𝓦} {𝓩} {𝒦} (pbase{𝑨} (prod{I}{𝒜} x)) = γ
--  where
--   IH : ⨅ 𝒜 ∈ PClo{𝓤}{𝓦} 𝒦
--   IH = prod{I = I}{𝒜 = 𝒜} x
--   γ : lift-alg (⨅ 𝒜) 𝓩 ∈ PClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
--   γ = lift-alg-PClo IH

-- PClo-idem' {𝓤} {𝓦} {𝓩} {𝒦} (pbase{𝑩} (piso{𝑨} PCloA A≅B)) = piso (lift-alg-PClo PCloA) lA≅lB
--  where
--   lA≅lB : (lift-alg 𝑨 𝓩) ≅ (lift-alg 𝑩 𝓩)
--   lA≅lB = lift-alg-iso (𝓤 ⊔ 𝓦) 𝓩 𝑨 𝑩 A≅B
-- PClo-idem' {𝓤} {𝓦} {𝓩} {𝒦} (prod{I}{𝒜} x) = γ
--  where
--   𝑰 : 𝓩 ̇
--   𝑰 = I
--   l𝒜 : (i : I) → Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓩) 𝑆
--   l𝒜 i = lift-alg (𝒜 i) (𝓩)

--   ξ : (i : I) → (l𝒜 i) ∈ PClo{𝓤}{𝓩 ⊔ 𝓦} 𝒦
--   ξ i = PClo-idem'{𝓤}{𝓦}{𝓩}{𝒦} (x i)

--   γ : ⨅ 𝒜 ∈ PClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
--   γ = {!!} -- prod{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = 𝓩}{I = I}{𝒜 = 𝒜} ?

-- PClo-idem' {𝓤} {𝓦} {𝓩} {𝒦} (piso x x₁) = piso (PClo-idem'{𝓤}{𝓦}{𝓩}{𝒦} x) x₁

-- Subalgebra→SClo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑪 : Algebra 𝓠 𝑆}
--  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓠}{𝓠} 𝒦
-- Subalgebra→SClo{𝓠}{𝒦}{𝑪}(𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = γ
--  where
--   C≤A : 𝑪 ≤ 𝑨
--   C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

--   γ : 𝑪 ∈ SClo 𝒦
--   γ = sub{𝑨 = 𝑨}(sclo-base KA)(𝑪 , C≤A)



-- Subalgebra→SClo'' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦))}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
--  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤 ⊔ 𝓦}{𝓦} 𝒦
-- Subalgebra→SClo''{𝓤}{𝓦}{𝒦}{𝑪}(𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = γ
--  where
--   C≤A : 𝑪 ≤ 𝑨
--   C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

--   CsubA : SUBALGEBRA 𝑨
--   CsubA = 𝑪 , C≤A

--   CsubLiftA : SUBALGEBRA (lift-alg 𝑨 𝓦)
--   CsubLiftA = 𝑪 , lift-alg-sub-lift 𝑨 C≤A

--   SCloLiftA : (lift-alg 𝑨 𝓦) ∈ SClo{𝓤 ⊔ 𝓦}{𝓦} 𝒦
--   SCloLiftA = sbase KA

--   γ : 𝑪 ∈ SClo{𝓤 ⊔ 𝓦}{𝓦} 𝒦
--   γ = sub{𝑨 = (lift-alg 𝑨 𝓦)} SCloLiftA CsubLiftA


-- SClo→Subalgebra' : {𝓠 𝓤 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑩 : Algebra (𝓠 ⊔ 𝓤) 𝑆}
--  →                𝑩 ∈ SClo{𝓠}{𝓤} 𝒦 →  𝑩 IsSubalgebraOfClass 𝒦
-- SClo→Subalgebra'{𝓠}{𝓤}{𝒦}{𝑩} x = {!!}




-- SClo→Subalgebra : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑨 : Algebra 𝓠 𝑆}
--  →                𝑨 ∈ SClo{𝓠}{𝓠} 𝒦 →  𝑨 IsSubalgebraOfClass 𝒦
-- SClo→Subalgebra{𝓠}{𝒦}{𝑩}(sbase{𝑨} x) = 𝑨 , (𝑨 , refl-≤) , x , sym-≅ lift-alg-≅
-- SClo→Subalgebra {𝓠} {𝒦} {.(fst sa)} (sub{𝑨 = 𝑨} x sa) = γ
--  where
--   IH : 𝑨 IsSubalgebraOfClass 𝒦
--   IH = SClo→Subalgebra x

--   𝑮 : Algebra 𝓠 𝑆
--   𝑮 = ∣ IH ∣

--   KG = fst ∥ snd IH ∥            -- KG : 𝑮 ∈ 𝒦
--   SG' = fst ∥ IH ∥               -- SG' : SUBALGEBRA 𝑮
--   𝑨' = ∣ SG' ∣                    -- 𝑨' : Algebra 𝓠 𝑆
--   𝑨'≤𝑮 = ∥ SG' ∥                 -- 𝑨'≤𝑮 : 𝑨' ≤ 𝑮
--   𝑨≅𝑨' = snd ∥ (snd IH) ∥        -- 𝑨≅𝑨' : 𝑨 ≅ 𝑨'

--   𝑨≤𝑮 : 𝑨 ≤ 𝑮
--   𝑨≤𝑮 = Iso-≤ 𝑮 𝑨 𝑨'≤𝑮 𝑨≅𝑨'

--   sa≤𝑮 : ∣ sa ∣ ≤ 𝑮
--   sa≤𝑮 = Trans-≤ 𝑮 ∣ sa ∣ 𝑨≤𝑮 ∥ sa ∥

--   γ : ∣ sa ∣ IsSubalgebraOfClass 𝒦
--   γ = 𝑮 , ((∣ sa ∣ , sa≤𝑮) , (KG , id≅))
-- SClo→Subalgebra {𝓠} {𝒦} {𝑨} (siso{𝑩} SCloB 𝑩≅𝑨) = γ
--  where
--   IH : 𝑩 IsSubalgebraOfClass 𝒦
--   IH = SClo→Subalgebra SCloB
--   𝔸 : Algebra _ 𝑆
--   𝔸 = ∣ IH ∣
--   SA : SUBALGEBRA 𝔸
--   SA = fst ∥ IH ∥
--   𝔸∈𝒦 : 𝔸 ∈ 𝒦
--   𝔸∈𝒦 = fst ∥ snd IH ∥
--   𝑩≅SA : 𝑩 ≅ ∣ SA ∣
--   𝑩≅SA = snd ∥ snd IH ∥
--   SA≤𝔸 : ∣ SA ∣ ≤ 𝔸
--   SA≤𝔸 = ∥ SA ∥
--   γ : 𝑨 IsSubalgebraOfClass 𝒦
--   γ = 𝔸 , SA , 𝔸∈𝒦 , trans-≅ 𝑨 𝑩 (∣ SA ∣) (sym-≅ 𝑩≅𝑨)  𝑩≅SA


-- LemPS⊆SP : {𝓠 : Universe} → hfunext 𝓠 𝓠
--  →         {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{I : 𝓠 ̇}{ℬ : I → Algebra 𝓠 𝑆}
--  →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
--           ----------------------------------------------------
--  →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓠}{𝓠} 𝒦)

-- LemPS⊆SP{𝓠}hfe{𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓠}{𝓠}{I = I}{𝒜 = 𝒜} PClo𝒜) , (⨅≅ gfe ℬ≅SA)
--  where
--   𝒜 = λ i → ∣ ℬ≤𝒦 i ∣                -- 𝒜 : I → Algebra 𝓠 𝑆
--   SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣        -- SA : I → Algebra 𝓠 𝑆
--   𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣       -- 𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
--   PClo𝒜 : ∀ i → (lift-alg (𝒜 i) 𝓠) ∈ PClo{𝓠}{𝓠} 𝒦
--   PClo𝒜 = λ i → pbase (𝒦𝒜 i)
--   SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣      -- SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
--   ℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥      -- ℬ≅SA : ∀ i → ℬ i ≅ SA i
--   h = λ i → ∣ SA≤𝒜 i ∣                 -- h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
--   ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
--   ⨅SA≤⨅𝒜 = i , ii , iii
--    where
--     i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
--     i = λ x i → (h i) (x i)
--     ii : is-embedding i
--     ii = embedding-lift hfe hfe{I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
--     iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
--     iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)

-- LemPS⊆SP' : {𝓘 𝓤 𝓦 : Universe} → hfunext 𝓘 (𝓘 ⊔ 𝓤) → hfunext 𝓘 (𝓤 ⊔ 𝓦)
--  →         {𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦))}{I : 𝓘 ̇}{ℬ : I → Algebra 𝓤 𝑆}
--  →         ((i : I) → (lift-alg (ℬ i) 𝓘) IsSubalgebraOfClass 𝒦)
--           ----------------------------------------------------
--  →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓤 ⊔ 𝓦}{𝓘} 𝒦)

-- LemPS⊆SP'{𝓘}{𝓤}{𝓦} hfe hfep {𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤 ⊔ 𝓦}{𝓘}{I = I}{𝒜 = 𝒜} PClo𝒜) , γ
--  where
--   𝒜 : I → Algebra (𝓤 ⊔ 𝓦) 𝑆
--   𝒜 = λ i → ∣ ℬ≤𝒦 i ∣

--   SA : I → Algebra (𝓘 ⊔ 𝓤) 𝑆
--   SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣

--   𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
--   𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣

--   PClo𝒜 : ∀ i → (lift-alg (𝒜 i) 𝓘) ∈ PClo{𝓤 ⊔ 𝓦}{𝓘} 𝒦
--   PClo𝒜 = λ i → pbase (𝒦𝒜 i)

--   SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
--   SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣

--   lℬ≅SA : ∀ i → (lift-alg (ℬ i) 𝓘) ≅ SA i
--   lℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥

--   ℬ≅SA : ∀ i → ℬ i ≅ SA i
--   ℬ≅SA i = trans-≅ _ _ _ lift-alg-≅ (lℬ≅SA i)

--   h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
--   h = λ i → ∣ SA≤𝒜 i ∣

--   ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
--   ⨅SA≤⨅𝒜 = i , ii , iii
--    where
--     i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
--     i = λ x i → (h i) (x i)
--     ii : is-embedding i
--     ii = embedding-lift{𝓠 = (𝓘 ⊔ 𝓤)}{𝓤 = (𝓤 ⊔ 𝓦)}{𝓘 = 𝓘} hfe hfep {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
--     iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
--     iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
--   γ : ⨅ ℬ ≅ ⨅ SA
--   γ = ⨅≅ gfe ℬ≅SA



-- PS⊆SP : {𝓠 : Universe} → hfunext 𝓠 𝓠 → {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
--  →      PClo{𝓠}{𝓠} (SClo{𝓠}{𝓠} 𝒦) ⊆ SClo{𝓠}{𝓠} (PClo{𝓠}{𝓠} 𝒦)
-- PS⊆SP hfe (pbase (sbase x)) = sbase (pbase x)
-- PS⊆SP {𝓠} hfe{𝒦}  (pbase (sub x sa)) = SClo-mono{𝓠}{𝓠}{𝒦}{PClo{𝓠}{𝓠} 𝒦} (PClo-expa{𝓠}{𝒦})
--                                            (siso (sub x sa) lift-alg-≅)
-- PS⊆SP {𝓠} hfe {𝒦}  (pbase (siso{𝑨}{𝑩} KA AB)) = sub α ζ
--  where
--   lB : Algebra 𝓠 𝑆
--   lB = lift-alg 𝑩 𝓠
--   α : 𝑨 ∈ SClo (PClo 𝒦)
--   α = SClo-mono{𝓠}{𝓠}{𝒦}{PClo 𝒦} PClo-expa KA
--   BA : 𝑩 ≤ 𝑨
--   BA = Iso-≤ 𝑨 𝑩 refl-≤ (sym-≅ AB)
--   β : SUBALGEBRA 𝑨
--   β = 𝑩 , BA
--   ζ : SUBALGEBRA 𝑨
--   ζ = lB , Iso-≤ 𝑨 lB BA (sym-≅ lift-alg-≅)

-- PS⊆SP {𝓠} hfe {𝒦} {.((∀ i → ∣ 𝒜 i ∣) , (λ f proj i → ∥ 𝒜 i ∥ f (λ args → proj args i)))}
--  (prod{I = I}{𝒜 = 𝒜} PSCloA) = γ
--   where
--    ζ : (i : I) → (lift-alg (𝒜 i) 𝓠) ∈ SClo (PClo 𝒦)
--    ζ i = PS⊆SP hfe (PSCloA i)
--    ξ : (i : I) → (lift-alg (𝒜 i) 𝓠) IsSubalgebraOfClass (PClo 𝒦)
--    ξ i = SClo→Subalgebra (ζ i)

--    η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo (PClo 𝒦))
--    η' = LemPS⊆SP' {𝓠} hfe hfe {PClo 𝒦}{I}{𝒜} ξ

--    η : ⨅ 𝒜 IsSubalgebraOfClass (PClo 𝒦)
--    η = mono-≤ (⨅ 𝒜) PClo-idem η'

--    γ : ⨅ 𝒜 ∈ SClo (PClo 𝒦)
--    γ = Subalgebra→SClo η
-- PS⊆SP hfe (piso x x₁) = siso (PS⊆SP hfe x) x₁

-- PS⊆SP'' : {𝓤 : Universe} → hfunext (OV 𝓤) 𝓤 → hfunext (OV 𝓤) (OV 𝓤) 
--  →       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →       PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝒦) ⊆ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)

-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (pbase{𝑨} (sbase x)) = γ
--  where
--   ξ : 𝑨 ∈ PClo{𝓤}{𝓤} 𝒦
--   ξ = pbase x
--   γ : (lift-alg 𝑨 (OV 𝓤)) ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   γ = sbase ξ

-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (pbase (sub x sa)) = ?
--  -- SClo-mono'{𝓤}{𝓤}{𝒦}{PClo{𝓤}{𝓤} 𝒦} (λ 𝑨 → pbase{𝑨 = 𝑨}) (siso (sub x sa) lift-alg-≅)
-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (pbase (siso{𝑨}{𝑩} SCloA AB)) = ? -- siso α' (lift-alg-iso (OV 𝓤) (OV 𝓤) 𝑨 𝑩 AB)
--  -- where
--  --  lA lB : Algebra (OV 𝓤) 𝑆
--  --  lA = lift-alg 𝑨 (OV 𝓤)
--  --  lB = lift-alg 𝑩 (OV 𝓤)
--  --  α : 𝑨 ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--  --  α = SClo-mono'{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = PClo 𝒦}(λ 𝑨 → pbase{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝑨 = 𝑨}) SCloA
--  --  α' : lA ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--  --  α' = lift-alg-SClo{𝓤}{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{𝓤} 𝒦)}{𝑩 = 𝑨} α

-- PS⊆SP'' {𝓤} hfe hfe'  {𝒦} (prod{I = I}{𝒜 = 𝒜} x) = γ
--  where
--   ⨅A : Algebra (OV 𝓤) 𝑆
--   ⨅A = ⨅ 𝒜

--   ζ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ SClo{𝓤}{OV 𝓤}(PClo{𝓤}{𝓤} (𝒦))
--   ζ i = PS⊆SP'' hfe hfe' (x i)

--   ξ : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) IsSubalgebraOfClass (PClo{𝓤}{𝓤} 𝒦)
--   ξ i = SClo→Subalgebra'{𝓤}{OV 𝓤} (ζ i)

--   η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤}𝒦))
--   η' = LemPS⊆SP'{𝓘 = (OV 𝓤)} {𝓤 = 𝓤} hfe' hfe {𝒦 = PClo{𝓤}{𝓤} 𝒦}{I}{𝒜} ξ

--   pci : (PClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤}𝒦)) ⊆ PClo{𝓤}{OV 𝓤} 𝒦
--   pci = ? -- PClo-idemp{𝓤}{𝓦 = (OV 𝓤)}

--   η : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
--   η = mono-≤ (⨅ 𝒜) pci η'

--   γ : ⨅ 𝒜 ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   γ = Subalgebra→SClo''{𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η
-- -- Subalgebra→SClo'' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦))}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
-- --  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤 ⊔ 𝓦}{𝓦} 𝒦

-- -- Subalgebra→SClo' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
-- --  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
-- PS⊆SP'' hfe (piso x x₁) = siso (PS⊆SP'' hfe x) x₁


-- class-product-S-∈-PS : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →       class-product (SClo{𝓤}{𝓤} 𝒦) ∈ PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝒦)
-- class-product-S-∈-PS {𝓤}{𝒦} = γ
--  where
--   I : (OV 𝓤) ̇
--   I = ℑ{𝓤} (SClo 𝒦)
--   𝒜 : I → Algebra 𝓤 𝑆
--   𝒜 = ℑ→A{𝓤} (SClo 𝒦)
--   ⨅𝒜 : Algebra (OV 𝓤) 𝑆
--   ⨅𝒜 = ⨅ 𝒜
--   KA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
--   KA i = ∥ i ∥
--   lKA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ PClo{𝓤}{OV 𝓤} (SClo 𝒦)
--   lKA i = pbase (KA i)
--   γ : ⨅ 𝒜 ∈ PClo{𝓤}{OV 𝓤} (SClo 𝒦)
--   γ = prod{I = I}{𝒜 = 𝒜} lKA




-- PClo-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →          PClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
-- PClo-idemp {𝓤}{𝓦} {𝒦} (pbase x) = piso x lift-alg-≅
-- PClo-idemp {𝓤}{𝓦} {𝒦} (prod{I}{𝒜} x) = {!!}
 -- where
 --  𝑰 : 𝓤 ⊔ 𝓦 ̇
 --  𝑰 = I
 -- --  h₀ : (i : I) → lift-alg (𝒜 i) (𝓤 ⊔ 𝓦) ∈ PClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦)
 -- --  h₀ = x
 --  l𝒜 : (i : I) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 --  l𝒜 i = lift-alg (𝒜 i) (𝓤 ⊔ 𝓦)

 --  ξ : (i : I) → (l𝒜 i) ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  ξ i = PClo-idemp{𝓤}{𝓦}{𝒦} (x i)

 --  γ' : ⨅ l𝒜 ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  γ' = {!!} -- prod{I = I}{𝒜 = 𝒜} ? -- ξ
 --  γ : ⨅ 𝒜 ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  γ = {!!} -- prod{𝓦 = (𝓤 ⊔ 𝓦)}{I = I}{𝒜 = 𝒜} ? -- ξ{!!} -- prod{𝓤 = 𝓤 ⊔ 𝓦}{𝓦 = 𝓤 ⊔ 𝓦}{I = I}{𝒜 = 𝒜} ξ
-- prod{I = I}{𝒜 = 𝒜} λ i → PClo-idemp{𝓤}{𝓦}{𝒦} (x i)
-- PClo-idemp {𝓤}{𝓦} {𝒦} (piso x x₁) = piso (PClo-idemp{𝓤}{𝓦} x) x₁


-- PS⊆SP : {𝓤 : Universe} → hfunext (OV 𝓤)(OV 𝓤)
--  →       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →       PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦) ⊆ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)

-- PS⊆SP {𝓤} hfe {𝒦} (pbase{𝑨} (sbase x)) = γ
--  where
--   ξ : 𝑨 ∈ PClo{𝓤}{OV 𝓤} 𝒦
--   ξ = pbase x
--   γ : (lift-alg 𝑨 (OV 𝓤)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
--   γ = sbase ξ

-- PS⊆SP {𝓤} hfe {𝒦} (pbase (sub x sa)) =
--  SClo-mono{𝓤}{(OV 𝓤)}{𝒦}{PClo{𝓤}{OV 𝓤} 𝒦} (λ 𝑨 → pbase{𝑨 = 𝑨}) (siso (sub x sa) lift-alg-≅)
-- PS⊆SP {𝓤} hfe {𝒦} (pbase (siso{𝑨}{𝑩} SCloA AB)) = siso α' (lift-alg-iso (OV 𝓤) (OV 𝓤) 𝑨 𝑩 AB)
--  where
--   lA lB : Algebra (OV 𝓤) 𝑆
--   lA = lift-alg 𝑨 (OV 𝓤)
--   lB = lift-alg 𝑩 (OV 𝓤)
--   α : 𝑨 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
--   α = SClo-mono{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = PClo 𝒦}(λ 𝑨 → pbase{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝑨 = 𝑨}) SCloA
--   α' : lA ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
--   α' = lift-alg-SClo{OV 𝓤}{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑩 = 𝑨} α

-- PS⊆SP {𝓤} hfe  {𝒦} (prod{I = I}{𝒜 = 𝒜} x) = γ
--  where
--   ⨅A : Algebra (OV 𝓤) 𝑆
--   ⨅A = ⨅ 𝒜

--   ζ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ SClo{OV 𝓤}{OV 𝓤}(PClo{𝓤}{OV 𝓤} (𝒦))
--   ζ i = PS⊆SP hfe (x i)

--   ξ : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
--   ξ i = SClo→Subalgebra{OV 𝓤}{OV 𝓤} (ζ i)

--   η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦))
--   η' = LemPS⊆SP{𝓘 = (OV 𝓤)} {𝓤 = (OV 𝓤)} hfe hfe {𝒦 = PClo{𝓤}{OV 𝓤} 𝒦}{I}{𝒜} ξ

--   pci : (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦)) ⊆ PClo{𝓤}{OV 𝓤} 𝒦
--   pci = PClo-idemp{𝓤}{𝓦 = (OV 𝓤)}

--   η : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
--   η = mono-≤ (⨅ 𝒜) pci η'

--   γ : ⨅ 𝒜 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
--   γ = Subalgebra→SClo{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η


-- PS⊆SP hfe (piso x x₁) = siso (PS⊆SP hfe x) x₁


 -- lift-alg-sclo : {𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 --  →                𝑩 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → (lift-alg 𝑩 𝓘) ∈ sclo{𝓤}{𝓦 ⊔ 𝓘} 𝒦
 -- lift-alg-sclo (sbase{𝑨} KA) = siso ξ (lift-alg-idemp{𝓤}{𝓦}{𝓘}{𝑨})
 --  where
 --   ξ : lift-alg 𝑨 (𝓦 ⊔ 𝓘) ∈ sclo{𝓤}{𝓦 ⊔ 𝓘} 𝒦
 --   ξ = sbase{𝓤 = 𝓤}{𝓦 = (𝓦 ⊔ 𝓘)}{𝑨 = 𝑨} KA

 -- lift-alg-sclo {.(𝑩)} (sub{𝑨} SCloA (𝑩 , B≤A)) = sub (lift-alg-sclo SCloA) (lB , lB≤lA)
 --  where
 --   lB : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆
 --   lB = lift-alg 𝑩 𝓘

 --   lB≤lA : lB ≤ lift-alg 𝑨 𝓘
 --   lB≤lA = lift-alg-lift-≤-lift 𝑩 {𝑨} B≤A

 -- lift-alg-sclo {𝑩} (siso{𝑨} SCloA A≅B) = siso (lift-alg-sclo SCloA) lA≅lB
 --  where
 --   lA≅lB : (lift-alg 𝑨 𝓘) ≅ (lift-alg 𝑩 𝓘)
 --   lA≅lB = lift-alg-iso (𝓤 ⊔ 𝓦) 𝓘 𝑨 𝑩 A≅B

----------------------------------------------------------------------------------
--Closure wrt H
-- data HClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
--  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ HClo 𝒦
--  himg : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ HClo{𝓤}{𝓦} 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦
--  hiso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦)  𝑆} → 𝑨 ∈ HClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ HClo 𝒦
-- --Closure wrt S
-- data SClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
--  sbase : {𝑨 :  Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ SClo 𝒦
--  sub : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ SClo{𝓤}{𝓦} 𝒦 → (sa : SUBALGEBRA 𝑨) → ∣ sa ∣ ∈ SClo 𝒦
--  siso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ SClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ SClo 𝒦
-- --Closure wrt P
-- data PClo {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
--  pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ PClo 𝒦
--  prod : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (lift-alg (𝒜 i) 𝓦) ∈ PClo{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ PClo 𝒦
--  piso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ PClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ PClo 𝒦
-- --Classes of algs closed under the taking of hom images, subalgebras, and products.
-- data VClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
--  vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ VClo 𝒦
--  vprod : {I : 𝓦 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (lift-alg (𝒜 i) 𝓦) ∈ VClo{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
--  vsub  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → (sa : Subalgebra 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
--  vhom  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
--  viso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ VClo 𝒦
