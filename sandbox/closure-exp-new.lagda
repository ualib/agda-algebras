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

----------------------------------------------------------------------------------
--Closure wrt H
data HClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
 hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ HClo 𝒦
 himg : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ HClo{𝓤}{𝓦} 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦
 hiso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦)  𝑆} → 𝑨 ∈ HClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ HClo 𝒦
--Closure wrt S
data SClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
 sbase : {𝑨 :  Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ SClo 𝒦
 sub : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ SClo{𝓤}{𝓦} 𝒦 → (sa : SUBALGEBRA 𝑨) → ∣ sa ∣ ∈ SClo 𝒦
 siso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ SClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ SClo 𝒦
--Closure wrt P
data PClo {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
 pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ PClo 𝒦
 prod : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (lift-alg (𝒜 i) 𝓦) ∈ PClo{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ PClo 𝒦
 piso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ PClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ PClo 𝒦

-- alternatives
data hclo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
 hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ hclo 𝒦
 himg : {𝑨 : Algebra 𝓤 𝑆} → lift-alg 𝑨 𝓦 ∈ hclo{𝓤}{𝓦} 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ hclo 𝒦
 hiso : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → lift-alg 𝑨 𝓦 ∈ hclo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 𝓤 ∈ hclo 𝒦
--Closure wrt S
data sclo {𝓤 𝓦 𝓘 : Universe}(𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
 sbase : {𝑨 :  Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ sclo 𝒦
 slift : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
 sub : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → (sa : SUBALGEBRA 𝑨) → ∣ sa ∣ ∈ sclo 𝒦
 siso : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ sclo 𝒦
--Closure wrt P

data pclo {𝓤 𝓦 𝓘 : Universe} (𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆) (OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))) : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆) (OV (𝓤 ⊔ 𝓦 ⊔ 𝓘)) where
 pbase : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ pclo 𝒦
 plift : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → 𝑨 ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦 → (lift-alg 𝑨 (𝓤 ⊔ 𝓦 ⊔ 𝓘)) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦
 prod : {I : 𝓘 ̇ }{𝒜 : I → Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆} → (∀ i → (𝒜 i) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦) → ⨅ 𝒜 ∈ pclo 𝒦
 piso : {𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦 → 𝑨 ≅ 𝑩 → lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ∈ pclo 𝒦

 -- maybe could have used: `piso : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ PClo 𝒦`
--Closure wrt HSP
--Classes of algs closed under the taking of hom images, subalgebras, and products.
data VClo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
 vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → (lift-alg 𝑨 𝓦) ∈ VClo 𝒦
 vprod : {I : 𝓦 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (lift-alg (𝒜 i) 𝓦) ∈ VClo{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
 vsub  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → (sa : Subalgebra 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
 vhom  : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
 viso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ VClo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ VClo 𝒦

module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} {𝑨 : Algebra 𝓤 𝑆} where
 pclo-base : 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo{𝓤}{𝓤} 𝒦
 pclo-base KA = piso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

 sclo-base : 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo{𝓤}{𝓤} 𝒦
 sclo-base KA = siso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (sbase KA) (sym-≅ lift-alg-≅)

 hclo-base : 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo{𝓤}{𝓤} 𝒦
 hclo-base KA = hiso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (hbase KA) (sym-≅ lift-alg-≅)

 vclo-base : 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo{𝓤}{𝓤} 𝒦
 vclo-base KA = viso{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (vbase KA) (sym-≅ lift-alg-≅)


lift-alg-idemp : {𝓤 𝓦 𝓩 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓩)
lift-alg-idemp {𝓤} {𝓦} {𝓩} {𝑨} = TRANS-≅ (TRANS-≅ ζ lift-alg-≅) lift-alg-≅
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅

lift-alg-SClo : {𝓤 𝓦 𝓩 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑩 ∈ SClo{𝓤}{𝓦} 𝒦 → (lift-alg 𝑩 𝓩) ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
lift-alg-SClo {𝓤} {𝓦} {𝓩} {𝒦} (sbase{𝑨} KA) = siso ξ (lift-alg-idemp{𝓤}{𝓦}{𝓩}{𝑨})
 where
  ξ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  ξ = sbase{𝓤 = 𝓤}{𝓦 = (𝓦 ⊔ 𝓩)}{𝑨 = 𝑨} KA

lift-alg-SClo {𝓤} {𝓦} {𝓩} {𝒦} {.(𝑩)} (sub{𝑨} SCloA (𝑩 , B≤A)) = sub (lift-alg-SClo SCloA) (lB , lB≤lA)
 where
  lB : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓩) 𝑆
  lB = lift-alg 𝑩 𝓩

  lB≤lA : lB ≤ lift-alg 𝑨 𝓩
  lB≤lA = lift-alg-lift-≤-lift 𝑩 {𝑨} B≤A

lift-alg-SClo {𝓤} {𝓦} {𝓩} {𝒦} {𝑩} (siso{𝑨} SCloA A≅B) = siso (lift-alg-SClo SCloA) lA≅lB
 where
  lA≅lB : (lift-alg 𝑨 𝓩) ≅ (lift-alg 𝑩 𝓩)
  lA≅lB = lift-alg-iso (𝓤 ⊔ 𝓦) 𝓩 𝑨 𝑩 A≅B

PClo⊆VClo : {𝓤 : Universe}
            {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
            --------------------------------
 →           PClo{𝓤}{𝓤} 𝒦 ⊆ VClo{𝓤}{𝓤} 𝒦
PClo⊆VClo {𝓤} {𝒦} (pbase x) = vbase x
PClo⊆VClo {𝓤} {𝒦} (prod{I}{𝒜} x) = vprod{𝓤}{𝓦 = 𝓤}{I = I}{𝒜 = 𝒜} λ (i : I) → PClo⊆VClo{𝓤}{𝒦}(x i)
PClo⊆VClo {𝓤} {𝒦} (piso x x₁) = viso (PClo⊆VClo x) x₁

SClo⊆VClo : {𝓤 : Universe}
            {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           ---------------------------------
 →          SClo{𝓤}{𝓤} 𝒦 ⊆ VClo{𝓤}{𝓤} 𝒦

SClo⊆VClo (sbase x) = vbase x
SClo⊆VClo (sub x sa) = vsub (SClo⊆VClo x) sa
SClo⊆VClo (siso x x₁) = viso (SClo⊆VClo x) x₁
SP⊆V : {𝓤 : Universe}
       {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
      ----------------------------------
 →      SClo{𝓤}{𝓤} (PClo{𝓤}{𝓤} 𝒦) ⊆ VClo{𝓤}{𝓤} 𝒦

SP⊆V {𝓤} {𝒦} (sbase{𝑨 = 𝑨} PCloA) = PClo⊆VClo{𝓤}{𝒦} (piso PCloA lift-alg-≅)
SP⊆V {𝓤} {𝒦} (sub x sa) = vsub (SP⊆V x) sa
SP⊆V {𝓤} {𝒦} (siso x x₁) = viso (SP⊆V x) x₁


-----------------------------------------------------------------------------
--SClo is a closure operator
--In particular, it's monotone.
SClo-mono : {𝓤 𝓦 : Universe}{𝒦₁ : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝒦₂ : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦))}
 →          ((𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ 𝒦₁ → (lift-alg 𝑨 𝓦) ∈ 𝒦₂) → SClo{𝓤}{𝓦} 𝒦₁ ⊆ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
SClo-mono {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (sbase {𝑨} KA) = γ
 where
  ξ : (lift-alg 𝑨 𝓦) ∈ 𝒦₂
  ξ = ant 𝑨 KA
  γ : (lift-alg 𝑨 𝓦) ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  γ = sclo-base{𝓤 = (𝓤 ⊔ 𝓦)}{𝒦 = 𝒦₂}{𝑨 = (lift-alg 𝑨 𝓦)} ξ
SClo-mono {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (sub{𝑨} SAK1 (𝑩 , B≤A)) = γ
 where
  SAK2 : 𝑨 ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  SAK2 = SClo-mono ant SAK1
  γ : 𝑩 ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  γ = sub SAK2 (𝑩 , B≤A)
SClo-mono {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (siso x x₁) = siso (SClo-mono ant x) x₁

SClo-idemp : {𝓤 𝓦 𝓩 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →           SClo {𝓤 ⊔ 𝓦}{𝓩} (SClo{𝓤}{𝓦} 𝒦) ⊆ SClo {𝓤}{𝓦 ⊔ 𝓩} 𝒦
SClo-idemp {𝓤} {𝓦} {𝓩} {𝒦} (sbase{lA} (sbase{𝑨} x)) = γ
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓩)
  ζ = lift-alg-idemp{𝑨 = 𝑨}
  ξ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  ξ = sbase{𝓤 = 𝓤}{𝓦 = (𝓦 ⊔ 𝓩)} x
  γ : (lift-alg (lift-alg 𝑨 𝓦) 𝓩) ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  γ = siso ξ ζ
SClo-idemp {𝓤} {𝓦} {𝓩} {𝒦} (sbase{𝑨 = 𝑩} (sub{𝑨 = 𝑨} SCloA x)) = sub SlA (lift-alg 𝑩 𝓩 , lB≤lA)
 where
  SlA : lift-alg 𝑨 𝓩 ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  SlA = lift-alg-SClo SCloA
  lB≤lA : lift-alg 𝑩 𝓩 ≤ lift-alg 𝑨 𝓩
  lB≤lA = lift-alg-lift-≤-lift 𝑩 {𝑨} ∥ x ∥

SClo-idemp {𝓤} {𝓦} {𝓩} {𝒦} (sbase{𝑩} (siso{𝑨} SCloA A≅B)) = siso (lift-alg-SClo SCloA) lA≅lB
 where
  lA≅lB : (lift-alg 𝑨 𝓩) ≅ (lift-alg 𝑩 𝓩)
  lA≅lB = lift-alg-iso (𝓤 ⊔ 𝓦) 𝓩 𝑨 𝑩 A≅B

SClo-idemp {𝓤} {𝓦} {𝓩} {𝒦} (sub {𝑨 = 𝑨} SCloA (𝑩 , B≤A)) = γ
 where
  SA : 𝑨 ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  SA = SClo-idemp SCloA
  γ : 𝑩 ∈ SClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
  γ = sub SA (𝑩 , B≤A)
SClo-idemp {𝓤} {𝓦} {𝓩} {𝒦} (siso x x₁) = siso (SClo-idemp x) x₁



module _ {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where
 All : Universe
 All = 𝓤 ⊔ 𝓦 ⊔ 𝓘

 pclo-idemp : pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
 pclo-idemp (pbase x) = x
 pclo-idemp (plift x) = plift (pclo-idemp x)
 pclo-idemp (prod x) = prod (λ i → pclo-idemp (x i))
 pclo-idemp (piso x x₁) = piso (pclo-idemp x) x₁

PClo-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → 𝒦 ⊆ PClo{𝓤}{𝓤} 𝒦
PClo-expa KA = pclo-base KA


----------------------------------------------------------------------------------------------
-- For a given algebra 𝑨, and class 𝒦 of algebras, we will find the following fact useful
-- (e.g., in proof of Birkhoff's HSP theorem):  𝑨 ∈ SClo 𝒦  ⇔  𝑨 IsSubalgebraOfClass 𝒦
Subalgebra→SClo : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
Subalgebra→SClo{𝓤}{𝓦}{𝒦}{𝑪}(𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = γ
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  CsubLiftA : SUBALGEBRA (lift-alg 𝑨 𝓦)
  CsubLiftA = 𝑪 , lift-alg-sub-lift 𝑨 C≤A

  γ : 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
  γ = sub{𝑨 = (lift-alg 𝑨 𝓦)} (sbase KA) CsubLiftA

module _ {𝓤 𝓦 𝓘 : Universe} {𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

 subalgebra→sclo : {𝑪 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆}
  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
 subalgebra→sclo {𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = sub (sbase KA) (𝑪 , Iso-≤ 𝑨 𝑪 B≤A C≅B)
  where
   C≤A : 𝑪 ≤ 𝑨
   C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

   CsubA : SUBALGEBRA 𝑨
   CsubA = 𝑪 , C≤A

   scloA : 𝑨 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
   scloA = sbase KA

   γ : 𝑪 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦
   γ = sub scloA CsubA

 -- sclo→subalgebra{𝓤}{𝓦}{𝓘} (ζ i)
 sclo→subalgebra : {𝑩 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆}
  →                𝑩 ∈ sclo{𝓤}{𝓦}{𝓘} 𝒦 →  𝑩 IsSubalgebraOfClass 𝒦
 sclo→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , refl-≅
 sclo→subalgebra (slift{𝑩} x) = 𝑨 , SA , KA , trans-≅ lB 𝑩 ∣ SA ∣ (sym-≅ lift-alg-≅) B≅SA
  where
   lB : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆
   lB = lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘)
   BsubK : 𝑩 IsSubalgebraOfClass 𝒦
   BsubK = sclo→subalgebra x
   𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆
   𝑨 = ∣ BsubK ∣
   SA : SUBALGEBRA 𝑨
   SA = fst ∥ BsubK ∥
   KA : 𝑨 ∈ 𝒦
   KA = ∣ snd ∥ BsubK ∥ ∣
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BsubK ∥ ∥

 sclo→subalgebra (sub{𝑩} x sa) = γ
  where
   BsubK : 𝑩 IsSubalgebraOfClass 𝒦
   BsubK = sclo→subalgebra x
   𝑨 : Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆
   𝑨 = ∣ BsubK ∣
   KA : 𝑨 ∈ 𝒦
   KA = ∣ snd ∥ BsubK ∥ ∣
   SA : SUBALGEBRA 𝑨
   SA = fst ∥ BsubK ∥
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BsubK ∥ ∥
   B≤A : 𝑩 ≤ 𝑨
   B≤A = Iso-≤ 𝑨 𝑩 ∥ SA ∥ B≅SA
   saa : SUBALGEBRA 𝑨
   saa = ∣ sa ∣ , Trans-≤ 𝑨 ∣ sa ∣ B≤A ∥ sa ∥ 
   γ : ∣ sa ∣ IsSubalgebraOfClass 𝒦
   γ = 𝑨 , saa , KA , refl-≅

 sclo→subalgebra (siso{𝑨}{𝑩} sA A≅B) = γ
  where
   lB : Algebra _ 𝑆
   lB = lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘)
   IH : 𝑨 IsSubalgebraOfClass 𝒦
   IH = sclo→subalgebra sA
   𝔸 : Algebra _ 𝑆
   𝔸 = ∣ IH ∣
   SA : SUBALGEBRA 𝔸
   SA = fst ∥ IH ∥
   𝔸∈𝒦 : 𝔸 ∈ 𝒦
   𝔸∈𝒦 = fst ∥ snd IH ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd IH ∥
   lB≅sa : lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) ≅ ∣ SA ∣
   lB≅sa = TRANS-≅ (TRANS-≅ (sym-≅ lift-alg-≅) (sym-≅ A≅B)) A≅SA 
   γ : lift-alg 𝑩 (𝓤 ⊔ 𝓦 ⊔ 𝓘) IsSubalgebraOfClass 𝒦
   γ = 𝔸 , SA , 𝔸∈𝒦 , lB≅sa

SClo→Subalgebra : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑩 ∈ SClo{𝓤}{𝓦} 𝒦 →  𝑩 IsSubalgebraOfClass 𝒦
SClo→Subalgebra {𝓤}{𝓦}{𝒦} (sbase{𝑨} KA) = 𝑨 , ((lift-alg 𝑨 𝓦) , lA≤A) , KA , refl-≅
 where
  lA≤A : (lift-alg 𝑨 𝓦) ≤ 𝑨
  lA≤A = lift-alg-lift-≤-lower 𝑨 {𝑨} refl-≤

SClo→Subalgebra {𝓤} {𝓦} {𝒦} {.(fst sa)} (sub{𝑨 = 𝑨} x sa) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra{𝓤}{𝓦}{𝒦}{𝑨} x

  𝑮 : Algebra 𝓤 𝑆
  𝑮 = ∣ IH ∣

  KG = fst ∥ snd IH ∥            -- KG : 𝑮 ∈ 𝒦
  SG' = fst ∥ IH ∥               -- SG' : SUBALGEBRA 𝑮
  𝑨' = ∣ SG' ∣                    -- 𝑨' : Algebra 𝓠 𝑆
  𝑨'≤𝑮 = ∥ SG' ∥                 -- 𝑨'≤𝑮 : 𝑨' ≤ 𝑮
  𝑨≅𝑨' = snd ∥ (snd IH) ∥        -- 𝑨≅𝑨' : 𝑨 ≅ 𝑨'
  𝑨≤𝑮 : 𝑨 ≤ 𝑮
  𝑨≤𝑮 = Iso-≤ 𝑮 𝑨 𝑨'≤𝑮 𝑨≅𝑨'

  sa≤𝑮 : ∣ sa ∣ ≤ 𝑮
  sa≤𝑮 = Trans-≤ 𝑮 ∣ sa ∣ 𝑨≤𝑮 ∥ sa ∥

  γ : ∣ sa ∣ IsSubalgebraOfClass 𝒦
  γ = 𝑮 , ((∣ sa ∣ , sa≤𝑮) , (KG , id≅))

SClo→Subalgebra {𝓤}{𝓦}{𝒦}{𝑩}(siso{𝑨} SCloA A≅B) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra SCloA
  𝔸 : Algebra 𝓤 𝑆
  𝔸 = ∣ IH ∣
  SA : SUBALGEBRA 𝔸
  SA = fst ∥ IH ∥
  𝔸∈𝒦 : 𝔸 ∈ 𝒦
  𝔸∈𝒦 = fst ∥ snd IH ∥
  A≅SA : 𝑨 ≅ ∣ SA ∣
  A≅SA = snd ∥ snd IH ∥
  SA≤𝔸 : ∣ SA ∣ ≤ 𝔸
  SA≤𝔸 = ∥ SA ∥
  γ : 𝑩 IsSubalgebraOfClass 𝒦
  γ = 𝔸 , SA , 𝔸∈𝒦 , trans-≅ 𝑩 𝑨 (∣ SA ∣) (sym-≅ A≅B) A≅SA



-- ----------------------------------------------------------------------------------------
-- -- The (near) lattice of closures

--TODO: combine the last proof and the next proof
LemPS⊆SP : {𝓘 𝓤 : Universe} → hfunext 𝓘 (𝓘 ⊔ 𝓤) → hfunext 𝓘 𝓤
 →         {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{I : 𝓘 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →         ((i : I) → (lift-alg (ℬ i) 𝓘) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓤}{𝓘} 𝒦)

LemPS⊆SP{𝓘}{𝓤} hfe hfep {𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤}{𝓘}{I = I}{𝒜 = 𝒜} PClo𝒜) , γ
 where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ ℬ≤𝒦 i ∣

  SA : I → Algebra (𝓘 ⊔ 𝓤) 𝑆
  SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣

  𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
  𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣

  PClo𝒜 : ∀ i → (lift-alg (𝒜 i) 𝓘) ∈ PClo{𝓤}{𝓘} 𝒦
  PClo𝒜 = λ i → pbase (𝒦𝒜 i)

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣

  lℬ≅SA : ∀ i → (lift-alg (ℬ i) 𝓘) ≅ SA i
  lℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥

  ℬ≅SA : ∀ i → ℬ i ≅ SA i
  ℬ≅SA i = trans-≅ _ _ _ lift-alg-≅ (lℬ≅SA i)

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → ∣ SA≤𝒜 i ∣

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift hfe hfep {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe ℬ≅SA




module _
 {𝓤 𝓦 𝓘 : Universe}
 {𝒦 𝒦' : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))} where

 sclo-mono : 𝒦 ⊆ 𝒦' → sclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ sclo{𝓤}{𝓦}{𝓘} 𝒦'
 sclo-mono ant (sbase x) = sbase (ant x)
 sclo-mono ant (slift x) = slift (sclo-mono ant x)
 sclo-mono ant (sub x sa) = sub (sclo-mono ant x) sa
 sclo-mono ant (siso x x₁) = siso (sclo-mono ant x) x₁

pclo-expa : {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}
 → 𝒦 ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
pclo-expa x = pbase x

s⊆sp : {𝓤 𝓦 𝓘 : Universe}{𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}
 →     sclo{𝓤}{𝓦}{𝓘} 𝒦 ⊆ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
s⊆sp {𝓤}{𝓦}{𝓘}{𝒦} = sclo-mono{𝒦 = 𝒦}{𝒦' = (pclo{𝓤}{𝓦}{𝓘} 𝒦)} pclo-expa

module _
 {𝓤 𝓦 𝓘 : Universe}
 {𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}
 {hfe : hfunext 𝓘 (𝓤 ⊔ 𝓦 ⊔ 𝓘)} where

 UWI : Universe
 UWI = 𝓤 ⊔ 𝓦 ⊔ 𝓘

 lemps⊆sp : {I : 𝓘 ̇}{ℬ : I → Algebra UWI 𝑆}
  →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
           ----------------------------------------------------
  →         ⨅ ℬ IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)

 lemps⊆sp {I}{ℬ} ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤}{𝓦}{𝓘}{I = I}{𝒜 = 𝒜} pclo𝒜) , γ
  where
   𝒜 : I → Algebra UWI 𝑆
   𝒜 = λ i → ∣ ℬ≤𝒦 i ∣

   SA : I → Algebra UWI 𝑆
   SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣

   𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
   𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣

   ℬ≅SA : ∀ i → ℬ i ≅ SA i
   ℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥
   pclo𝒜 : ∀ i → (𝒜 i) ∈ pclo{𝓤}{𝓦}{𝓘} 𝒦
   pclo𝒜 = λ i → pbase (𝒦𝒜 i)

   SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
   SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣

   h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
   h = λ i → ∣ SA≤𝒜 i ∣

   ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
   ⨅SA≤⨅𝒜 = i , ii , iii
    where
     i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
     i = λ x i → (h i) (x i)
     ii : is-embedding i
     ii = embedding-lift{𝓠 = UWI}{𝓤 = UWI}{𝓘 = 𝓘} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
     iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
     iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
   γ : ⨅ ℬ ≅ ⨅ SA
   γ = ⨅≅ gfe ℬ≅SA

module _
 {𝓤 𝓦 𝓘 : Universe}
 {𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦 ⊔ 𝓘) 𝑆)(OV (𝓤 ⊔ 𝓦 ⊔ 𝓘))}
 {hfe : hfunext 𝓘 (𝓤 ⊔ 𝓦 ⊔ 𝓘)} where
 ALL : Universe
 ALL = 𝓤 ⊔ 𝓦 ⊔ 𝓘

 ps⊆sp : pclo{𝓤}{𝓦}{𝓘} (sclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)

 ps⊆sp (pbase {𝑨} (sbase x)) = sbase (pbase x)
 ps⊆sp (pbase {.(lift-alg 𝑨 ALL)} (slift{𝑨} x)) = slift (s⊆sp x)
 ps⊆sp (pbase {.(𝑩)} (sub{𝑨} x (𝑩 , B≤A))) = sub (s⊆sp x) (𝑩 , B≤A)
 ps⊆sp (pbase {.(lift-alg 𝑩 ALL)} (siso{𝑨}{𝑩} x A≅B)) = siso (s⊆sp x) A≅B
 ps⊆sp (plift x) = slift (ps⊆sp x)
 ps⊆sp (prod{I = I}{𝒜 = 𝒜} x) = γ
  where
   ⨅A : Algebra ALL 𝑆
   ⨅A = ⨅ 𝒜

   ζ : (i : I) → (𝒜 i) ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
   ζ i = ps⊆sp (x i)

  --  IH : ⨅ 𝒜 ∈ (pclo{𝓤}{𝓦}{𝓘} (sclo{𝓤}{𝓦}{𝓘} 𝒦))
  --  IH = prod x
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
   ξ i = sclo→subalgebra{𝓤}{𝓦}{𝓘} (ζ i)

   η' : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦))
   η' = lemps⊆sp {hfe = hfe}{I = I}{ℬ = 𝒜} ξ

   pci : pclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦) ⊆ pclo{𝓤}{𝓦}{𝓘} 𝒦
   pci = pclo-idemp

   η : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓤}{𝓦}{𝓘} 𝒦)
   η = mono-≤ (⨅ 𝒜) pci η'

   -- γ : ⨅ 𝒜 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
   -- γ = Subalgebra→SClo{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η
   γ : ⨅ 𝒜 ∈ sclo{𝓤}{𝓦}{𝓘} (pclo{𝓤}{𝓦}{𝓘} 𝒦)
   γ = subalgebra→sclo{𝓤}{𝓦}{𝓘}{𝒦 = (pclo{𝓤}{𝓦}{𝓘} 𝒦)}{𝑪 = ⨅ 𝒜} η

 ps⊆sp (piso x x₁) = siso (ps⊆sp x) x₁

ℑ : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆) (OV 𝓤) → (OV 𝓤) ̇
ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

ℑ→A : {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
 →    (i : ℑ 𝒦) → Algebra 𝓤 𝑆
ℑ→A _ i = ∣ i ∣

class-product : {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Algebra (OV 𝓤) 𝑆
class-product 𝒦 = ⨅ (ℑ→A 𝒦)

class-product-S-∈-PS : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 →       class-product (SClo{𝓤}{𝓤} 𝒦) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
class-product-S-∈-PS {𝓤}{𝒦} = γ
 where
  I : (OV 𝓤) ̇
  I = ℑ{𝓤} (SClo{𝓤}{𝓤} 𝒦)
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = ℑ→A{𝓤} (SClo 𝒦)
  l𝒜 : I → Algebra (OV 𝓤) 𝑆
  l𝒜 i = lift-alg (𝒜 i) (OV 𝓤)

  SA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
  SA i = ∥ i ∥

  SlA : (i : I) → l𝒜 i ∈ (SClo{𝓤}{OV 𝓤} 𝒦)
  SlA i = lift-alg-SClo (SA i)
  PSllA : (i : I) → lift-alg (l𝒜 i) (OV 𝓤) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
  PSllA i = pbase (SlA i)
  γ' : ⨅ l𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
  γ' = prod{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)}{I = I}{𝒜 = l𝒜} PSllA

  lid : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ≅ lift-alg (lift-alg (𝒜 i) (OV 𝓤)) (OV 𝓤)
  lid i = lift-alg-idemp{𝓤}{OV 𝓤}{OV 𝓤}{𝒜 i}

  PSlA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ (PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦))
  PSlA i = piso (PSllA i) (sym-≅ (lid i))

  lAi≅Ai : (i : I) → (lift-alg (𝒜 i) (OV 𝓤) ≅ 𝒜 i)
  lAi≅Ai = λ i → (sym-≅ lift-alg-≅)

  lA≅A : ⨅ l𝒜 ≅ ⨅ 𝒜
  lA≅A = ⨅≅ gfe lAi≅Ai

  γ : ⨅ 𝒜 ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
  γ = piso γ' lA≅A


class-prod-S-∈-SP : {𝓤 : Universe} → hfunext (OV 𝓤) (OV 𝓤)
 →                  {𝑲 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                    --------------------------------------------------
 →                  (class-product (SClo{𝓤}{𝓤} 𝑲)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)

class-prod-S-∈-SP {𝓤} hfe {𝑲} = γ
 where
  ξ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝑲)
  ξ = class-product-S-∈-PS {𝓤}{𝑲}

  γ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)
  γ = {!!} -- ps⊆sp {𝓤} ? ξ







-- -----------=====================================================================================


----------------------------------------------------------------------------
----------------        RECENT EXPERIMENTAL STUFF       ---------------------
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
