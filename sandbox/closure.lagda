\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 23 Dec 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂; Π)

module closure
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

-- lift-alg-PClo : {𝓤 𝓦 𝓩 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
--  →                𝑩 ∈ PClo{𝓤}{𝓦} 𝒦 → (lift-alg 𝑩 𝓩) ∈ PClo{𝓤}{𝓦 ⊔ 𝓩} 𝒦
-- lift-alg-PClo {𝓤} {𝓦} {𝓩} {𝒦} x = ?






Subalgebra→SClo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑪 : Algebra 𝓠 𝑆}
 →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓠}{𝓠} 𝒦
Subalgebra→SClo{𝓠}{𝒦}{𝑪}(𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = γ
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  γ : 𝑪 ∈ SClo 𝒦
  γ = sub{𝑨 = 𝑨}(sclo-base KA)(𝑪 , C≤A)

Subalgebra→SClo' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
Subalgebra→SClo'{𝓤}{𝓦}{𝒦}{𝑪}(𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = γ
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  CsubA : SUBALGEBRA 𝑨
  CsubA = 𝑪 , C≤A

  CsubLiftA : SUBALGEBRA (lift-alg 𝑨 𝓦)
  CsubLiftA = 𝑪 , lift-alg-sub-lift 𝑨 C≤A

  SCloLiftA : (lift-alg 𝑨 𝓦) ∈ SClo{𝓤}{𝓦} 𝒦
  SCloLiftA = sbase KA

  γ : 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
  γ = sub{𝑨 = (lift-alg 𝑨 𝓦)} SCloLiftA CsubLiftA


-- SClo→Subalgebra' : {𝓠 𝓤 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑩 : Algebra (𝓠 ⊔ 𝓤) 𝑆}
--  →                𝑩 ∈ SClo{𝓠}{𝓤} 𝒦 →  𝑩 IsSubalgebraOfClass 𝒦
-- SClo→Subalgebra'{𝓠}{𝓤}{𝒦}{𝑩} x = {!!}


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
SClo-mono : {𝓤 𝓦 : Universe}{𝒦₁ 𝒦₂ : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →          𝒦₁ ⊆ 𝒦₂ → SClo{𝓤}{𝓦} 𝒦₁ ⊆ SClo{𝓤}{𝓦} 𝒦₂
SClo-mono h₀ (sbase x) = sbase (h₀ x)
SClo-mono h₀ (sub x sa) = sub (SClo-mono h₀ x) sa
SClo-mono h₀ (siso x x₁) = siso (SClo-mono h₀ x) x₁

SClo-mono' : {𝓤 𝓦 : Universe}{𝒦₁ : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝒦₂ : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦))}
 →          ((𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ 𝒦₁ → (lift-alg 𝑨 𝓦) ∈ 𝒦₂) → SClo{𝓤}{𝓦} 𝒦₁ ⊆ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
SClo-mono' {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (sbase {𝑨} KA) = γ
 where
  ξ : (lift-alg 𝑨 𝓦) ∈ 𝒦₂
  ξ = ant 𝑨 KA
  γ : (lift-alg 𝑨 𝓦) ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  γ = sclo-base{𝓤 = (𝓤 ⊔ 𝓦)}{𝒦 = 𝒦₂}{𝑨 = (lift-alg 𝑨 𝓦)} ξ
SClo-mono' {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (sub{𝑨} SAK1 (𝑩 , B≤A)) = γ
 where
  SAK2 : 𝑨 ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  SAK2 = SClo-mono' ant SAK1
  γ : 𝑩 ∈ SClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} 𝒦₂
  γ = sub SAK2 (𝑩 , B≤A)
SClo-mono' {𝓤} {𝓦} {𝒦₁} {𝒦₂} ant (siso x x₁) = siso (SClo-mono' ant x) x₁


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


PClo-idem : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →          PClo{𝓤}{𝓤} (PClo{𝓤}{𝓤} 𝒦) ⊆ PClo{𝓤}{𝓤} 𝒦
PClo-idem {𝓤} {𝒦} (pbase x) = piso x lift-alg-≅
PClo-idem {𝓤} {𝒦} (prod{I}{𝒜} x) = prod{𝓤}{I = I}{𝒜 = 𝒜} λ i → PClo-idem{𝓤}{𝒦} (x i)
PClo-idem (piso x x₁) = piso (PClo-idem x) x₁


PClo-idem''' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →          PClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
PClo-idem''' {𝓤}{𝓦} {𝒦} (pbase x) = piso x lift-alg-≅
PClo-idem''' {𝓤}{𝓦} {𝒦} (prod{I}{𝒜} x) = {!!}
 -- where
 --  h₀ : (i : I) → lift-alg (𝒜 i) (𝓤 ⊔ 𝓦) ∈ PClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦)
 --  h₀ = x
 --  l𝒜 : (i : I) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 --  l𝒜 i = lift-alg (𝒜 i) (𝓤 ⊔ 𝓦)

 --  ξ : (i : I) → (l𝒜 i) ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  ξ i = PClo-idem'''{𝓤}{𝓦}{𝒦} (x i)

 --  -- γ' : ⨅ 𝒜 ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  -- γ' = prod{𝓤 = 𝓤 ⊔ 𝓦}{𝓦 = 𝓤 ⊔ 𝓦}{I = I}{𝒜 = 𝒜} ξ
 --  γ : ⨅ 𝒜 ∈ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
 --  γ = {!!} -- prod{𝓤 = 𝓤 ⊔ 𝓦}{𝓦 = 𝓤 ⊔ 𝓦}{I = I}{𝒜 = 𝒜} ξ
-- prod{I = I}{𝒜 = 𝒜} λ i → PClo-idem'''{𝓤}{𝓦}{𝒦} (x i)
PClo-idem''' {𝓤}{𝓦} {𝒦} (piso x x₁) = piso (PClo-idem'''{𝓤}{𝓦} x) x₁

PClo-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → 𝒦 ⊆ PClo{𝓤}{𝓤} 𝒦
PClo-expa KA = pclo-base KA



----------------------------------------------------------------------------------------------
-- For a given algebra 𝑨, and class 𝒦 of algebras, we will find the following fact useful
-- (e.g., in proof of Birkhoff's HSP theorem):  𝑨 ∈ SClo 𝒦  ⇔  𝑨 IsSubalgebraOfClass 𝒦

SClo→Subalgebra : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑨 : Algebra 𝓠 𝑆}
 →                𝑨 ∈ SClo{𝓠}{𝓠} 𝒦 →  𝑨 IsSubalgebraOfClass 𝒦
SClo→Subalgebra{𝓠}{𝒦}{𝑩}(sbase{𝑨} x) = 𝑨 , (𝑨 , refl-≤) , x , sym-≅ lift-alg-≅
SClo→Subalgebra {𝓠} {𝒦} {.(fst sa)} (sub{𝑨 = 𝑨} x sa) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra x

  𝑮 : Algebra 𝓠 𝑆
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
SClo→Subalgebra {𝓠} {𝒦} {𝑨} (siso{𝑩} SCloB 𝑩≅𝑨) = γ
 where
  IH : 𝑩 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra SCloB
  𝔸 : Algebra _ 𝑆
  𝔸 = ∣ IH ∣
  SA : SUBALGEBRA 𝔸
  SA = fst ∥ IH ∥
  𝔸∈𝒦 : 𝔸 ∈ 𝒦
  𝔸∈𝒦 = fst ∥ snd IH ∥
  𝑩≅SA : 𝑩 ≅ ∣ SA ∣
  𝑩≅SA = snd ∥ snd IH ∥
  SA≤𝔸 : ∣ SA ∣ ≤ 𝔸
  SA≤𝔸 = ∥ SA ∥
  γ : 𝑨 IsSubalgebraOfClass 𝒦
  γ = 𝔸 , SA , 𝔸∈𝒦 , trans-≅ 𝑨 𝑩 (∣ SA ∣) (sym-≅ 𝑩≅𝑨)  𝑩≅SA


SClo→Subalgebra' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑩 ∈ SClo{𝓤}{𝓦} 𝒦 →  𝑩 IsSubalgebraOfClass 𝒦
SClo→Subalgebra' {𝓤}{𝓦}{𝒦} (sbase{𝑨} KA) = 𝑨 , ((lift-alg 𝑨 𝓦) , lA≤A) , KA , refl-≅
 where
  lA≤A : (lift-alg 𝑨 𝓦) ≤ 𝑨
  lA≤A = lift-alg-lift-≤-lower 𝑨 {𝑨} refl-≤

SClo→Subalgebra' {𝓤} {𝓦} {𝒦} {.(fst sa)} (sub{𝑨 = 𝑨} x sa) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra'{𝓤}{𝓦}{𝒦}{𝑨} x

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

SClo→Subalgebra' {𝓤}{𝓦}{𝒦}{𝑩}(siso{𝑨} SCloA A≅B) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = SClo→Subalgebra' SCloA
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
LemPS⊆SP : {𝓠 : Universe} → hfunext 𝓠 𝓠
 →         {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{I : 𝓠 ̇}{ℬ : I → Algebra 𝓠 𝑆}
 →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓠}{𝓠} 𝒦)

LemPS⊆SP{𝓠}hfe{𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓠}{𝓠}{I = I}{𝒜 = 𝒜} PClo𝒜) , (⨅≅ gfe ℬ≅SA)
 where
  𝒜 = λ i → ∣ ℬ≤𝒦 i ∣                -- 𝒜 : I → Algebra 𝓠 𝑆
  SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣        -- SA : I → Algebra 𝓠 𝑆
  𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣       -- 𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
  PClo𝒜 : ∀ i → (lift-alg (𝒜 i) 𝓠) ∈ PClo{𝓠}{𝓠} 𝒦
  PClo𝒜 = λ i → pbase (𝒦𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ ℬ≤𝒦 i ∥ ∣      -- SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  ℬ≅SA = λ i → ∥ snd ∥ ℬ≤𝒦 i ∥ ∥      -- ℬ≅SA : ∀ i → ℬ i ≅ SA i
  h = λ i → ∣ SA≤𝒜 i ∣                 -- h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift hfe hfe{I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)

--TODO: combine the last proof and the next proof
LemPS⊆SP' : {𝓘 𝓤 : Universe} → hfunext 𝓘 (𝓘 ⊔ 𝓤) → hfunext 𝓘 𝓤
 →         {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{I : 𝓘 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →         ((i : I) → (lift-alg (ℬ i) 𝓘) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓤}{𝓘} 𝒦)

LemPS⊆SP'{𝓘}{𝓤} hfe hfep {𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤}{𝓘}{I = I}{𝒜 = 𝒜} PClo𝒜) , γ
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

LemPS⊆SP'' : {𝓘 𝓤 𝓦 : Universe} → hfunext 𝓘 (𝓘 ⊔ 𝓤) → hfunext 𝓘 (𝓤 ⊔ 𝓦)
 →         {𝒦 : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦))}{I : 𝓘 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →         ((i : I) → (lift-alg (ℬ i) 𝓘) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (PClo{𝓤 ⊔ 𝓦}{𝓘} 𝒦)

LemPS⊆SP''{𝓘}{𝓤}{𝓦} hfe hfep {𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (prod{𝓤 ⊔ 𝓦}{𝓘}{I = I}{𝒜 = 𝒜} PClo𝒜) , γ
 where
  𝒜 : I → Algebra (𝓤 ⊔ 𝓦) 𝑆
  𝒜 = λ i → ∣ ℬ≤𝒦 i ∣

  SA : I → Algebra (𝓘 ⊔ 𝓤) 𝑆
  SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣

  𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
  𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣

  PClo𝒜 : ∀ i → (lift-alg (𝒜 i) 𝓘) ∈ PClo{𝓤 ⊔ 𝓦}{𝓘} 𝒦
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
    ii = embedding-lift{𝓠 = (𝓘 ⊔ 𝓤)}{𝓤 = (𝓤 ⊔ 𝓦)}{𝓘 = 𝓘} hfe hfep {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe ℬ≅SA

PS⊆SP : {𝓠 : Universe} → hfunext 𝓠 𝓠 → {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
 →      PClo{𝓠}{𝓠} (SClo{𝓠}{𝓠} 𝒦) ⊆ SClo{𝓠}{𝓠} (PClo{𝓠}{𝓠} 𝒦)
PS⊆SP hfe (pbase (sbase x)) = sbase (pbase x)
PS⊆SP {𝓠} hfe{𝒦}  (pbase (sub x sa)) = SClo-mono{𝓠}{𝓠}{𝒦}{PClo{𝓠}{𝓠} 𝒦} (PClo-expa{𝓠}{𝒦})
                                           (siso (sub x sa) lift-alg-≅)
PS⊆SP {𝓠} hfe {𝒦}  (pbase (siso{𝑨}{𝑩} KA AB)) = sub α ζ
 where
  lB : Algebra 𝓠 𝑆
  lB = lift-alg 𝑩 𝓠
  α : 𝑨 ∈ SClo (PClo 𝒦)
  α = SClo-mono{𝓠}{𝓠}{𝒦}{PClo 𝒦} PClo-expa KA
  BA : 𝑩 ≤ 𝑨
  BA = Iso-≤ 𝑨 𝑩 refl-≤ (sym-≅ AB)
  β : SUBALGEBRA 𝑨
  β = 𝑩 , BA
  ζ : SUBALGEBRA 𝑨
  ζ = lB , Iso-≤ 𝑨 lB BA (sym-≅ lift-alg-≅)

PS⊆SP {𝓠} hfe {𝒦} {.((∀ i → ∣ 𝒜 i ∣) , (λ f proj i → ∥ 𝒜 i ∥ f (λ args → proj args i)))}
 (prod{I = I}{𝒜 = 𝒜} PSCloA) = γ
  where
   ζ : (i : I) → (lift-alg (𝒜 i) 𝓠) ∈ SClo (PClo 𝒦)
   ζ i = PS⊆SP hfe (PSCloA i)
   ξ : (i : I) → (lift-alg (𝒜 i) 𝓠) IsSubalgebraOfClass (PClo 𝒦)
   ξ i = SClo→Subalgebra (ζ i)

   η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo (PClo 𝒦))
   η' = LemPS⊆SP' {𝓠} hfe hfe {PClo 𝒦}{I}{𝒜} ξ

   η : ⨅ 𝒜 IsSubalgebraOfClass (PClo 𝒦)
   η = mono-≤ (⨅ 𝒜) PClo-idem η'

   γ : ⨅ 𝒜 ∈ SClo (PClo 𝒦)
   γ = Subalgebra→SClo η
PS⊆SP hfe (piso x x₁) = siso (PS⊆SP hfe x) x₁




PS⊆SP''' : {𝓤 : Universe} → hfunext (OV 𝓤)(OV 𝓤)
 →       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 →       PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦) ⊆ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)

PS⊆SP''' {𝓤} hfe {𝒦} (pbase{𝑨} (sbase x)) = γ
 where
  ξ : 𝑨 ∈ PClo{𝓤}{OV 𝓤} 𝒦
  ξ = pbase x
  γ : (lift-alg 𝑨 (OV 𝓤)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
  γ = sbase ξ

-- PS⊆SP''' {𝓤} hfe {𝒦} (pbase {.(Σ.pr₁ sa)} (sub x sa)) = {!!}
PS⊆SP''' {𝓤} hfe {𝒦} (pbase (sub x sa)) =
 SClo-mono'{𝓤}{(OV 𝓤)}{𝒦}{PClo{𝓤}{OV 𝓤} 𝒦} (λ 𝑨 → pbase{𝑨 = 𝑨}) (siso (sub x sa) lift-alg-≅)
PS⊆SP''' {𝓤} hfe {𝒦} (pbase (siso{𝑨}{𝑩} SCloA AB)) = siso α' (lift-alg-iso (OV 𝓤) (OV 𝓤) 𝑨 𝑩 AB)
 where
  lA lB : Algebra (OV 𝓤) 𝑆
  lA = lift-alg 𝑨 (OV 𝓤)
  lB = lift-alg 𝑩 (OV 𝓤)
  α : 𝑨 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
  α = SClo-mono'{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = PClo 𝒦}(λ 𝑨 → pbase{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝑨 = 𝑨}) SCloA
  α' : lA ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
  α' = lift-alg-SClo{OV 𝓤}{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑩 = 𝑨} α

PS⊆SP''' {𝓤} hfe  {𝒦} (prod{I = I}{𝒜 = 𝒜} x) = γ
 where
  ⨅A : Algebra (OV 𝓤) 𝑆
  ⨅A = ⨅ 𝒜

  ζ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ SClo{OV 𝓤}{OV 𝓤}(PClo{𝓤}{OV 𝓤} (𝒦))
  ζ i = PS⊆SP''' hfe (x i)

  ξ : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
  ξ i = SClo→Subalgebra'{OV 𝓤}{OV 𝓤} (ζ i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦))
  η' = LemPS⊆SP'{𝓘 = (OV 𝓤)} {𝓤 = (OV 𝓤)} hfe hfe {𝒦 = PClo{𝓤}{OV 𝓤} 𝒦}{I}{𝒜} ξ

  pci : (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦)) ⊆ PClo{𝓤}{OV 𝓤} 𝒦
  pci = PClo-idem'''{𝓤}{𝓦 = (OV 𝓤)}

  η : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
  η = mono-≤ (⨅ 𝒜) pci η'

  γ : ⨅ 𝒜 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
  γ = Subalgebra→SClo'{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η


PS⊆SP''' hfe (piso x x₁) = siso (PS⊆SP''' hfe x) x₁


-- S⊆SP : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
--       ------------------------------------
--  →     SClo{𝓠}{𝓠} 𝒦  ⊆  SClo (PClo 𝒦)
-- S⊆SP  = SClo-mono PClo-expa

-- -- SPS⊆SP : {𝓠 : Universe} → hfunext 𝓠 𝓠 → {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
-- --         ----------------------------------------
-- --  →       SClo{𝓠}{𝓠} (PClo{𝓠}{𝓠} (SClo{𝓠}{𝓠} 𝒦)) ⊆ SClo{𝓠}{𝓠} (PClo{𝓠}{𝓠} 𝒦)

-- -- SPS⊆SP {𝓠} hfe {𝒦} {.(Lift (Σ.pr₁ _) , (λ f x₁ → lift (Σ.pr₂ _ f (λ i → Lift.lower (x₁ i)))))} (sbase x) = {!γ!}
-- -- SPS⊆SP hfe {𝒦} {.(Σ.pr₁ sa)} (sub x sa) = {!!}
-- -- SPS⊆SP hfe {𝒦} {𝑨} (siso x x₁) = {!!}
-- -- (sbase (pbase (sbase x))) = sbase ? -- (pbase x)
-- -- SPS⊆SP {𝓠} hfe {𝒦} {.(fst sa)} (sbase (pbase (sub x sa))) = sub ? ? -- (S⊆SP x) sa
-- -- SPS⊆SP hfe {𝒦} {𝑨} (sbase (pbase (siso{𝑩} x x₁))) = siso {𝑨 = 𝑩}{𝑩 = 𝑨} (S⊆SP x) x₁

-- -- SPS⊆SP hfe {𝒦} {.((∀ i → ∣ 𝒜 i ∣ ) , (λ f 𝒂 i → ∥ 𝒜 i ∥ f (λ args → 𝒂 args i)))} (sbase (prod{I}{𝒜} x)) = PS⊆SP hfe (prod x)
-- -- SPS⊆SP hfe {𝒦} {𝑨} (sbase (piso{𝑩} x x₁)) = siso{𝑨 = 𝑩}{𝑩 = 𝑨} (PS⊆SP hfe x) x₁
-- -- SPS⊆SP hfe {𝒦} {.(Σ.pr₁ sa)} (sub x sa) = sub (SPS⊆SP hfe x) sa
-- -- SPS⊆SP hfe {𝒦} {𝑨} (siso x x₁) = siso (SPS⊆SP hfe x) x₁


-- {-We also need a way to construct products of all the algebras in a given collection.
--   More precisely, if 𝒦 : Pred (Algebra 𝓤 𝑆) 𝓣 is a class of algebras, we need to
--   construct an index set I and a function 𝒜 : I → Algebra 𝓤 𝑆, where 𝒜 runs through all
--   algebras in 𝒦, so that we can construct the product ⨅ 𝒜 of all algebras in 𝒦. -}



-- ------------------------------------------------------------------------------------
-- -- Products of predicates and their meaning --
-- {-
-- Recall:
-- Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-- Π {𝓤} {𝓥} {X} A = (x : X) → A x
-- -Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-- -Π X Y = Π Y
-- syntax -Π A (λ x → b) = Π x ꞉ A , b
-- Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
-- Pred A 𝓥 = A → 𝓥 ̇
-- ⨅ : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
-- ⨅ {𝓘}{𝓤}{I} 𝒜 =((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}
-- -}

-- ClassUniverses : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → Pred (𝓠 ̇) (OV 𝓠)
-- ClassUniverses 𝒦 A = Σ 𝑨 ꞉ Algebra _ 𝑆 , (𝑨 ∈ 𝒦) × (A ≡ ∣ 𝑨 ∣)

-- ΠU : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ̇
-- ΠU 𝒦 = Π (ClassUniverses 𝒦)

-- ΠP : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ̇
-- ΠP 𝒦 = Π 𝒦

-- -- A proof p : Π 𝒦 is a proof that every algebra of type Algebra 𝓠 𝑆 belongs to 𝒦.
-- ΠP-meaning : {𝓠 : Universe}(𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠))
--  →            Π 𝒦  →  (𝑨 : Algebra 𝓠 𝑆) → 𝑨 ∈ 𝒦
-- ΠP-meaning 𝒦 p 𝑨 = p 𝑨


-- ΠSClo : {𝓠 : Universe} (𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)) → _ ̇
-- ΠSClo{𝓠} 𝒦 = Π (SClo{𝓠}{𝓠} 𝒦)


ℑ : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆) (OV 𝓤) → (OV 𝓤) ̇
ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

ℑ→A : {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
 →    (i : ℑ 𝒦) → Algebra 𝓤 𝑆
ℑ→A _ i = ∣ i ∣

class-product : {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Algebra (OV 𝓤) 𝑆
class-product 𝒦 = ⨅ (ℑ→A 𝒦)

class-product-S-∈-PS : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 →       class-product (SClo{𝓤}{𝓤} 𝒦) ∈ PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝒦)
class-product-S-∈-PS {𝓤}{𝒦} = γ
 where
  I : (OV 𝓤) ̇
  I = ℑ{𝓤} (SClo 𝒦)
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = ℑ→A{𝓤} (SClo 𝒦)
  ⨅𝒜 : Algebra (OV 𝓤) 𝑆
  ⨅𝒜 = ⨅ 𝒜
  KA : (i : I) → 𝒜 i ∈ (SClo{𝓤}{𝓤} 𝒦)
  KA i = ∥ i ∥
  lKA : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) ∈ PClo{𝓤}{OV 𝓤} (SClo 𝒦)
  lKA i = pbase (KA i)
  γ : ⨅ 𝒜 ∈ PClo{𝓤}{OV 𝓤} (SClo 𝒦)
  γ = prod{I = I}{𝒜 = 𝒜} lKA


class-product-S-∈-PS' : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 →       class-product (SClo{𝓤}{𝓤} 𝒦) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
class-product-S-∈-PS' {𝓤}{𝒦} = γ
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


class-prod-S-∈-SP' : {𝓤 : Universe} → hfunext (OV 𝓤) (OV 𝓤)
 →                  {𝑲 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                    --------------------------------------------------
 →                  (class-product (SClo{𝓤}{𝓤} 𝑲)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)

class-prod-S-∈-SP' {𝓤} hfe {𝑲} = γ
 where
  ξ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝑲)
  ξ = class-product-S-∈-PS' {𝓤}{𝑲}

  γ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝑲)
  γ = PS⊆SP''' {𝓤} hfe ξ




-- class-prod-S-∈-SP : {𝓤 : Universe} → hfunext (OV 𝓤) 𝓤 → hfunext (OV 𝓤) (OV 𝓤)
--  →                  {𝑲 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--                     --------------------------------------------------
--  →                  class-product (SClo{𝓤}{𝓤} 𝑲) ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝑲)
-- class-prod-S-∈-SP {𝓤} hfe hfe' {𝑲} = γ
--  where
--   ξ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝑲)
--   ξ = class-product-S-∈-PS {𝓤}{𝑲}

--   γ : class-product (SClo{𝓤}{𝓤} 𝑲) ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝑲)
--   γ = PS⊆SP'' {𝓤} hfe hfe' ξ




------------------------------------------------------------------------------------------
-- Compatibilities
-- ---------------
products-preserve-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
                               (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →                             ((i : I) → (𝒜 i) ⊧ p ≈ q)
                               --------------------------------------------------
 →                             ⨅ 𝒜 ⊧ p ≈ q

products-preserve-identities p q I 𝒜 𝒜pq = γ
  where
   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = gfe λ a →
    (p ̇ ⨅ 𝒜) a                           ≡⟨ interp-prod gfe p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ gfe (λ i → cong-app (𝒜pq i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ ⨅ 𝒜) a                           ∎

lift-products-preserve-ids : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
                               (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →                             ((i : I) → (lift-alg (𝒜 i) 𝓦) ⊧ p ≈ q)
                               --------------------------------------------------
 →                             ⨅ 𝒜 ⊧ p ≈ q

lift-products-preserve-ids {𝓤}{𝓦} p q I 𝒜 lApq = products-preserve-identities p q I 𝒜 Aipq
  where
   Aipq : (i : I) → (𝒜 i) ⊧ p ≈ q
   Aipq i = ⊧-≅ (lift-alg (𝒜 i) 𝓦) (𝒜 i) p q (lApq i) (sym-≅ lift-alg-≅)

products-in-class-preserve-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                        {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                                        (p q : Term{𝓧}{X})
                                        (I : 𝓤 ̇)(𝒜 : I → Algebra 𝓤 𝑆)
 →                                      𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
                                        -----------------------------------------------------
 →                                       ⨅ 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities p q I 𝒜 α K𝒜 = γ
  where
   β : ∀ i → (𝒜 i) ⊧ p ≈ q
   β i = α (K𝒜 i)

   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 β

subalgebras-preserve-identities : {𝓤 𝓠 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
                                  (p q : Term)
                                  (𝑩 : SubalgebraOfClass 𝒦)
 →                                𝒦 ⊧ p ≋ q
                                  -------------
 →                                ∣ 𝑩 ∣ ⊧ p ≈ q

subalgebras-preserve-identities {𝓤}{X = X} p q (𝑩 , 𝑨 , SA , (KA , BisSA)) Kpq = γ
 where
  𝑩' : Algebra 𝓤 𝑆
  𝑩' = ∣ SA ∣

  h' : hom 𝑩' 𝑨
  h' = (∣ snd SA ∣ , snd ∥ snd SA ∥ )

  f : hom 𝑩 𝑩'
  f = ∣ BisSA ∣

  h : hom 𝑩 𝑨
  h = HCompClosed 𝑩 𝑩' 𝑨 f h'

  hem : is-embedding ∣ h ∣
  hem = ∘-embedding h'em fem
   where
    h'em : is-embedding ∣ h' ∣
    h'em = fst ∥ snd SA ∥

    fem : is-embedding ∣ f ∣
    fem = iso→embedding BisSA

  β : 𝑨 ⊧ p ≈ q
  β = Kpq KA

  ξ : (b : X → ∣ 𝑩 ∣ ) → ∣ h ∣ ((p ̇ 𝑩) b) ≡ ∣ h ∣ ((q ̇ 𝑩) b)
  ξ b =
   ∣ h ∣((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 h p b ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ b) ≡⟨ intensionality β (∣ h ∣ ∘ b) ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 h q b)⁻¹ ⟩
   ∣ h ∣((q ̇ 𝑩) b)  ∎

  hlc : {b b' : domain ∣ h ∣} → ∣ h ∣ b ≡ ∣ h ∣ b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc ∣ h ∣ hem) hb≡hb'

  γ : 𝑩 ⊧ p ≈ q
  γ = gfe λ b → hlc (ξ b)


-- ⇒ (the "only if" direction)
identities-compatible-with-homs : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                                  (p q : Term) →  𝒦 ⊧ p ≋ q
                                 -----------------------------------------------------
 →                                ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻 X) 𝑨)
                                  →  ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X)

identities-compatible-with-homs {X = X} p q α 𝑨 KA h = γ
 where
  β : ∀(𝒂 : X → ∣ 𝑻 X ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
  β 𝒂 = intensionality (α KA) (∣ h ∣ ∘ 𝒂)

  ξ : ∀(𝒂 : X → ∣ 𝑻 X ∣ ) → ∣ h ∣ ((p ̇ 𝑻 X) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻 X) 𝒂)
  ξ 𝒂 =
   ∣ h ∣ ((p ̇ 𝑻 X) 𝒂)  ≡⟨ comm-hom-term gfe (𝑻 X) 𝑨 h p 𝒂 ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ β 𝒂 ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 h q 𝒂)⁻¹ ⟩
   ∣ h ∣ ((q ̇ 𝑻 X) 𝒂)  ∎

  γ : ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X)
  γ = gfe ξ

-- ⇐ (the "if" direction)
homs-compatible-with-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                                  (p q : Term)
 →                                ( ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom (𝑻 X) 𝑨)
                                           → ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X) )
                                  ----------------------------------------------------
 →                                 𝒦 ⊧ p ≋ q

homs-compatible-with-identities {X = X} p q β {𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
   h 𝒂 = lift-hom 𝑨 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂            ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨(comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻 X)) ℊ  ≡⟨ ap (λ - → - ℊ) (β 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻 X)) ℊ  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) q ℊ) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (q ̇ 𝑨) 𝒂             ∎

compatibility-of-identities-and-homs : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                                       (p q : Term{𝓧}{X})
                 ----------------------------------------------------------------
 →                (𝒦 ⊧ p ≋ q) ⇔ (∀(𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦)(hh : hom (𝑻 X) 𝑨)
                                           →   ∣ hh ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻 X))

compatibility-of-identities-and-homs p q = identities-compatible-with-homs p q ,
                                             homs-compatible-with-identities p q

---------------------------------------------------------------
--Compatibility of identities with interpretation of terms
hom-id-compatibility : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                       (p q : Term{𝓧}{X})
                       (𝑨 : Algebra 𝓤 𝑆)(ϕ : hom (𝑻 X) 𝑨)
 →                      𝑨 ⊧ p ≈ q
                      ------------------
 →                     ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

hom-id-compatibility {X = X} p q 𝑨 ϕ β = ∣ ϕ ∣ p            ≡⟨ ap ∣ ϕ ∣ (term-agreement p) ⟩
                                 ∣ ϕ ∣ ((p ̇ 𝑻 X) ℊ)  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 ϕ p ℊ) ⟩
                                 (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality β (∣ ϕ ∣ ∘ ℊ)  ⟩
                                 (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 ϕ q ℊ)⁻¹ ⟩
                                 ∣ ϕ ∣ ((q ̇ 𝑻 X) ℊ)  ≡⟨ (ap ∣ ϕ ∣ (term-agreement q))⁻¹ ⟩
                                 ∣ ϕ ∣ q              ∎

--------------------------------------------------------------------------------
 --Identities for product closure
pclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (PClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
pclo-id1 p q α (pbase x) = lift-alg-⊧ _ p q (α x) -- α x
pclo-id1 {𝓤}{𝓧}{X} p q α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
 where
  lA : I → Algebra 𝓤 𝑆
  lA i = (lift-alg (𝒜 i) 𝓤)

  IH : (i : I) → (p ̇ (lA i)) ≡ (q ̇ (lA i))
  IH = λ i → pclo-id1{𝓤}{𝓧}{X} p q α  ( 𝒜-P𝒦  i )

  γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
  γ = lift-products-preserve-ids p q I 𝒜 IH

pclo-id1 p q α (piso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = pclo-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁


pclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → ((PClo{𝓤}{𝓤} 𝒦) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
pclo-id2 PCloKpq KA = PCloKpq (pclo-base KA)

-----------------------------------------------------------------
--Identities for subalgebra closure
-- The singleton set.
｛_｝ : {𝓤 : Universe} → Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(OV 𝓤)
｛ 𝑨 ｝ 𝑩 = 𝑨 ≡ 𝑩


sclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (SClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
sclo-id1 p q α (sbase x) = lift-alg-⊧ _ p q (α x)
sclo-id1 {𝓤}{𝓧}{X}{𝒦} p q α (sub {𝑨 = 𝑨} SCloA sa) =
 --Apply subalgebras-preserve-identities to the class 𝒦 ∪ ｛ 𝑨 ｝
 subalgebras-preserve-identities p q (∣ sa ∣ , 𝑨 , sa , inj₂ 𝓇ℯ𝒻𝓁 , id≅) γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = sclo-id1 {𝓤}{𝓧}{X}p q α SCloA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq (refl _) = β

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Apq y
sclo-id1 p q α (siso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = sclo-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁

sclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (SClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
sclo-id2 p KA = p (sclo-base KA)

--------------------------------------------------------------------
--Identities for hom image closure
hclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (HClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
hclo-id1 p q α (hbase x) = lift-alg-⊧ _ p q (α x) -- α KA
hclo-id1 {𝓤}{𝓧}{X} p q α (himg{𝑨} HCloA (𝑩 , ϕ , (ϕhom , ϕsur))) = γ
 where
  β : 𝑨 ⊧ p ≈ q
  β = (hclo-id1{𝓤}{𝓧}{X} p q α) HCloA

  preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur (𝒃 x)))

  ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur (𝒃 x))

  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ 𝒃 →
   (p ̇ 𝑩) 𝒃              ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
   (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
   ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality β (preim 𝒃)) ⟩
   ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
   (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
   (q ̇ 𝑩) 𝒃               ∎
hclo-id1 p q α (hiso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = hclo-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁


hclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (HClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
hclo-id2 p x = p (hclo-base x)

--------------------------------------------------------------------
--Identities for HSP closure
vclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (VClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
vclo-id1 p q α (vbase x) = lift-alg-⊧ _ p q (α x)
vclo-id1 {𝓤}{𝓧}{X} p q α (vprod{I = I}{𝒜 = 𝒜} VClo𝒜) = γ
 where
  lA : I → Algebra 𝓤 𝑆
  lA i = (lift-alg (𝒜 i) 𝓤)
  IH : (i : I) → lA i ⊧ p ≈ q
  IH i = vclo-id1{𝓤}{𝓧}{X} p q α (VClo𝒜 i)

  γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
  γ = lift-products-preserve-ids p q I 𝒜 IH

vclo-id1{𝓤}{𝓧}{X}{𝒦} p q α ( vsub {𝑨 = 𝑨} VCloA sa ) =
 subalgebras-preserve-identities p q (∣ sa ∣ , 𝑨 , sa , inj₂ 𝓇ℯ𝒻𝓁 , id≅) γ
  where
   IH : 𝑨 ⊧ p ≈ q
   IH = vclo-id1 {𝓤}{𝓧}{X}p q α VCloA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq (refl _) = IH

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Asinglepq y


vclo-id1 {𝓤}{𝓧}{X} p q α (vhom{𝑨 = 𝑨} VCloA (𝑩 , ϕ , (ϕh , ϕE))) = γ
 where
  IH : 𝑨 ⊧ p ≈ q
  IH = vclo-id1 {𝓤}{𝓧}{X}p q α VCloA

  preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE (𝒃 x)))

  ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE (𝒃 x))

  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ 𝒃 →
   (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
   (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
   ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality IH (preim 𝒃)) ⟩
   ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
   (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))   ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
   (q ̇ 𝑩) 𝒃                ∎

vclo-id1 p q α (viso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = vclo-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁


vclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (VClo{𝓤}{𝓤} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
vclo-id2 p KA = p (vclo-base KA)






-- -----------=====================================================================================

-- -- PS⊆SP' : {𝓤 : Universe} → hfunext (OV 𝓤) (OV 𝓤)
-- --  →       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
-- --  →       PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦) ⊆ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)

-- -- PS⊆SP' {𝓤} hfe {𝒦} (pbase{𝑨} (sbase x)) = γ
-- --  where
-- --   ξ : 𝑨 ∈ PClo{𝓤}{OV 𝓤} 𝒦
-- --   ξ = pbase x
-- --   γ : (lift-alg 𝑨 (OV 𝓤)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   γ = sbase ξ
-- -- PS⊆SP' {𝓤} hfe {𝒦} (pbase (sub x sa)) = γ
-- --  where
-- --   SCloSA : ∣ sa ∣ ∈ SClo{𝓤}{OV 𝓤} 𝒦
-- --   SCloSA = sub x sa
-- --   SCloSA' : (lift-alg ∣ sa ∣ (OV 𝓤)) ∈ SClo{𝓤}{OV 𝓤} 𝒦
-- --   SCloSA' = lift-alg-SClo{𝓤}{OV 𝓤}{OV 𝓤}{𝒦}{∣ sa ∣} SCloSA
-- --   Smono : SClo{𝓤}{OV 𝓤} 𝒦 ⊆ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   Smono = SClo-mono'{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = (PClo{𝓤}{OV 𝓤} 𝒦)} (λ 𝑨 → pbase{𝓤}{OV 𝓤})
-- --   γ : SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦) (lift-alg ∣ sa ∣ (OV 𝓤))
-- --   γ = Smono SCloSA'

-- -- PS⊆SP' {𝓤} hfe {𝒦} (pbase (siso{𝑨}{𝑩} SCloA AB)) = γ
-- --  where
-- --   lB : Algebra (OV 𝓤) 𝑆
-- --   lB = lift-alg 𝑩 (OV 𝓤)
-- --   α : 𝑨 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   α = SClo-mono'{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = PClo 𝒦}(λ 𝑨 → pbase{𝓤 = 𝓤}{𝓦 = (OV 𝓤)}{𝑨 = 𝑨}) SCloA
-- --   BA : 𝑩 ≤ 𝑨
-- --   BA = Iso-≤ 𝑨 𝑩 refl-≤ (sym-≅ AB)
-- --   β : SUBALGEBRA 𝑨
-- --   β = 𝑩 , BA
-- --   ξ : 𝑩 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   ξ = sub α β
-- --   γ : (lift-alg 𝑩 (OV 𝓤)) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   γ = lift-alg-SClo {OV 𝓤}{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑩} ξ

-- -- PS⊆SP' {𝓤} hfe {𝒦} (prod{I = I}{𝒜 = 𝒜} pscloa) = γ
-- --  where
-- --   τ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ PClo{OV 𝓤}{OV 𝓤} (SClo{𝓤}{OV 𝓤} 𝒦)
-- --   τ i = pscloa i
-- --   ζ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   ζ i = PS⊆SP' hfe (τ i)
-- --   ξ : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   ξ i = SClo→Subalgebra'{OV 𝓤}{OV 𝓤} (ζ i)
-- --   η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦))
-- --   η' = LemPS⊆SP'{𝓘 = (OV 𝓤)} {𝓤 = (OV 𝓤)} hfe hfe {𝒦 = PClo{𝓤}{OV 𝓤} 𝒦}{I}{𝒜} ξ
-- --   pci : (PClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤}𝒦)) ⊆ PClo{𝓤}{OV 𝓤} 𝒦
-- --   pci = PClo-idem'{𝓤}{𝓦 = (OV 𝓤)}
-- --   η : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   η = mono-≤ (⨅ 𝒜) pci η'
-- --   γ : ⨅ 𝒜 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- --   γ = Subalgebra→SClo'{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η
-- -- PS⊆SP' {𝓤} hfe (piso x x₁) = siso (PS⊆SP' hfe x) x₁























-- PS⊆SP'' : {𝓤 : Universe} → hfunext (OV 𝓤) 𝓤 → hfunext (OV 𝓤) (OV 𝓤)
--  →       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →       PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝒦) ⊆ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
-- -- →       PClo{𝓤}{OV 𝓤} (SClo{𝓤}{𝓤} 𝒦) ⊆ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (pbase{𝑨} (sbase x)) = γ
--  where
--   ξ : 𝑨 ∈ PClo{𝓤}{𝓤} 𝒦
--   ξ = pbase x
--   γ : (lift-alg 𝑨 (OV 𝓤)) ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   γ = sbase ξ
-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (pbase (sub x sa)) = γ
--  where
--   SCloSA : ∣ sa ∣ ∈ SClo{𝓤}{𝓤} 𝒦
--   SCloSA = sub x sa
--   SCloSA' : (lift-alg ∣ sa ∣ (OV 𝓤)) ∈ SClo{𝓤}{OV 𝓤} 𝒦
--   SCloSA' = lift-alg-SClo{𝓤}{𝓤}{OV 𝓤}{𝒦}{∣ sa ∣} SCloSA
--   Smono : SClo{𝓤}{OV 𝓤} 𝒦 ⊆ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   Smono = SClo-mono{𝓤}{OV 𝓤}{𝒦₁ = 𝒦}{𝒦₂ = (PClo{𝓤}{𝓤} 𝒦)} pclo-base
--   γ : SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦) (lift-alg ∣ sa ∣ (OV 𝓤))
--   γ = Smono SCloSA'

-- PS⊆SP'' {𝓤} hfe hfe'{𝒦} (pbase (siso{𝑨}{𝑩} SCloA AB)) = γ
--  where
--   lA lB : Algebra (OV 𝓤) 𝑆
--   lA = lift-alg 𝑨 (OV 𝓤)
--   lB = lift-alg 𝑩 (OV 𝓤)
--   α : 𝑨 ∈ SClo{𝓤}{𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   α = SClo-mono'{𝓤}{𝓤}{𝒦₁ = 𝒦}{𝒦₂ = PClo 𝒦}(λ 𝑨 → pbase{𝓤 = 𝓤}{𝓦 = 𝓤}{𝑨 = 𝑨}) SCloA
--   α' : lA ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   α' = lift-alg-SClo{𝓤}{𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{𝓤} 𝒦)}{𝑩 = 𝑨} α
--   lA≅lB : lA ≅ lB
--   lA≅lB = lift-alg-iso 𝓤 (OV 𝓤) 𝑨 𝑩 AB
--   γ : (lift-alg 𝑩 (OV 𝓤)) ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   γ = siso α' lA≅lB

-- PS⊆SP'' {𝓤} hfe hfe' {𝒦} (prod{I = I}{𝒜 = 𝒜} pscloa) = γ
--  where
--   ⨅A : Algebra (OV 𝓤) 𝑆
--   ⨅A = ⨅ 𝒜

--   ζ : (i : I) → lift-alg (𝒜 i) (OV 𝓤) ∈ SClo{𝓤}{OV 𝓤}(PClo{𝓤}{𝓤} (𝒦))
--   ζ i = PS⊆SP'' hfe hfe' (pscloa i)

--   ξ : (i : I) → (lift-alg (𝒜 i) (OV 𝓤)) IsSubalgebraOfClass (PClo{𝓤}{𝓤} 𝒦)
--   ξ i = SClo→Subalgebra'{𝓤}{OV 𝓤} (ζ i)

--   η' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤}𝒦))
--   η' = LemPS⊆SP'{𝓘 = (OV 𝓤)} {𝓤 = 𝓤} hfe' hfe {𝒦 = PClo{𝓤}{𝓤} 𝒦}{I}{𝒜} ξ

--   pci : (PClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤}𝒦)) ⊆ PClo{𝓤}{OV 𝓤} 𝒦
--   pci = PClo-idem''{𝓤}{𝓦 = (OV 𝓤)}

--   η : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{OV 𝓤} 𝒦)
--   η = mono-≤ (⨅ 𝒜) pci η'

--   η'' : ⨅ 𝒜 IsSubalgebraOfClass (PClo{𝓤}{𝓤} 𝒦)
--   η'' = {!!} -- mono-≤ (⨅ 𝒜) pci η'

--   γ' : ⨅ 𝒜 ∈ SClo{OV 𝓤}{OV 𝓤} (PClo{𝓤}{OV 𝓤} 𝒦)
--   γ' = Subalgebra→SClo'{OV 𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{OV 𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η
-- -- Subalgebra→SClo' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}{𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
-- --  →                𝑪 IsSubalgebraOfClass 𝒦 → 𝑪 ∈ SClo{𝓤}{𝓦} 𝒦
--   γ : ⨅ 𝒜 ∈ SClo{𝓤}{OV 𝓤} (PClo{𝓤}{𝓤} 𝒦)
--   γ = Subalgebra→SClo'{𝓤}{OV 𝓤}{𝒦 = (PClo{𝓤}{𝓤} 𝒦)}{𝑪 = ⨅ 𝒜} η''

-- PS⊆SP'' {𝓤} hfe hfe'(piso x x₁) = siso (PS⊆SP'' hfe hfe' x) x₁



-- PClo-idem' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → PClo{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓦} 𝒦) ⊆ PClo{𝓤}{𝓦} 𝒦
-- PClo-idem' {𝓤}{𝓦} {𝒦} (pbase x) = piso x lift-alg-≅
-- PClo-idem' {𝓤}{𝓦} {𝒦} (prod{I}{𝒜} x) = {!!}
-- PClo-idem' (piso x x₁) = piso (PClo-idem' x) x₁


-- PClo-idem'' : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
--  →          PClo{𝓤}{𝓤 ⊔ 𝓦} (PClo{𝓤}{𝓤} 𝒦) ⊆ PClo{𝓤}{𝓤 ⊔ 𝓦} 𝒦
-- PClo-idem'' {𝓤}{𝓦} {𝒦} (pbase x) = {!!} -- piso x lift-alg-≅
-- PClo-idem'' {𝓤}{𝓦} {𝒦} (prod{I}{𝒜} x) = {!!} -- prod{I = I}{𝒜 = 𝒜} λ i → PClo-idem'{𝓤}{𝓦}{𝒦} (x i)
-- PClo-idem'' {𝓤}{𝓦} {𝒦} (piso x x₁) = piso (PClo-idem''{𝓤}{𝓦} x) x₁

