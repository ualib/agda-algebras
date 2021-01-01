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

iso-id-compatibility -- (alias)
 ⊧-≅ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
      {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}(p q : Term{𝓧}{X})
 →    𝑨 ⊧ p ≈ q → 𝑨 ≅ 𝑩 → 𝑩 ⊧ p ≈ q
⊧-≅ {𝓤}{𝓦}{𝓧}{X}{𝑨}{𝑩} p q Apq (fh , gh , f∼g , g∼f) = γ
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

iso-id-compatibility = ⊧-≅

lift-alg-id-compatibility
 lift-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
       (𝑨 : Algebra 𝓤 𝑆)(p q : Term{𝓧}{X})
  →    𝑨 ⊧ p ≈ q → (lift-alg 𝑨 𝓦) ⊧ p ≈ q
lift-alg-⊧ 𝑨 p q Apq = ⊧-≅ p q Apq lift-alg-≅
lift-alg-id-compatibility = lift-alg-⊧

lower-alg-id-compatibility : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)
                             (p q : Term{𝓧}{X})
 →                           lift-alg 𝑨 𝓦 ⊧ p ≈ q → 𝑨 ⊧ p ≈ q
lower-alg-id-compatibility {𝓤}{𝓦}{𝓧}{X} 𝑨 p q lApq =
 ⊧-≅ p q lApq (sym-≅ lift-alg-≅)

------------------------------------------------------------------------
-- Equational theories and classes
Th : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →   Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

Mod : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

--alternatives---
--Closure wrt H
data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  hlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H{𝓤}{𝓦} 𝒦
  himg  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H{𝓤}{𝓦} 𝒦

--Closure wrt S
data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S{𝓤}{𝓦} 𝒦
  sub   : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦

--Closure wrt P
data P {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P{𝓤}{𝓦} 𝒦
  produ  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P{𝓤}{𝓦} 𝒦
  prodw  : {I : 𝓦 ̇ }{𝒜 : I → Algebra (𝓤 ⊔ 𝓦) 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P{𝓤}{𝓦} 𝒦
  pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P{𝓤}{𝓦} 𝒦
  pisow  : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P{𝓤}{𝓦} 𝒦

data V {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vlift : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ V{𝓤}{𝓦} 𝒦
  vimg : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦
  vsub  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦
  vprodu : {I : 𝓦 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ V{𝓤}{𝓦} 𝒦
  vprodw : {I : 𝓦 ̇}{𝒜 : I → Algebra (𝓤 ⊔ 𝓦) 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ V{𝓤}{𝓦} 𝒦
  visou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦
  visow  : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V{𝓤}{𝓦} 𝒦


lift-alg-assoc : {𝓤 𝓦 𝓘 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
lift-alg-assoc {𝓤} {𝓦} {𝓘} {𝑨} = TRANS-≅ (TRANS-≅ ζ lift-alg-≅) lift-alg-≅
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅

lower-class : {𝓤 𝓦 : Universe} → Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) → Pred (Algebra 𝓤 𝑆)(OV (𝓤 ⊔ 𝓦))
lower-class {𝓤}{𝓦}𝒦 = λ (𝑨 : Algebra 𝓤 𝑆) → lift-alg 𝑨 𝓦 ∈ 𝒦

-- --P is a closure operator ----------------------------------------
-- --In particular, it's expansive...
P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ P{𝓤}{𝓤} 𝒦
P-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

P-idemp : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P{𝓤}{𝓦} (P{𝓤}{𝓤} 𝒦) ⊆ P{𝓤}{𝓦} 𝒦

P-idemp (pbase x) = pliftu x
P-idemp {𝓤} (pliftu x) = pliftu (P-idemp{𝓤}{𝓤} x)
P-idemp (pliftw x) = pliftw (P-idemp x)
P-idemp {𝓤} (produ x) = produ (λ i → P-idemp{𝓤}{𝓤} (x i))
P-idemp (prodw x) = prodw (λ i → P-idemp (x i))
P-idemp {𝓤} (pisou x x₁) = pisou (P-idemp{𝓤}{𝓤} x) x₁
P-idemp (pisow x x₁) = pisow (P-idemp x) x₁


P-idemp' : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →        P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P-idemp' (pbase x) = pliftw x
P-idemp' {𝓤} {𝓦} (pliftu x) = pliftw (P-idemp' {𝓤}{𝓦} x)
P-idemp' {𝓤} {𝓦} (pliftw x) = pliftw (P-idemp' {𝓤}{𝓦} x)
P-idemp' {𝓤} {𝓦} (produ x) = prodw (λ i → P-idemp' {𝓤}{𝓦} (x i))
P-idemp' {𝓤} {𝓦} (prodw x) = prodw (λ i → P-idemp' {𝓤}{𝓦} (x i))
P-idemp' {𝓤} {𝓦} (pisou x x₁) = pisow (P-idemp' {𝓤}{𝓦} x) x₁
P-idemp' {𝓤} {𝓦} (pisow x x₁) = pisow (P-idemp' {𝓤}{𝓦} x) x₁


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
  plA = pliftu pA

  γ : lB IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  γ = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 𝑪 B≅C)


--S is a closure operator -------------------------------------------
--In particular, it's monotone.
S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'
S-mono ante (sbase x) = sbase (ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S-mono{𝓤}{𝓤} ante x)
S-mono ante (sub{𝑨}{𝑩} sA B≤A) = sub (S-mono ante sA) B≤A
S-mono ante (siso x x₁) = siso (S-mono ante x) x₁

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


module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} where

 S→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦
 S→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
 S→subalgebra (slift{𝑩} x) = 𝑨 , SA , KA , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
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

 S→subalgebra {𝑩} (sub{𝑨} sA B≤A) = 𝑨' , (𝑩 , B≤A') , KA , refl-≅
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

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) = γ
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


S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (sbase{𝑨} x) =
 siso spllA (sym-≅ lift-alg-≅)
  where
   llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   llA = lift-alg (lift-alg 𝑨 𝓦) (𝓤 ⊔ 𝓦)

   spllA : llA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
   spllA = sbase{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = (𝓤 ⊔ 𝓦)} (pbase x)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) =
 subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lift-alg 𝑨 𝓦} lAsc
  where
   splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} x

   Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : (lift-alg 𝑨 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
   lAsc = lift-alg-subP Asc

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (sub{𝑨} sA B≤A) =
 sub{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp (lift-alg-sub-lift 𝑨 B≤A)
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

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP (S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu)

  lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B


lemPS⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →        {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →        ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lemPS⊆SP {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K =
 ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (produ{𝓤}{𝓦}{I = I}{𝒜 = 𝒜} (λ i → P-expa (KA i)) ) , γ
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

module _ {𝓤 : Universe}{𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} {hfe : hfunext (OV 𝓤)(OV 𝓤)} where

 PS⊆SP : (P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦u)) ⊆ (S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u))
 PS⊆SP (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP (pbase (slift{𝑨} x)) = slift splA
  where
   splA : (lift-alg 𝑨 (OV 𝓤)) ∈ S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u)
   splA = S⊆SP{𝓤}{OV 𝓤}{𝒦u} (slift x)

 PS⊆SP (pbase {𝑩} (sub{𝑨} sA B≤A)) = siso γ refl-≅
  where
   lA lB : Algebra (OV 𝓤) 𝑆
   lA = lift-alg 𝑨 (OV 𝓤)
   lB = lift-alg 𝑩 (OV 𝓤)

   ζ : lB ≤ lA
   ζ = lift-alg-lift-≤-lift 𝑩{𝑨} B≤A

   spA : lA ∈ S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u)
   spA = S⊆SP{𝓤}{OV 𝓤}{𝒦u} (slift sA)

   γ : (lift-alg 𝑩 (OV 𝓤)) ∈ (S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u))
   γ = sub{𝓤 = (OV 𝓤)} spA ζ


 PS⊆SP (pbase (siso{𝑨}{𝑩} x A≅B)) = siso splA ζ
  where
   lA lB : Algebra (OV 𝓤) 𝑆
   lA = lift-alg 𝑨 (OV 𝓤)
   lB = lift-alg 𝑩 (OV 𝓤)

   ζ : lA ≅ lB
   ζ = lift-alg-iso 𝓤 (OV 𝓤) 𝑨 𝑩 A≅B

   splA : lA ∈ S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u)
   splA = S⊆SP (slift x)

 PS⊆SP (pliftu x) = slift (PS⊆SP x)
 PS⊆SP (pliftw x) = slift (PS⊆SP x)

 PS⊆SP (produ{I}{𝒜} x) = γ
  where
   uw : Universe
   uw = OV 𝓤

   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{uw} 𝒦u)
   ξ i = S→subalgebra{𝒦 = (P{𝓤}{uw} 𝒦u)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
   η' = lemPS⊆SP{𝓤 = (uw)}{uw}{𝒦 = (P{𝓤}{uw} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{uw}{uw} (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
   η = subalgebra→S{𝓤 = (uw)}{𝓦 = uw}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{uw}{uw} (P{𝓤}{uw} 𝒦u)
   γ = (S-mono{𝓤 = (uw)}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝒦' = (P{𝓤}{uw} 𝒦u)} (P-idemp')) η

 PS⊆SP (prodw{I}{𝒜} x) = γ
  where
   uw : Universe
   uw = OV 𝓤

   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{uw} 𝒦u)
   ξ i = S→subalgebra{𝒦 = (P{𝓤}{uw} 𝒦u)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
   η' = lemPS⊆SP{𝓤 = (uw)}{uw}{𝒦 = (P{𝓤}{uw} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{uw}{uw} (P{uw}{uw} (P{𝓤}{uw} 𝒦u))
   η = subalgebra→S{𝓤 = (uw)}{𝓦 = uw}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{uw}{uw} (P{𝓤}{uw} 𝒦u)
   γ = (S-mono{𝓤 = (uw)}{𝒦 = (P{uw}{uw} (P{𝓤}{uw} 𝒦u))}{𝒦' = (P{𝓤}{uw} 𝒦u)} (P-idemp')) η

 PS⊆SP (pisou{𝑨}{𝑩} pA A≅B) = siso{OV 𝓤}{OV 𝓤}{P{𝓤}{OV 𝓤} 𝒦u}{𝑨}{𝑩} spA A≅B
  where
   spA : 𝑨 ∈ S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u)
   spA = PS⊆SP pA

 PS⊆SP (pisow{𝑨}{𝑩} pA A≅B) = siso{OV 𝓤}{OV 𝓤}{P{𝓤}{OV 𝓤} 𝒦u}{𝑨}{𝑩} spA A≅B
  where
   spA : 𝑨 ∈ S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦u)
   spA = PS⊆SP pA


--We now show how to construct the full product of all algebras in a class 𝒦--

-- ℑ will serve as the index of the product
ℑ : {𝓤 : Universe} →  Pred (Algebra 𝓤 𝑆)(OV 𝓤) → (OV 𝓤) ̇
ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

-- 𝔄 produces an algebra for each index (i : ℑ).

𝔄 : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → ℑ 𝒦 → Algebra 𝓤 𝑆
𝔄{𝓤}{𝒦} = λ (i : (ℑ 𝒦)) → ∣ i ∣

-- So the product of all members of 𝒦 can be written simply as follows:
class-product : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
class-product {𝓤} 𝒦 = ⨅ ( 𝔄{𝓤}{𝒦} )

-- To see it more explicitly, here is the expansion of this indexed product.
class-product' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
class-product'{𝓤} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦)) → ∣ i ∣

-- For example, the product of all subalgebras of members of the class 𝒦 is
-- constructed as follows:
ℑs : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → (OV 𝓤) ̇
ℑs{𝓤}{𝒦} = ℑ (S{𝓤}{𝓤} 𝒦)

𝔄s : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → ℑs{𝓤}{𝒦} → Algebra 𝓤 𝑆
𝔄s {𝓤}{𝒦} = 𝔄 {𝒦 = (S{𝓤}{𝓤} 𝒦)}

-- or in a single step, as
class-prod-s : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
class-prod-s {𝓤} 𝒦 = ⨅ ( 𝔄{𝒦 = S{𝓤}{𝓤} 𝒦} )

-- or, in a way that is probably easier to read,
class-prod-s' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
class-prod-s' {𝓤} 𝒦 = class-product ( S{𝓤}{𝓤} 𝒦 )

-- We now prove that the product of all subalgebras of a class 𝒦 belongs to PS(𝒦).
class-prod-s-∈-ps : {𝓤 𝓦 : Universe} {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
                  -----------------------------------------------------------------
 →                  class-product (S{𝓤}{𝓤} 𝒦) ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦))

class-prod-s-∈-ps{𝓤}{𝓦}{𝒦} = pisou{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} ps⨅llA ⨅llA≅cpK
 where
  I : (OV 𝓤) ̇
  I = ℑ (S{𝓤}{𝓤} 𝒦)

  sA : (i : I) → (𝔄 i) ∈ (S{𝓤}{𝓤} 𝒦)
  sA i = ∥ i ∥

  lA llA : I → Algebra (OV 𝓤) 𝑆
  lA i =  lift-alg (𝔄 i) (OV 𝓤)
  llA i = lift-alg (lA i) (OV 𝓤)

  slA : (i : I) → (lA i) ∈ (S{𝓤}{(OV 𝓤)} 𝒦)
  slA i = siso (sA i) lift-alg-≅

  psllA : (i : I) → (llA i) ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{(OV 𝓤)} 𝒦))
  psllA i = pbase{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} (slA i)

  ps⨅llA : ⨅ llA ∈ P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦)
  ps⨅llA = produ{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} psllA

  llA≅A : (i : I) → (llA i) ≅ (𝔄 i)
  llA≅A i = Trans-≅ (llA i) (𝔄 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

  ⨅llA≅cpK : ⨅ llA ≅ class-product (S{𝓤}{𝓤} 𝒦)
  ⨅llA≅cpK = ⨅≅ gfe llA≅A

-- So, since PS⊆SP, we see that that the product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
class-prod-s-∈-sp : {𝓤 𝓦 : Universe} → hfunext (OV 𝓤) (OV 𝓤)
 →                  {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
                --------------------------------------------------------------
 →              class-product (S{𝓤}{𝓤} 𝒦) ∈ (S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦))

class-prod-s-∈-sp{𝓤}{𝓦} hfe = PS⊆SP{hfe = hfe} (class-prod-s-∈-ps{𝓤}{𝓦})



------------------------------------------------------------------------------------------
-- Compatibilities
-- ---------------

product-id-compatibility -- (alias)
 products-preserve-identities
  : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
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
product-id-compatibility = products-preserve-identities

lift-product-id-compatibility -- (alias)
 lift-products-preserve-ids : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
                               (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →                             ((i : I) → (lift-alg (𝒜 i) 𝓦) ⊧ p ≈ q)
                               --------------------------------------------------
 →                             ⨅ 𝒜 ⊧ p ≈ q

lift-products-preserve-ids {𝓤}{𝓦} p q I 𝒜 lApq = products-preserve-identities p q I 𝒜 Aipq
  where
   Aipq : (i : I) → (𝒜 i) ⊧ p ≈ q
   Aipq i = ⊧-≅ p q (lApq i) (sym-≅ lift-alg-≅)   -- (lift-alg (𝒜 i) 𝓦) (𝒜 i) p q 
lift-product-id-compatibility = lift-products-preserve-ids

class-product-id-compatibility -- (alias)
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
class-product-id-compatibility = products-in-class-preserve-identities

subalgebra-id-compatibility -- (alias)
 subalgebras-preserve-identities : {𝓤 𝓠 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
                                  (p q : Term{𝓧}{X})
                                  (𝑩 : SubalgebraOfClass{𝓤}{𝓠} 𝒦)
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

subalgebra-id-compatibility = subalgebras-preserve-identities


-- ⇒ (the "only if" direction)
id-class-hom-compatibility -- (alias)
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
id-class-hom-compatibility = identities-compatible-with-homs

-- ⇐ (the "if" direction)
class-hom-id-compatibility -- (alias)
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
class-hom-id-compatibility = homs-compatible-with-identities

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
P-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (P{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
P-id1 p q α (pbase x) = lift-alg-⊧ _ p q (α x)
P-id1 p q α (pliftu x) = lift-alg-⊧ _ p q ((P-id1 p q α) x)
P-id1 p q α (pliftw x) = lift-alg-⊧ _ p q ((P-id1 p q α) x)
P-id1 {𝓤} {𝓧} p q α (produ{I}{𝒜} x) = γ
 where
  lA : I → Algebra 𝓤 𝑆
  lA i = (lift-alg (𝒜 i) 𝓤)

  IH : (i : I) → (p ̇ (lA i)) ≡ (q ̇ (lA i))
  IH i = lift-alg-⊧ (𝒜 i) p q ((P-id1{𝓤}{𝓧} p q α) (x i))

  γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
  γ = lift-products-preserve-ids p q I 𝒜 IH

P-id1{𝓤}{𝓧} p q α (prodw{I}{𝒜} x) = γ
 where
  lA : I → Algebra 𝓤 𝑆
  lA i = (lift-alg (𝒜 i) 𝓤)

  IH : (i : I) → (p ̇ (lA i)) ≡ (q ̇ (lA i))
  IH i = lift-alg-⊧ (𝒜 i) p q ((P-id1{𝓤}{𝓧} p q α) (x i))

  γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
  γ = lift-products-preserve-ids p q I 𝒜 IH
P-id1 p q α (pisou{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = P-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁
P-id1 p q α (pisow{𝑨}{𝑩} x x₁) =  γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = P-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁

P-id2 : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → ((P{𝓤}{𝓦} 𝒦) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
P-id2 {𝓤}{𝓦}{𝓧}{X} {𝒦} {p}{q} PKpq {𝑨} KA = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  plA : lA ∈ P{𝓤}{𝓦} 𝒦
  plA = pbase KA

  ξ : lA ⊧ p ≈ q
  ξ = PKpq plA
  γ : 𝑨 ⊧ p ≈ q
  γ = lower-alg-id-compatibility 𝑨 p q ξ


-----------------------------------------------------------------
--Identities for subalgebra closure
-- The singleton set.
｛_｝ : {𝓤 : Universe} → Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(OV 𝓤)
｛ 𝑨 ｝ 𝑩 = 𝑨 ≡ 𝑩


S-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (S{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
S-id1 p q α (sbase x) = lift-alg-⊧ _ p q (α x)
S-id1 p q α (slift x) = lift-alg-⊧ _ p q ((S-id1 p q α) x)
-- S-id1 p q α (sub{𝑨}{𝑩} x x₁) = γ
S-id1 {𝓤}{𝓧}{X}{𝒦} p q α (sub{𝑨}{𝑩} sA B≤A) =
 --Apply subalgebras-preserve-identities to the class 𝒦 ∪ ｛ 𝑨 ｝
 subalgebras-preserve-identities p q ((𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ 𝓇ℯ𝒻𝓁 , id≅) ) γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = S-id1 {𝓤}{𝓧}{X}p q α sA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq (refl _) = β

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Apq y

S-id1 p q α (siso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = S-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁

S-id2 : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (S{𝓤}{𝓦} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
S-id2 {𝓤}{𝓦}{𝓧}{X} {𝒦} {p}{q} Spq {𝑨} KA = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  plA : lA ∈ S{𝓤}{𝓦} 𝒦
  plA = sbase KA

  ξ : lA ⊧ p ≈ q
  ξ = Spq plA
  γ : 𝑨 ⊧ p ≈ q
  γ = lower-alg-id-compatibility 𝑨 p q ξ



--------------------------------------------------------------------
--Identities for hom image closure
H-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (H{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
H-id1 p q α (hbase x) = lift-alg-⊧ _ p q (α x)
H-id1 {𝓤}{𝓧}{X}{𝒦} p q α (hlift{𝑨} x) = γ
 where
  β : 𝑨 ⊧ p ≈ q
  β = H-id1 p q α x
  γ : lift-alg 𝑨 𝓤 ⊧ p ≈ q
  γ = lift-alg-⊧ _ p q β

H-id1 {𝓤} {𝓧} {X} p q α (himg{𝑨}{𝑪} HA ((𝑩 , ϕ , (ϕhom , ϕsur)) , B≅C) ) = ⊧-≅ p q γ B≅C
 where
  β : 𝑨 ⊧ p ≈ q
  β = (H-id1{𝓤}{𝓧}{X} p q α) HA

  preim : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → ∣ 𝑨 ∣
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
H-id1 p q α (hiso{𝑨}{𝑩} x x₁) = γ
 where
  ζ : 𝑨 ⊧ p ≈ q
  ζ = H-id1 p q α x
  γ : 𝑩 ⊧ p ≈ q
  γ = lemma-⊧-≅ p q ζ x₁


H-id2 : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (H{𝓤}{𝓦} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
H-id2 {𝓤}{𝓦}{𝓧}{X} {𝒦} {p}{q} Hpq {𝑨} KA = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  plA : lA ∈ H{𝓤}{𝓦} 𝒦
  plA = hbase KA

  ξ : lA ⊧ p ≈ q
  ξ = Hpq plA
  γ : 𝑨 ⊧ p ≈ q
  γ = lower-alg-id-compatibility 𝑨 p q ξ

--------------------------------------------------------------------
--Identities for HSP closure
V-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           (p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (V{𝓤}{𝓤} 𝒦 ⊧ p ≋ q)
V-id1 p q α (vbase x) = lift-alg-⊧ _ p q (α x)
V-id1 {𝓤}{𝓧}{X}{𝒦} p q α (vlift{𝑨} x) = γ
 where
  β : 𝑨 ⊧ p ≈ q
  β = (V-id1 p q α) x
  γ : lift-alg 𝑨 𝓤 ⊧ p ≈ q
  γ = lift-alg-id-compatibility 𝑨 p q β

V-id1 {𝓤}{𝓧}{X} p q α ( vimg{𝑨}{𝑪} VA ((𝑩 , ϕ , (ϕh , ϕE)) , B≅C) ) = ⊧-≅ p q γ B≅C
 where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1 {𝓤}{𝓧}{X}p q α VA

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

V-id1{𝓤}{𝓧}{X}{𝒦} p q α ( vsub {𝑨}{𝑩} VA B≤A ) =
 subalgebras-preserve-identities p q ((𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ 𝓇ℯ𝒻𝓁 , id≅) ) γ
  where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 {𝓤}{𝓧}{X}p q α VA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq (refl _) = IH

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Asinglepq y

V-id1 {𝓤}{𝓧}{X} p q α (vprodu{I}{𝒜} V𝒜) = γ
 where
  IH : (i : I) → 𝒜 i ⊧ p ≈ q
  IH i = V-id1{𝓤}{𝓧}{X} p q α (V𝒜 i)

  γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
  γ = product-id-compatibility p q I 𝒜 IH

V-id1 {𝓤}{𝓧}{X} p q α (vprodw{I}{𝒜} V𝒜) = γ
 where
  IH : (i : I) → 𝒜 i ⊧ p ≈ q
  IH i = V-id1{𝓤}{𝓧}{X} p q α (V𝒜 i)

  γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
  γ = product-id-compatibility p q I 𝒜 IH
V-id1 p q α (visou{𝑨}{𝑩} VA A≅B) = ⊧-≅ p q (V-id1 p q α VA) A≅B
V-id1 p q α (visow{𝑨}{𝑩} VA A≅B) = ⊧-≅ p q (V-id1 p q α VA) A≅B


V-id2 : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
           {p q : Term{𝓧}{X}} → (V{𝓤}{𝓦} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
V-id2 {𝓤}{𝓦}{𝓧}{X} {𝒦} {p}{q} Vpq {𝑨} KA = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  vlA : lA ∈ V{𝓤}{𝓦} 𝒦
  vlA = vbase KA

  ξ : lA ⊧ p ≈ q
  ξ = Vpq vlA
  γ : 𝑨 ⊧ p ≈ q
  γ = lower-alg-id-compatibility 𝑨 p q ξ








