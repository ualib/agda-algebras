\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 19 Sep 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂; Π)

module closure-alternatives
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
data pclo {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ∈ pclo 𝒦
  prod : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → 𝒜 i ∈ pclo{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ pclo 𝒦
  piso : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ pclo{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ pclo{𝓤}{𝓦} 𝒦

data hclo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra 𝓤 𝑆) (OV 𝓤) where
 hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ hclo 𝒦
 himg : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ hclo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ hclo 𝒦
 hiso : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ hclo 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ hclo 𝒦

data sclo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra 𝓤 𝑆) (OV 𝓤) where
 sbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ sclo 𝒦
 sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ sclo 𝒦 → (sa : SUBALGEBRA 𝑨) → ∣ sa ∣ ∈ sclo 𝒦
 siso : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ sclo 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ sclo 𝒦

data vclo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) : Pred (Algebra 𝓤 𝑆) (OV 𝓤) where
 vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ vclo 𝒦
 vprod : {I : 𝓤 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → 𝒜 i ∈ vclo 𝒦) → ⨅ 𝒜 ∈ vclo 𝒦
 vsub  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ vclo 𝒦 → (sa : Subalgebra 𝑨) → ∣ sa ∣ ∈ vclo 𝒦
 vhom  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ vclo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ vclo 𝒦
 viso : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ vclo 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ vclo 𝒦

lift-alg-sub-lift : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑪 IsSubalgebraOf 𝑨 → 𝑪 IsSubalgebraOf (lift-alg 𝑨 𝓦)
lift-alg-sub-lift {𝓤}{𝓦} 𝑨 {𝑪} C≤A = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  A≅lA : 𝑨 ≅ lA
  A≅lA = lift-alg-≅

  f : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  f = ∣ C≤A ∣

  g : ∣ 𝑨 ∣ → ∣ lA ∣
  g = map-≅ A≅lA

  h : ∣ 𝑪 ∣ → ∣ lA ∣
  h = g ∘ f

  hemb : is-embedding h
  hemb = ∘-embedding (map-≅-is-embedding A≅lA) (fst ∥ C≤A ∥)

  hhom : is-homomorphism 𝑪 lA h
  hhom = ∘-hom 𝑪 𝑨 lA {f}{g} (snd ∥ C≤A ∥) (snd ∣ A≅lA ∣)

  γ : 𝑪 IsSubalgebraOf lift-alg 𝑨 𝓦
  γ = h , hemb , hhom


lift-alg-idemp : {𝓤 𝓦 𝓩 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓩)
lift-alg-idemp {𝓤} {𝓦} {𝓩} {𝑨} = γ
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅
  ξ : 𝑨 ≅ lift-alg 𝑨 𝓦
  ξ = lift-alg-≅
  η : lift-alg 𝑨 𝓦 ≅ lift-alg (lift-alg 𝑨 𝓦) 𝓩
  η = lift-alg-≅
  γ :  lift-alg 𝑨 (𝓦 ⊔ 𝓩) ≅ lift-alg (lift-alg 𝑨 𝓦) 𝓩
  γ = TRANS-≅ (TRANS-≅ ζ ξ) η



pclo-idem : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →          pclo{𝓤}{𝓤} (pclo{𝓤}{𝓤} 𝒦) ⊆ pclo{𝓤}{𝓤} 𝒦
pclo-idem (pbase x) = prod x
pclo-idem (prod x) = prod (λ i → pclo-idem (x i))
pclo-idem (piso x x₁) = piso (pclo-idem x) x₁

pclo-idem' : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →          pclo{𝓤}{OV 𝓤} (pclo{𝓤}{𝓤} 𝒦) ⊆ pclo{𝓤}{OV 𝓤} 𝒦
pclo-idem' (pbase{I}{𝒜} x) = prod x -- prod x
pclo-idem' {𝓤}{𝒦} (prod{I}{𝒜} x) = prod{𝓤}{I = I}{𝒜 = 𝒜} (λ i → pclo-idem (x i))
pclo-idem' (piso x x₁) = piso (pclo-idem' x) x₁

----------------------------------------------------------------------------------------------
-- For a given algebra 𝑨, and class 𝒦 of algebras, we will find the following fact useful
-- (e.g., in proof of Birkhoff's HSP theorem):  𝑨 ∈ SClo 𝒦  ⇔  𝑨 IsSubalgebraOfClass 𝒦


----------------------------------------------------------------------------------------
-- The (near) lattice of closures

sclo→subalgebra : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑨 : Algebra 𝓠 𝑆}
 →                𝑨 ∈ sclo 𝒦 →  𝑨 IsSubalgebraOfClass 𝒦
sclo→subalgebra {𝓠} {𝒦} {𝑨} (sbase x) = 𝑨 , (𝑨 , refl-≤) , x , (((λ x → x) , id-is-hom) ,
                                                                (((λ x → x) , id-is-hom) ,
                                                                  ((λ x₁ → refl _) , λ x₁ → refl _)))
sclo→subalgebra {𝓠} {𝒦} {.(fst sa)} (sub{𝑨 = 𝑨} x sa) = γ
 where
  IH : 𝑨 IsSubalgebraOfClass 𝒦
  IH = sclo→subalgebra x

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
sclo→subalgebra {𝓠} {𝒦} {𝑨} (siso{𝑩} SCloB 𝑩≅𝑨) = γ
 where
  IH : 𝑩 IsSubalgebraOfClass 𝒦
  IH = sclo→subalgebra SCloB
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

subalgebra→sclo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{𝑩 : Algebra 𝓠 𝑆}
 →                𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 ∈ sclo 𝒦
subalgebra→sclo{𝓠}{𝒦}{𝑩}(𝑨 , sa , (KA , B≅sa)) = sub{𝑨 = 𝑨}(sbase KA)(𝑩 , (ISO-≤ 𝑨 ∣ sa ∣ 𝑩 ∥ sa ∥ B≅sa ))

subalgebra→sclo' : {𝓠 : Universe}{𝒦 : Pred (Algebra (OV 𝓠) 𝑆) (OV (OV 𝓠))}{𝑩 : Algebra (OV 𝓠) 𝑆}
 →                𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 ∈ sclo{OV 𝓠} 𝒦
subalgebra→sclo'{𝓠}{𝒦}{𝑩}(𝑨 , sa , (KA , B≅sa)) = sub{𝑨 = 𝑨}(sbase KA)(𝑩 , (ISO-≤ 𝑨 ∣ sa ∣ 𝑩 ∥ sa ∥ B≅sa ))


lemps⊆sp : {𝓠 : Universe} → hfunext 𝓠 𝓠
 →         {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{I : 𝓠 ̇}{ℬ : I → Algebra 𝓠 𝑆}
 →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (pclo 𝒦)

lemps⊆sp{𝓠}hfe{𝒦}{I}{ℬ}ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , pbase 𝒦𝒜 , (⨅≅ gfe ℬ≅SA)
 where
  𝒜 = λ i → ∣ ℬ≤𝒦 i ∣                -- 𝒜 : I → Algebra 𝓠 𝑆
  SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣        -- SA : I → Algebra 𝓠 𝑆
  𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
  𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣
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

ps⊆sp : {𝓠 : Universe} → hfunext 𝓠 𝓠 → {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
 →      pclo{𝓠}{𝓠} (sclo 𝒦) ⊆ sclo (pclo 𝒦)
ps⊆sp {𝓠} hfe {𝒦} {pA}(pbase{I}{𝒜} scloKAi) = sub→sclo
 where
  sclo→sub : (i : I) → 𝒜 i IsSubalgebraOfClass 𝒦
  sclo→sub i = sclo→subalgebra (scloKAi i)

  ⨅𝒜-is-sub-pcloK : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓠}{𝓠} 𝒦)
  ⨅𝒜-is-sub-pcloK = lemps⊆sp hfe sclo→sub

  sub→sclo : ⨅ 𝒜 ∈ sclo (pclo 𝒦)
  sub→sclo = subalgebra→sclo ⨅𝒜-is-sub-pcloK

ps⊆sp {𝓠} hfe {𝒦} {.((∀ i → ∣ 𝒜 i ∣) , (λ f proj i → ∥ 𝒜 i ∥ f (λ args → proj args i)))}
 (prod{I = I}{𝒜 = 𝒜} pscloa) = γ -- lem1 PSCloA -- (works)
 where
  ζ : (i : I) → (𝒜 i) ∈ sclo (pclo 𝒦)
  ζ i = ps⊆sp hfe (pscloa i)

  ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (pclo 𝒦)
  ξ i = sclo→subalgebra (ζ i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (pclo (pclo 𝒦))
  η' = lemps⊆sp {𝓠} hfe {pclo 𝒦}{I}{𝒜} ξ

  η : ⨅ 𝒜 IsSubalgebraOfClass (pclo 𝒦)
  η = mono-≤ (⨅ 𝒜) pclo-idem η'

  γ : ⨅ 𝒜 ∈ sclo (pclo 𝒦)
  γ = subalgebra→sclo η


ps⊆sp {𝓠} hfe {𝒦} (piso x x₁) = siso (ps⊆sp hfe x) x₁


-----------------------------------------------------------------------------------
-- Alternatives --


lemps⊆sp' : {𝓠 : Universe} → hfunext (OV 𝓠) 𝓠
 →         {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}{I : (OV 𝓠) ̇}{ℬ : I → Algebra 𝓠 𝑆}
 →         ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (pclo{𝓠}{OV 𝓠} 𝒦)

lemps⊆sp' {𝓠} hfe {𝒦} {I} {ℬ} ℬ≤𝒦 = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , pbase 𝒦𝒜 , (⨅≅ gfe ℬ≅SA)
 where
  𝒜 = λ i → ∣ ℬ≤𝒦 i ∣                -- 𝒜 : I → Algebra 𝓠 𝑆
  SA = λ i → ∣ fst ∥ ℬ≤𝒦 i ∥ ∣        -- SA : I → Algebra 𝓠 𝑆
  𝒦𝒜 : ∀ i → 𝒜 i ∈ 𝒦
  𝒦𝒜 = λ i → ∣ snd ∥ ℬ≤𝒦 i ∥ ∣
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

ps⊆sp' : {𝓠 : Universe}
 →       hfunext (OV 𝓠) 𝓠 → hfunext 𝓠 𝓠
 →       {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
 →      pclo{𝓠}{OV 𝓠} (sclo 𝒦) ⊆ sclo{OV 𝓠} (pclo{𝓠}{OV 𝓠} 𝒦)
ps⊆sp' {𝓠} hfe hfep {𝒦} {pA}(pbase{I}{𝒜} scloKAi) = sub→sclo
 where
  sclo→sub : (i : I) → 𝒜 i IsSubalgebraOfClass 𝒦
  sclo→sub i = sclo→subalgebra (scloKAi i)

  ⨅𝒜-is-sub-pcloK : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓠}{OV 𝓠} 𝒦)
  ⨅𝒜-is-sub-pcloK = lemps⊆sp' hfe sclo→sub

  sub→sclo : ⨅ 𝒜 ∈ sclo (pclo 𝒦)
  sub→sclo = subalgebra→sclo ⨅𝒜-is-sub-pcloK

ps⊆sp' {𝓠} hfe hfep {𝒦} {.((∀ (i : I) → ∣ 𝒜 i ∣) , (λ f proj i → ∥ 𝒜 i ∥ f (λ args → proj args i)))}
 (prod{I = I}{𝒜 = 𝒜} pscloa) = γ
 where
  ζ : (i : I) → (𝒜 i) ∈ sclo (pclo{𝓠}{𝓠} 𝒦)
  ζ i = ps⊆sp{𝓠} hfep {𝒦} (pscloa i)

  ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (pclo 𝒦)
  ξ i = sclo→subalgebra{𝓠} (ζ i)

  η' : ⨅ 𝒜 IsSubalgebraOfClass (pclo{𝓠}{OV 𝓠} (pclo{𝓠}{𝓠}𝒦))
  η' = lemps⊆sp' {𝓠} hfe {pclo 𝒦}{I}{𝒜} ξ

  η : ⨅ 𝒜 IsSubalgebraOfClass (pclo 𝒦)
  η = mono-≤ (⨅ 𝒜) pclo-idem' η'

  γ : ⨅ 𝒜 ∈ sclo{OV 𝓠} (pclo{𝓠}{OV 𝓠} 𝒦)
  γ = subalgebra→sclo'{𝓠} η
ps⊆sp' {𝓠} hfe hfep {𝒦} (piso x x₁) = siso (ps⊆sp' hfe hfep x) x₁





{-We also need a way to construct products of all the algebras in a given collection.
  More precisely, if 𝒦 : Pred (Algebra 𝓤 𝑆) 𝓣 is a class of algebras, we need to
  construct an index set I and a function 𝒜 : I → Algebra 𝓤 𝑆, where 𝒜 runs through all
  algebras in 𝒦, so that we can construct the product ⨅ 𝒜 of all algebras in 𝒦. -}



------------------------------------------------------------------------------------
-- Products of predicates and their meaning --
{-
Recall:
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x
-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
syntax -Π A (λ x → b) = Π x ꞉ A , b
Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred A 𝓥 = A → 𝓥 ̇
⨅ : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
⨅ {𝓘}{𝓤}{I} 𝒜 =((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}
-}

ClassUniverses : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → Pred (𝓠 ̇) (OV 𝓠)
ClassUniverses 𝒦 A = Σ 𝑨 ꞉ Algebra _ 𝑆 , (𝑨 ∈ 𝒦) × (A ≡ ∣ 𝑨 ∣)

ΠU : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ̇
ΠU 𝒦 = Π (ClassUniverses 𝒦)

ΠP : {𝓠 : Universe} → Pred (Algebra 𝓠 𝑆) (OV 𝓠) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ̇
ΠP 𝒦 = Π 𝒦

-- A proof p : Π 𝒦 is a proof that every algebra of type Algebra 𝓠 𝑆 belongs to 𝒦.
ΠP-meaning : {𝓠 : Universe}(𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠))
 →            Π 𝒦  →  (𝑨 : Algebra 𝓠 𝑆) → 𝑨 ∈ 𝒦
ΠP-meaning 𝒦 p 𝑨 = p 𝑨




ℑ : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆) (OV 𝓤) → (OV 𝓤) ̇
ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

ℑ→A : {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
 →    (i : ℑ 𝒦) → Algebra 𝓤 𝑆
ℑ→A _ i = ∣ i ∣

class-product : {𝓠 : Universe}(𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)) → Algebra (OV 𝓠) 𝑆
class-product 𝒦 = ⨅ (ℑ→A 𝒦)

class-prod-s-∈-ps : {𝓠 : Universe}{𝑲 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
 →  class-product (sclo 𝑲) ∈ pclo{𝓠}{(OV 𝓠)} (sclo 𝑲)
class-prod-s-∈-ps {𝓠}{𝑲} = γ
 where
  I : (OV 𝓠) ̇
  I = ℑ{𝓠} (sclo 𝑲)
  𝒜 : I → Algebra 𝓠 𝑆
  𝒜 = ℑ→A{𝓠} (sclo 𝑲)
  ⨅𝒜 : Algebra (OV 𝓠) 𝑆
  ⨅𝒜 = ⨅ 𝒜
  KA : (i : I) → 𝒜 i ∈ (sclo 𝑲)
  KA i = ∥ i ∥
  γ : ⨅ 𝒜 ∈ pclo{𝓠}{OV 𝓠} (sclo 𝑲)
  γ = pbase{I = I}{𝒜 = 𝒜} KA


class-prod-s-∈-sp : {𝓠 : Universe}
 →                  hfunext (OV 𝓠) 𝓠 → hfunext 𝓠 𝓠
 →                  {𝑲 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
                    --------------------------------------------------
 →                  class-product (sclo 𝑲) ∈ sclo (pclo 𝑲)
class-prod-s-∈-sp {𝓠} hfe hfep {𝑲} = ps⊆sp' {𝓠} hfe hfep {𝑲} (class-prod-s-∈-ps{𝓠} {𝑲})

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

-- ⊧-≅ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
--       (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(p q : Term{𝓧}{X})
--  →    𝑨 ⊧ p ≈ q → 𝑨 ≅ 𝑩 → 𝑩 ⊧ p ≈ q
-- ⊧-≅ 𝑨 𝑩 p q Apq (fh , gh , f∼g , g∼f) = γ

-- lemma-⊧-≅ : {𝓠 𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
--            (p q : Term{𝓧}{X}) → (𝑨 ⊧ p ≈ q) → (𝑨 ≅ 𝑩) → 𝑩 ⊧ p ≈ q
-- lemma-⊧-≅ {𝓠}{𝓤}{𝓧}{X}{𝑨}{𝑩} p q Apq AisoB = γ

