--File: Closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 1 Mar 2020
--UPDATED: 4 Mar 2020
--NOTATION: 𝑨 `\MIA`, 𝑩 `\MIB`, 𝓐 `\MCA`, 𝓚 `\MCK`

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic
open import Subuniverse
open import Hom

-- Keep I at the same universe as A so that both A and Π A can be classified by PClo
data PClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) :
  Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    pbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
    prod : {I : Set k} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ PClo 𝓚) → Π 𝓐 ∈ PClo 𝓚

module _ {i j k l : Level} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) where

-- Subalgebras
module _ {i j k l : Level} {S : Signature i j} where
  data SClo (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    sbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
    sub : {𝑨 𝑩 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚

-- RIP typechecker 19??-2020
data HClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  hbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
  hhom : {𝑨 𝑩 : Algebra k S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ HClo 𝓚 → 𝑩 ∈ HClo 𝓚
    ->   (SubunivAlg{S = S}{𝑨 = 𝑩} {HomImage{S = S}{𝑨 = 𝑨}{𝑩 = 𝑩} f} (hom-image-is-sub{S = S}{𝑨}{𝑩} f)) ∈ HClo 𝓚

data VClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  vbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
  vprod : {I : Set k} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ VClo 𝓚) → Π 𝓐 ∈ VClo 𝓚
  vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
  vhom : {𝑨 𝑩 : Algebra k S} {f : Hom 𝑨 𝑩} →
    𝑨 ∈ VClo 𝓚 → 𝑩 ∈ VClo 𝓚 → SubunivAlg {S = S} {𝑩} {HomImage {S = S} {𝑨} {𝑩} f}
      (hom-image-is-sub {S = S} {𝑨} {𝑩} f) ∈ VClo 𝓚

module _ {i j k l} (S : Signature i j) (𝓚 : Pred (Algebra k S) l) (X : Set k) where
  open import Free{S = S}{X = X}

  pclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (PClo 𝓚 ⊢ p ≋ q)
  pclo-id1 {p} {q} α (pbase x) = α x
  pclo-id1 {p} {q} α (prod{I}{𝓐} x₁) =
      begin
        (p ̇ Π 𝓐)
      ≡⟨ interp-prod2 p 𝓐 ⟩
        (λ (args : X -> ∣ Π 𝓐 ∣ )
          -> (λ i₁ -> (p ̇ 𝓐 i₁) (λ x -> (args x) i₁)))
      ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x
           -> ∀-extensionality-ℓ₁-ℓ₂ λ x₂
                -> cong-app ((pclo-id1{p}{q} α) (x₁ x₂))
                     (λ x₃ → x x₃ x₂)) ⟩
        (λ (args : X -> ∣ Π 𝓐 ∣ )
          -> (λ i₁ -> (q ̇ 𝓐 i₁) (λ x -> (args x) i₁)))
      ≡⟨ sym (interp-prod2 q 𝓐) ⟩
        (q ̇ Π 𝓐)
      ∎

  sclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (SClo 𝓚 ⊢ p ≋ q)
  sclo-id1 {p} {q} α (sbase x) = α x
  sclo-id1 {p} {q} α (sub{𝑨}{𝑩} 𝑨∈SClo𝓚 (mem B≤𝑨)) = 
    let 𝑨⊢p≈q = (sclo-id1{p}{q} α) 𝑨∈SClo𝓚 in 
      begin
        p ̇ 𝑩
      ≡⟨ refl ⟩
        p ̇ (∣ 𝑩 ∣ , ⟦ 𝑩 ⟧) 
      ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x → {!!})  ⟩
        q ̇ (∣ 𝑩 ∣ , ⟦ 𝑩 ⟧) 
      ≡⟨ refl ⟩
        q ̇ 𝑩
      ∎
-- Goal: (p ̇ (∃ P , B)) x ≡ (q ̇ (∃ P , B)) x
-- ————————————————————————————————————————————————————————————
-- 𝑨⊢p≈q   : 𝑨 ⊢ p ≈ q
-- 𝑩       : Algebra k S
-- x       : X → ∃ P
-- B≤𝑨     : (𝓸 : ∣ S ∣) (x₁ : ⟦ S ⟧ 𝓸 → ∃ P) →
--           ∣ B 𝓸 x₁ ∣ ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i₁ → ∣ x₁ i₁ ∣)
-- 𝑨∈SClo𝓚 : 𝑨 ∈ SClo 𝓚
-- α       : 𝓚 ⊢ p ≋ q
-- q       : Term
-- p       : Term
-- X       : Set k
-- 𝓚       : Pred (Algebra k S) l
-- B       : (𝓸 : ∣ S ∣) → Op (⟦ S ⟧ 𝓸) (∃ P)  (not in scope)
-- P       : Pred ∣ 𝑨 ∣ k  (not in scope)
-- 𝑨       : Algebra k S

-- data HClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
--   hbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
--   hhom : {𝑨 B : Algebra k S} {f : Hom 𝑨 B} →
--     𝑨 ∈ HClo 𝓚 → B ∈ HClo 𝓚 → SubunivAlg {S = S} {B} {HomImage {S = S} {𝑨} {B} f}
--       (hom-image-is-sub {S = S} {𝑨} {B} f) ∈ HClo 𝓚

  hclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (HClo 𝓚 ⊢ p ≋ q)
  hclo-id1 {p} {q} α (hbase x) = α x
  hclo-id1 {p} {q} α (hhom{𝑨}{𝑩}{f} 𝑨∈HClo𝓚 𝑩∈HClo𝓚 ) =
    let 𝑨⊢p≈q = (hclo-id1{p}{q} α) 𝑨∈HClo𝓚 in
    let 𝑩⊢p≈q = (hclo-id1{p}{q} α) 𝑩∈HClo𝓚 in
    let hyp𝑨 = cong-app (𝑨⊢p≈q)  in
    let hyp𝑩 = cong-app (𝑩⊢p≈q)  in
    let subuni = SubunivAlg{i}{j}{k}{S}{𝑩}{HomImage{i}{j}{k}{S}{𝑨}{𝑩} f}
                 (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)) in 
       begin
         (p ̇ subuni)
       ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x → {!!}) ⟩
         (q ̇ subuni)
       ∎
       -- begin
       --   (p ̇ SubunivAlg (hom-image-is-sub f))
       -- ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x → {!!}) ⟩
       --   (q ̇ SubunivAlg (hom-image-is-sub f))
       -- ∎

       -- Goal: (p ̇ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)))
       --       x
       --       ≡ (q ̇ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧))) x
       -- ————————————————————————————————————————————————————————————
       -- 𝑨⊢p≈q   : 𝑨 ⊢ p ≈ q
       -- x       : X →
       --           ∣ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)) ∣
       -- 𝑩∈HClo𝓚 : 𝑩 ∈ HClo 𝓚
       -- 𝑨∈HClo𝓚 : 𝑨 ∈ HClo 𝓚
       -- α       : 𝓚 ⊢ p ≋ q
       -- q       : Term
       -- p       : Term
       -- X       : Set k
       -- 𝓚       : Pred (Algebra k S) l
       -- f       : Hom 𝑨 B
       -- 𝑩       : Algebra k S


  vclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (VClo 𝓚 ⊢ p ≋ q)
  vclo-id1 {p} {q} α (vbase x) = α x
  vclo-id1 {p} {q} α (vprod x₁) = {!!}
  vclo-id1 {p} {q} α (vsub x x₁) = {!!}
  vclo-id1 {p} {q} α (vhom x x₁) = {!!}

  pclo-id2 : ∀ {p q} → (PClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  pclo-id2 p 𝑨∈𝓚 = p (pbase 𝑨∈𝓚)

  hclo-id2 : ∀ {p q} → (HClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  hclo-id2 p 𝑨∈𝓚 = p (hbase 𝑨∈𝓚)

  sclo-id2 : ∀ {p q} → (SClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  sclo-id2 p 𝑨∈𝓚 = p (sbase 𝑨∈𝓚)

  vclo-id2 : ∀ {p q} → (VClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  vclo-id2 p 𝑨∈𝓚 = p (vbase 𝑨∈𝓚)

  postulate
    homclo-id1 : ∀ {p q} → 𝓚 ⊢ p ≋ q → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q
    homclo-id2 : ∀ {p q} → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q → 𝓚 ⊢ p ≋ q
