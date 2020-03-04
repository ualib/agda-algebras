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
    pbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
    prod : {I : Set k} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ PClo 𝓚) → ⊗ 𝓐 ∈ PClo 𝓚

-- Subalgebras
module _ {i j k l : Level} {S : Signature i j} where
  data SClo (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    sbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
    sub : {𝑨 𝑩 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚

-- RIP typechecker 19??-2020
data HClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  hbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
  hhom : {𝑨 B : Algebra k S} {f : Hom 𝑨 B} →
    𝑨 ∈ HClo 𝓚 → B ∈ HClo 𝓚 → SubunivAlg {S = S} {B} {HomImage {S = S} {𝑨} {B} f}
      (hom-image-is-sub {S = S} {𝑨} {B} f) ∈ HClo 𝓚

data VClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  vbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
  vprod : {I : Set k} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ VClo 𝓚) → Π 𝓐 ∈ VClo 𝓚
  vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
  vhom : {𝑨 𝑩 : Algebra k S} {f : Hom 𝑨 𝑩} →
    𝑨 ∈ VClo 𝓚 → 𝑩 ∈ VClo 𝓚 → SubunivAlg {S = S} {𝑩} {HomImage {S = S} {𝑨} {𝑩} f}
      (hom-image-is-sub {S = S} {𝑨} {𝑩} f) ∈ VClo 𝓚

module _ {i j k l m} (S : Signature i j) (𝓚 : Pred (Algebra k S) l) (X : Set m) where
  open import Free{S = S}{X = X}

  pclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (PClo 𝓚 ⊢ p ≋ q)
  pclo-id1 {p} α (pbase x) = α x
  pclo-id1 {p} {q} α (prod{I}{𝓐} x₁) = extensionality λ x -> 
    -- Goal: (p ̇ ⊗ 𝓐) x ≡ (q ̇ ⊗ 𝓐) x
    begin
      (p ̇ ⊗ 𝓐) x
    ≡⟨ iterp-prod p 𝓐 x ⟩
      (λ i -> (p ̇ (𝓐 i))(λ j -> x j i))
    ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x₂ → {!!}) ⟩
      (λ i -> (q ̇ (𝓐 i))(λ j -> x j i))
    ≡⟨ sym (iterp-prod q 𝓐 x)  ⟩
      (q ̇ ⊗ 𝓐) x
    ∎

  -- Goal: (p ̇ 𝓐 x₂) (λ j₁ → x j₁ x₂) ≡ (q ̇ 𝓐 x₂) (λ j₁ → x j₁ x₂)
  -- ————————————————————————————————————————————————————————————
  -- x₂ : I
  -- x  : X → ∣ ⊗ 𝓐 ∣
  -- x₁ : (i₁ : I) → 𝓐 i₁ ∈ PClo 𝓚
  -- α  : 𝓚 ⊢ p ≋ q
  -- q  : Term
  -- p  : Term
  -- X  : Set m
  -- 𝓚  : Pred (Algebra k S) l
  -- 𝓐  : I → Algebra k S
  -- I  : Set k

  -- pclo-id1 {p} α (pbase 𝑨∈𝓚) = α 𝑨∈𝓚
  -- pclo-id1 {p} {q} α Π∈𝓚 = {!!} -- (prod {𝑨 = 𝑨} Π∈𝓚) = ?
    --extensionality λ a →
    --let β i = intensionality (pclo-id1 {p} {q} α (Π∈𝓚 i)) λ x → a x i in
    --{!!}

  postulate
    sclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (SClo 𝓚 ⊢ p ≋ q)
    hclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (HClo 𝓚 ⊢ p ≋ q)
    vclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (VClo 𝓚 ⊢ p ≋ q)

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
