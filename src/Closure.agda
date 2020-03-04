{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic
open import Subuniverse
open import Hom

-- Keep I at the same universe as A so that both A and Π A can be classified by PClo
data PClo {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) :
  Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    pbase : {A : Algebra _ S} → A ∈ K → A ∈ PClo K
    prod : {I : Set k} {A : I → Algebra _ S} → (∀ i → A i ∈ PClo K) → Π A ∈ PClo K

-- Subalgebras
module _ {i j k l : Level} {S : Signature i j} where
  data SClo (K : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    sbase : {A : Algebra _ S} → A ∈ K → A ∈ SClo K
    sub : {A B : Algebra _ S} → A ∈ SClo K → B is-subalgebra-of A → B ∈ SClo K

-- RIP typechecker 19??-2020
data HClo {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  hbase : {A : Algebra k S} → A ∈ K → A ∈ HClo K
  hhom : {A B : Algebra k S} {f : Hom A B} →
    A ∈ HClo K → B ∈ HClo K → SubunivAlg {S = S} {B} {HomImage {S = S} {A} {B} f}
      (hom-image-is-sub {S = S} {A} {B} f) ∈ HClo K

data VClo {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  vbase : {A : Algebra k S} → A ∈ K → A ∈ VClo K
  vprod : {I : Set k} {A : I → Algebra _ S} → (∀ i → A i ∈ VClo K) → Π A ∈ VClo K
  vsub : ∀ {A : Algebra _ S} {B : Algebra _ S} → A ∈ VClo K → B is-subalgebra-of A → B ∈ VClo K
  vhom : {A B : Algebra k S} {f : Hom A B} →
    A ∈ VClo K → B ∈ VClo K → SubunivAlg {S = S} {B} {HomImage {S = S} {A} {B} f}
      (hom-image-is-sub {S = S} {A} {B} f) ∈ VClo K

module _ {i j k l m} (S : Signature i j) (K : Pred (Algebra k S) l) (X : Set m) where
  open import Free{S = S}{X = X}

  postulate
    pclo-id1 : ∀ {p q} → (K ⊢ p ≋ q) → (PClo K ⊢ p ≋ q)
  --pclo-id1 {p} α (pbase A∈K) = α A∈K
  --pclo-id1 {p} {q} α (prod {A = A} Π∈K) =
    --extensionality λ a →
    --let β i = intensionality (pclo-id1 {p} {q} α (Π∈K i)) λ x → a x i in
    --{!!}
    sclo-id1 : ∀ {p q} → (K ⊢ p ≋ q) → (SClo K ⊢ p ≋ q)
    hclo-id1 : ∀ {p q} → (K ⊢ p ≋ q) → (HClo K ⊢ p ≋ q)
    vclo-id1 : ∀ {p q} → (K ⊢ p ≋ q) → (VClo K ⊢ p ≋ q)

  pclo-id2 : ∀ {p q} → (PClo K ⊢ p ≋ q) → (K ⊢ p ≋ q)
  pclo-id2 p A∈K = p (pbase A∈K)

  hclo-id2 : ∀ {p q} → (HClo K ⊢ p ≋ q) → (K ⊢ p ≋ q)
  hclo-id2 p A∈K = p (hbase A∈K)

  sclo-id2 : ∀ {p q} → (SClo K ⊢ p ≋ q) → (K ⊢ p ≋ q)
  sclo-id2 p A∈K = p (sbase A∈K)

  vclo-id2 : ∀ {p q} → (VClo K ⊢ p ≋ q) → (K ⊢ p ≋ q)
  vclo-id2 p A∈K = p (vbase A∈K)

  postulate
    homclo-id1 : ∀ {p q} → K ⊢ p ≋ q → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q
    homclo-id2 : ∀ {p q} → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q → K ⊢ p ≋ q
