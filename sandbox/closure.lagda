\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 19 Sep 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂)

module closure
 {𝑆 : Signature 𝓞 𝓥}
 {𝓦 : Universe}
 -- {X : 𝓤 ̇}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import homomorphisms {𝑆 = 𝑆} public
open import subuniverses {𝑆 = 𝑆}{𝓤 = 𝓤}{𝕏 = 𝕏}{fe = gfe} public
open import terms {𝑆 = 𝑆}{𝓤 = 𝓤}{𝕏 = 𝕏}{gfe = gfe} renaming (generator to ℊ) public

_⊧_≈_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Algebra 𝓤 𝑆 → Term{𝓧}{X} → Term → 𝓤 ⊔ 𝓧 ̇
𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 →      Term{𝓧}{X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇
_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

OVU+ OVU++ W W+ : Universe
OVU+ = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
OVU++ = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺
W = OVU+ ⊔ 𝓦
W+ = OVU++ ⊔ 𝓦 ⁺

------------------------------------------------------------------------
-- Equational theories and classes
Th : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 →   Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

Mod : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q


----------------------------------------------------------------------------------
--Closure under products
data PClo {𝓤 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ PClo 𝒦) → ⨅ 𝒜 ∈ PClo 𝒦

--------------------------------------------------------------------------------------
--Closure under hom images
data HClo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
 hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦

----------------------------------------------------------------------
-- Subalgebra Closure
data SClo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
  sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo 𝒦

----------------------------------------------------------------------
-- Variety Closure
-- Finally, we have a datatype that represents classes of algebras that are close under the taking of
-- homomorphic images, subalgebras, and products of algebras in the class.

data VClo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
 vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo 𝒦
 vprod : {I : 𝓤 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
 vsub  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
 vhom  : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

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

products-in-class-preserve-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                        {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
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

subalgebras-preserve-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
                                  (p q : Term{𝓧}{X})
                                  ((_ , _ , (𝑩 , _ , _)) : SubalgebrasOfClass' 𝒦)
 →                                𝒦 ⊧ p ≋ q
                                  -------------
 →                                𝑩 ⊧ p ≈ q

subalgebras-preserve-identities {X = X}{𝒦 = 𝒦} p q (𝑨 , KA , (𝑩 , h , (hem , hhm))) Kpq = γ
 where
  β : 𝑨 ⊧ p ≈ q
  β = Kpq KA

  ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
  ξ b =
   h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
   (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality β (h ∘ b) ⟩
   (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
   h ((q ̇ 𝑩) b)  ∎

  hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

  γ : 𝑩 ⊧ p ≈ q
  γ = gfe λ b → hlc (ξ b)


-- ⇒ (the "only if" direction)
identities-compatible-with-homs : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
                                  (p q : Term{𝓧}{X}) →  𝒦 ⊧ p ≋ q
                                 -----------------------------------------------------
 →                                ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻{𝓧}{X}) 𝑨)
                                  →  ∣ h ∣ ∘ (p ̇ 𝑻{𝓧}{X}) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)

identities-compatible-with-homs {𝓤 = 𝓤}{𝓧 = 𝓧} {X = X}p q α 𝑨 KA h = γ
  where
  β : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
  β 𝒂 = intensionality (α KA) (∣ h ∣ ∘ 𝒂)

  ξ : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → ∣ h ∣ ((p ̇ 𝑻) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻) 𝒂)
  ξ 𝒂 =
   ∣ h ∣ ((p ̇ 𝑻) 𝒂)  ≡⟨ comm-hom-term{𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺}{𝓦 = 𝓤} gfe (𝑻{𝓧}) 𝑨 h p 𝒂 ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ β 𝒂 ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term{𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺}{𝓦 = 𝓤} gfe 𝑻 𝑨 h q 𝒂)⁻¹ ⟩
   ∣ h ∣ ((q ̇ 𝑻) 𝒂)  ∎

  γ : ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)
  γ = gfe ξ

-- ⇐ (the "if" direction)
homs-compatible-with-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                  {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
                                  (p q : Term{𝓧}{X})
 →                                ( ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom 𝑻 𝑨)
                                           → ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻) )
                                  ----------------------------------------------------
 →                                 𝒦 ⊧ p ≋ q

homs-compatible-with-identities {X = X} p q β {𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝑻 𝑨
   h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂            ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨(comm-hom-term gfe 𝑻 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻)) ℊ  ≡⟨ ap (λ - → - ℊ) (β 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻)) ℊ  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 (h 𝒂) q ℊ) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (q ̇ 𝑨) 𝒂             ∎

compatibility-of-identities-and-homs : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                                       {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
                                       (p q : Term{𝓧}{X})
                 ----------------------------------------------------------------
 →                (𝒦 ⊧ p ≋ q) ⇔ (∀(𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦)(hh : hom 𝑻 𝑨)
                                           →   ∣ hh ∣ ∘ (p ̇ 𝑻) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻))

compatibility-of-identities-and-homs p q = identities-compatible-with-homs p q ,
                                             homs-compatible-with-identities p q

---------------------------------------------------------------
--Compatibility of identities with interpretation of terms
hom-id-compatibility : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                       (p q : Term{𝓧}{X})
                       (𝑨 : Algebra 𝓤 𝑆)(ϕ : hom 𝑻 𝑨)
 →                      𝑨 ⊧ p ≈ q
                      ------------------
 →                     ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

hom-id-compatibility p q 𝑨 ϕ β = ∣ ϕ ∣ p              ≡⟨ ap ∣ ϕ ∣ (term-agree p) ⟩
                                 ∣ ϕ ∣ ((p ̇ 𝑻) ℊ)    ≡⟨ (comm-hom-term gfe 𝑻 𝑨 ϕ p ℊ) ⟩
                                 (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality β (∣ ϕ ∣ ∘ ℊ)  ⟩
                                 (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 ϕ q ℊ)⁻¹ ⟩
                                 ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)    ≡⟨ (ap ∣ ϕ ∣ (term-agree q))⁻¹ ⟩
                                 ∣ ϕ ∣ q              ∎


module _ {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where

 --------------------------------------------------------------------------------
  --Identities for product closure
 pclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (PClo 𝒦 ⊧ p ≋ q)
 pclo-id1 p q α (pbase x) = α x
 pclo-id1 {𝓤}{𝓧}{X} p q α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{𝓤}{𝓧}{X} p q α  ( 𝒜-P𝒦  i )

   γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 pclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{p q : Term{𝓧}{X}} → ((PClo 𝒦) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
 pclo-id2 PCloKpq KA = PCloKpq (pbase KA)

 -----------------------------------------------------------------
 --Identities for subalgebra closure
 -- The singleton set.
 ｛_｝ : {𝓤 : Universe} → Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 ｛ 𝑨 ｝ 𝑩 = 𝑨 ≡ 𝑩

 sclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (SClo 𝒦 ⊧ p ≋ q)
 sclo-id1 p q α (sbase KA) = α KA
 sclo-id1 {𝓤}{𝓧}{X} p q α (sub {𝑨 = 𝑨} SCloA sa) =
  --Apply subalgebras-preserve-identities to the class 𝒦 ∪ ｛ 𝑨 ｝
  subalgebras-preserve-identities p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) γ
   where
    β : 𝑨 ⊧ p ≈ q
    β = sclo-id1 {𝓤}{𝓧}{X}p q α SCloA

    Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Apq (refl _) = β

    γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    γ {𝑩} (inj₁ x) = α x
    γ {𝑩} (inj₂ y) = Apq y

 sclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{p q : Term{𝓧}{X}} → (SClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p KA = p (sbase KA)

 --------------------------------------------------------------------
 --Identities for hom image closure
 hclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
 hclo-id1 p q α (hbase KA) = α KA
 hclo-id1 {𝓤}{𝓧}{X} p q α (hhom{𝑨} HCloA (𝑩 , ϕ , (ϕhom , ϕsur))) = γ
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

 hclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{p q : Term{𝓧}{X}} → (HClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 hclo-id2 p KA = p (hbase KA)

 --------------------------------------------------------------------
 --Identities for HSP closure
 vclo-id1 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X}) → (𝒦 ⊧ p ≋ q) → (VClo 𝒦 ⊧ p ≋ q)
 vclo-id1 p q α (vbase KA) = α KA
 vclo-id1 {𝓤}{𝓧}{X}p q α (vprod{I = I}{𝒜 = 𝒜} VClo𝒜) = γ
  where
   IH : (i : I) → 𝒜 i ⊧ p ≈ q
   IH i = vclo-id1{𝓤}{𝓧}{X} p q α (VClo𝒜 i)

   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1{𝓤}{𝓧}{X} p q α ( vsub {𝑨 = 𝑨} VCloA sa ) =
  subalgebras-preserve-identities p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) γ
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

 vclo-id2 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{p q : Term{𝓧}{X}} → (VClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p KA = p (vbase KA)








-- Ψ' : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- Ψ' (p , q) = ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q


-- 𝑻img⊧Ψ' : ∀ p q → (p , q) ∈ Ψ' → (ti : 𝑻img)
--         -----------------------------------------------
--  →       ∣ (𝑻ϕ ti) ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ (𝑻ϕ ti) ∣ ((q ̇ 𝑻) ℊ)

-- 𝑻img⊧Ψ' p q pΨq ti = γ
--  where
--   𝑪 : Algebra 𝓤 𝑆
--   𝑪 = ∣ ti ∣

--   ϕ : hom 𝑻 𝑪
--   ϕ = 𝑻ϕ ti

--   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
--   pCq = pΨq ti

--   γ : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
--   γ = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣(term-agree q))




-- ψ'' : {𝑪 : Algebra 𝓤 𝑆}(ϕ : hom (𝑻{𝓤}{X}) 𝑪) → Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) _ -- (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- ψ'' ϕ (p , q) = ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

-- ψ' : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- ψ' (p , q) = ∀ (𝑪 : Algebra 𝓤 𝑆) (ϕ : hom (𝑻{𝓤}{X}) 𝑪) → ψ''{𝑪} ϕ (p , q)

-- ψ'Rel : Rel ∣ 𝑻 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- ψ'Rel p q = ψ' (p , q)





-- Ψ''⊧ : {𝑪 : Algebra 𝓤 𝑆}(ϕ : hom (𝑻{𝓤}{X}) 𝑪)
--  →     ∀ p q → (p , q) ∈ (ψ''{𝑪} ϕ)
--        ----------------------------------------
--  →     ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)

-- Ψ''⊧ ϕ p q pΨq = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pΨq ∙ (ap ∣ ϕ ∣(term-agree q))


