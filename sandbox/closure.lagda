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
 {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import homomorphisms {𝑆 = 𝑆} public
open import terms {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = gfe} renaming (generator to ℊ) public
open import subuniverses {𝑆 = 𝑆}{𝕏 = 𝕏}{fe = gfe} public

_⊧_≈_ : Algebra 𝓤 𝑆 → Term{𝓤}{X} → Term → 𝓤 ̇
𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Term → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

------------------------------------------------------------------------
-- Equational theories and classes
Th :  Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

Mod : Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

----------------------------------------------------------------------
--Closure under products
data PClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ PClo) → ⨅ 𝒜 ∈ PClo

----------------------------------------------------------------------
--Closure under hom images
data HClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo
 hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo

----------------------------------------------------------------------
-- Subalgebra Closure
data SClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo
  sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo

----------------------------------------------------------------------
-- Variety Closure
-- Finally, we have a datatype that represents classes of algebras that are close under the taking of
-- homomorphic images, subalgebras, and products of algebras in the class.

data VClo : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo
 vprod : {I : 𝓤 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo) → ⨅ 𝒜 ∈ VClo
 vsub  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo
 vhom  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo

products-preserve-identities : (p q : Term{𝓤}{X}) (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →                             ((i : I) → (𝒜 i) ⊧ p ≈ q)
                               ------------------------------------------------------
 →                             ⨅ 𝒜 ⊧ p ≈ q

products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
  where
   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = gfe λ a →
    (p ̇ ⨅ 𝒜) a                           ≡⟨ interp-prod{𝓤 = 𝓤} fevu p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ ⨅ 𝒜) a                           ∎

products-in-class-preserve-identities : (p q : Term{𝓤}{X})(I : 𝓤 ̇)(𝒜 : I → Algebra 𝓤 𝑆)
 →                                      𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
                                        -----------------------------------------------------
 →                                       ⨅ 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities p q I 𝒜 α K𝒜 = γ
  where
   β : ∀ i → (𝒜 i) ⊧ p ≈ q
   β i = α (K𝒜 i)

   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 β

subalgebras-preserve-identities : {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}(p q : Term)
                                  ((_ , _ , (𝑩 , _ , _)) : SubalgebrasOfClass' 𝒦)
 →                                𝒦 ⊧ p ≋ q
                                  -------------
 →                                𝑩 ⊧ p ≈ q

subalgebras-preserve-identities {𝒦} p q (𝑨 , KA , (𝑩 , h , (hem , hhm))) Kpq = γ
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
identities-compatible-with-homs : (p q : Term{𝓤}{X})  →  𝒦 ⊧ p ≋ q
                                 -----------------------------------------------------
 →                                ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻{𝓤}{X}) 𝑨)
                                  →  ∣ h ∣ ∘ (p ̇ 𝑻{𝓤}{X}) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)

identities-compatible-with-homs p q α 𝑨 KA h = γ
  where
  β : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
  β 𝒂 = intensionality (α KA) (∣ h ∣ ∘ 𝒂)

  ξ : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → ∣ h ∣ ((p ̇ 𝑻) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻) 𝒂)
  ξ 𝒂 =
   ∣ h ∣ ((p ̇ 𝑻) 𝒂)  ≡⟨ comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu 𝑻 𝑨 h p 𝒂 ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ β 𝒂 ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu 𝑻 𝑨 h q 𝒂)⁻¹ ⟩
   ∣ h ∣ ((q ̇ 𝑻) 𝒂)  ∎

  γ : ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)
  γ = gfe ξ

-- ⇐ (the "if" direction)
homs-compatible-with-identities : (p q : Term{𝓤}{X})
 →                                ( ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom 𝑻 𝑨)
                                           → ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻) )
                                  ----------------------------------------------------
 →                                 𝒦 ⊧ p ≋ q

homs-compatible-with-identities p q β {𝑨} KA = γ
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

compatibility-of-identities-and-homs : (p q : Term{𝓤}{X})
                 ----------------------------------------------------------------
 →                (𝒦 ⊧ p ≋ q) ⇔ (∀(𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦)(hh : hom 𝑻 𝑨)
                                           →   ∣ hh ∣ ∘ (p ̇ 𝑻) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻))

compatibility-of-identities-and-homs p q = identities-compatible-with-homs p q ,
                                             homs-compatible-with-identities p q

---------------------------------------------------------------
--Compatibility of identities with interpretation of terms
hom-id-compatibility : (p q : ∣ 𝑻{𝓤}{X} ∣)(𝑨 : Algebra 𝓤 𝑆)(ϕ : hom 𝑻 𝑨)
 →                      𝑨 ⊧ p ≈ q
                      ------------------
 →                     ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

hom-id-compatibility p q 𝑨 ϕ β = ∣ ϕ ∣ p              ≡⟨ ap ∣ ϕ ∣ (term-agree p) ⟩
                                 ∣ ϕ ∣ ((p ̇ 𝑻) ℊ)    ≡⟨ (comm-hom-term fevu 𝑻 𝑨 ϕ p ℊ) ⟩
                                 (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality β (∣ ϕ ∣ ∘ ℊ)  ⟩
                                 (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term fevu 𝑻 𝑨 ϕ q ℊ)⁻¹ ⟩
                                 ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)    ≡⟨ (ap ∣ ϕ ∣ (term-agree q))⁻¹ ⟩
                                 ∣ ϕ ∣ q              ∎


--------------------------------------------------------------------------------
 --Identities for product closure
pclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (PClo ⊧ p ≋ q)
pclo-id1 {p} {q} α (pbase x) = α x
pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
 where
  IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
  IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )

  γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
  γ = products-preserve-identities p q I 𝒜 IH

pclo-id2 : ∀{p q} → ((PClo) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
pclo-id2 p KA = p (pbase KA)

-----------------------------------------------------------------
--Identities for subalgebra closure
-- The singleton set.
｛_｝ : Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
｛ 𝑨 ｝ 𝑩 = 𝑨 ≡ 𝑩

sclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (SClo ⊧ p ≋ q)
sclo-id1 {p} {q} α (sbase KA) = α KA
sclo-id1 {p} {q} α (sub {𝑨 = 𝑨} SCloA sa) =
 --Apply subalgebras-preserve-identities to the class 𝒦 ∪ ｛ 𝑨 ｝
 subalgebras-preserve-identities p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = sclo-id1{p}{q} α SCloA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq (refl _) = β

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Apq y

sclo-id2 : ∀ {p q} → (SClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
sclo-id2 p KA = p (sbase KA)

--------------------------------------------------------------------
--Identities for hom image closure
hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo ⊧ p ≋ q)
hclo-id1 {p}{q} α (hbase KA) = α KA
hclo-id1 {p}{q} α (hhom{𝑨} HCloA (𝑩 , ϕ , (ϕhom , ϕsur))) = γ
 where
  β : 𝑨 ⊧ p ≈ q
  β = (hclo-id1{p}{q} α) HCloA

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

hclo-id2 : ∀ {p q} → (HClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)

--------------------------------------------------------------------
--Identities for HSP closure
vclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (VClo ⊧ p ≋ q)
vclo-id1 {p} {q} α (vbase KA) = α KA
vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} VClo𝒜) = γ
 where
  IH : (i : I) → 𝒜 i ⊧ p ≈ q
  IH i = vclo-id1{p}{q} α (VClo𝒜 i)

  γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
  γ = products-preserve-identities p q I 𝒜 IH

vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} VCloA sa ) =
 subalgebras-preserve-identities p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) γ
  where
   IH : 𝑨 ⊧ p ≈ q
   IH = vclo-id1{p}{q} α VCloA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq (refl _) = IH

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Asinglepq y


vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} VCloA (𝑩 , ϕ , (ϕh , ϕE))) = γ
 where
  IH : 𝑨 ⊧ p ≈ q
  IH = vclo-id1{p}{q} α VCloA

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

vclo-id2 : ∀ {p q} → (VClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
vclo-id2 p KA = p (vbase KA)


---------------------------
--Axiomatization of a class
---------------------------

--We conclude the `closure module`_ by proving that a class 𝒦 of structures is axiomatized by ``Th (VClo 𝒦)``,
--which is the set of equations satisfied by all members of the varietal closure of 𝒦.

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
ThHSP-axiomatizes : (p q : ∣ 𝑻 ∣)
       ---------------------------------------
 →       𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo))

ThHSP-axiomatizes p q = (λ α VCloA → vclo-id1{p}{q} α VCloA) ,  λ Thpq KA → Thpq (vbase KA)



---------------------------
--The free algebra in Agda
---------------------------

𝑻HI = HomImagesOf (𝑻{𝓤}{X})
𝑻img : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑻img = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ hom (𝑻{𝓤}{X}) 𝑨 , (𝑨 ∈ SClo) × Epic ∣ ϕ ∣

SClo→𝑻img : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ SClo → 𝑻img
SClo→𝑻img 𝑨 SCloA = 𝑨 , (fst (𝑻hom-gen 𝑨)) , (SCloA , (snd (𝑻hom-gen 𝑨)))

mkti : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ SClo → 𝑻img
mkti {𝑨} SCloA = (𝑨 , fst thg , SCloA , snd thg)
 where
  thg : Σ h ꞉ (hom 𝑻 𝑨), Epic ∣ h ∣
  thg = 𝑻hom-gen 𝑨

𝑻𝑨 : 𝑻img → Algebra 𝓤 𝑆
𝑻𝑨 ti = ∣ ti ∣

𝑻ϕ : {ti : 𝑻img} → hom 𝑻 (𝑻𝑨 ti)
𝑻ϕ {ti} = fst (snd ti)

𝑻ϕE : {ti : 𝑻img} → Epic ∣ 𝑻ϕ {ti} ∣
𝑻ϕE {ti} = snd (snd ∥ ti ∥)

𝑻KER : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑻KER = Σ (p , q) ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
         ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo) → (p , q) ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ 𝑻ϕ {mkti SCloA} ∣

Ψ : Pred (∣ 𝑻{𝓤}{X} ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
Ψ (p , q) = ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo)
              → ∣ 𝑻ϕ {mkti SCloA} ∣ ∘ (p ̇ 𝑻) ≡ ∣ 𝑻ϕ {mkti SCloA} ∣ ∘ (q ̇ 𝑻)

ψ : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
ψ (p , q) = ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo) → ∣ 𝑻ϕ {mkti SCloA} ∣ p ≡ ∣ 𝑻ϕ {mkti SCloA} ∣ q

ψRel : Rel ∣ 𝑻 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
ψRel p q = ψ (p , q)

ψcompatible : compatible 𝑻 ψRel
ψcompatible f {i} {j} iψj 𝑨 SCloA = γ
 where
  ti : 𝑻img
  ti = mkti {𝑨} SCloA

  ϕ : hom 𝑻 𝑨
  ϕ = 𝑻ϕ {ti}

  γ : ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻) j)
  γ = ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡⟨ ∥ ϕ ∥ f i ⟩
      (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 SCloA)) ⟩
      (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
      ∣ ϕ ∣ ((f ̂ 𝑻) j) ∎

ψSym : symmetric ψRel
ψSym p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

ψTra : transitive ψRel
ψTra p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

ψIsEquivalence : IsEquivalence ψRel
ψIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ψSym ; trans = ψTra }

ψCon : Congruence (𝑻{𝓤}{X})
ψCon = mkcon ψRel ψcompatible ψIsEquivalence

𝔽 : Algebra ((𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)) 𝑆
𝔽 = 𝑻{𝓤}{X} ╱ ψCon

-- Claim: 𝔽 ∈ SClo
-- SCloF : 𝔽 ∈ SClo
-- SCloF = ?

 -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
 -- it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.
 --
 --    𝑻---- g --->>𝔽  (ker g = Ψ)
 --     \         .
 --      \       .
 --       h     ∃ϕ     (want: Ψ ⊆ ker h)
 --        \   .
 --         \ .
 --          V
 --          𝑨

 -----------------------------------

--More tools for Birkhoff's theorem
--Here are some key facts/identities needed to complete the proof of Birkhoff's HSP theorem.

𝑻i⊧ψ : {p q : ∣ 𝑻 ∣}{𝑪 : Algebra 𝓤 𝑆}{SCloC : 𝑪 ∈ SClo}
 →       (p , q) ∈ ψ
        ----------------------------------------------------------------
 →       ∣ 𝑻ϕ{mkti SCloC} ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ 𝑻ϕ{mkti SCloC} ∣ ((q ̇ 𝑻) ℊ)

𝑻i⊧ψ {p}{q}{𝑪}{SCloC} pψq = γ
 where

  ϕ : hom 𝑻 𝑪
  ϕ = 𝑻ϕ{mkti SCloC}

  pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
  pCq = pψq 𝑪 SCloC

  γ : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
  γ = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣(term-agree q))




Ψ⊆ThSClo : Ψ ⊆ (Th SClo)
Ψ⊆ThSClo {p , q} pΨq {𝑪} SCloC = γ
 where
  ti : 𝑻img
  ti = mkti {𝑪} SCloC -- SClo→𝑻img 

  ϕ : hom 𝑻 𝑪
  ϕ = 𝑻ϕ{ti}

  ϕE : Epic ∣ ϕ ∣
  ϕE = 𝑻ϕE{ti}

  ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
  ϕsur 𝒄 x = ϕE (𝒄 x)

  pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
  pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

  ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
  ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

  β : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
  β = pΨq 𝑪 SCloC

  γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
  γ = gfe λ 𝒄 →
   (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
   (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
   ∣ ϕ ∣ ((p ̇ 𝑻)(pre 𝒄))       ≡⟨ intensionality β (pre 𝒄) ⟩
   ∣ ϕ ∣ ((q ̇ 𝑻)(pre 𝒄))       ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (pre 𝒄) ⟩
   (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
   (q ̇ 𝑪) 𝒄                   ∎

Ψ⊆Th𝒦 : ∀ p q → (p , q) ∈ Ψ → 𝒦 ⊧ p ≋ q
Ψ⊆Th𝒦 p q pΨq {𝑨} KA = Ψ⊆ThSClo{p , q} pΨq (sbase KA)










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


