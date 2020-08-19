--FILE: clo.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 17 Aug 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; 𝓤ω)

module clo
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext} where

open import homomorphisms {𝑆 = 𝑆} public

open import subuniverses
 {𝑆 = 𝑆}
 {𝕏 = 𝕏}
 {fe = gfe}

open import terms
 {𝑆 = 𝑆}
 {𝕏 = 𝕏}
 {gfe = gfe} renaming (generator to ℊ) public

_⊧_≈_ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → Algebra 𝓦 𝑆
 →      Term{𝓤}{X} → Term{𝓤}{X} → 𝓤 ⊔ 𝓦 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
 →      Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)
 →      Term{𝓤}{X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇

_⊧_≋_ {𝓤} {𝓦} 𝒦 p q = {𝑨 : Algebra 𝓦 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q


----------------------------------------------------------------------
--Closure under products
data PClo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) 𝓤) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     ⨅ 𝒜 ∈ PClo 𝒦

P-closed : (ℒ𝒦 : (𝓣 : Universe) → Pred (Algebra 𝓣 𝑆) (𝓣 ⁺ ))
 →      (𝓘 : Universe)(I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 𝑆)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  ⨅ 𝒜  ∈ (ℒ𝒦 𝓘)

----------------------------------------------------------------------
--Closure under subalgebras
data SClo {𝓤 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) :
 Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
  sub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo 𝒦

S-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
 →         (𝓤 : Universe) → (𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
S-closed ℒ𝒦 =
 λ 𝓤 B → (B is-subalgebra-of-class (ℒ𝒦 𝓤)) → (B ∈ ℒ𝒦 𝓤)

----------------------------------------------------------------------
--Closure under hom images
data HClo {𝓤 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) :
 Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
  hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦

------------------------------------------------------------------------
-- Equational theories and classes
TH : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
 →   Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)  → _ ̇
TH {𝓤}{𝓦}{X} 𝒦 = Σ (p , q) ꞉ (Term{𝓤}{X} × Term{𝓤}{X}) , 𝒦 ⊧ p ≋ q

Th : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
 →   Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)
 →   Pred (Term{𝓤}{X} × Term{𝓤}{X}) _
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
      (ℰ : Pred (Term{𝓤}{X} × Term{𝓤}{X}) 𝓤)
 →    𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇

MOD {𝓤}{𝓦} ℰ =
 Σ A ꞉ (Algebra 𝓦 𝑆) ,
    ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

Mod : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
 →    Pred (Term{𝓤}{X} × Term{𝓤}{X}) 𝓤
 →    Pred (Algebra 𝓦 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓦)

Mod {𝓤}{𝓦} ℰ =
 λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

products-preserve-identities :
       {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
       {fevw : dfunext 𝓥 𝓦}
       (p q : Term{𝓤}{X})
       (I : 𝓦 ̇ ) (𝒜 : I → Algebra 𝓦 𝑆)
  →    ((i : I) → (𝒜 i) ⊧ p ≈ q)
      -----------------------------------
  →     ⨅ 𝒜 ⊧ p ≈ q

products-preserve-identities
 {𝓤}{𝓦}{X}{fevw} p q I 𝒜 𝒜⊧p≈q = γ
  where
   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = gfe λ a →
    (p ̇ ⨅ 𝒜) a
        ≡⟨ interp-prod{𝓤}{𝓦} fevw p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i)))
        ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i)))
        ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ ⨅ 𝒜) a
        ∎

products-in-class-preserve-identities :
      {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
      {fevw : dfunext 𝓥 𝓦}
      (𝒦 : Pred (Algebra 𝓦 𝑆) (𝓦 ⁺))
      (p q : Term{𝓤}{X})
      (I : 𝓦 ̇ ) (𝒜 : I → Algebra 𝓦 𝑆)
  →   𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
      ------------------------------------
  →    ⨅ 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities
 {𝓤}{𝓦}{X}{fevw} 𝒦 p q I 𝒜 𝒦⊧p≋q all𝒜i∈𝒦 = γ
  where
   𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
   𝒜⊧p≈q i = 𝒦⊧p≋q (all𝒜i∈𝒦 i)

   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = products-preserve-identities {𝓤}{𝓦}{X}{fevw} p q I 𝒜 𝒜⊧p≈q

module subalgebra-compatibility
 {𝓤 : Universe}
 {X : 𝓤 ̇ } where

 subalgebras-preserve-identities :
     (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺))
     (p q : Term)
     (p≋q : 𝒦 ⊧ p ≋ q)
     (SAK : SubalgebrasOfClass 𝒦)
    ----------------------------------
  →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q

 subalgebras-preserve-identities 𝒦 p q p≋q SAK = γ
  where

   𝑨 : Algebra 𝓤 𝑆
   𝑨 = ∣ SAK ∣

   A∈𝒦 : 𝑨 ∈ 𝒦
   A∈𝒦 = ∣ pr₂ SAK ∣

   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = p≋q A∈𝒦

   subalg : SubalgebrasOf 𝑨
   subalg = ∥ pr₂ SAK ∥

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = pr₁ subalg

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = ∣ pr₂ subalg ∣

   hem : is-embedding h
   hem = pr₁ ∥ pr₂ subalg ∥

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = pr₂ ∥ pr₂ subalg ∥

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : 𝑩 ⊧ p ≈ q
   γ = gfe λ b → hlc (ξ b)



-- ⇒ (the "only if" direction)
identities-compatible-with-homs :
        {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
        {fevw : funext 𝓥 𝓦}
        {𝒦 : Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)}
        (p q : Term{𝓤}{X})
        (p≋q : 𝒦 ⊧ p ≋ q)
       ----------------------------------------------------
 →     ∀ (𝑨 : Algebra 𝓦 𝑆)
         (KA : 𝒦 𝑨)
         (h : hom (𝑻{𝓤}{X}) 𝑨)
        → ∣ h ∣ ∘ (p ̇ 𝑻{𝓤}{X}) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)

identities-compatible-with-homs
 {𝓤}{𝓦}{X}{fevw} {𝒦} p q p≋q 𝑨 KA h = γ
  where
   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻 ∣ )
    →        (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻 ∣ )
    →        ∣ h ∣ ((p ̇ 𝑻) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ 𝑻) 𝒂)  ≡⟨ comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺}{𝓦}{𝓤}{X} fevw (𝑻{𝓤}{X}) 𝑨 h p 𝒂 ⟩
    (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺}{𝓦}{𝓤}{X} fevw 𝑻 𝑨 h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ 𝑻) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)
   γ = gfe hpa≡hqa


-- ⇐ (the "if" direction)
homs-compatible-with-identities :
        {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
        {fevw : funext 𝓥 𝓦}
        {𝒦 : Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)}
        (p q : Term{𝓤}{X})
        (hp≡hq : ∀ (𝑨 : Algebra 𝓦 𝑆)
                   (KA : 𝑨 ∈ 𝒦)
                   (h : hom (𝑻{𝓤}{X}) 𝑨)
                  → ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻))
       ------------------------------------------------------
 →      𝒦 ⊧ p ≋ q
 --inferred types: 𝑨 : Algebra 𝓤 𝑆, KA : 𝑨 ∈ 𝒦, h : hom 𝑻 𝑨

homs-compatible-with-identities
 {𝓤}{𝓦}{X}{fevw}{𝒦} p q hp≡hq {𝑨} KA = γ
 where
  h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝑻 𝑨
  h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

  γ : 𝑨 ⊧ p ≈ q
  γ = gfe λ 𝒂 →
   (p ̇ 𝑨) 𝒂
     ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)
     ≡⟨(comm-hom-term gfe 𝑻 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
   (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻)) ℊ
     ≡⟨ ap (λ - → - ℊ) (hp≡hq 𝑨 KA (h 𝒂)) ⟩
   (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻)) ℊ
     ≡⟨ (comm-hom-term gfe 𝑻 𝑨 (h 𝒂) q ℊ) ⟩
   (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)
     ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (q ̇ 𝑨) 𝒂
     ∎

compatibility-of-identities-and-homs :
    {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
    {fevw : funext 𝓥 𝓦}
    {𝒦 : Pred (Algebra 𝓦 𝑆) (𝓦 ⁺)}
    (p q : Term{𝓤}{X})
   -------------------------------------------------
 →  (𝒦 ⊧ p ≋ q)
     ⇔ (∀(𝑨 : Algebra 𝓦 𝑆)
          (KA : 𝑨 ∈ 𝒦)
          (hh : hom (𝑻{𝓤}{X}) 𝑨)
       →  ∣ hh ∣ ∘ (p ̇ 𝑻) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻))

compatibility-of-identities-and-homs
 {𝓤}{𝓦}{X} {fevw} {𝒦} p q =
  identities-compatible-with-homs {𝓤}{𝓦}{X}{fevw}{𝒦} p q ,
  homs-compatible-with-identities {𝓤}{𝓦}{X}{fevw}{𝒦} p q

---------------------------------------------------------------

--Compatibility of identities with interpretation of terms
hom-id-compatibility :
        {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
        {fevw : funext 𝓥 𝓦}
        (p q : ∣ 𝑻{𝓤}{X} ∣ )
        (𝑨 : Algebra 𝓦 𝑆)
        (ϕ : hom 𝑻 𝑨)
        (p≈q : 𝑨 ⊧ p ≈ q)
        -------------------
 →      ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

hom-id-compatibility
 {𝓤}{𝓦}{X}{fevw} p q 𝑨 ϕ p≈q =
    ∣ ϕ ∣ p              ≡⟨ ap ∣ ϕ ∣ (term-agreement p) ⟩
    ∣ ϕ ∣ ((p ̇ 𝑻) ℊ)  ≡⟨ (comm-hom-term fevw (𝑻{𝓤}{X}) 𝑨 ϕ p ℊ) ⟩
    (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality p≈q (∣ ϕ ∣ ∘ ℊ)  ⟩
    (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term fevw (𝑻{𝓤}{X}) 𝑨 ϕ q ℊ)⁻¹ ⟩
    ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)  ≡⟨ (ap ∣ ϕ ∣ (term-agreement q))⁻¹ ⟩
    ∣ ϕ ∣ q  ∎


-- We need a type that allows for different universe levels.
data vclo {𝓤 : Universe}
           (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) :
            Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
 vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ vclo{𝓤} 𝒦
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → 𝒜 i ∈ vclo 𝒦) → (⨅ 𝒜) ∈ vclo 𝒦
 vsub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ vclo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ vclo 𝒦
 vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ vclo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ vclo 𝒦


module _
 {ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {ℒ𝒦' : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) 𝓤}
 {ℒ𝒦'' : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)} where

 -- ==========================================================
 -- The free algebra in Agda
 -- ------------------------
 -- 𝑻HI = HomImagesOf 𝑻

 𝑻img : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → _ ̇

 𝑻img {𝓤}{𝓦}{X} =
  Σ 𝑨 ꞉ (Algebra 𝓦 𝑆) ,
    Σ ϕ ꞉ hom (𝑻{𝓤}{X}) 𝑨 ,
      (𝑨 ∈ SClo{𝓤 = 𝓦}(ℒ𝒦 𝓦)) × Epic ∣ ϕ ∣


 𝑻𝑨 : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
      (ti : 𝑻img{𝓤}{𝓦}{X})
  →   Algebra 𝓦 𝑆

 𝑻𝑨 ti = ∣ ti ∣


 𝑻𝑨∈SClo : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
           (ti : 𝑻img{𝓤}{𝓦}{X})
  →        (𝑻𝑨{𝓤}{𝓦}{X} ti) ∈ SClo (ℒ𝒦 𝓦)
 𝑻𝑨∈SClo ti = ∣ pr₂ ∥ ti ∥ ∣

 𝑻ϕ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
      (ti : 𝑻img{𝓤}{𝓦}{X})
  →   hom (𝑻{𝓤}{X}) (𝑻𝑨{𝓤}{𝓦}{X} ti)

 𝑻ϕ ti = pr₁ ∥ ti ∥


 𝑻ϕE : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
       (ti : 𝑻img{𝓤}{𝓦}{X})
  →    Epic ∣ (𝑻ϕ ti) ∣

 𝑻ϕE ti = ∥ pr₂ ∥ ti ∥ ∥


 𝑻KER : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇

 𝑻KER {𝓤}{𝓦}{X} = Σ (p , q) ꞉ (∣ 𝑻{𝓤}{X} ∣ × ∣ 𝑻{𝓤}{X} ∣) ,
    ∀ ti → (p , q) ∈ KER-pred{B = ∣ (𝑻𝑨{𝓤}{𝓦}{X} ti) ∣} ∣ 𝑻ϕ{𝓤}{𝓦}{X} ti ∣


 Ψ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → Rel ∣ 𝑻{𝓤}{X} ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓦 ⁺)
 Ψ {𝓤}{𝓦}{X} p q =
    ∀ (ti : 𝑻img{𝓤}{𝓦}{X}) → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)


 Ψ-IsEquivalence : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
  → IsEquivalence{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}{A = ∣ (𝑻{𝓤}{X}) ∣} (Ψ{𝓤}{𝓦}{X})

 Ψ-IsEquivalence =
  record { rfl = λ p ti → 𝓇ℯ𝒻𝓁
         ; sym = λ p q p≡q ti → (p≡q ti)⁻¹
         ; trans = λ p q r p≡q q≡r ti → (p≡q ti) ∙ (q≡r ti)
         }

 𝑻compatible-op : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
  →               ∣ 𝑆 ∣ → Rel ∣ 𝑻{𝓤}{X} ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ̇
 𝑻compatible-op f R = (lift-rel R) =[ (f ̂ 𝑻) ]⇒ R

 𝑻compatible : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
  →            Rel ∣ 𝑻{𝓤}{X} ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ̇
 𝑻compatible {𝓤}{𝓦}{X} R = ∀ f → 𝑻compatible-op{𝓤}{𝓦}{X} f R

 record 𝑻Congruence {𝓤 𝓦 : Universe}{X : 𝓤 ̇} : (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺ ̇  where
  constructor mk𝑻con
  field
   ⟨_⟩ : Rel ∣ 𝑻{𝓤}{X} ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
   Compatible : 𝑻compatible{𝓤}{𝓦}{X} ⟨_⟩
   IsEquiv : IsEquivalence ⟨_⟩

 open 𝑻Congruence

 tcongruence : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺ ̇
 tcongruence {𝓤}{𝓦}{X} =
  Σ θ ꞉ (Rel ∣ 𝑻{𝓤}{X} ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) , IsEquivalence θ × 𝑻compatible{𝓤}{𝓦}{X} θ

 Ψ-𝑻compatible : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → 𝑻compatible{𝓤}{𝓦}{X} Ψ
 Ψ-𝑻compatible {𝓤}{𝓦}{X} f {𝒕}{𝒔} 𝒕𝒔∈Ψ ti = gfe λ x → γ x
  where
   𝑨 : Algebra 𝓤 𝑆
   𝑨 = 𝑻𝑨 ti

   ϕ : hom 𝑻 𝑨
   ϕ = 𝑻ϕ ti

   𝒕s 𝒔s : (i : ∥ 𝑆 ∥ f) → (X → ∣ 𝑻 ∣) → ∣ 𝑻 ∣
   𝒕s i = 𝒕 i ̇ 𝑻
   𝒔s i = 𝒔 i ̇ 𝑻

   𝒕≡𝒔 : (i : ∥ 𝑆 ∥ f) → ∣ ϕ ∣ ∘ (𝒕s i) ≡ ∣ ϕ ∣ ∘ (𝒔s i)
   𝒕≡𝒔 i = 𝒕𝒔∈Ψ i ti

   γ : ∀ x
    →  ∣ ϕ ∣((f ̂ 𝑻) (λ i → (𝒕 i ̇ 𝑻) x))
         ≡ ∣ ϕ ∣ ((f ̂ 𝑻)(λ i → (𝒔 i ̇ 𝑻) x))
   γ x =
    ∣ ϕ ∣ ((f ̂ 𝑻) (λ i → 𝒕s i x)) ≡⟨ ∥ ϕ ∥ f (λ i → 𝒕s i x) ⟩
    ((f ̂ 𝑨) (λ i → ∣ ϕ ∣ (𝒕s i x))) ≡⟨  ap (f ̂ 𝑨) (gfe λ i → intensionality (𝒕≡𝒔 i) x) ⟩
    ((f ̂ 𝑨) (λ i → ∣ ϕ ∣ (𝒔s i x))) ≡⟨  (∥ ϕ ∥ f (λ i → 𝒔s i x))⁻¹ ⟩
    ∣ ϕ ∣ ((f ̂ 𝑻) (λ i → (𝒔s i x))) ∎

 ConΨ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → 𝑻Congruence{𝓤}{𝓦}{X}
 ConΨ {𝓤}{𝓦}{X} = mk𝑻con Ψ (Ψ-𝑻compatible{𝓤}{𝓦}{X}) Ψ-IsEquivalence

 conΨ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → tcongruence{𝓤}{𝓦}{X}
 conΨ {𝓤}{𝓦}{X} = Ψ , (Ψ-IsEquivalence , Ψ-𝑻compatible{𝓤}{𝓦}{X})

 𝔽 : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺) 𝑆
 𝔽{𝓤}{𝓦}{X} = (
        -- carrier
        (  ∣ 𝑻{𝓤}{X} ∣ // ⟨ ConΨ{𝓤}{𝓦}{X} ⟩  ) ,

        -- operations
        (  λ f args
            → ([ (f ̂ 𝑻) (λ i₁ → ⌜ args i₁ ⌝) ] ⟨ ConΨ{𝓤}{𝓦}{X} ⟩) ,
                ((f ̂ 𝑻) (λ i₁ → ⌜ args i₁ ⌝) , 𝓇ℯ𝒻𝓁 )   )
      )

 𝔽-is-universal-for : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}(𝑨 : Algebra 𝓦 𝑆) → hom (𝔽{𝓤}{𝓦}{X}) 𝑨
 𝔽-is-universal-for {𝓤}{𝓦}{X} 𝑨 = ϕ , ϕhom
  where
   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst (𝕏{𝓦}{𝓤}{X} 𝑨)

   hE : Epic h₀
   hE = snd (𝕏 𝑨)

   h : hom 𝑻 𝑨
   h = lift-hom{𝑨 = 𝑨} h₀

   ϕ : ∣ 𝑻 ∣ // ⟨ ConΨ{𝓤}{𝓦}{X} ⟩ → ∣ 𝑨 ∣
   ϕ = λ 𝒂 → ∣ h ∣ ⌜ 𝒂 ⌝

   ϕhom : is-homomorphism (𝔽{𝓤}{𝓦}{X}) 𝑨 ϕ
   ϕhom f a = γ
    where
     γ : ϕ ((f ̂ 𝔽{𝓤}{𝓦}{X}) a) ≡ (f ̂ 𝑨) (λ x → ϕ (a x))
     γ = ϕ ((f ̂ 𝔽{𝓤}{𝓦}{X}) a) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ϕ (([ (f ̂ 𝑻) (λ i → ⌜ a i ⌝) ] ⟨ ConΨ{𝓤}{𝓦}{X} ⟩) ,
           ((f ̂ 𝑻) (λ i → ⌜ a i ⌝) , refl _ ))
                        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ∣ h ∣ ((f ̂ 𝑻) (λ i → ⌜ a i ⌝))
                        ≡⟨ ∥ h ∥ f ((λ i → ⌜ a i ⌝)) ⟩
         (f ̂ 𝑨) (∣ h ∣ ∘ (λ i → ⌜ a i ⌝))
                        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         (f ̂ 𝑨) (ϕ ∘ a) ∎

 𝔽∈vclo : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}
  →        𝔽{𝓤}{𝓦}{X} ∈ vclo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺}(ℒ𝒦 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺))

 --We will prove this by showing that 𝔽 is a subalgebra of 𝑨{𝓜}{𝓜}, where
 --𝑨{𝓜}{𝓜} is a product of elements from the type Σ 𝑨 ꞉ (Algebra 𝓜 𝑆) , 𝑨 ∈ (ℒ𝒦 𝓜 𝓜).
 --Note that the *index* of the product has type Σ 𝑨 ꞉ (Algebra 𝓜 𝑆) , 𝑨 ∈ (ℒ𝒦 𝓜 𝓜),
 --which is 𝓘 = 𝓞 ⊔ 𝓥 ⊔ 𝓜 ⊔ 𝓜 ⁺.
 --𝑨{𝓜}{𝓜} ∈ vclo{𝓜 ⁺}{𝓜 ⁺} (ℒ𝒦 (𝓜 ⁺) (𝓜 ⁺))
 -- vsub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ vclo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ vclo 𝒦
 -- γ : 𝔽 ∈ vclo{𝓜 ⁺}{𝓜 ⁺} (ℒ𝒦 (𝓜 ⁺)(𝓜 ⁺))
 -- γ = vsub 𝑨∈vclo 𝔽sub


 𝔽∈vclo {𝓤}{𝓦}{X} = γ
  where
   ΣP : {𝓘 : Universe} → Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓘) → (𝓞 ⊔ 𝓥 ⊔ 𝓘) ⁺ ̇
   ΣP {𝓘} K = Σ 𝑨 ꞉ (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) , 𝑨 ∈ K

   𝒜ΣP : {𝓘 : Universe}{K : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓘)}
    →    ΣP{𝓘} K → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆
   𝒜ΣP i = ∣ i ∣

   ⨅𝒜ΣP : {𝓘 : Universe} → Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓘) ⁺) 𝑆
   ⨅𝒜ΣP {𝓘} = ⨅ (𝒜ΣP{𝓘 = 𝓘}{K = (ℒ𝒦' (𝓞 ⊔ 𝓥 ⊔ 𝓘))})

   𝑨 : Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺) 𝑆
   𝑨 = ⨅𝒜ΣP {𝓘 = 𝓤}

   ⨅𝒦∈vclo : {𝓤 𝓘 : Universe}{I : (𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺) ̇}{𝒜 : I → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺) 𝑆}
              (p : ∀ (i : I) → 𝒜 i ∈ vclo{𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺}(ℒ𝒦 (𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺)))
     →        ⨅ 𝒜 ∈ vclo{𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺}(ℒ𝒦 (𝓞 ⊔ 𝓥 ⊔ 𝓘 ⁺))
   ⨅𝒦∈vclo p = vprod p

   ⨅ℒ𝒦 : {𝓤 : Universe}{I : 𝓤 ̇}{𝒜 : I → Algebra 𝓤 𝑆}
    →      (∀ (i : I) → 𝒜 i ∈ vclo{𝓤} (ℒ𝒦 𝓤))
    →      Algebra 𝓤 𝑆
   ⨅ℒ𝒦 {𝒜 = 𝒜} _ = ⨅ 𝒜


   ϕ : hom (𝔽{𝓤}{𝓦}{X}) 𝑨
   ϕ = 𝔽-is-universal-for 𝑨

   h : ∣ 𝔽{𝓤}{𝓦}{X} ∣ → ∣ 𝑨 ∣
   h = ∣ ϕ ∣

   kerh : Rel (∣ 𝑻{𝓤}{X} ∣ // ⟨ ConΨ{𝓤}{𝓦}{X} ⟩ ) ((𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺)
   kerh [s] [t] = h [s] ≡ h [t]

   kerh⊆Ψ : ∀(s t : ∣ 𝑻 ∣)(ti : 𝑻img{𝓤}{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}{X})
    →       kerh ⟦ s ⟧ ⟦ t ⟧
    →       ∣ (𝑻ϕ ti) ∣ ∘ (s ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (t ̇ 𝑻)
   kerh⊆Ψ s t ti kerhst = γ
    where
     -- 𝑩 : Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤) 𝑆
     -- 𝑩 = 𝑻𝑨{𝓤}{𝓞 ⊔ 𝓥 ⊔ 𝓤}{X} ti

     -- 𝑩∈SCloℒ𝒦 : 𝑩 ∈ SClo(ℒ𝒦 (𝓞 ⊔ 𝓥 ⊔ 𝓤))
     -- 𝑩∈SCloℒ𝒦 = 𝑻𝑨∈SClo{𝓤}{(𝓞 ⊔ 𝓥 ⊔ 𝓤)}{X} ti

     -- 𝑩∈ΣP : ΣP{𝓘 = 𝓤} (ℒ𝒦' (𝓞 ⊔ 𝓥 ⊔ 𝓤))
     -- 𝑩∈ΣP = 𝑩 , {!!}

     -- hAB : hom 𝑨 𝑩
     -- hAB = {!!}

     γ : ∣ 𝑻ϕ ti ∣ ∘ (s ̇ 𝑻) ≡ ∣ 𝑻ϕ ti ∣ ∘ (t ̇ 𝑻)
     γ = {!!}

   hembe : is-embedding h
   hembe = λ a fibhy fibhy' → {!!}

   hhomo : is-homomorphism (𝔽{𝓤}{𝓦}{X}) 𝑨 h
   hhomo = ∥ ϕ ∥

   𝔽sub : SubalgebrasOf 𝑨
   𝔽sub = {!!} -- (𝔽{𝓤}{𝓦}{X} , h , (hembe , hhomo))

   γ : 𝔽{𝓤}{𝓦}{X} ∈ vclo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺}(ℒ𝒦 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺))
   γ = {!!} -- vsub (𝑨∈vclo{𝓘 = 𝓤}) 𝔽sub



   -- 𝒜ΣP→𝑨-𝑨∈𝒦 : {𝓘 : Universe}{K : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓘)}
   --  →    ΣP{𝓘} K → Σ 𝑨 ꞉ (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) , 𝑨 ∈ K
   -- 𝒜ΣP→𝑨-𝑨∈𝒦 i = i

   -- 𝒜ΣP∈𝒦 : {𝓘 : Universe}{K : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓘) 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓘)}
   --  →    (i : ΣP{𝓘} K) → ∣ i ∣ ∈ K
   -- 𝒜ΣP∈𝒦 = λ i → ∥ i ∥

