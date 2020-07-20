--FILE: closure.lagda.rst
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 2 Jul 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op; _̂_)

open import subuniverses using (Subuniverses; -- SubunivAlg; _is-subalgebra-of_;
 Subalgebra) -- ; -- _is-subalgebra-of-class_; SubalgebrasOfClass)

open import homomorphisms using (hom; is-homomorphism; HomImagesOf)

open import terms using (Term; generator; node; _̇_; interp-prod2;
 interp-prod; comm-hom-term)

module closure
 {S : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {ua : Univalence}
 {X : 𝓤 ̇ } -- {X : 𝓧 ̇ }
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤) where

_⊧_≈_ : Algebra 𝓤 S
 →      Term{X = X} → Term → 𝓤 ̇

A ⊧ p ≈ q = (p ̇ A) ≡ (q ̇ A)

_⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝒦 p q = {A : Algebra _ S} → 𝒦 A → A ⊧ p ≈ q


-- Closure data types

data PClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     Π' 𝒜 ∈ PClo 𝒦

-- Subalgebra Closure
data SClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {A :  Algebra _ S} → A ∈ 𝒦 → A ∈ SClo 𝒦
 sub : {A : Algebra _ S} → A ∈ SClo 𝒦 → (sa : Subalgebra {A = A} ua) → ∣ sa ∣ ∈ SClo 𝒦

-- Homomorphic Image Closure
data HClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
 hhom : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦

-- Variety Closure
data VClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo 𝒦
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S} → (∀ i → 𝒜 i ∈ VClo 𝒦) → Π' 𝒜 ∈ VClo 𝒦
 vsub : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ VClo 𝒦 → (sa : Subalgebra {A = 𝑨} ua) → ∣ sa ∣ ∈ VClo 𝒦
 vhom : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦



-- Product Closure
P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 S)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  Π' 𝒜  ∈ (ℒ𝒦 𝓘)

products-preserve-identities :
      (p q : Term{X = X})
      (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →    ((i : I) → (𝒜 i) ⊧ p ≈ q)
     -----------------------------------
 →     Π' 𝒜 ⊧ p ≈ q

products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
 where
   γ : (p ̇ Π' 𝒜) ≡ (q ̇ Π' 𝒜)
   γ = gfe λ a →
    (p ̇ Π' 𝒜) a
      ≡⟨ interp-prod gfe p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i)))
      ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i)))
      ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ Π' 𝒜) a
      ∎

products-in-class-preserve-identities :
     (𝒦 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))
     (p q : Term{X = X})
     (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →   𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
     ------------------------------------
 →    Π' 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities 𝒦 p q I 𝒜 𝒦⊧p≋q all𝒜i∈𝒦 = γ
 where
   𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
   𝒜⊧p≈q i = 𝒦⊧p≋q (all𝒜i∈𝒦 i)

   γ : (p ̇ Π' 𝒜) ≡ (q ̇ Π' 𝒜)
   γ = products-preserve-identities p q I 𝒜 𝒜⊧p≈q

module _ (𝒦 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )) where

 pclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (PClo 𝒦 ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )
   γ : p ̇ (Π' 𝒜)  ≡ q ̇ (Π' 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 pclo-id2 : ∀{p q} → ((PClo 𝒦) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
 pclo-id2 p A∈𝒦 = p (pbase A∈𝒦)

 sclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (SClo 𝒦 ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝒦⊧p≋q (sbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 sclo-id1 {p} {q} 𝒦⊧p≋q (sub {A = A} A∈SClo𝒦 sa) = γ
  where
   A⊧p≈q : A ⊧ p ≈ q
   A⊧p≈q = sclo-id1{p}{q} 𝒦⊧p≋q A∈SClo𝒦

   B : Algebra 𝓤 S
   B = ∣ sa ∣

   h : ∣ B ∣ → ∣ A ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism B A h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ B ∣ ) → h ((p ̇ B) b) ≡ h ((q ̇ B) b)
   ξ b =
    h ((p ̇ B) b)  ≡⟨ comm-hom-term gfe B A (h , hhm) p b ⟩
    (p ̇ A)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ A)(h ∘ b) ≡⟨ (comm-hom-term gfe B A (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ B) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ B ≡ q ̇ B
   γ = gfe λ b → hlc (ξ b)

 sclo-id2 : ∀ {p q} → (SClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)

 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

   𝑩 : Algebra 𝓤 S
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕhom : is-homomorphism 𝑨 𝑩 ϕ
   ϕhom = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃 ∎

 hclo-id2 : ∀ {p q} → (HClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)

 vclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (VClo 𝒦 ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝒦) = α A∈𝒦
 vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo𝒦) = γ
  where
   IH : (i : I) → 𝒜 i ⊧ p ≈ q
   IH i = vclo-id1{p}{q} α (𝒜∈VClo𝒦 i)

   γ : p ̇ (Π' 𝒜)  ≡ q ̇ (Π' 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo𝒦 sa ) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 S
   𝑩 = ∣ sa ∣

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ 𝑩 ≡ q ̇ 𝑩
   γ = gfe λ b → hlc (ξ b)

 vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} A∈VClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 S
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕh : is-homomorphism 𝑨 𝑩 ϕ
   ϕh = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕE : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕE 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃 ∎

 vclo-id2 : ∀ {p q} → (VClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)
