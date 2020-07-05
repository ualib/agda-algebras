--FILE: closure.lagda.rst
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 2 Jul 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op)

open import subuniverses using (Subuniverses; SubunivAlg; hom-image-alg;
 _is-subalgebra-of_; Subalgebra; _is-subalgebra-of-class_; SubalgebrasOfClass)

open import homomorphisms using (hom; is-homomorphism)

open import terms using (Term; generator; node; _̇_; _̂_; interp-prod2;
 interp-prod; comm-hom-term')

module closure
 {S : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {𝓤★ : Univalence}
 {X : 𝓤 ̇ } -- {X : 𝓧 ̇ }
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤) where

-- Product Closure
𝑷-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 S)
 →      (( i : I ) → 𝒜 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
𝑷-closed 𝓛𝓚 = λ 𝓘 I 𝒜 𝒜i∈𝓛𝓚 →  Π' 𝒜  ∈ (𝓛𝓚 𝓘)

-- data PClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
data PClo (𝓚 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S}
  →     (∀ i → 𝒜 i ∈ PClo 𝓚)
  →     Π' 𝒜 ∈ PClo 𝓚

_⊧_≈_ : Algebra 𝓤 S
 →      Term{X = X} → Term → 𝓤 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊧ p ≈ q

products-preserve-identities :
      (p q : Term{X = X})
      (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →    ((i : I) → (𝒜 i) ⊧ p ≈ q)
     -----------------------------------
 →     Π' 𝒜 ⊧ p ≈ q

products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
 where
   γ : (p ̇ Π' 𝒜) ≡ (q ̇ Π' 𝒜)
   γ = gfe λ 𝒂 →
    (p ̇ Π' 𝒜) 𝒂
      ≡⟨ interp-prod gfe p 𝒜 𝒂 ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (𝒂 x) i)))
      ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (𝒂 x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (𝒂 x) i)))
      ≡⟨ (interp-prod gfe q 𝒜 𝒂)⁻¹ ⟩
    (q ̇ Π' 𝒜) 𝒂
      ∎

products-in-class-preserve-identities :
     (𝓚 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))
     (p q : Term{X = X})
     (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →   𝓚 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝓚)
     ------------------------------------
 →    Π' 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities 𝓚 p q I 𝒜 𝓚⊧p≋q all𝒜i∈𝓚 = γ
 where
   𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
   𝒜⊧p≈q i = 𝓚⊧p≋q (all𝒜i∈𝓚 i)

   γ : (p ̇ Π' 𝒜) ≡ (q ̇ Π' 𝒜)
   γ = products-preserve-identities p q I 𝒜 𝒜⊧p≈q

-- Subalgebra Closure
data SClo (𝓚 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {𝑨 :  Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
 sub : {𝑨 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → (sa : Subalgebra {𝑨 = 𝑨} 𝓤★) → ∣ sa ∣ ∈ SClo 𝓚

-- Homomorphic Image Closure
data HClo (𝓚 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
 hhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ HClo 𝓚
  →     hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ HClo 𝓚

-- Variety Closure
data VClo (𝓚 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S} → (∀ i → 𝒜 i ∈ VClo 𝓚) → Π' 𝒜 ∈ VClo 𝓚
 vsub : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ VClo 𝓚 → (sa : Subalgebra {𝑨 = 𝑨} 𝓤★) → ∣ sa ∣ ∈ VClo 𝓚
 vhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ VClo 𝓚 → hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚

module _ (𝓚 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )) where

 pclo-id1 : ∀ {p q} → (𝓚 ⊧ p ≋ q) → (PClo 𝓚 ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝓚 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝓚  i )
   γ : p ̇ (Π' 𝒜)  ≡ q ̇ (Π' 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 pclo-id2 : ∀{p q} → ((PClo 𝓚) ⊧ p ≋ q ) → (𝓚 ⊧ p ≋ q)
 pclo-id2 p 𝑨∈𝓚 = p (pbase 𝑨∈𝓚)

 sclo-id1 : ∀{p q} → (𝓚 ⊧ p ≋ q) → (SClo 𝓚 ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝓚⊧p≋q (sbase A∈𝓚) = 𝓚⊧p≋q A∈𝓚
 sclo-id1 {p} {q} 𝓚⊧p≋q (sub {𝑨 = 𝑨} A∈SClo𝓚 sa) = γ
  where
   𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
   𝑨⊧p≈q = sclo-id1{p}{q} 𝓚⊧p≋q A∈SClo𝓚

   𝑩 : Algebra 𝓤 S
   𝑩 = ∣ sa ∣

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (𝒃 : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) 𝒃) ≡ h ((q ̇ 𝑩) 𝒃)
   ξ 𝒃 =
    h ((p ̇ 𝑩) 𝒃)  ≡⟨ comm-hom-term' gfe 𝑩 𝑨 (h , hhm) p 𝒃 ⟩
    (p ̇ 𝑨)(h ∘ 𝒃) ≡⟨ intensionality 𝑨⊧p≈q (h ∘ 𝒃) ⟩
    (q ̇ 𝑨)(h ∘ 𝒃) ≡⟨ (comm-hom-term' gfe 𝑩 𝑨 (h , hhm) q 𝒃)⁻¹ ⟩
    h ((q ̇ 𝑩) 𝒃)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ 𝑩 ≡ q ̇ 𝑩
   γ = gfe λ 𝒃 → hlc (ξ 𝒃)

 sclo-id2 : ∀ {p q} → (SClo 𝓚 ⊧ p ≋ q) → (𝓚 ⊧ p ≋ q)
 sclo-id2 p 𝑨∈𝓚 = p (sbase 𝑨∈𝓚)

 hclo-id1 : ∀{p q} → (𝓚 ⊧ p ≋ q) → (HClo 𝓚 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝓚⊧p≋q (hbase A∈𝓚) = 𝓚⊧p≋q A∈𝓚
 hclo-id1 {p}{q} 𝓚⊧p≋q (hhom{A}{B}{f} A∈HClo𝓚) = γ
  where
   A⊧p≈q : A ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝓚⊧p≋q ) A∈HClo𝓚

   IH : (p ̇ A) ≡ (q ̇ A)
   IH = A⊧p≈q

   HIA = hom-image-alg{𝑨 = A}{𝑩 = B} f
   -- HIA = Σ (Image_∋_ ∣ f ∣) ,  ops-interp
   -- (where ops-interp : (𝑓 : ∣ S ∣) → Op (∥ S ∥ 𝑓) hom-image

   𝒂 : (𝒃 : X → Σ (Image_∋_ ∣ f ∣))(x : X) → ∣ A ∣
   𝒂 = λ 𝒃 x → (Inv ∣ f ∣ (∣ 𝒃 x ∣)(∥ 𝒃 x ∥))

   ζ : (𝒃 : X → Σ (Image_∋_ ∣ f ∣))(x : X) → ∣ f ∣ (𝒂 𝒃 x) ≡ ∣ 𝒃 x ∣
   ζ 𝒃 x = InvIsInv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥


   τ : (𝑎 : X → ∣ A ∣ ) → ∣ f ∣ ((p ̇ A) 𝑎) ≡ ∣ f ∣ ((q ̇ A) 𝑎)
   τ 𝑎 = ap (λ - → ∣ f ∣ - ) (intensionality IH 𝑎)

   ψ : (𝑎 : X → ∣ A ∣ ) → (p ̇ B) (∣ f ∣ ∘ 𝑎) ≡ (q ̇ B) (∣ f ∣ ∘ 𝑎)
   ψ 𝑎 =
    (p ̇ B) (∣ f ∣ ∘ 𝑎) ≡⟨ (comm-hom-term' gfe A B f p 𝑎)⁻¹ ⟩
    ∣ f ∣ ((p ̇ A) 𝑎) ≡⟨ τ 𝑎 ⟩
    ∣ f ∣ ((q ̇ A) 𝑎) ≡⟨ comm-hom-term' gfe A B f q 𝑎 ⟩
    (q ̇ B) (∣ f ∣ ∘ 𝑎) ∎

   ψ' : (𝑏 : X → Σ (Image_∋_ ∣ f ∣ )) → (p ̇ B) 𝑏  ≡ (q ̇ B) 𝑏
   ψ' 𝑏  = {!!}
   -- ψ' : (𝑏 : X → ∣ B ∣ ) → (∀ x → Image ∣ f ∣ ∋ (𝑏 x)) → (p ̇ B) 𝑏  ≡ (q ̇ B) 𝑏
   -- ψ' 𝑏 Imgf∋b = {!!}
    -- (p ̇ B) (∣ f ∣ ∘ 𝑎) ≡⟨ (comm-hom-term' gfe A B f p 𝑎)⁻¹ ⟩
    -- ∣ f ∣ ((p ̇ A) 𝑎) ≡⟨ τ 𝑎 ⟩
    -- ∣ f ∣ ((q ̇ A) 𝑎) ≡⟨ comm-hom-term' gfe A B f q 𝑎 ⟩
    -- (q ̇ B) (∣ f ∣ ∘ 𝑎) ∎

   γ : (p ̇ HIA) ≡ (q ̇ HIA)
   γ = {!!} -- (p ̇ HIA)
   --       ≡⟨ refl _ ⟩
   --     (λ (𝒃 : X → ∣ HIA ∣) → (p ̇ HIA) 𝒃)
   --       ≡⟨ gfe (λ x → hiti x p) ⟩
   --     (λ 𝒃 → ∣ f ∣ ((p ̇ A) (𝒂 𝒃)) , im ((p ̇ A) (𝒂 𝒃)))
   --       ≡⟨ ap (λ - → λ 𝒃 → ∣ f ∣ (- (𝒂 𝒃))  , im (- (𝒂 𝒃))) IH ⟩
   --     (λ 𝒃 → ∣ f ∣ ((q ̇ A) (𝒂 𝒃)) , im ((q ̇ A)(𝒂 𝒃)))
   --       ≡⟨ (gfe (λ x → hiti x q))⁻¹ ⟩
   --     (λ 𝒃 → (q ̇ HIA) 𝒃)
   --       ≡⟨ refl _ ⟩
   --     (q ̇ HIA)    ∎


   hom-image-term-interp : (𝒃 : X → ∣ HIA ∣)(p : Term)
    → ∣ (p ̇ HIA ) 𝒃 ∣ ≡ ∣ f ∣ ((p ̇ A)(𝒂 𝒃))
   hom-image-term-interp 𝒃 (generator x) = (ζ 𝒃 x)⁻¹
   hom-image-term-interp 𝒃 (node 𝓸 𝒕) = {!!} -- ap (λ - → (𝓸 ̂ HIA) -) (gfe λ x → φIH x)

   hom-image-term-interpretation hiti : (𝒃 : X → ∣ HIA ∣)(p : Term)
    → (p ̇ HIA ) 𝒃 ≡ ∣ f ∣ ((p ̇ A)(𝒂 𝒃)) , im ((p ̇ A)(𝒂 𝒃))

   hom-image-term-interpretation 𝒃 (generator x) = {!!}
    where
     iiif : ∣ 𝒃 x ∣ ≡ ∣ f ∣ (Inv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥)
     iiif = InvIsInv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥ ⁻¹

     fstbx : ∣ 𝒃 x ∣ ≡ ∣ f ∣ (𝒂 𝒃 x)
     fstbx = ζ 𝒃 x ⁻¹
     -- we need a proof of `Image ∣ f ∣ ∋ pr₁ (𝒃 x)`
     -- and 𝒃 takes x to ∣ HIA ∣ = hom-image = Σ (Image_∋_ ∣ ℎ ∣)
     ∥bx∥ : Image ∣ f ∣ ∋ pr₁ (𝒃 x)
     ∥bx∥ = ∥ 𝒃 x ∥

     -- γ : 𝒃 x ≡ ∣ f ∣ (𝒂 𝒃 x) , im (𝒂 𝒃 x)
     -- γ = 𝒃 x ≡⟨ refl _ ⟩ ∣ 𝒃 x ∣ , ∥ 𝒃 x ∥
     --         ≡⟨ {!!} ⟩ ∣ f ∣ (Inv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥) , im (Inv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥)
     --         ≡⟨ refl _ ⟩ ∣ f ∣ (𝒂 𝒃 x) , im (𝒂 𝒃 x) ∎

   hom-image-term-interpretation 𝒃 (node 𝓸 𝒕) =  ap (λ - → (𝓸 ̂ HIA) -) (gfe λ x → φIH x)
    where
     φIH : (x : ∥ S ∥ 𝓸)
      → (𝒕 x ̇ HIA) 𝒃  ≡ ∣ f ∣ (( 𝒕 x ̇ A )(𝒂 𝒃)) , im ((𝒕 x ̇ A)(𝒂 𝒃))
     φIH x = hom-image-term-interpretation 𝒃 (𝒕 x)

   hiti = hom-image-term-interpretation  -- alias

   -- γ : (p ̇ HIA) ≡ (q ̇ HIA)
   -- γ = (p ̇ HIA)
   --       ≡⟨ refl _ ⟩
   --     (λ (𝒃 : X → ∣ HIA ∣) → (p ̇ HIA) 𝒃)
   --       ≡⟨ gfe (λ x → hiti x p) ⟩
   --     (λ 𝒃 → ∣ f ∣ ((p ̇ A) (𝒂 𝒃)) , im ((p ̇ A) (𝒂 𝒃)))
   --       ≡⟨ ap (λ - → λ 𝒃 → ∣ f ∣ (- (𝒂 𝒃))  , im (- (𝒂 𝒃))) IH ⟩
   --     (λ 𝒃 → ∣ f ∣ ((q ̇ A) (𝒂 𝒃)) , im ((q ̇ A)(𝒂 𝒃)))
   --       ≡⟨ (gfe (λ x → hiti x q))⁻¹ ⟩
   --     (λ 𝒃 → (q ̇ HIA) 𝒃)
   --       ≡⟨ refl _ ⟩
   --     (q ̇ HIA)    ∎

 hclo-id2 : ∀ {p q} → (HClo 𝓚 ⊧ p ≋ q) → (𝓚 ⊧ p ≋ q)
 hclo-id2 p 𝑨∈𝓚 = p (hbase 𝑨∈𝓚)

 vclo-id1 : ∀ {p q} → (𝓚 ⊧ p ≋ q) → (VClo 𝓚 ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝓚) = α A∈𝓚
 vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo𝓚) = γ
   where
    IH : (i : I) → 𝒜 i ⊧ p ≈ q
    IH i = vclo-id1{p}{q} α (𝒜∈VClo𝓚 i)

    γ : p ̇ (Π' 𝒜)  ≡ q ̇ (Π' 𝒜)
    γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo𝓚 sa ) = γ
   where
    𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
    𝑨⊧p≈q = vclo-id1{p}{q} α A∈VClo𝓚

    𝑩 : Algebra 𝓤 S
    𝑩 = ∣ sa ∣

    h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
    h = pr₁ ∥ sa ∥

    hem : is-embedding h
    hem = ∣ pr₂ ∥ sa ∥ ∣

    hhm : is-homomorphism 𝑩 𝑨 h
    hhm = ∥ pr₂ ∥ sa ∥ ∥

    ξ : (𝒃 : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) 𝒃) ≡ h ((q ̇ 𝑩) 𝒃)
    ξ 𝒃 =
     h ((p ̇ 𝑩) 𝒃)  ≡⟨ comm-hom-term' gfe 𝑩 𝑨 (h , hhm) p 𝒃 ⟩
     (p ̇ 𝑨)(h ∘ 𝒃) ≡⟨ intensionality 𝑨⊧p≈q (h ∘ 𝒃) ⟩
     (q ̇ 𝑨)(h ∘ 𝒃) ≡⟨ (comm-hom-term' gfe 𝑩 𝑨 (h , hhm) q 𝒃)⁻¹ ⟩
     h ((q ̇ 𝑩) 𝒃)  ∎

    hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
    hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

    γ : p ̇ 𝑩 ≡ q ̇ 𝑩
    γ = gfe λ 𝒃 → hlc (ξ 𝒃)

 --vhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ VClo 𝓚 →  hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚
 vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨}{𝑩 = 𝑩}{f = f} 𝑨∈VClo𝓚) = γ
   where
    𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
    𝑨⊧p≈q = vclo-id1{p}{q} α 𝑨∈VClo𝓚

    HIA : Algebra 𝓤 S
    HIA = hom-image-alg{𝑨 = 𝑨}{𝑩 = 𝑩} f

    ar : (X → ∣ HIA ∣ ) → (X → ∣ 𝑨 ∣ )
    ar b = λ x → Inv ∣ f ∣ ∣ b x ∣ ∥ b x ∥

    arbr : (X → ∣ HIA ∣ ) → (X → ∣ 𝑩 ∣ )
    arbr b = λ x →  ∣ f ∣ (Inv ∣ f ∣ ∣ b x ∣ ∥ b x ∥)

    HIA⊧p≈q : HIA ⊧ p ≈ q
    HIA⊧p≈q = gfe λ 𝒃 → {!!}

    γ : (p ̇ HIA) ≡ (q ̇ HIA)
    γ = gfe λ 𝒃 →  {!!}



 vclo-id2 : ∀ {p q} → (VClo 𝓚 ⊧ p ≋ q) → (𝓚 ⊧ p ≋ q)
 vclo-id2 p 𝑨∈𝓚 = p (vbase 𝑨∈𝓚)

 -- sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sbase x₂) (mem B≤𝑨 )) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
 --     γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
 --            (λ 𝒂 → 𝒂 x₁) ∎

 -- sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sub x₂ x₃) (mem B≤𝑨)) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
 --     γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
 --            (λ 𝒂 → 𝒂 x₁) ∎

 -- sclo-id1 {generator x} {node 𝓸 𝒕} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((node 𝓸 𝒕) ̇ (Σ _ , _) )
 --     γ =  ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
 --           ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎

 -- sclo-id1 {node 𝓸 𝒕} {generator x} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((generator x) ̇ (Σ _ , _) )
 --     γ = ( ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
 --            ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎ ) ⁻¹

 -- sclo-id1 {node 𝓸 𝒕} {node 𝓸₁ 𝒕₁} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((node 𝓸₁ 𝒕₁) ̇ (Σ _ , _) )
 --     γ = {!!}
