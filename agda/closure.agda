--FILE: closure.lagda.rst
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 2 Jul 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op)

open import subuniverses using (Subuniverses; SubunivAlg; _is-subalgebra-of_;
 Subalgebra; _is-subalgebra-of-class_; SubalgebrasOfClass)

open import homomorphisms using (hom; is-homomorphism; hom-image-alg)

open import terms using (Term; generator; node; _̇_; _̂_; interp-prod2;
 interp-prod; comm-hom-term')

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


-- Product Closure
P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 S)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  Π' 𝒜  ∈ (ℒ𝒦 𝓘)

data PClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     Π' 𝒜 ∈ PClo 𝒦

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

-- Subalgebra Closure
data SClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {A :  Algebra _ S} → A ∈ 𝒦 → A ∈ SClo 𝒦
 sub : {A : Algebra _ S} → A ∈ SClo 𝒦 → (sa : Subalgebra {A = A} ua) → ∣ sa ∣ ∈ SClo 𝒦

-- Homomorphic Image Closure
data HClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ HClo 𝒦
 hhom : {A B : Algebra 𝓤 S}{ϕ : hom A B}
  →     A ∈ HClo 𝒦
  →     hom-image-alg {A = A}{B = B} ϕ ∈ HClo 𝒦

-- Variety Closure
data VClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ VClo 𝒦
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S} → (∀ i → 𝒜 i ∈ VClo 𝒦) → Π' 𝒜 ∈ VClo 𝒦
 vsub : {A : Algebra 𝓤 S} → A ∈ VClo 𝒦 → (sa : Subalgebra {A = A} ua) → ∣ sa ∣ ∈ VClo 𝒦
 vhom : {A B : Algebra 𝓤 S}{ϕ : hom A B}
  →     A ∈ VClo 𝒦 → hom-image-alg {A = A}{B = B} ϕ ∈ VClo 𝒦

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
    h ((p ̇ B) b)  ≡⟨ comm-hom-term' gfe B A (h , hhm) p b ⟩
    (p ̇ A)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ A)(h ∘ b) ≡⟨ (comm-hom-term' gfe B A (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ B) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ B ≡ q ̇ B
   γ = gfe λ b → hlc (ξ b)

 sclo-id2 : ∀ {p q} → (SClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)

 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{A}{B}{ϕ} A∈HClo𝒦) = γ
  where
   A⊧p≈q : A ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

   IH : (p ̇ A) ≡ (q ̇ A)
   IH = A⊧p≈q

   HIA = hom-image-alg{A = A}{B = B} ϕ
   -- HIA = Σ (Image_∋_ ∣ ϕ ∣) ,  ops-interp
   -- (where ops-interp : (𝑓 : ∣ S ∣) → Op (∥ S ∥ 𝑓) hom-image

   preim : (b : X → Σ (Image_∋_ ∣ ϕ ∣))(x : X) → ∣ A ∣
   preim = λ b x → (Inv ∣ ϕ ∣ (∣ b x ∣)(∥ b x ∥))

   ζ : (b : X → Σ (Image_∋_ ∣ ϕ ∣))(x : X) → ∣ ϕ ∣ (preim b x) ≡ ∣ b x ∣
   ζ b x = InvIsInv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥


   τ : (𝑎 : X → ∣ A ∣ ) → ∣ ϕ ∣ ((p ̇ A) 𝑎) ≡ ∣ ϕ ∣ ((q ̇ A) 𝑎)
   τ 𝑎 = ap (λ - → ∣ ϕ ∣ - ) (intensionality IH 𝑎)

   ψ : (𝑎 : X → ∣ A ∣ ) → (p ̇ B) (∣ ϕ ∣ ∘ 𝑎) ≡ (q ̇ B) (∣ ϕ ∣ ∘ 𝑎)
   ψ 𝑎 =
    (p ̇ B) (∣ ϕ ∣ ∘ 𝑎) ≡⟨ (comm-hom-term' gfe A B ϕ p 𝑎)⁻¹ ⟩
    ∣ ϕ ∣ ((p ̇ A) 𝑎) ≡⟨ τ 𝑎 ⟩
    ∣ ϕ ∣ ((q ̇ A) 𝑎) ≡⟨ comm-hom-term' gfe A B ϕ q 𝑎 ⟩
    (q ̇ B) (∣ ϕ ∣ ∘ 𝑎) ∎

   -- hom-image-term-interp : (b : X → ∣ HIA ∣)(p : Term)
   --  → ∣ (p ̇ HIA ) b ∣ ≡ ∣ ϕ ∣ ((p ̇ A)(preim b))
   -- hom-image-term-interp b (generator x) = (ζ b x)⁻¹
   -- hom-image-term-interp b (node 𝓸 t) =  {!!} -- gfe φIH -- ap (𝓸 ̂ HIA) ? ?
   --  where
     -- φIH : (x : ∥ S ∥ 𝓸) → (t x ̇ HIA) b ≡ ∣ ϕ ∣ (( t x ̇ A )(preim b))
     -- φIH x = hom-image-term-interp b (t x)

   hom-image-interp : (b : X → ∣ HIA ∣)(p : Term)
    → (p ̇ HIA ) b ≡ ∣ ϕ ∣ ((p ̇ A)(preim b)) , im ((p ̇ A)(preim b))

   hom-image-interp b (generator x) = to-subtype-≡ {!!} fstbx
    where
     iiiϕ : ∣ b x ∣ ≡ ∣ ϕ ∣ (Inv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥)
     iiiϕ = InvIsInv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥ ⁻¹

     fstbx : ∣ b x ∣ ≡ ∣ ϕ ∣ (preim b x)
     fstbx = ζ b x ⁻¹
     -- we need a proof of `Image ∣ ϕ ∣ ∋ pr₁ (b x)`
     -- and b takes x to ∣ HIA ∣ = hom-image = Σ (Image_∋_ ∣ ℎ ∣)
     ∥bx∥ : Image ∣ ϕ ∣ ∋ pr₁ (b x)
     ∥bx∥ = ∥ b x ∥

   hom-image-interp b (node 𝓸 t) = ap (𝓸 ̂ HIA) (gfe φIH)
    where
     φIH : (x : ∥ S ∥ 𝓸)
      → (t x ̇ HIA) b  ≡ ∣ ϕ ∣ (( t x ̇ A )(preim b)) , im ((t x ̇ A)(preim b))
     φIH x = hom-image-interp b (t x)

   γ : (p ̇ HIA) ≡ (q ̇ HIA)
   γ = (p ̇ HIA)
         ≡⟨ refl _ ⟩
       (λ (b : X → ∣ HIA ∣) → (p ̇ HIA) b)
         ≡⟨ gfe (λ x → hom-image-interp x p) ⟩
       (λ b → ∣ ϕ ∣ ((p ̇ A) (preim b)) , im ((p ̇ A) (preim b)))
         ≡⟨ ap (λ - → λ b → ∣ ϕ ∣ (- (preim b))  , im (- (preim b))) IH ⟩
       (λ b → ∣ ϕ ∣ ((q ̇ A) (preim b)) , im ((q ̇ A)(preim b)))
         ≡⟨ (gfe (λ x → hom-image-interp x q))⁻¹ ⟩
       (λ b → (q ̇ HIA) b)
         ≡⟨ refl _ ⟩
       (q ̇ HIA)    ∎


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

 vclo-id1 {p} {q} α ( vsub {A = A} A∈VClo𝒦 sa ) = γ
   where
    A⊧p≈q : A ⊧ p ≈ q
    A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

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
     h ((p ̇ B) b)  ≡⟨ comm-hom-term' gfe B A (h , hhm) p b ⟩
     (p ̇ A)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
     (q ̇ A)(h ∘ b) ≡⟨ (comm-hom-term' gfe B A (h , hhm) q b)⁻¹ ⟩
     h ((q ̇ B) b)  ∎

    hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
    hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

    γ : p ̇ B ≡ q ̇ B
    γ = gfe λ b → hlc (ξ b)

 vclo-id1 {p}{q} α (vhom{A = A}{B = B}{ϕ = ϕ} A∈VClo𝒦) = γ
   where
    A⊧p≈q : A ⊧ p ≈ q
    A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

    HIA : Algebra 𝓤 S
    HIA = hom-image-alg{A = A}{B = B} ϕ

    ar : (X → ∣ HIA ∣ ) → (X → ∣ A ∣ )
    ar b = λ x → Inv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥

    arbr : (X → ∣ HIA ∣ ) → (X → ∣ B ∣ )
    arbr b = λ x →  ∣ ϕ ∣ (Inv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥)

    HIA⊧p≈q : HIA ⊧ p ≈ q
    HIA⊧p≈q = gfe λ b → {!!}

    γ : (p ̇ HIA) ≡ (q ̇ HIA)
    γ = gfe λ b →  {!!}



 vclo-id2 : ∀ {p q} → (VClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)

 
