-- FILE: terms.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π')
open import homomorphisms using (HOM; Hom; hom)
open import relations using (Con; compatible-fun)
module terms {𝑆 : Signature 𝓞 𝓥} where

data Term {X : 𝓧 ̇}  :  𝓞 ⊔ 𝓥 ⊔ 𝓧 ̇  where
  generator : X → Term {X = X}
  node : (𝑓 : ∣ 𝑆 ∣) → (𝒕 : ∥ 𝑆 ∥ 𝑓 → Term {X = X}) → Term

open Term

𝔉 : {X : 𝓧 ̇} → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧) 𝑆
𝔉 {X = X} = Term{X = X} , node

module _ {𝑨 : Algebra 𝓤 𝑆} {X : 𝓧 ̇ } where

 --1.a. Every map (X → A) lifts.
 free-lift : (h : X → ∣ 𝑨 ∣)  →   ∣ 𝔉 ∣ → ∣ 𝑨 ∣
 free-lift h (generator x) = h x
 free-lift h (node 𝑓 args) = ∥ 𝑨 ∥ 𝑓 λ i → free-lift h (args i)

 --I. Extensional proofs (using hom's)
 --1.b.' The lift is (extensionally) a hom
 lift-hom : (h : X → ∣ 𝑨 ∣) →  hom 𝔉 𝑨
 lift-hom h = free-lift h , λ 𝑓 𝒂 → ap (∥ 𝑨 ∥ _) (refl _)

 --2.' The lift to (free → A) is (extensionally) unique.
 free-unique : funext 𝓥 𝓤 → (g h : hom (𝔉 {X = X}) 𝑨)
  →           (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
  →           (𝒕 : Term )
             ---------------------------
  →            ∣ g ∣ 𝒕 ≡ ∣ h ∣ 𝒕

 free-unique fe g h p (generator x) = p x
 free-unique fe g h p (node 𝑓 args) =
    ∣ g ∣ (node 𝑓 args)            ≡⟨ ∥ g ∥ 𝑓 args ⟩
    ∥ 𝑨 ∥ 𝑓 (λ i → ∣ g ∣ (args i))  ≡⟨ ap (∥ 𝑨 ∥ _) γ ⟩
    ∥ 𝑨 ∥ 𝑓 (λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ 𝑓 args)⁻¹ ⟩
    ∣ h ∣ (node 𝑓 args)             ∎
    where γ = fe λ i → free-unique fe g h p (args i)

 --1.b. that free-lift is (intensionally) a hom.
 lift-HOM : (h : X → ∣ 𝑨 ∣) →  HOM 𝔉 𝑨
 lift-HOM  h = free-lift h , refl _

 --2. The lift to  (free → A)  is (intensionally) unique.

 free-intensionally-unique : funext 𝓥 𝓤
  →             (g h : HOM (𝔉{X = X}) 𝑨)
  →             (∣ g ∣ ∘ generator) ≡ (∣ h ∣ ∘ generator)
  →             (𝒕 : Term)
               --------------------------------
  →              ∣ g ∣ 𝒕 ≡ ∣ h ∣ 𝒕

 free-intensionally-unique fe g h p (generator x) =
  intensionality p x

 free-intensionally-unique fe g h p (node 𝑓 args) =
  ∣ g ∣ (node 𝑓 args)   ≡⟨ ap (λ - → - 𝑓 args) ∥ g ∥ ⟩
  ∥ 𝑨 ∥ 𝑓(∣ g ∣ ∘ args) ≡⟨ ap (∥ 𝑨 ∥ _) γ ⟩
  ∥ 𝑨 ∥ 𝑓(∣ h ∣ ∘ args) ≡⟨ (ap (λ - → - 𝑓 args) ∥ h ∥ ) ⁻¹ ⟩
  ∣ h ∣ (node 𝑓 args)  ∎
   where
    γ = fe λ i → free-intensionally-unique fe g h p (args i)

_̂_ : (𝑓 : ∣ 𝑆 ∣)
 →   (𝑨 : Algebra 𝓤 𝑆)
 →   (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

𝑓 ̂ 𝑨 = λ x → (∥ 𝑨 ∥ 𝑓) x

_̇_ : {X : 𝓧 ̇ } → Term{X = X}
 →   (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

((generator x)̇ 𝑨) 𝒂 = 𝒂 x

((node 𝑓 args)̇ 𝑨) 𝒂 = (𝑓 ̂ 𝑨) λ{x → (args x ̇ 𝑨) 𝒂}


interp-prod : funext 𝓥 𝓤
 →            {X : 𝓧 ̇}{I : 𝓤 ̇}(p : Term{X = X})
              (𝓐 : I → Algebra 𝓤 𝑆)
              (x : X → ∀ i → ∣ (𝓐 i) ∣)
 →            (p ̇ (Π' 𝓐)) x ≡ (λ i → (p ̇ 𝓐 i) (λ j → x j i))

interp-prod fe (generator x₁) 𝓐 x = refl _

interp-prod fe (node 𝑓 𝒕) 𝓐 x =
 let IH = λ x₁ → interp-prod fe (𝒕 x₁) 𝓐 x in
  ∥ Π' 𝓐 ∥ 𝑓 (λ x₁ → (𝒕 x₁ ̇ Π' 𝓐) x)
      ≡⟨ ap (∥ Π' 𝓐 ∥ 𝑓 ) (fe IH) ⟩
  ∥ Π' 𝓐 ∥ 𝑓 (λ x₁ → (λ i₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁)))
      ≡⟨ refl _ ⟩
  (λ i₁ → ∥ 𝓐 i₁ ∥ 𝑓 (λ x₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁)))
      ∎

interp-prod2 : global-dfunext
 →             {X : 𝓧 ̇ }{I : 𝓤 ̇ }
               (p : Term{X = X}) (A : I → Algebra 𝓤 𝑆)
     -----------------------------------------------------------
 → (p ̇ Π' A) ≡ λ(args : X → ∣ Π' A ∣)
                   → (λ i → (p ̇ A i)(λ x → args x i))

interp-prod2 fe (generator x₁) A = refl _

interp-prod2 fe {X = X} (node 𝑓 𝒕) A =
  fe λ (tup : X → ∣ Π' A ∣) →
   let IH = λ x → interp-prod fe (𝒕 x) A  in
   let tᴬ = λ z → 𝒕 z ̇ Π' A in
    (𝑓 ̂ Π' A) (λ s → tᴬ s tup)
      ≡⟨ refl _ ⟩
    ∥ Π' A ∥ 𝑓 (λ s →  tᴬ s tup)
      ≡⟨ ap ( ∥ Π' A ∥ 𝑓 ) (fe  λ x → IH x tup) ⟩
    ∥ Π' A ∥ 𝑓 (λ s → (λ j → (𝒕 s ̇ A j)(λ ℓ → tup ℓ j)))
      ≡⟨ refl _ ⟩
    (λ i → (𝑓 ̂ A i)(λ s → (𝒕 s ̇ A i)(λ ℓ → tup ℓ i)))
      ∎

-- Proof of 1. (homomorphisms commute with terms).
comm-hom-term : global-dfunext
 →              {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
                (ℎ : HOM 𝑨 𝑩) (𝒕 : Term{X = X})
               ---------------------------------------------
 →              ∣ ℎ ∣ ∘ (𝒕 ̇ 𝑨) ≡ (𝒕 ̇ 𝑩) ∘ (λ 𝒂 → ∣ ℎ ∣ ∘ 𝒂 )

comm-hom-term gfe 𝑨 𝑩 ℎ (generator x) = refl _

comm-hom-term gfe {X = X}𝑨 𝑩 ℎ (node 𝑓 args) = γ
 where
  γ : ∣ ℎ ∣ ∘ (λ 𝒂 → (𝑓 ̂ 𝑨) (λ i → (args i ̇ 𝑨) 𝒂))
      ≡ (λ 𝒂 → (𝑓 ̂ 𝑩)(λ i → (args i ̇ 𝑩) 𝒂)) ∘ _∘_ ∣ ℎ ∣
  γ = ∣ ℎ ∣ ∘ (λ 𝒂 → (𝑓 ̂ 𝑨) (λ i → (args i ̇ 𝑨) 𝒂))
        ≡⟨ ap (λ - → (λ 𝒂 → - 𝑓 (λ i → (args i ̇ 𝑨) 𝒂))) ∥ ℎ ∥ ⟩
      (λ 𝒂 → (𝑓 ̂ 𝑩)(∣ ℎ ∣ ∘ (λ i →  (args i ̇ 𝑨) 𝒂)))
        ≡⟨ refl _ ⟩
      (λ 𝒂 → (𝑓 ̂ 𝑩)(λ i → ∣ ℎ ∣ ((args i ̇ 𝑨) 𝒂)))
        ≡⟨ ap (λ - → (λ 𝒂 → (𝑓 ̂ 𝑩)(- 𝒂))) ih ⟩
    (λ 𝒂 → (𝑓 ̂ 𝑩)(λ i → (args i ̇ 𝑩) 𝒂)) ∘ _∘_ ∣ ℎ ∣
        ∎
    where
     IH : (𝒂 : X → ∣ 𝑨 ∣)(i : ∥ 𝑆 ∥ 𝑓)
      →   (∣ ℎ ∣ ∘ (args i ̇ 𝑨)) 𝒂 ≡ ((args i ̇ 𝑩) ∘ _∘_ ∣ ℎ ∣) 𝒂
     IH 𝒂 i = intensionality (comm-hom-term gfe 𝑨 𝑩 ℎ (args i)) 𝒂

     ih : (λ 𝒂 → (λ i → ∣ ℎ ∣ ((args i ̇ 𝑨) 𝒂)))
           ≡ (λ 𝒂 → (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ ℎ ∣) 𝒂))
     ih = gfe λ 𝒂 → gfe λ i → IH 𝒂 i

compatible-term : {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)
                  ( 𝒕 : Term{X = X} ) (θ : Con 𝑨)
                 ---------------------------------
 →                 compatible-fun (𝒕 ̇ 𝑨) ∣ θ ∣

compatible-term 𝑨 (generator x) θ p = p x
compatible-term 𝑨 (node 𝑓 args) θ p =
 pr₂( ∥ θ ∥ ) 𝑓 λ{x → (compatible-term 𝑨 (args x) θ) p}

-- Proof of 1. (homomorphisms commute with terms).
comm-hom-term' : global-dfunext --  𝓥 𝓤
 →               {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
 →               (ℎ : hom 𝑨 𝑩) (𝒕 : Term{X = X}) (𝒂 : X → ∣ 𝑨 ∣)
               --------------------------------------------
 →               ∣ ℎ ∣ ((𝒕 ̇ 𝑨) 𝒂) ≡ (𝒕 ̇ 𝑩) (∣ ℎ ∣ ∘ 𝒂)

comm-hom-term' fe 𝑨 𝑩 ℎ (generator x) 𝒂 = refl _

comm-hom-term' fe 𝑨 𝑩 ℎ (node 𝑓 args) 𝒂 =
 ∣ ℎ ∣ ((𝑓 ̂ 𝑨)  (λ i₁ → (args i₁ ̇ 𝑨) 𝒂))
   ≡⟨ ∥ ℎ ∥ 𝑓 ( λ r → (args r ̇ 𝑨) 𝒂 ) ⟩
 (𝑓 ̂ 𝑩) (λ i₁ →  ∣ ℎ ∣ ((args i₁ ̇ 𝑨) 𝒂))
   ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term' fe 𝑨 𝑩 ℎ (args i₁) 𝒂))⟩
 (𝑓 ̂ 𝑩) (λ r → (args r ̇ 𝑩) (∣ ℎ ∣ ∘ 𝒂))
   ∎

-- Proof of 2. (If t : Term, θ : Con A, then a θ b → t(a) θ t(b))
compatible-term' : {X : 𝓧 ̇}
           (𝑨 : Algebra 𝓤 𝑆) (𝒕 : Term{X = X}) (θ : Con 𝑨)
           --------------------------------------------------
 →                   compatible-fun (𝒕 ̇ 𝑨) ∣ θ ∣

compatible-term' 𝑨 (generator x) θ p = p x

compatible-term' 𝑨 (node 𝑓 args) θ p =
 pr₂( ∥ θ ∥ ) 𝑓 λ{x → (compatible-term' 𝑨 (args x) θ) p}

