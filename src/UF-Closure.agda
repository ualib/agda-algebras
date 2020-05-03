--File: UF-Closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 1 Mar 2020
--UPDATED: 28 Apr 2020
--NOTATION: 𝑨 `\MIA`, 𝑩 `\MIB`, 𝓐 `\MCA`, 𝓚 `\MCK`, 𝓤 ̇ `\MCU \^.`

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude
open import UF-Basic
open import UF-Subuniverse
open import UF-Hom
open import UF-Extensionality using (funext; global-funext; global-dfunext; happly; extensionality-lemma; dfunext)
open import UF-Free

module UF-Closure  {S : Signature 𝓞 𝓥}  where

-- Products.
data PClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) :
  Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
    pbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
    prod : {I : 𝓤 ̇} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ PClo 𝓚) → Π' 𝓐 ∈ PClo 𝓚

-- Subalgebras
data SClo ( 𝓚 : Pred ( Algebra 𝓤 S ) 𝓣 ) : Pred ( Algebra 𝓤 S ) ( 𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
  sbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
  sub : {𝑨 𝑩 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚

-- Hom Images
data HClo  (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S) ( 𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
  hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
  hhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ HClo 𝓚 →  hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ HClo 𝓚

-- Varieties
data VClo  (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
  vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
  vprod : {I : 𝓤 ̇} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ VClo 𝓚) → Π' 𝓐 ∈ VClo 𝓚
  vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
  vhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ VClo 𝓚 →  hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚

module _  (𝓚 : Pred (Algebra 𝓤 S) 𝓣 ) (X : 𝓤 ̇) (gfe : global-funext) ( dfe : dfunext 𝓤 𝓤) where

  pclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (PClo 𝓚 ⊢ p ≋ q)
  pclo-id1 {p} {q} α (pbase x) = α x
  pclo-id1 {p} {q} α (prod{I}{𝓐} 𝓐-P𝓚 ) = γ
   where
    IH : (i : I)  → (p ̇ 𝓐 i) ≡ (q ̇ 𝓐 i)
    IH = λ i → pclo-id1{p}{q} α  ( 𝓐-P𝓚  i )
    γ : p ̇ (Π' 𝓐)  ≡ q ̇ (Π' 𝓐)
    γ = (p ̇ (Π' 𝓐) )     ≡⟨ interp-prod2 gfe p 𝓐 ⟩
          ( λ ( args : X → ∣ Π' 𝓐 ∣ ) → ( λ i → (p ̇ 𝓐 i ) ( λ x → (args x) i ) ) )
                                ≡⟨  dfe (λ args → ( ap (λ - → (λ i → ( - i ) (λ x → args x i ) ) )  (dfe IH) ) )  ⟩
          ( λ ( args : X → ∣ Π' 𝓐 ∣ ) → (λ i → (q ̇ 𝓐 i ) (λ x → (args x) i ) ) )   ≡⟨ (interp-prod2 gfe q 𝓐)⁻¹ ⟩
          (q ̇ (Π' 𝓐) )     ∎

  pclo-id2 : ∀ {p q} → (PClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  pclo-id2 p 𝑨∈𝓚 = p (pbase 𝑨∈𝓚)

  sclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (SClo 𝓚 ⊢ p ≋ q)
  sclo-id1 {p} {q} 𝓚⊢p≋q (sbase A∈𝓚) = 𝓚⊢p≋q A∈𝓚
  sclo-id1 {p} {q} 𝓚⊢p≋q (sub{A}{B} A∈SClo𝓚 B≤A) = {!!}

  sclo-id2 : ∀ {p q} → (SClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  sclo-id2 p 𝑨∈𝓚 = p (sbase 𝑨∈𝓚)

  hclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (HClo 𝓚 ⊢ p ≋ q)
  hclo-id1 {p} {q} 𝓚⊢p≋q (hbase A∈𝓚) =  𝓚⊢p≋q A∈𝓚
  hclo-id1 {p} {q} 𝓚⊢p≋q (hhom{A}{B}{f} A∈HClo𝓚 ) =  γ
   where
    A⊢p≈q : A ⊢ p ≈ q
    A⊢p≈q = (hclo-id1{p}{q} 𝓚⊢p≋q ) A∈HClo𝓚

    IH : (p ̇ A) ≡ (q ̇ A)
    IH = A⊢p≈q

    HIA = hom-image-alg{𝑨 = A}{𝑩 = B} f

    𝒂 : {𝓸 : ∣ S ∣ } ( 𝒃 : X → Σ (Image_∋_ ∣ f ∣ ) )  ( x : X )   →   ∣ A ∣
    𝒂 = λ 𝒃 x → ( Inv ∣ f ∣ ( ∣ 𝒃 x ∣ ) ( ∥ 𝒃 x ∥ ) )

    hom-image-term-interpretation hiti :  ( 𝒃 : X → ∣ HIA ∣  )  (p : Term)
     →     ( p ̇ HIA ) 𝒃  ≡  ∣ f ∣ ( (p ̇ A) ( λ i → 𝒂 𝒃 i ) ) , im ( (p ̇ A) ( λ i → 𝒂 𝒃 i ) )

    hom-image-term-interpretation 𝒃 (generator x) =
     let iiif = ( InvIsInv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥ )⁻¹ in
      𝒃 x ≡⟨  {!!}  ⟩ ∣ f ∣ (𝒂 𝒃 x) , im (𝒂 𝒃 x) ∎

    hom-image-term-interpretation 𝒃 (node 𝓸 𝒕) =  ap (λ - → (𝓸 ̂ HIA) -) (gfe λ x → φIH x)
     where
      φIH : (x : ∥ S ∥ 𝓸)
       → ( 𝒕 x ̇ HIA ) 𝒃  ≡ ∣ f ∣ ( ( 𝒕 x ̇ A ) (𝒂 𝒃) ) , im ((𝒕 x ̇ A) (𝒂 𝒃 ) )
      φIH x = hom-image-term-interpretation 𝒃 (𝒕 x)

    hiti = hom-image-term-interpretation  -- alias


    γ : (p ̇ HIA) ≡ (q ̇ HIA)
    γ = (p ̇ HIA)                                                               ≡⟨ refl _ ⟩
          ( λ ( 𝒃 : X → ∣ HIA ∣ ) → (p ̇ HIA) ( λ x → (𝒃 x) ) )         ≡⟨ gfe (λ x → hiti x p) ⟩
          ( λ ( 𝒃 : X → ∣ HIA ∣ ) → ∣ f ∣ ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) ) , im ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) ) )
                                                                                    ≡⟨ ap (λ - → (λ 𝒃 → ∣ f ∣ (- (λ x → 𝒂 𝒃 x) )   , im (-  (λ x → 𝒂 𝒃 x) )) ) IH ⟩
          ( λ ( 𝒃 : X → ∣ HIA ∣ ) → ∣ f ∣ ( (q ̇ A) ( λ x → 𝒂 𝒃 x ) ) , im ( (q ̇ A) ( λ x → 𝒂 𝒃 x ) ) )  ≡⟨ ( gfe (λ x → hiti x q) )⁻¹ ⟩
          ( λ ( args : X → ∣ HIA ∣ ) → (q ̇ HIA) ( λ x → (args x) ) )   ≡⟨ refl _ ⟩
          (q ̇ HIA)                                                                ∎

  hclo-id2 : ∀ {p q} → (HClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  hclo-id2 p 𝑨∈𝓚 = p (hbase 𝑨∈𝓚)

-- vclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (VClo 𝓚 ⊢ p ≋ q)
-- vclo-id1 {p} {q} α (vbase x) = α x
-- vclo-id1 {p} {q} α (vprod x₁) = {!!}
-- vclo-id1 {p} {q} α (vsub x x₁) = {!!}
-- vclo-id1 {p} {q} α (vhom x x₁) = {!!}

  vclo-id2 : ∀ {p q} → (VClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
  vclo-id2 p 𝑨∈𝓚 = p (vbase 𝑨∈𝓚)

--   postulate
--     homclo-id1 : ∀ {p q} → 𝓚 ⊢ p ≋ q → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q
--     homclo-id2 : ∀ {p q} → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q → 𝓚 ⊢ p ≋ q

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
