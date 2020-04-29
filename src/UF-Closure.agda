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
open import UF-Extensionality using (funext; global-funext; happly)
open import UF-Free -- using (_⊢_; _⊢_≋_)

-- Products.
-- Keep I at the same universe as A so that both A and Π A can be classified by PClo
data PClo {S : Signature 𝓞 𝓥} (𝓚 : Pred (Algebra 𝓤 S) 𝓣) :
  Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
    pbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
    prod : {I : 𝓤 ̇} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ PClo 𝓚) → Π' 𝓐 ∈ PClo 𝓚

module _ {S : Signature 𝓞 𝓥} where
  -- Subalgebras
  data SClo ( 𝓚 : Pred ( Algebra 𝓤 S ) 𝓣 ) : Pred ( Algebra 𝓤 S ) ( 𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
    sbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
    sub : {𝑨 𝑩 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚

module _ {S : Signature 𝓞 𝓥} {𝑨 𝑩 : Algebra 𝓤 S} {fext : funext 𝓥 𝓤} (f : Hom 𝑨 𝑩) where
  -- Hom Images
  data HClo {S : Signature 𝓞 𝓥} (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S) ( 𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
    hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
    hhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ HClo 𝓚 → 𝑩 ∈ HClo 𝓚
     →    SubunivAlg {S = S} {𝑨 = 𝑩} { HomImage{S = S}{𝑨 = 𝑨}{𝑩 = 𝑩} f } {{!!}}
             ( hom-image-is-sub{S = S} {𝑨 = 𝑨}{𝑩 = 𝑩} f fext ) ∈ HClo 𝓚
        -- We need to specify the operations (of type `(𝓸 : ∣ S ∣) → Op (∥ S ∥ 𝓸) (Σ (HomImage f))` ) in the hole

  data VClo  (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
    vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
    vprod : {I : 𝓤 ̇} {𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ VClo 𝓚) → Π' 𝓐 ∈ VClo 𝓚
    vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
    vhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} →
      𝑨 ∈ VClo 𝓚 → 𝑩 ∈ VClo 𝓚 → SubunivAlg {S = S} {𝑨 = 𝑩} {HomImage {S = S} {𝑨 = 𝑨} {𝑩 = 𝑩} f} { {!!} }
        ( hom-image-is-sub {S = S} {𝑨 = 𝑨} {𝑩 = 𝑩} f fext ) ∈ VClo 𝓚

module _ (S : Signature 𝓞 𝓥) (𝓚 : Pred (Algebra 𝓤 S) 𝓣 ) (X : 𝓤 ̇) (gfe : global-funext) (fe : funext 𝓥 𝓤) where
  --open import Free{S = S}{X = X}

  pclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (PClo 𝓚 ⊢ p ≋ q)
  pclo-id1 {p} {q} α (pbase x) = α x
  pclo-id1 {p} {q} α (prod{I}{𝓐} 𝓐-P𝓚 ) = γ
   where
    IH : (i : I) (args : X → ∣ 𝓐 i ∣ ) → (p ̇ 𝓐 i) args ≡ (q ̇ 𝓐 i) args
    IH = λ i → cong-app ( ( pclo-id1{p}{q} α ) ( 𝓐-P𝓚  i ) )

    γ : p ̇ (Π' 𝓐)  ≡ q ̇ (Π' 𝓐)
    γ = (p ̇ (Π' 𝓐) )                                                                          ≡⟨ interp-prod2 gfe p 𝓐 ⟩
          ( λ ( args : X → ∣ Π' 𝓐 ∣ ) → ( λ i → (p ̇ 𝓐 i ) ( λ x → (args x) i ) ) ) ≡⟨ gfe {!!} ⟩
          ( λ ( args : X → ∣ Π' 𝓐 ∣ ) → (λ i → (q ̇ 𝓐 i ) (λ x → (args x) i ) ) )   ≡⟨ (interp-prod2 gfe q 𝓐)⁻¹ ⟩
          (q ̇ (Π' 𝓐) )                                           ∎


  sclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (SClo 𝓚 ⊢ p ≋ q)
  sclo-id1 {p} {q} α (sbase x) = α x

  sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sbase x₂) (mem B≤𝑨)) = γ
    where
      γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
      γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
             (λ 𝒂 → 𝒂 x₁) ∎

  sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sub x₂ x₃) (mem B≤𝑨)) = γ
    where
      γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
      γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
             (λ 𝒂 → 𝒂 x₁) ∎

  sclo-id1 {generator x} {node 𝓸 𝒕} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
    where
      γ : ((generator x) ̇ (Σ _ , _)) ≡ ((node 𝓸 𝒕) ̇ (Σ _ , _) )
      γ =  ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
            ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎

  sclo-id1 {node 𝓸 𝒕} {generator x} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
    where
      γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((generator x) ̇ (Σ _ , _) )
      γ = ( ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
             ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎ ) ⁻¹

  sclo-id1 {node 𝓸 𝒕} {node 𝓸₁ 𝒕₁} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
    where
      γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((node 𝓸₁ 𝒕₁) ̇ (Σ _ , _) )
      γ = {!!}

    -- let 𝑨⊢p≈q = (sclo-id1{p}{q} α) 𝑨∈SClo𝓚 in
    --     p ̇ 𝑩                     ≡⟨ refl _ ⟩
    --     p ̇ (∣ 𝑩 ∣ , ∥ 𝑩 ∥)       ≡⟨ γ ⟩ 
    --     q ̇ (∣ 𝑩 ∣ , ∥ 𝑩 ∥)       ≡⟨ refl _ ⟩
    --     q ̇ 𝑩                     ∎
    -- where
    --   γ : ( p ̇ ( ∣ 𝑩 ∣ , ∥ 𝑩 ∥ ) )≡ ( q ̇ ( ∣ 𝑩 ∣ , ∥ 𝑩 ∥ ) )
    --   γ = gfe λ x → {!!}

-- -- ————————————————————————————————————————————————————————————
-- -- 𝑨⊢p≈q   : 𝑨 ⊢ p ≈ q
-- -- 𝑩       : Algebra k S
-- -- x       : X → ∃ P
-- -- B≤𝑨     : (𝓸 : ∣ S ∣) (x₁ : ⟦ S ⟧ 𝓸 → ∃ P) →
-- --           ∣ B 𝓸 x₁ ∣ ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i₁ → ∣ x₁ i₁ ∣)
-- -- 𝑨∈SClo𝓚 : 𝑨 ∈ SClo 𝓚
-- -- α       : 𝓚 ⊢ p ≋ q
-- -- q       : Term
-- -- p       : Term
-- -- X       : Set k
-- -- 𝓚       : Pred (Algebra k S) l
-- -- B       : (𝓸 : ∣ S ∣) → Op (⟦ S ⟧ 𝓸) (∃ P)  (not in scope)
-- -- P       : Pred ∣ 𝑨 ∣ k  (not in scope)
-- -- 𝑨       : Algebra k S

-- -- data HClo {i j k l} {S : Signature i j} (𝓚 : Pred (Algebra k S) l) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
-- --   hbase : {𝑨 : Algebra k S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
-- --   hhom : {𝑨 B : Algebra k S} {f : Hom 𝑨 B} →
-- --     𝑨 ∈ HClo 𝓚 → B ∈ HClo 𝓚 → SubunivAlg {S = S} {B} {HomImage {S = S} {𝑨} {B} f}
-- --       (hom-image-is-sub {S = S} {𝑨} {B} f) ∈ HClo 𝓚

--   hclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (HClo 𝓚 ⊢ p ≋ q)
--   hclo-id1 {p} {q} α (hbase x) = α x
--   hclo-id1 {p} {q} α (hhom{𝑨}{𝑩}{f} 𝑨∈HClo𝓚 𝑩∈HClo𝓚 ) =
--     let 𝑨⊢p≈q = (hclo-id1{p}{q} α) 𝑨∈HClo𝓚 in
--     let 𝑩⊢p≈q = (hclo-id1{p}{q} α) 𝑩∈HClo𝓚 in
--     let hyp𝑨 = cong-app (𝑨⊢p≈q)  in
--     let hyp𝑩 = cong-app (𝑩⊢p≈q)  in
--     let subuni = SubunivAlg{i}{j}{k}{S}{𝑩}{HomImage{i}{j}{k}{S}{𝑨}{𝑩} f}
--                  (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)) in 
--        begin
--          (p ̇ subuni)
--        ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x → {!!}) ⟩
--          (q ̇ subuni)
--        ∎
--        -- begin
--        --   (p ̇ SubunivAlg (hom-image-is-sub f))
--        -- ≡⟨ ∀-extensionality-ℓ₁-ℓ₂ (λ x → {!!}) ⟩
--        --   (q ̇ SubunivAlg (hom-image-is-sub f))
--        -- ∎

--        -- Goal: (p ̇ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)))
--        --       x
--        --       ≡ (q ̇ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧))) x
--        -- ————————————————————————————————————————————————————————————
--        -- 𝑨⊢p≈q   : 𝑨 ⊢ p ≈ q
--        -- x       : X →
--        --           ∣ SubunivAlg (hom-image-is-sub ((λ z → ∣ f ∣ z) , ⟦ f ⟧)) ∣
--        -- 𝑩∈HClo𝓚 : 𝑩 ∈ HClo 𝓚
--        -- 𝑨∈HClo𝓚 : 𝑨 ∈ HClo 𝓚
--        -- α       : 𝓚 ⊢ p ≋ q
--        -- q       : Term
--        -- p       : Term
--        -- X       : Set k
--        -- 𝓚       : Pred (Algebra k S) l
--        -- f       : Hom 𝑨 B
--        -- 𝑩       : Algebra k S


--   vclo-id1 : ∀ {p q} → (𝓚 ⊢ p ≋ q) → (VClo 𝓚 ⊢ p ≋ q)
--   vclo-id1 {p} {q} α (vbase x) = α x
--   vclo-id1 {p} {q} α (vprod x₁) = {!!}
--   vclo-id1 {p} {q} α (vsub x x₁) = {!!}
--   vclo-id1 {p} {q} α (vhom x x₁) = {!!}

--   pclo-id2 : ∀ {p q} → (PClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
--   pclo-id2 p 𝑨∈𝓚 = p (pbase 𝑨∈𝓚)

--   hclo-id2 : ∀ {p q} → (HClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
--   hclo-id2 p 𝑨∈𝓚 = p (hbase 𝑨∈𝓚)

--   sclo-id2 : ∀ {p q} → (SClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
--   sclo-id2 p 𝑨∈𝓚 = p (sbase 𝑨∈𝓚)

--   vclo-id2 : ∀ {p q} → (VClo 𝓚 ⊢ p ≋ q) → (𝓚 ⊢ p ≋ q)
--   vclo-id2 p 𝑨∈𝓚 = p (vbase 𝑨∈𝓚)

--   postulate
--     homclo-id1 : ∀ {p q} → 𝓚 ⊢ p ≋ q → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q
--     homclo-id2 : ∀ {p q} → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q → 𝓚 ⊢ p ≋ q
