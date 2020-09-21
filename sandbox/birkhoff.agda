--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --without-K --exact-split #-}

open import basic
open import prelude using (global-dfunext; dfunext; Pred)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {X : 𝓤 ̇ }
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤} where

open import closure
 {𝑆 = 𝑆}
 {𝕏 = 𝕏}
 {gfe = gfe}
 {dfe = dfe}

--Equalizers of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
--cf. definition 𝓔 in the homomorphisms module

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
       (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
       --------------------------------------------------
 →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p =
   (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂))    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
 →  {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h =
 mksub (𝑬𝑯 {𝑨}{𝑩} g h)
  λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
           (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →         (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
         ---------------------------------------------------
 →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )   ∎
 where
  induction-hypothesis =
    λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

module birkhoff-theorem
 {𝓤 : Universe}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {X : 𝓤 ̇}
 {fevu : dfunext 𝓥 𝓤} where

 open closure-definitions {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}
 open closure-identities {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}{fevu = fevu}
 open compatibility {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}{fevu = fevu}

 -- Birkhoff's theorem: every variety is an equational class.
 birkhoff : -- (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺))
            (𝑨 : Algebra 𝓤 𝑆)
            ------------------------------------
  →         𝑨 ∈ Mod (Th VClo) → 𝑨 ∈ VClo
 birkhoff 𝑨 A∈ModThV = 𝑨∈VClo
  where
   ℋ : X ↠ 𝑨
   ℋ = 𝕏 𝑨

   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst ℋ

   -- hE : Epic h₀
   -- hE = snd ℋ

   h : hom 𝑻 𝑨
   h = lift-hom{𝑨 = 𝑨} h₀

   Ψ⊆ThVClo : Ψ ⊆ Th VClo
   Ψ⊆ThVClo {p , q} pΨq =
    (lr-implication (ThHSP-axiomatizes p q)) (Ψ⊆Th𝒦 p q pΨq)

   Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ → 𝑨 ⊧ p ≈ q
   Ψ⊆A⊧ {p} {q} pΨq = A∈ModThV p q (Ψ⊆ThVClo {p , q} pΨq)

   Ψ⊆Kerh : Ψ ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
   Ψ⊆Kerh {p , q} pΨq = hp≡hq
    where
     hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
     hp≡hq = hom-id-compatibility p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

   --We need to find 𝑪 : Algebra 𝒰 𝑆 such that 𝑪 ∈ VClo and ∃ ϕ : hom 𝑪 𝑨 with ϕE : Epic ∣ ϕ ∣.
   --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom 𝑪∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
   -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
   𝑪 : Algebra 𝓤 𝑆
   𝑪 = {!!}

   ϕ : Σ h ꞉ (hom 𝑪 𝑨) , Epic ∣ h ∣
   ϕ = {!!}

   hic : HomImagesOf 𝑪
   hic = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

   𝑨∈VClo : 𝑨 ∈ VClo
   𝑨∈VClo = vhom{𝑪} {!!} hic

