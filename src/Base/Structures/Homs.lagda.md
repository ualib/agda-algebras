---
layout: default
title : "Base.Structures.Homs"
date : "2021-06-22"
author: "agda-algebras development team"
---

### <a id="homomorphisms-of-general-structures">Homomorphisms of General Structures</a>

This is the [Base.Structures.Homs][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Homs where

-- Imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using () renaming ( lzero to ℓ₀ ; Set to Type )
open import Axiom.Extensionality.Propositional
                             using () renaming (Extensionality to funext)
open import Data.Product     using ( _×_ ; Σ-syntax ; _,_ )
                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base    using ( _∘_ ; id )
open import Level            using ( _⊔_ ; suc ; Level ; Lift ; lift )
open import Relation.Binary  using ( IsEquivalence )
open import Relation.Binary.PropositionalEquality
                             using ( _≡_ ; refl ; sym ; cong ; module ≡-Reasoning ; trans )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture              using ( _∙_ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; Π-syntax )
open import Base.Functions        using ( Image_∋_ ; IsSurjective ; IsInjective )
open import Base.Relations        using ( ker ; kerlift ; ⟪_⟫ ; mkblk )
open import Base.Equality         using ( swelldef )

open import Examples.Structures.Signatures  using ( S∅ )

open import Base.Structures.Basic  using ( signature ; structure ; Lift-Struc )
                                   using ( Lift-Strucʳ ; Lift-Strucˡ )
                                   using ( compatible ; siglʳ ; sigl )

open import Base.Structures.Congruences  using ( con ; _╱_)
open import Base.Structures.Products     using ( ⨅ )
open structure ; open signature

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 α ρᵃ β ρᵇ γ ρᶜ ℓ : Level

module _ (𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}) (𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}) where
 private
  A = carrier 𝑨
  B = carrier 𝑩

 preserves : (symbol 𝑅) → (A → B) → Type (siglʳ 𝑅 ⊔ α ⊔ ρᵃ ⊔ ρᵇ)
 preserves 𝑟 h = ∀ a → ((rel 𝑨) 𝑟 a) → ((rel 𝑩) 𝑟) (h ∘ a)

 is-hom-rel : (A → B) → Type (sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ ρᵇ)
 is-hom-rel h = ∀ (r : symbol 𝑅) → preserves r h

 comm-op : (A → B) → (symbol 𝐹) → Type (siglʳ 𝐹 ⊔ α ⊔ β)
 comm-op h f = ∀ a → h (((op 𝑨) f) a) ≡ ((op 𝑩) f) (h ∘ a)

 is-hom-op : (A → B) → Type (sigl 𝐹 ⊔ α ⊔ β)
 is-hom-op h = ∀ f → comm-op h f

 is-hom : (A → B) → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-hom h = is-hom-rel h × is-hom-op h

 -- homomorphism
 hom : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ[ h ∈ (A → B) ] is-hom h

-- endomorphism
end : structure 𝐹 𝑅 {α}{ρᵃ} → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ)
end 𝑨 = hom 𝑨 𝑨

module _  {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}}
          {𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}}
          {𝑪 : structure 𝐹 𝑅 {γ}{ρᶜ}} where

 private A = carrier 𝑨 ; B = carrier 𝑩 ; C = carrier 𝑪

 ∘-is-hom-rel :  (f : A → B)(g : B → C)
  →              is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel f g fhr ghr R a = λ z → ghr R (λ z₁ → f (a z₁)) (fhr R a z)

 ∘-is-hom-op :  (f : A → B)(g : B → C)
  →             is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op f g fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom :  (f : A → B)(g : B → C)
  →          is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)
 ∘-is-hom f g fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel f g ∣ fhro ∣ ∣ ghro ∣

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op f g ∥ fhro ∥ ∥ ghro ∥

 ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪 → hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom f g fh gh


𝒾𝒹 : {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} → end 𝑨
𝒾𝒹 = id , (λ _ _ z → z)  , (λ _ _ → refl)


module _ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} {𝑩 : structure 𝐹 𝑅  {β}{ρᵇ}} where

 private A = carrier 𝑨 ; B = carrier 𝑩

 is-mon : (A → B) → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-mon g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ[ g ∈ (A → B) ] is-mon g

 mon→hom : mon → hom 𝑨 𝑩
 mon→hom ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

 is-epi : (A → B) → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-epi g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ[ g ∈ (A → B) ] is-epi g

 epi→hom : epi → hom 𝑨 𝑩
 epi→hom ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

open Lift

𝓁𝒾𝒻𝓉ˡ : {ℓ : Level}{𝑨 : structure 𝐹 𝑅  {α}{ρᵃ}} → hom 𝑨 (Lift-Strucˡ ℓ 𝑨)
𝓁𝒾𝒻𝓉ˡ = lift , (λ _ _ x → x) , λ _ _ → refl

𝓁𝒾𝒻𝓉ʳ : {ρ : Level}{𝑨 : structure 𝐹 𝑅  {α}{ρᵃ}} → hom 𝑨 (Lift-Strucʳ ρ 𝑨)
𝓁𝒾𝒻𝓉ʳ = id , (λ _ _ x → lift x) , λ _ _ → refl

𝓁𝒾𝒻𝓉 : {ℓˡ ℓʳ : Level}{𝑨 : structure 𝐹 𝑅  {α}{ρᵃ}} → hom 𝑨 (Lift-Struc ℓˡ ℓʳ 𝑨)
𝓁𝒾𝒻𝓉 = lift , ((λ _ _ x → lift x) , λ _ _ → refl)

𝓁ℴ𝓌ℯ𝓇ˡ : {ℓ : Level}{𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} → hom (Lift-Strucˡ ℓ 𝑨) 𝑨
𝓁ℴ𝓌ℯ𝓇ˡ = lower , (λ _ _ x → x) , (λ _ _ → refl)

𝓁ℴ𝓌ℯ𝓇ʳ : {ρ : Level}{𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} → hom (Lift-Strucʳ ρ 𝑨) 𝑨
𝓁ℴ𝓌ℯ𝓇ʳ = id , ((λ _ _ x → lower x) , λ _ _ → refl)

𝓁ℴ𝓌ℯ𝓇 : {ℓˡ ℓʳ : Level}{𝑨 : structure 𝐹 𝑅  {α}{ρᵃ}} → hom (Lift-Struc ℓˡ ℓʳ 𝑨) 𝑨
𝓁ℴ𝓌ℯ𝓇 = lower , (λ _ _ x → lower x) , (λ _ _ → refl)
```



#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>


```agda


open ≡-Reasoning
module _ {𝑨 : structure 𝐹 𝑅  {α}{β ⊔ ρᵃ}}{𝑩 : structure 𝐹 𝑅 {β} {ρᵇ}} where

 homker-comp :  (h : hom 𝑨 𝑩){wd : swelldef (siglʳ 𝐹) β}
  →             compatible 𝑨 (ker ∣ h ∣)

 homker-comp (h , hhom) {wd} f {u}{v} kuv =
  h (((op 𝑨)f) u)    ≡⟨ ∥ hhom ∥ f u ⟩
  ((op 𝑩) f)(h ∘ u)  ≡⟨ wd ((op 𝑩)f) (h ∘ u) (h ∘ v) kuv ⟩
  ((op 𝑩) f)(h ∘ v)  ≡⟨ (∥ hhom ∥ f v)⁻¹ ⟩
  h (((op 𝑨)f) v)    ∎

 kerlift-comp :  (h : hom 𝑨 𝑩){wd : swelldef (siglʳ 𝐹) β}
  →              compatible 𝑨 (kerlift ∣ h ∣ (α ⊔ ρᵃ) )

 kerlift-comp (h , hhom) {wd} f {u}{v} kuv = lift goal
  where
  goal : h (op 𝑨 f u) ≡ h (op 𝑨 f v)
  goal =  h (op 𝑨 f u)     ≡⟨ ∥ hhom ∥ f u ⟩
          (op 𝑩 f)(h ∘ u)  ≡⟨ wd (op 𝑩 f)(h ∘ u)(h ∘ v)(lower ∘ kuv) ⟩
          (op 𝑩 f)(h ∘ v)  ≡⟨ (∥ hhom ∥ f v ) ⁻¹ ⟩
          h (op 𝑨 f v)     ∎


 kercon : hom 𝑨 𝑩 → {wd : swelldef (siglʳ 𝐹) β} → con 𝑨
 kercon (h , hhom) {wd} =  ((λ x y → Lift (α ⊔ ρᵃ) (h x ≡ h y)) , goal)
                           , kerlift-comp (h , hhom) {wd}
  where
  goal : IsEquivalence (λ x y → Lift (α ⊔ ρᵃ) (h x ≡ h y))
  goal = record  { refl = lift refl
                 ; sym = λ p → lift (sym (lower p))
                 ; trans = λ p q → lift (trans (lower p)(lower q))
                 }

 kerquo :  hom 𝑨 𝑩 → {wd : swelldef (siglʳ 𝐹) β}
  →        structure 𝐹 𝑅 {suc (α ⊔ β ⊔ ρᵃ)} {β ⊔ ρᵃ}

 kerquo h {wd} = 𝑨 ╱ (kercon h {wd})

ker[_⇒_] :  (𝑨 : structure 𝐹 𝑅 {α} {β ⊔ ρᵃ} )(𝑩 : structure 𝐹 𝑅 {β}{ρᵇ} )
 →          hom 𝑨 𝑩 → {wd : swelldef (siglʳ 𝐹) β} → structure 𝐹 𝑅

ker[_⇒_] {ρᵃ = ρᵃ} 𝑨 𝑩 h {wd} = kerquo{ρᵃ = ρᵃ}{𝑨 = 𝑨}{𝑩} h {wd}
```



#### <a id="canonical-projections">Canonical projections</a>


```agda


module _ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ} } where

 open Image_∋_

 πepi : (θ : con 𝑨) → epi {𝑨 = 𝑨}{𝑩 = 𝑨 ╱ θ}
 πepi θ = (λ a → ⟪ a ⟫ {fst ∣ θ ∣}) , (γrel , (λ _ _ → refl)) , cπ-is-epic
  where
  γrel : is-hom-rel 𝑨 (𝑨 ╱ θ) (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  γrel R a x = x
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  cπ-is-epic (C , mkblk a refl) = eq a refl

 πhom : (θ : con 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom {𝑨 = 𝑨} {𝑩 = (𝑨 ╱ θ)} (πepi θ)

module _ {𝑨 : structure 𝐹 𝑅  {α}{β ⊔ ρᵃ}}{𝑩 : structure 𝐹 𝑅 {β} {ρᵇ}} where

 πker :  (h : hom 𝑨 𝑩){wd : swelldef (siglʳ 𝐹) β}
  →      epi {𝑨 = 𝑨} {𝑩 = (ker[_⇒_]{ρᵃ = ρᵃ} 𝑨 𝑩 h {wd})}

 πker h {wd} = πepi (kercon{ρᵃ = ρᵃ} {𝑨 = 𝑨}{𝑩 = 𝑩} h {wd})


module _ {I : Type ℓ} where

  module _  {𝑨 : structure 𝐹 𝑅  {α}{ρᵃ}}{ℬ : I → structure 𝐹 𝑅  {β}{ρᵇ}} where

   ⨅-hom-co : funext ℓ β → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
   ⨅-hom-co fe h =  (λ a i → ∣ h i ∣ a)
                    , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R a x)
                    , λ f a → fe (λ i → snd ∥ h i ∥ f a)

  module _  {𝒜 : I → structure 𝐹 𝑅 {α}{ρᵃ}}
            {ℬ : I → structure 𝐹 𝑅  {β}{ρᵇ}} where

   ⨅-hom : funext ℓ β → Π[ i ∈ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
   ⨅-hom fe h =  (λ a i → ∣ h i ∣ (a i))
                 , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R (λ z → a z 𝔦) (x 𝔦))
                 , λ f a → fe (λ i → snd ∥ h i ∥ f λ z → a z i)

  -- Projection out of products
  module _ {𝒜 : I → structure 𝐹 𝑅 {α}{ρᵃ}} where
   ⨅-projection-hom : Π[ i ∈ I ] hom (⨅ 𝒜) (𝒜 i)
   ⨅-projection-hom = λ x → (λ z → z x) , (λ R a z → z x)  , λ f a → refl

-- The special case when 𝑅 = ∅ (i.e., purely algebraic structures)
module _ {𝑨 : structure 𝐹 S∅ {α}{ℓ₀}} {𝑩 : structure 𝐹 S∅ {β}{ℓ₀}} where

 -- The type of homomorphisms from one algebraic structure to another.
 hom-alg : Type (sigl 𝐹 ⊔ α ⊔ β)
 hom-alg = Σ[ h ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-hom-op 𝑨 𝑩 h
```


--------------------------------

<span style="float:left;">[← Base.Structures.Congruences](Base.Structures.Congruences.html)</span>
<span style="float:right;">[Base.Structures.Isos →](Base.Structures.Isos.html)</span>

{% include UALib.Links.md %}
