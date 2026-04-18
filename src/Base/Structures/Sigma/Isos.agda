
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Sigma.Isos where

open import Axiom.Extensionality.Propositional
                            using () renaming (Extensionality to funext)
open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base   using ( _∘_ )
open import Level           using ( Level ; Lift ; lift ; lower )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong ; cong-app )

open import Overture        using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower )
open import Base.Structures.Sigma.Basic     using ( Signature ; Structure ; Lift-Struc )
open import Base.Structures.Sigma.Homs      using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-hom)
open import Base.Structures.Sigma.Products  using ( ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )

private variable 𝑅 𝐹 : Signature

module _ {α ρᵃ β ρᵇ : Level} where

 record _≅_ (𝑨 : Structure  𝑅 𝐹 {α}{ρᵃ})(𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}) : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   to : hom 𝑨 𝑩
   from : hom 𝑩 𝑨
   to∼from : ∣ to ∣ ∘ ∣ from ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣
   from∼to : ∣ from ∣ ∘ ∣ to ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣

 open _≅_ public

module _ {α ρᵃ : Level} where

 ≅-refl : {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}} → 𝑨 ≅ 𝑨
 ≅-refl {𝑨 = 𝑨} =
  record { to = 𝒾𝒹 𝑨 ; from = 𝒾𝒹 𝑨 ; to∼from = λ _ → refl ; from∼to = λ _ → refl }

module _ {α ρᵃ β ρᵇ : Level} where

 ≅-sym :  {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}}
  →       𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
 ≅-sym A≅B = record { to = from A≅B ; from = to A≅B ; to∼from = from∼to A≅B ; from∼to = to∼from A≅B }

module _  {α ρᵃ β ρᵇ γ ρᶜ : Level}
          (𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}){𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}}
          (𝑪 : Structure 𝑅 𝐹 {γ}{ρᶜ}) where

 ≅-trans : 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

 ≅-trans ab bc = record { to = f ; from = g ; to∼from = τ ; from∼to = ν }
  where
  f1 : hom 𝑨 𝑩
  f1 = to ab
  f2 : hom 𝑩 𝑪
  f2 = to bc
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = from bc
  g2 : hom 𝑩 𝑨
  g2 = from ab
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(to∼from ab (∣ g1 ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(from∼to bc (∣ f1 ∣ x)))∙(from∼to ab) x

open Level

module _ {α ρᵃ : Level} where

 Lift-≅ : (ℓ ρ : Level) → {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}} → 𝑨 ≅ (Lift-Struc ℓ ρ 𝑨)
 Lift-≅ ℓ ρ {𝑨} = record  { to = 𝓁𝒾𝒻𝓉 ℓ ρ 𝑨
                          ; from = 𝓁ℴ𝓌ℯ𝓇 ℓ ρ 𝑨
                          ; to∼from = cong-app lift∼lower
                          ; from∼to = cong-app (lower∼lift{α}{ρ}) }

module _  {α ρᵃ β ρᵇ : Level}
          {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}} where

 Lift-Struc-iso : (ℓ ρ ℓ' ρ' : Level) → 𝑨 ≅ 𝑩 → Lift-Struc ℓ ρ 𝑨 ≅ Lift-Struc ℓ' ρ' 𝑩

 Lift-Struc-iso ℓ ρ ℓ' ρ' A≅B =  ≅-trans (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
                                 ( ≅-trans (Lift-Struc ℓ ρ 𝑨) 𝑩 (≅-sym (Lift-≅ ℓ ρ)) A≅B )
                                 (Lift-≅ ℓ' ρ')

module _  {ι : Level}{I : Type ι}
          {α ρᵃ β ρᵇ : Level} {fe : funext ρᵇ ρᵇ}
          {fiu : funext ι α} {fiw : funext ι β} where

  ⨅≅ :  {𝒜 : I → Structure 𝑅 𝐹 {α}{ρᵃ}}{ℬ : I → Structure 𝑅 𝐹 {β}{ρᵇ}}
   →    (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

  ⨅≅ {𝒜 = 𝒜}{ℬ} AB = record  { to = ϕ , ϕhom
                             ; from = ψ , ψhom
                             ; to∼from = ϕ~ψ
                             ; from∼to = ψ~ϕ
                             }
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ to (AB i) ∣ (a i)

   ϕhom : is-hom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom =  ( λ r a x 𝔦 → fst ∥ to (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦))
           , λ f a → fiw (λ i → snd ∥ to (AB i) ∥ f (λ z → a z i) )

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ from (AB i) ∣ (b i)

   ψhom : is-hom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom =  ( λ r a x 𝔦 → fst ∥ from (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦))
           , λ f a → fiu (λ i → snd ∥ from (AB i) ∥ f (λ z → a z i) )

   ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ~ψ 𝒃 = fiw λ i → (to∼from (AB i)) (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ~ϕ a = fiu λ i → (from∼to (AB i)) (a i)

