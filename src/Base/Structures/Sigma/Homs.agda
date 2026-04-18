
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Sigma.Homs where

open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level ; Lift ; lift ; lower )
open import Function.Base   using ( _∘_ ; id )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ;  cong ; refl ; module ≡-Reasoning )

open import Overture        using ( ∣_∣ ; ∥_∥ ; _∙_ ; _⁻¹)
open import Base.Functions  using ( IsInjective ; IsSurjective )
open import Base.Relations  using ( _|:_ ; 0[_] ; ker ; Equivalence ; Quotient )
                            using ( 0[_]Equivalence ; ker-IsEquivalence ; ⟪_⟫ )
                            using ( kerlift-IsEquivalence ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Base.Equality   using ( swelldef )
open import Base.Structures.Sigma.Basic
                            using ( Signature ; Structure ; Compatible ; _ʳ_ ; _ᵒ_ )
                            using ( Lift-Strucʳ ; Lift-Strucˡ ; Lift-Struc )

private variable 𝑅 𝐹 : Signature

module _  {α ρᵃ : Level} (𝑨 : Structure  𝑅 𝐹 {α}{ρᵃ})
          {β ρᵇ : Level} (𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}) where

 preserves : ∣ 𝑅 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 preserves r h = ∀ a → ((r ʳ 𝑨) a) → ((r ʳ 𝑩) (h ∘ a))

 is-hom-rel : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 is-hom-rel h = ∀ r →  preserves r h

 comp-op : ∣ 𝐹 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 comp-op f h = ∀ a → h ((f ᵒ 𝑨) a) ≡ (f ᵒ 𝑩) (h ∘ a)

 is-hom-op : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 is-hom-op h = ∀ f → comp-op f h

 is-hom : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-hom h = is-hom-rel h × is-hom-op h

 hom : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ[ h ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-hom h

module _  {𝑅 𝐹 : Signature}
          {α ρᵃ : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ})
          {β ρᵇ : Level}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}}
          {γ ρᶜ : Level}(𝑪 : Structure 𝑅 𝐹 {γ}{ρᶜ}) where

 ∘-is-hom-rel :  {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →              is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)

 ∘-is-hom-rel {f}{g} fhr ghr R a = λ z → ghr R (λ z₁ → f (a z₁)) (fhr R a z)

 ∘-is-hom-op :  {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →             is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)

 ∘-is-hom-op {f}{g} fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom :  {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →          is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)

 ∘-is-hom {f} {g} fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel {f}{g} (fst fhro) (fst ghro)

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op {f}{g} (snd fhro) (snd ghro)

 ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪 → hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom {f}{g} fh gh

module _ {α ρ : Level} where

 𝒾𝒹 : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , (λ R a z → z)  , (λ f a → refl)

module _  {α ρᵃ : Level} (𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ})
          {β ρᵇ : Level} (𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}) where

 is-mon : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-mon g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-mon g

 is-epi : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-epi g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epi g

 mon→hom : mon → hom 𝑨 𝑩
 mon→hom ϕ = (fst ϕ) , fst (snd ϕ )

 epi→hom : epi → hom 𝑨 𝑩
 epi→hom ϕ = (fst ϕ) , fst (snd ϕ)

module _ {𝑅 𝐹 : Signature}{α ρᵃ : Level} where
 open Lift

 𝓁𝒾𝒻𝓉 : (ℓ ρ : Level)(𝑨 : Structure  𝑅 𝐹{α}{ρᵃ}) → hom 𝑨 (Lift-Struc ℓ ρ 𝑨)
 𝓁𝒾𝒻𝓉 = λ ℓ ρ 𝑨 → lift , ( (λ R a x → lift x) , λ f a → refl )

 𝓁ℴ𝓌ℯ𝓇 : (ℓ ρ : Level)(𝑨 : Structure  𝑅 𝐹{α}{ρᵃ}) → hom (Lift-Struc ℓ ρ 𝑨) 𝑨
 𝓁ℴ𝓌ℯ𝓇 = λ ℓ ρ 𝑨 → lower , (λ R a x → lower x) , (λ f a → refl)

module _  {𝑅 𝐹 : Signature}{α ρᵃ β ρᵇ : Level}{𝑅 𝐹 : Signature}
          {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}} where

 Lift-Hom : (ℓ ρ ℓ' ρ' : Level) → hom 𝑨 𝑩 → hom (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
 Lift-Hom ℓ ρ ℓ' ρ' (h , hhom) = lift ∘ h ∘ lower , Goal
  where
  lABh : is-hom (Lift-Struc ℓ ρ 𝑨) 𝑩 (h ∘ lower)
  lABh = ∘-is-hom{𝑅 = 𝑅}{𝐹} (Lift-Struc ℓ ρ 𝑨) 𝑩{lower}{h} ((λ R a x → lower x) , (λ f a → refl)) hhom

  Goal : is-hom (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩) (lift ∘ h ∘ lower)
  Goal = ∘-is-hom  {𝑅 = 𝑅}{𝐹} (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
                   {h ∘ lower}{lift} lABh ((λ R a x → lift x) , (λ f a → refl))

open ≡-Reasoning
module _  {𝑅 𝐹 : Signature} {α ρᵃ β ρᵇ : Level}
          {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹{β}{ρᵇ}} where

 Homker-comp : swelldef ℓ₀ β → (h : hom 𝑨 𝑩) → Compatible 𝑨 (ker ∣ h ∣)
 Homker-comp wd h f {u}{v} kuv =  (∣ h ∣ ((f ᵒ 𝑨) u))   ≡⟨(snd ∥ h ∥) f u ⟩
                                  ((f ᵒ 𝑩)(∣ h ∣ ∘ u))  ≡⟨ wd (f ᵒ 𝑩) (∣ h ∣ ∘ u) (∣ h ∣ ∘ v) kuv ⟩
                                  ((f ᵒ 𝑩)(∣ h ∣ ∘ v))  ≡⟨((snd ∥ h ∥) f v)⁻¹ ⟩
                                  (∣ h ∣((f ᵒ 𝑨) v))    ∎

