
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( Signature; 𝓞 ; 𝓥 )

module Base.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  renaming ( Set to Type )   using ()
open import Data.Product    renaming ( proj₁ to fst )
                            using ( _,_ ; Σ ;  _×_ ; Σ-syntax)
open import Function        using ( _∘_ ; id )
open import Level           using ( Level ; _⊔_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Overture               using ( ∣_∣ ; ∥_∥ )
open import Base.Functions         using ( IsInjective ; IsSurjective )
open import Base.Algebras {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; Lift-Alg )

private variable α β : Level

module _ (𝑨 : Algebra α)(𝑩 : Algebra β) where

 compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(α ⊔ 𝓥 ⊔ β)
 compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

 is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

 hom : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 hom = Σ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) is-homomorphism

𝒾𝒹 : (𝑨 : Algebra α) → hom 𝑨 𝑨
𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

open Level

𝓁𝒾𝒻𝓉 : {β : Level}(𝑨 : Algebra α) → hom 𝑨 (Lift-Alg 𝑨 β)
𝓁𝒾𝒻𝓉 _ = lift , λ 𝑓 𝑎 → refl

𝓁ℴ𝓌ℯ𝓇 : {β : Level}(𝑨 : Algebra α) → hom (Lift-Alg 𝑨 β) 𝑨
𝓁ℴ𝓌ℯ𝓇 _ = lower , λ 𝑓 𝑎 → refl

is-monomorphism : (𝑨 : Algebra α)(𝑩 : Algebra β) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsInjective g

mon : Algebra α → Algebra β → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
mon 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-monomorphism 𝑨 𝑩 g

is-epimorphism : (𝑨 : Algebra α)(𝑩 : Algebra β) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

epi : Algebra α → Algebra β → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
epi 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epimorphism 𝑨 𝑩 g

mon→hom : (𝑨 : Algebra α){𝑩 : Algebra β} → mon 𝑨 𝑩 → hom 𝑨 𝑩
mon→hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

epi→hom : {𝑨 : Algebra α}(𝑩 : Algebra β) → epi 𝑨 𝑩 → hom 𝑨 𝑩
epi→hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

