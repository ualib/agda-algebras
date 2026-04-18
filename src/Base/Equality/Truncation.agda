
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Equality.Truncation where

open import Agda.Primitive   renaming ( Set to Type )                  using ()
open import Data.Product     renaming ( proj₁ to fst ; proj₂ to snd )  using ( _,_ ; Σ ; Σ-syntax ; _×_ )
open import Function                                                   using ( _∘_ ; id )
open import Level                                                      using ( _⊔_ ; suc ; Level )
open import Relation.Binary  renaming ( Rel to BinRel )                using ( IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡                 using ( _≡_ ; module ≡-Reasoning )
open import Relation.Unary                                             using ( Pred ; _⊆_ )

open import Overture         using ( _⁻¹ ; transport ; ∥_∥ ; _≈_ ; ∣_∣ )
open import Base.Functions    using ( IsInjective )
open import Base.Relations   using ( IsBlock ; Rel ; REL )

private variable α β ρ 𝓥 : Level

is-center : (A : Type α ) → A → Type α
is-center A c = (x : A) → c ≡ x

is-singleton : Type α → Type α
is-singleton A = Σ A (is-center A)

is-prop : Type α → Type α
is-prop A = (x y : A) → x ≡ y

is-prop-valued : {A : Type α} → BinRel A ρ → Type(α ⊔ ρ)
is-prop-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

open ≡-Reasoning
singleton-is-prop : {α : Level}(X : Type α) → is-singleton X → is-prop X
singleton-is-prop X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

fiber : {A : Type α } {B : Type β } (f : A → B) → B → Type (α ⊔ β)
fiber {α}{β}{A} f y = Σ[ x ∈ A ] f x ≡ y

is-equiv : {A : Type α } {B : Type β } → (A → B) → Type (α ⊔ β)
is-equiv f = ∀ y → is-singleton (fiber f y)

hfunext :  ∀ α β → Type (suc (α ⊔ β))
hfunext α β = {A : Type α}{B : A → Type β} (f g : (x : A) → B x) → is-equiv (≡.cong-app{f = f}{g})

is-set : Type α → Type α
is-set A = is-prop-valued{A = A} _≡_

module _ {A : Type α}{B : A → Type β} where

 to-Σ-≡ : {σ τ : Σ[ x ∈ A ] B x} → (Σ[ p ∈ (fst σ ≡ fst τ) ] (transport B p ∥ σ ∥) ≡ ∥ τ ∥) → σ ≡ τ
 to-Σ-≡ (≡.refl , ≡.refl) = ≡.refl

is-embedding : {A : Type α}{B : Type β} → (A → B) → Type (α ⊔ β)
is-embedding f = ∀ b → is-prop (fiber f b)

singleton-type : {A : Type α} → A → Type α
singleton-type {α}{A} x = Σ[ y ∈ A ] y ≡ x

module _ {A : Type α}{B : Type β} where

 invertible : (A → B) → Type (α ⊔ β)
 invertible f = Σ[ g ∈ (B → A) ] ((g ∘ f ≈ id) × (f ∘ g ≈ id))

 equiv-is-embedding : (f : A → B) → is-equiv f → is-embedding f
 equiv-is-embedding f i y = singleton-is-prop (fiber f y) (i y)

private variable
 A : Type α
 B : Type β

monic-is-embedding|Set : (f : A → B) → is-set B → IsInjective f → is-embedding f
monic-is-embedding|Set f Bset fmon b (u , fu≡b) (v , fv≡b) = γ
 where
 fuv : f u ≡ f v
 fuv = ≡.trans fu≡b (fv≡b ⁻¹)

 uv : u ≡ v
 uv = fmon fuv

 arg1 : Σ[ p ∈ u ≡ v ] transport (λ a → f a ≡ b) p fu≡b ≡ fv≡b
 arg1 = uv , Bset (f v) b (transport (λ a → f a ≡ b) uv fu≡b) fv≡b

 γ : (u , fu≡b) ≡ (v , fv≡b)
 γ = to-Σ-≡ arg1

blk-uip : (A : Type α)(R : BinRel A ρ ) → Type(α ⊔ suc ρ)
blk-uip A R = ∀ (C : Pred A _) → is-prop (IsBlock C {R})

module _ {I : Type 𝓥} where

 IsRelProp : {ρ : Level}(A : Type α) → Rel A I{ρ}  → Type (𝓥 ⊔ α ⊔ ρ)
 IsRelProp B P = ∀ (b : (I → B)) → is-prop (P b)

 RelProp : Type α → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
 RelProp A ρ = Σ[ P ∈ Rel A I{ρ} ] IsRelProp A P

 RelPropExt : Type α → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
 RelPropExt A ρ = {P Q : RelProp A ρ } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

 IsRELProp : {ρ : Level} (𝒜 : I → Type α) → REL I 𝒜 {ρ}  → Type (𝓥 ⊔ α ⊔ ρ)
 IsRELProp 𝒜 P = ∀ (a : ((i : I) → 𝒜 i)) → is-prop (P a)

 RELProp : (I → Type α) → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
 RELProp 𝒜 ρ = Σ[ P ∈ REL I 𝒜 {ρ} ] IsRELProp 𝒜 P

 RELPropExt : (I → Type α) → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
 RELPropExt 𝒜 ρ = {P Q : RELProp 𝒜 ρ} → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

