
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive         using () renaming ( Set to Type )
open import Data.Empty.Polymorphic using ( ⊥ )
open import Data.Product           using ( _,_ )
open import Data.Sum               using ( _⊎_ )
                                   renaming ( inj₁ to inl ; inj₂ to inr )
open import Function               using ( Func )
open import Level                  using ( Level ; Lift ; _⊔_ )
open import Relation.Binary        using ( Setoid ; IsEquivalence )
                                   using ( Reflexive ; Symmetric ; Transitive )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

open import Overture using ( ∥_∥ )
open import Setoid.Algebras  {𝑆 = 𝑆}  using ( Algebra ; ov ; _̂_)
open import Base.Terms       {𝑆 = 𝑆}  using ( Term )

open Func renaming ( to to _⟨$⟩_ )
open Term

private variable
 χ α ℓ : Level
 X Y : Type χ

module _ {X : Type χ } where

 data _≐_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≐ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≐ (t i)) → (node f s) ≐ (node f t)

 open Level
 ≐-isRefl : Reflexive _≐_
 ≐-isRefl {ℊ _} = rfl ≡.refl
 ≐-isRefl {node _ _} = gnl (λ _ → ≐-isRefl)

 ≐-isSym : Symmetric _≐_
 ≐-isSym (rfl x) = rfl (≡.sym x)
 ≐-isSym (gnl x) = gnl (λ i → ≐-isSym (x i))

 ≐-isTrans : Transitive _≐_
 ≐-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≐-isTrans (gnl x) (gnl y) = gnl (λ i → ≐-isTrans (x i) (y i))

 ≐-isEquiv : IsEquivalence _≐_
 ≐-isEquiv = record { refl = ≐-isRefl ; sym = ≐-isSym ; trans = ≐-isTrans }

TermSetoid : (X : Type χ) → Setoid (ov χ) (ov χ)
TermSetoid X = record { Carrier = Term X ; _≈_ = _≐_ ; isEquivalence = ≐-isEquiv }

open Algebra

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Domain (𝑻 X) = TermSetoid X
Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Interp (𝑻 X)) (≡.refl , ss≐ts) = gnl ss≐ts

Sub : Type χ → Type χ → Type (ov χ)
Sub X Y = (y : Y) → Term X

_[_] : (t : Term Y) (σ : Sub X Y) → Term X
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])

module Environment (𝑨 : Algebra α ℓ) where
 open Algebra 𝑨  renaming( Domain to A ; Interp  to InterpA )  using()
 open Setoid A   renaming( _≈_ to _≈ₐ_ ; Carrier to ∣A∣ )      using( refl ; sym ; trans )

 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → ∣A∣
                 ; _≈_ = λ ρ ρ' → (x : X) → ρ x ≈ₐ ρ' x
                 ; isEquivalence = record  { refl = λ _ → refl
                                           ; sym = λ h x → sym (h x)
                                           ; trans = λ g h x → trans (g x) (h x)
                                           }
                 }

 open Algebra using ( Domain ; Interp )

 EnvAlgebra : Type χ → Algebra (α ⊔ χ) (ℓ ⊔ χ)
 Domain (EnvAlgebra X) = Env X
 (Interp (EnvAlgebra X) ⟨$⟩ (f , aϕ)) x = (f ̂ 𝑨) (λ i → aϕ i x)
 cong (Interp (EnvAlgebra X)) {f , a} {.f , b} (≡.refl , aibi) x = cong InterpA (≡.refl , (λ i → aibi i x))

 ⟦_⟧ : {X : Type χ}(t : Term X) → Func (Env X) A
 ⟦ ℊ x ⟧ ⟨$⟩ ρ = ρ x
 ⟦ node f args ⟧ ⟨$⟩ ρ = InterpA ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v = u≈v x
 cong ⟦ node f args ⟧ x≈y = cong InterpA (≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

 open Setoid using () renaming ( Carrier to ∣_∣ )

 Equal : ∀ {X : Type χ} (s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : ∣ Env X ∣) →  ⟦ s ⟧ ⟨$⟩ ρ ≈ₐ ⟦ t ⟧ ⟨$⟩ ρ

 ≐→Equal : {X : Type χ}(s t : Term X) → s ≐ t → Equal s t
 ≐→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≐→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong InterpA (≡.refl , λ i → ≐→Equal(s i)(t i)(x i)ρ )

 isEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 IsEquivalence.refl   isEquiv = λ _ → refl
 IsEquivalence.sym    isEquiv = λ x=y ρ → sym (x=y ρ)
 IsEquivalence.trans  isEquiv = λ ij jk ρ → trans (ij ρ) (jk ρ)

 ⟦_⟧s : {X Y : Type χ} → Sub X Y → ∣ Env X ∣ → ∣ Env Y ∣
 ⟦ σ ⟧s ρ x = ⟦ σ x ⟧ ⟨$⟩ ρ

 substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : ∣ Env X ∣ )
  →              ⟦ t [ σ ] ⟧ ⟨$⟩ ρ  ≈ₐ  ⟦ t ⟧ ⟨$⟩ (⟦ σ ⟧s ρ)

 substitution (ℊ x) σ ρ = refl
 substitution (node f ts) σ ρ = cong InterpA (≡.refl , λ i → substitution (ts i) σ ρ)

