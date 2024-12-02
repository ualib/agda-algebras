
{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Setoid.Functions.Injective where

open import Agda.Primitive    using ( _⊔_ ; Level )  renaming ( Set to Type )
open import Function.Bundles  using ( Injection )    renaming ( Func to _⟶_ )
open import Function.Base     using ( _∘_ ; id )
open import Relation.Binary   using ( _Preserves_⟶_ )
open import Relation.Binary   using ( Rel )

import Function.Definitions as FD

open import Setoid.Functions.Basic     using ( 𝑖𝑑 ) renaming ( _⊙_ to _⟨⊙⟩_ )
open import Setoid.Functions.Inverses  using ( Image_∋_ ; Inv )

private variable a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

module _ {𝑨 : Setoid a α}{𝑩 : Setoid b β} where

 open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩  using ( trans ; sym )  renaming (Carrier to B; _≈_ to _≈₂_)

 open Injection {From = 𝑨}{To = 𝑩} using ( function ; injective )  renaming (to to _⟨$⟩_)
 open _⟶_ {a = a}{α}{b}{β}{From = 𝑨}{To = 𝑩}                     renaming (to to _⟨$⟩_ )
 open FD

 IsInjective : 𝑨 ⟶ 𝑩  →  Type (a ⊔ α ⊔ β)
 IsInjective f = Injective _≈₁_ _≈₂_ (_⟨$⟩_ f)

 open Image_∋_

 LeftInvPreserves≈ :  (F : Injection 𝑨 𝑩)
                      {b₀ b₁ : B}(u : Image (function F) ∋ b₀)(v : Image (function F) ∋ b₁)
  →                   b₀ ≈₂ b₁ → Inv (function F) u ≈₁ Inv (function F) v

 LeftInvPreserves≈ F (eq a₀ x₀) (eq a₁ x₁) bb = Goal
  where
  fa₀≈fa₁ : (F ⟨$⟩ a₀) ≈₂ (F ⟨$⟩ a₁)
  fa₀≈fa₁ = trans (sym x₀) (trans bb x₁)
  Goal : a₀ ≈₁ a₁
  Goal = injective F fa₀≈fa₁

module compose  {A : Type a}(_≈₁_ : Rel A α)
                {B : Type b}(_≈₂_ : Rel B β)
                {C : Type c}(_≈₃_ : Rel C γ) where
 open FD

 ∘-injective-bare :  {f : A → B}{g : B → C}
  →                  Injective _≈₁_ _≈₂_ f → Injective _≈₂_ _≈₃_ g
  →                  Injective _≈₁_ _≈₃_ (g ∘ f)

 ∘-injective-bare finj ginj = finj ∘ ginj

module _ {𝑨 : Setoid a α}{𝑩 : Setoid b β}{𝑪 : Setoid c γ} where

 ⊙-injective :  (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪)
  →             IsInjective f → IsInjective g
  →             IsInjective (g ⟨⊙⟩ f)

 ⊙-injective _ _ finj ginj = finj ∘ ginj

 ⊙-injection : Injection 𝑨 𝑩 → Injection 𝑩 𝑪 → Injection 𝑨 𝑪
 ⊙-injection fi gi = record
  { to = to gi ∘ to fi
  ; cong = cong gi ∘ cong fi
  ; injective = ⊙-injective (function fi) (function gi) (injective fi) (injective gi)
  }
  where open Injection

id-is-injective : {𝑨 : Setoid a α} → IsInjective{𝑨 = 𝑨}{𝑨} 𝑖𝑑
id-is-injective = id

