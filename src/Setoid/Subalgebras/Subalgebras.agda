
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
                             renaming ( _×_ to _∧_ ; proj₂ to snd )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( REL )
open import Relation.Unary   using ( Pred ; _∈_ )

open import Overture          using ( ∣_∣ ; ∥_∥ )
open import Setoid.Functions  using ( IsInjective )

open import Setoid.Algebras       {𝑆 = 𝑆} using ( Algebra ; ov )
open import Setoid.Homomorphisms  {𝑆 = 𝑆} using
 ( hom ; mon ; mon→intohom ; kerquo ; FirstHomTheorem )

private variable α ρᵃ β ρᵇ ℓ : Level

_≥_  -- (alias for supalgebra (aka overalgebra))
 _IsSupalgebraOf_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

_≤_  -- (alias for subalgebra relation))
 _IsSubalgebraOf_ : Algebra α ρᵃ → Algebra β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩
𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)) where
 field
  algebra : Algebra α ρᵃ
  subalgebra : Algebra β ρᵇ
  issubalgebra : subalgebra ≤ algebra

Subalgebra : Algebra α ρᵃ → {β ρᵇ : Level} → Type _
Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (Algebra β ρᵇ) ] 𝑩 ≤ 𝑨

{- usage note: for 𝑨 : Algebra α ρᵃ, inhabitant of `Subalgebra 𝑨` is a pair
               `(𝑩 , p) : Subalgebra 𝑨`  providing
                                         - `𝑩 : Algebra β ρᵇ` and
                                         - `p : 𝑩 ≤ 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴. -}

IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (Algebra α ρᵃ)(Algebra β ρᵇ) ℓ → Type _
IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → 𝑨 ≤ 𝑩

record SubalgebraREL(R : REL (Algebra β ρᵇ)(Algebra α ρᵃ) ℓ) : Type (ov (α ⊔ β ⊔ ρᵇ ⊔ ℓ))
 where
 field isSubalgebraREL : IsSubalgebraREL R

_≤c_
 _IsSubalgebraOfClass_ : Algebra β ρᵇ → Pred (Algebra α ρᵃ) ℓ → Type _
𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 ≤ 𝑨))

𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦  -- (alias)

record SubalgebraOfClass : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
 field
  class : Pred (Algebra α ρᵃ) ℓ
  subalgebra : Algebra β ρᵇ
  issubalgebraofclass : subalgebra ≤c class

record SubalgebraOfClass' : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
 field
  class : Pred (Algebra α ρᵃ) ℓ
  classalgebra : Algebra α ρᵃ
  isclassalgebra : classalgebra ∈ class
  subalgebra : Algebra β ρᵇ
  issubalgebra : subalgebra ≤ classalgebra

SubalgebrasOfClass : Pred (Algebra α ρᵃ) ℓ → {β ρᵇ : Level} → Type _
SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 ≤c 𝒦

FirstHomCorollary :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}
                     (hh : hom 𝑨 𝑩) → (kerquo hh) IsSubalgebraOf 𝑩

FirstHomCorollary hh = ∣ FirstHomTheorem hh ∣ , snd ∥ FirstHomTheorem hh ∥

