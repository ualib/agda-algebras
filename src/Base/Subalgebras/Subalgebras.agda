
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature )

module Base.Subalgebras.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₂ to snd )
open import Level           using ( Level ; _⊔_ )
open import Relation.Unary  using ( Pred ; _∈_ )

open  import Overture       using ( ∣_∣ ; ∥_∥ )
open  import Base.Functions using ( IsInjective )
open  import Base.Equality  using ( swelldef ; is-set ; blk-uip ; pred-ext )

open  import Base.Algebras       {𝑆 = 𝑆} using ( Algebra ; ov )
open  import Base.Terms          {𝑆 = 𝑆} using ( 𝑻 ; Term )
open  import Base.Homomorphisms  {𝑆 = 𝑆} using ( hom ; kercon ; ker[_⇒_]_↾_ )
                                         using ( FirstHomTheorem|Set ; _≅_ )

private variable α β γ 𝓧 : Level

_≤_  -- (alias for subalgebra relation))
 _IsSubalgebraOf_ : Algebra α → Algebra β → Type _
𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

_≥_  -- (alias for supalgebra (aka overalgebra))
 _IsSupalgebraOf_ : Algebra α → Algebra β → Type _
𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩
𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩

record SubalgebraOf : Type (ov (α ⊔ β)) where
 field
  algebra : Algebra α
  subalgebra : Algebra β
  issubalgebra : subalgebra ≤ algebra

Subalgebra : Algebra α → {β : Level} → Type _
Subalgebra  𝑨 {β} = Σ[ 𝑩 ∈ (Algebra β) ] 𝑩 ≤ 𝑨

module _  (𝑨 : Algebra α)(𝑩 : Algebra β)(h : hom 𝑨 𝑩)
          (pe : pred-ext α β)(fe : swelldef 𝓥 β)

          (Bset : is-set ∣ 𝑩 ∣)
          (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)
          where

 FirstHomCorollary|Set : (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
 FirstHomCorollary|Set = ϕhom , ϕinj
  where
   hh = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip
   ϕhom : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩
   ϕhom = ∣ hh ∣

   ϕinj : IsInjective ∣ ϕhom ∣
   ϕinj = ∣ snd ∥ hh ∥ ∣

module _  (X : Type 𝓧)(𝑩 : Algebra β)(h : hom (𝑻 X) 𝑩)
          (pe : pred-ext (ov 𝓧) β)(fe : swelldef 𝓥 β)

          (Bset : is-set ∣ 𝑩 ∣)
          (buip : blk-uip (Term X) ∣ kercon fe {𝑩} h ∣)
          where

 free-quot-subalg : (ker[ 𝑻 X ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
 free-quot-subalg = FirstHomCorollary|Set{α = ov 𝓧}(𝑻 X) 𝑩 h pe fe Bset buip

module _ {α β : Level} where

 _IsSubalgebraOfClass_ : Algebra β → Pred (Algebra α) γ → Type _
 𝑩 IsSubalgebraOfClass 𝒦 =  Σ[ 𝑨 ∈ Algebra α ]
                            Σ[ sa ∈ Subalgebra 𝑨 {β} ] ((𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ sa ∣))

 SubalgebraOfClass : Pred (Algebra α)(ov α) → Type (ov (α ⊔ β))
 SubalgebraOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra β ] 𝑩 IsSubalgebraOfClass 𝒦

