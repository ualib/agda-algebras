
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Algebras.Products {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax )
open import Function          using ( flip ; Func )
open import Level             using( _⊔_ ; Level )
open import Relation.Binary   using ( Setoid ;  IsEquivalence ; Decidable )
open import Relation.Binary.PropositionalEquality  using ( refl ; _≡_ )
open import Relation.Unary                         using ( Pred ; _⊆_ ; _∈_ )

open Func           using ( cong )           renaming ( to to _⟨$⟩_ )
open Setoid         using ( Carrier ; _≈_ )  renaming ( isEquivalence to isEqv )
open IsEquivalence  using ()                 renaming ( refl to reflE ; sym to symE ; trans to transE )

open import Overture        using ( ∣_∣; ∥_∥ )
open import Base.Functions  using ( proj ; projIsOnto ) renaming ( IsSurjective to onto )

open import Setoid.Algebras.Basic {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; ov ; 𝕌[_])

private variable α ρ ι : Level

open Algebra

⨅ : {I : Type ι }(𝒜 : I → Algebra α ρ) → Algebra (α ⊔ ι) (ρ ⊔ ι)

Domain (⨅ {I} 𝒜) =
 record  { Carrier = ∀ i → Carrier (Domain (𝒜 i))
         ; _≈_ = λ a b → ∀ i → Domain (𝒜 i) ._≈_ (a i) (b i)
         ; isEquivalence =
            record  { refl   = λ i      → reflE   (isEqv (Domain (𝒜 i)))
                    ; sym    = λ x i    → symE    (isEqv (Domain (𝒜 i)))(x i)
                    ; trans  = λ x y i  → transE  (isEqv (Domain (𝒜 i)))(x i)(y i)
                    }
         }

(Interp (⨅ {I} 𝒜)) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
cong (Interp (⨅ {I} 𝒜)) (refl , f=g ) = λ i → cong  (Interp (𝒜 i)) (refl , flip f=g i )

module _ {𝒦 : Pred (Algebra α ρ) (ov α)} where

 ℑ : Type (ov(α ⊔ ρ))
 ℑ = Σ[ 𝑨 ∈ (Algebra α ρ) ] 𝑨 ∈ 𝒦

 𝔄 : ℑ → Algebra α ρ
 𝔄 i = ∣ i ∣

 class-product : Algebra (ov (α ⊔ ρ)) _
 class-product = ⨅ 𝔄

module _  {I : Type ι}                  -- index type
          {_≟_ : Decidable{A = I} _≡_}  -- with decidable equality
          {𝒜 : I → Algebra α ρ}         -- indexed collection of algebras
          {𝒜I : ∀ i → 𝕌[ 𝒜 i ] }        -- each of which is nonempty
          where

 ProjAlgIsOnto : ∀{i} → Σ[ h ∈ (𝕌[ ⨅ 𝒜 ] → 𝕌[ 𝒜 i ]) ] onto h
 ProjAlgIsOnto {i} = (proj _≟_ 𝒜I i) , projIsOnto _≟_ 𝒜I

