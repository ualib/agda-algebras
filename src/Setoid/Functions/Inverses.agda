
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Functions.Inverses where

open import Agda.Primitive    using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function          using ( id ; _$_ )   renaming ( Func to _⟶_ )
open import Data.Product      using ( _,_ ; Σ-syntax )
                              renaming ( proj₁ to fst ; proj₂ to snd ; _×_ to _∧_)
open import Relation.Unary    using ( Pred ; _∈_ )
open import Relation.Binary   using ( Setoid ; _Preserves_⟶_ )

open import Overture using ( ∣_∣ ; ∥_∥ ; ∃-syntax )

private variable α ρᵃ β ρᵇ : Level

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Setoid 𝑨 using()  renaming ( Carrier to A ; _≈_ to _≈₁_ )
                        renaming ( refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
 open Setoid 𝑩 using()  renaming ( Carrier to B ; _≈_ to _≈₂_ )
                        renaming ( refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

 open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (to to _⟨$⟩_ )

 data Img_∋_ (f : A → B) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → (a : A) → b ≈₂ (f a) → Img f ∋ b

 data Image_∋_ (F : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → (a : A) → b ≈₂ (F ⟨$⟩ a) → Image F ∋ b

 open Image_∋_

 IsInRange : (𝑨 ⟶ 𝑩) → Pred B (α ⊔ ρᵇ)
 IsInRange F b = ∃[ a ∈ A ] (F ⟨$⟩ a) ≈₂ b

 Image⊆Range : ∀ {F b} → Image F ∋ b → b ∈ IsInRange F
 Image⊆Range (eq a x) = a , (sym₂ x)

 IsInRange→IsInImage : ∀ {F b} → b ∈ IsInRange F → Image F ∋ b
 IsInRange→IsInImage (a , x) = eq a (sym₂ x)

 Imagef∋f : ∀ {F a} → Image F ∋ (F ⟨$⟩ a)
 Imagef∋f = eq _ refl₂

 _range : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵇ)
 F range = Σ[ b ∈ B ] ∃[ a ∈ A ](F ⟨$⟩ a) ≈₂ b

 _image : (F : 𝑨 ⟶ 𝑩) → F range → B
 (F image) (b , (_ , _)) = b

 _preimage : (F : 𝑨 ⟶ 𝑩) → F range → A
 (F preimage) (_ , (a , _)) = a

 f∈range : ∀ {F} → A → F range
 f∈range {F} a = (F ⟨$⟩ a) , (a , refl₂)

 ⌜_⌝ : (F : 𝑨 ⟶ 𝑩) → A → F range
 ⌜ F ⌝ a = f∈range{F} a

 Ran : (𝑨 ⟶ 𝑩) → Setoid (α ⊔ β ⊔ ρᵇ) ρᵇ
 Ran F = record  { Carrier = F range
                 ; _≈_ = λ x y → ((F image) x) ≈₂ ((F image) y)
                 ; isEquivalence = record  { refl = refl₂
                                           ; sym = sym₂
                                           ; trans = trans₂
                                           }
                 }

 RRan : (𝑨 ⟶ 𝑩) → Setoid (α ⊔ β ⊔ ρᵇ) (ρᵃ ⊔ ρᵇ)
 RRan F = record  { Carrier = F range
                  ; _≈_ = λ x y →  (F preimage) x ≈₁ (F preimage) y
                                   ∧ (F image) x ≈₂ (F image) y

                  ; isEquivalence =
                     record  { refl = refl₁ , refl₂
                             ; sym = λ x → sym₁ ∣ x ∣ , sym₂ ∥ x ∥
                             ; trans = λ x y → trans₁ ∣ x ∣ ∣ y ∣ , trans₂ ∥ x ∥ ∥ y ∥
                             }
                  }

 _preimage≈image : ∀ F r → F ⟨$⟩ (F preimage) r ≈₂ (F image) r
 (F preimage≈image) (_ , (_ , p)) = p

 Dom : (𝑨 ⟶ 𝑩) → Setoid α ρᵇ
 Dom F = record  { Carrier = A
                 ; _≈_ = λ x y → F ⟨$⟩ x ≈₂ F ⟨$⟩ y
                 ; isEquivalence = record  { refl = refl₂
                                           ; sym = sym₂
                                           ; trans = trans₂
                                           }
                 }

 inv : (f : A → B){b : B} → Img f ∋ b → A
 inv _ (eq a _) = a

 Inv : (F : 𝑨 ⟶ 𝑩){b : B} → Image F ∋ b → A
 Inv _ (eq a _) = a

 Inv' : (F : 𝑨 ⟶ 𝑩){b : B} → b ∈ IsInRange F → A
 Inv' _ (a , _) = a

 [_]⁻¹ : (F : 𝑨 ⟶ 𝑩) → F range → A
 [ F ]⁻¹ = F preimage

 ⟦_⟧⁻¹ : (F : 𝑨 ⟶ 𝑩) → Ran F ⟶ Dom F
 ⟦ F ⟧⁻¹ = record
   { to = F preimage
   ; cong = λ {x}{y} ix≈iy → trans₂  ((F preimage≈image) x)
                                     (trans₂ ix≈iy $ sym₂ $ (F preimage≈image) y)
   }

 invIsInvʳ : {f : A → B}{b : B}(q : Img f ∋ b) → (f (inv f q)) ≈₂ b
 invIsInvʳ (eq _ p) = sym₂ p

 InvIsInverseʳ : {F : 𝑨 ⟶ 𝑩}{b : B}(q : Image F ∋ b) → (F ⟨$⟩ (Inv F q)) ≈₂ b
 InvIsInverseʳ (eq _ p) = sym₂ p

 ⁻¹IsInverseʳ : {F : 𝑨 ⟶ 𝑩}{bap : F range} → (F ⟨$⟩ ([ F ]⁻¹ bap )) ≈₂ ∣ bap ∣
 ⁻¹IsInverseʳ {bap = (_ , (_ , p))} = p

 InvIsInverseˡ : ∀ {F a} → Inv F {b = F ⟨$⟩ a} Imagef∋f ≈₁ a
 InvIsInverseˡ = refl₁

 ⁻¹IsInverseˡ : ∀ {F a} → [ F ]⁻¹ (f∈range{F} a) ≈₁ a
 ⁻¹IsInverseˡ = refl₁

