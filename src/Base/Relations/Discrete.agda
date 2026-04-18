
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Relations.Discrete where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Data.Product                 using ( _,_ ; _×_ )
open import Function.Base                using ( _∘_ )
open import Level                        using ( _⊔_ ; Level ; Lift )
open import Relation.Binary              using ( IsEquivalence ; _⇒_ ; _=[_]⇒_ )
                                      renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Binary.Definitions  using ( Reflexive ; Transitive )
open import Relation.Unary               using ( _∈_; Pred )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Overture using (_≈_ ; Π-syntax ; Op)

private variable a b ρ 𝓥 : Level

module _ {A : Type a} where

 PointWise : {B : Type b} (_≋_ : BinRel B ρ) → BinRel (A → B) _
 PointWise {B = B} _≋_ = λ (f g : A → B) → ∀ x → f x ≋ g x

 depPointWise :  {B : A → Type b }
                 (_≋_ : {γ : Level}{C : Type γ} → BinRel C ρ)
  →              BinRel ((a : A) → B a) _
 depPointWise {B = B} _≋_ = λ (f g : (a : A) → B a) → ∀ x → f x ≋ g x

 Im_⊆_ : {B : Type b} → (A → B) → Pred B ρ → Type (a ⊔ ρ)
 Im f ⊆ S = ∀ x → f x ∈ S

 PredType : Pred A ρ → Type a
 PredType _ = A

 Level-of-Rel : {ℓ : Level} → BinRel A ℓ → Level
 Level-of-Rel {ℓ} _ = ℓ

module _ {A : Type a}{B : Type b} where

 ker : (A → B) → BinRel A b
 ker g x y = g x ≡ g y

 kerRel : {ρ : Level} → BinRel B ρ → (A → B) → BinRel A ρ
 kerRel _≈_ g x y = g x ≈ g y

 kernelRel : {ρ : Level} → BinRel B ρ → (A → B) → Pred (A × A) ρ
 kernelRel _≈_ g (x , y) = g x ≈ g y

 open IsEquivalence

 kerRelOfEquiv :  {ρ : Level}{R : BinRel B ρ}
  →               IsEquivalence R → (h : A → B) → IsEquivalence (kerRel R h)

 kerRelOfEquiv eqR h = record  { refl = refl eqR
                               ; sym = sym eqR
                               ; trans = trans eqR
                               }

 kerlift : (A → B) → (ρ : Level) → BinRel A (b ⊔ ρ)
 kerlift g ρ x y = Lift ρ (g x ≡ g y)

 ker' : (A → B) → (I : Type 𝓥) → BinRel (I → A) (b ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) b
 kernel g (x , y) = g x ≡ g y

0[_] : (A : Type a) → {ρ : Level} → BinRel A (a ⊔ ρ)
0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)

module _ {A : Type (a ⊔ ρ)} where

 _⊑_ : BinRel A ρ → BinRel A ρ → Type (a ⊔ ρ)
 P ⊑ Q = ∀ x y → P x y → Q x y

 ⊑-refl : Reflexive _⊑_
 ⊑-refl = λ _ _ z → z

 ⊑-trans : Transitive _⊑_
 ⊑-trans P⊑Q Q⊑R x y Pxy = Q⊑R x y (P⊑Q x y Pxy)

eval-rel : {A : Type a}{I : Type 𝓥} → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

eval-pred : {A : Type a}{I : Type 𝓥} → Pred (A × A) ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-pred P u v = ∀ i → (u i , v i) ∈ P

_preserves_ : {A : Type a}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

_|:_ : {A : Type a}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f |: R  = (eval-rel R) =[ f ]⇒ R

_preserves-pred_ : {A : Type a}{I : Type 𝓥} → Op A I → Pred ( A × A ) ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f preserves-pred P  = ∀ u v → (eval-pred P) u v → (f u , f v) ∈ P

_|:pred_ : {A : Type a}{I : Type 𝓥} → Op A I → Pred (A × A) ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f |:pred P  = (eval-pred P) =[ f ]⇒ λ x y → (x , y) ∈ P

module _ {A : Type a}{I : Type 𝓥}{f : Op A I}{R : BinRel A ρ} where
 compatibility-agreement : f preserves R → f |: R
 compatibility-agreement c {x}{y} Rxy = c x y Rxy
 compatibility-agreement' : f |: R → f preserves R
 compatibility-agreement' c = λ u v x → c x

