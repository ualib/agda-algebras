open import Preliminaries using (Level; ∃; _,_; ∣_∣; _≡_; refl; _∘_; Pred)
open import Basic

module Hom where

private
  variable
    i j k : Level
    S : Signature i j

-- The category of algebras Alg with morphisms as Homs
Hom : Algebra k S → Algebra k S → Set _
Hom {S = F , ρ} (a , A) (b , B) =
  ∃ λ (f : a → b) → (o : F) (x : ρ o → a) → f (A o x) ≡ B o (f ∘ x)

id : (A : Algebra k S) → Hom A A
id (a , A) = (λ x → x) , λ _ _ → refl

private
  variable
    A B : Algebra k S

_>>>_ : {C : Algebra k S} → Hom A B → Hom B C → Hom A C
_>>>_ {S = F , ρ} {A = a , A} {C = c , C} (f , α) (g , β) = g ∘ f , γ where
  γ : (o : F) (x : ρ o → a) → (g ∘ f) (A o x) ≡ C o (g ∘ f ∘ x)
  γ o x rewrite α o x = β o (f ∘ x)

-- Equalizers in Alg
_~_ : Hom A B → Hom A B → Pred ∣ A ∣ _
_~_ (f , _) (g , _) x = f x ≡ g x
