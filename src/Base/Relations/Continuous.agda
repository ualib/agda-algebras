
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations.Continuous where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( _⊔_ ; suc ; Level  )

open import Overture        using ( Π ; Π-syntax ; Op ; arity[_] )

private variable a ρ : Level

module _ {𝓥 : Level} where
 ar : Type (suc 𝓥)
 ar = Type 𝓥

 Rel : Type a → ar → {ρ : Level} → Type (a ⊔ 𝓥 ⊔ suc ρ)
 Rel A I {ρ} = (I → A) → Type ρ

 Rel-syntax : Type a → ar → (ρ : Level) → Type (𝓥 ⊔ a ⊔ suc ρ)
 Rel-syntax A I ρ = Rel A I {ρ}

 syntax Rel-syntax A I ρ = Rel[ A ^ I ] ρ
 infix 6 Rel-syntax

 REL : (I : ar) → (I → Type a) → {ρ : Level} → Type (𝓥 ⊔ a ⊔ suc ρ)
 REL I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

 REL-syntax : (I : ar) → (I → Type a) → {ρ : Level} → Type (𝓥 ⊔ a ⊔ suc ρ)
 REL-syntax I 𝒜 {ρ} = REL I 𝒜 {ρ}

 syntax REL-syntax I (λ i → 𝒜) = REL[ i ∈ I ] 𝒜
 infix 6 REL-syntax

 eval-Rel : {I : ar}{A : Type a} → Rel A I{ρ} → (J : ar) → (I → J → A) → Type (𝓥 ⊔ ρ)
 eval-Rel R J t = ∀ (j : J) → R λ i → t i j

 compatible-Rel : {I J : ar}{A : Type a} → Op(A) J → Rel A I{ρ} → Type (𝓥 ⊔ a ⊔ ρ)
 compatible-Rel f R  = ∀ t → eval-Rel R arity[ f ] t → R λ i → f (t i)

 eval-REL :  {I J : ar}{𝒜 : I → Type a}
  →          REL I 𝒜 {ρ}          -- the relation type: subsets of Π[ i ∈ I ] 𝒜 i
  →          ((i : I) → J → 𝒜 i)  -- an I-tuple of (𝒥 i)-tuples
  →          Type (𝓥 ⊔ ρ)

 eval-REL{I = I}{J}{𝒜} R t = ∀ j → R λ i → (t i) j

 compatible-REL :  {I J : ar}{𝒜 : I → Type a}
  →                (∀ i → Op (𝒜 i) J)  -- for each i : I, an operation of type  Op(𝒜 i){J} = (J → 𝒜 i) → 𝒜 i
  →                REL I 𝒜 {ρ}         -- a subset of Π[ i ∈ I ] 𝒜 i
  →                Type (𝓥 ⊔ a ⊔ ρ)
 compatible-REL {I = I}{J}{𝒜} 𝑓 R  = Π[ t ∈ ((i : I) → J → 𝒜 i) ] eval-REL R t

