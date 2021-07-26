---
layout: default
title : Overture.Transformers module
date : 2021-07-26
author: [agda-algebras development team][]
---

### Type Transformers

This is the [Overture.Transformers][] module of the [agda-algebras][] library.  Here we define functions for tanslating from one type to another.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module Overture.Transformers where

-- Imports from Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality       using ( _≡_ ; refl )
open import Agda.Primitive              using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product                using ( _,_ ; _×_ )
open import Data.Fin.Base               using ( Fin )
open import Function.Base               using ( _∘_ ; id )

-- Imports from agda-algebras
open import Overture.Preliminaries using ( _≈_ )

private variable
 α β : Level

\end{code}

#### Bijections of nondependent function types

In set theory, these would simply be bijections between sets, or "set isomorphisms."

\begin{code}

record Bijection (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≡ id
  from-to : from ∘ to ≡ id

-- Notation.
∣_∣=∣_∣ : (A : Type α)(B : Type β) → Type (α ⊔ β)
∣ A ∣=∣ B ∣ = Bijection A B


record PointwiseBijection (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≈ id
  from-to : from ∘ to ≈ id

-- Notation.
∣_∣≈∣_∣ : (A : Type α)(B : Type β) → Type (α ⊔ β)
∣ A ∣≈∣ B ∣ = PointwiseBijection A B


uncurry₀ : {A : Type α} → A → A → (A × A)
uncurry₀ x y = x , y

module _ {A : Type α} {B : Type β} where

 Curry : ((A × A) → B) → A → A → B
 Curry f x y = f (uncurry₀ x y)

 Uncurry : (A → A → B) → A × A → B
 Uncurry f (x , y) = f x y


 A×A→B≅A→A→B : ∣ (A × A → B) ∣=∣ (A → A → B) ∣
 A×A→B≅A→A→B = record { to = Curry
                      ; from = Uncurry
                      ; to-from = refl
                      ; from-to = refl }

\end{code}

#### Non-bijective transformations

\begin{code}

open Fin renaming (zero to z ; suc to s)

module _ {A : Type α} where

 A→A→Fin2A : A → A → Fin 2 → A
 A→A→Fin2A x y z = x
 A→A→Fin2A x y (s _) = y

 A→A→Fin2A' : A → A → Fin 2 → A
 A→A→Fin2A' x y = u
  where
  u : Fin 2 → A
  u z = x
  u (s z) = y

 A→A→Fin2A-pointwise-agreement : (x y : A) → ∀ i → (A→A→Fin2A x y) i ≡ (A→A→Fin2A' x y) i
 A→A→Fin2A-pointwise-agreement x y z = refl
 A→A→Fin2A-pointwise-agreement x y (s z) = refl

 A×A→Fin2A : A × A → Fin 2 → A
 A×A→Fin2A (x , y) z = x
 A×A→Fin2A (x , y) (s z) = y

 Fin2A→A×A : (Fin 2 → A) → A × A
 Fin2A→A×A u = u z , u (s z)

 Fin2A~A×A : {A : Type α} → Fin2A→A×A ∘ A×A→Fin2A ≡ id
 Fin2A~A×A = refl

 A×A~Fin2A-pointwise : ∀ u → (A×A→Fin2A (Fin2A→A×A u)) ≈ u
 A×A~Fin2A-pointwise u z = refl
 A×A~Fin2A-pointwise u (s z) = refl

 A→A~Fin2A-pointwise : (v : Fin 2 → A) → ∀ i → A→A→Fin2A (v z) (v (s z)) i ≡ v i
 A→A~Fin2A-pointwise v z = refl
 A→A~Fin2A-pointwise v (s z) = refl

 Fin2A : (Fin 2 → A) → Fin 2 → A
 Fin2A u z = u z
 Fin2A u (s z) = u (s z)
 Fin2A u (s (s ()))

 Fin2A≡ : (u : Fin 2 → A) → ∀ i → (Fin2A u) i ≡ u i
 Fin2A≡ u z = refl
 Fin2A≡ u (s z) = refl

\end{code}

Somehow we cannot establish a bijection between the two seemingly isomorphic
function types, `(Fin 2 → A) → B` and `A × A → B`, nor between the types
`(Fin 2 → A) → B` and `A → A → B`.

\begin{code}

module _ {A : Type α} {B : Type β} where

 CurryFin2 : ((Fin 2 → A) → B) → A → A → B
 CurryFin2 f x y = f (A→A→Fin2A x y)

 UncurryFin2 : (A → A → B) → ((Fin 2 → A) → B)
 UncurryFin2 f u = f (u z) (u (s z))

 CurryFin2~UncurryFin2 : CurryFin2 ∘ UncurryFin2 ≡ id
 CurryFin2~UncurryFin2 = refl

 CurryFin3 : {A : Type α} → ((Fin 3 → A) → B) → A → A → A → B
 CurryFin3 {A = A} f x₁ x₂ x₃ = f u
  where
  u : Fin 3 → A
  u z = x₁
  u (s z) = x₂
  u (s (s z)) = x₃

 UncurryFin3 : (A → A → A → B) → ((Fin 3 → A) → B)
 UncurryFin3 f u = f (u z) (u (s z)) (u (s (s z)))

 Fin2A→B-to-A×A→B : ((Fin 2 → A) → B) → A × A → B
 Fin2A→B-to-A×A→B f = f ∘ A×A→Fin2A

 A×A→B-to-Fin2A→B : (A × A → B) → ((Fin 2 → A) → B)
 A×A→B-to-Fin2A→B f = f ∘ Fin2A→A×A

 Fin2A→B~A×A→B : Fin2A→B-to-A×A→B ∘ A×A→B-to-Fin2A→B ≡ id
 Fin2A→B~A×A→B = refl

\end{code}



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


















-- open PE.≡-Reasoning
 -- Fin2A→B≅A×A→B : ∣ ((Fin 2 → A) → B) ∣≈∣ (A × A → B) ∣
 -- Fin2A→B≅A×A→B = record { to = Fin2A→B-to-A×A→B
 --                      ; from = A×A→B-to-Fin2A→B
 --                      ; to-from = λ _ → refl
 --                      ; from-to = ? }
 -- Problem: Fin2A→B-to-A×A→B might not be injective...?




 -- f-of-A×A~Fin2A : (f : (Fin 2 → A) → A)(u : Fin 2 → A) → f (A×A→Fin2A (Fin2A→A×A u)) ≡ f u
 -- f-of-A×A~Fin2A f u = Goal
 --  where
 --  ξ : (A×A→Fin2A (Fin2A→A×A u)) z ≡ u z
 --  ξ = refl
 --  ζ : (A×A→Fin2A (Fin2A→A×A u)) (s z) ≡ u (s z)
 --  ζ = refl

 --  part1 : ∀ {a x y} → x ≡ y → f (A×A→Fin2A (a , x)) ≡ f (A×A→Fin2A (a , y))
 --  part1 refl = refl

 --  part2 : ∀ {x y b} → x ≡ y → f (A×A→Fin2A (x , b)) ≡ f (A×A→Fin2A (y , b))
 --  part2 refl = refl

 --  Goal : f (A×A→Fin2A (Fin2A→A×A u)) ≡ f u
 --  Goal = f (A×A→Fin2A (Fin2A→A×A u)) ≡⟨ refl ⟩
 --         f (A×A→Fin2A ((u z), (u (s z)))) ≡⟨ {!!} ⟩
 --         (Fin2A→B-to-A×A→B f) ((u z) ,  (u (s z))) ≡⟨ {!refl!} ⟩
 --         f u ∎

