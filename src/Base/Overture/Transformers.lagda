---
layout: default
title : "Base.Overture.Transformers module"
date : "2021-07-26"
author: "the agda-algebras development team"
---

### <a id="type-transformers">Type Transformers</a>

This is the [Base.Overture.Transformers][] module of the [agda-algebras][] library.  Here we define functions for tanslating from one type to another.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Overture.Transformers where

-- Imports from Agda and the Agda Standard Library ---------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product   using ( _,_ ; _×_ )
open import Data.Fin.Base  using ( Fin )
open import Function.Base  using ( _∘_ ; id )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; refl ; module ≡-Reasoning )

-- Imports from agda-algebras ------------------------------------------------------
open import Base.Overture.Preliminaries using ( _≈_ )

private variable
 α β : Level
\end{code}


#### <a id="bijections-of-nondependent-function-types">Bijections of nondependent function types</a>

In set theory, these would simply be bijections between sets, or "set isomorphisms."
\begin{code}

record Bijection (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≡ id
  from-to : from ∘ to ≡ id

∣_∣=∣_∣ : (A : Type α)(B : Type β) → Type (α ⊔ β)
∣ A ∣=∣ B ∣ = Bijection A B

record PointwiseBijection (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≈ id
  from-to : from ∘ to ≈ id

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

#### <a id="non-bijective-transformations">Non-bijective transformations</a>

\begin{code}

module _ {A : Type α} where

 open Fin renaming (zero to z ; suc to s)

 A×A→Fin2A : A × A → Fin 2 → A
 A×A→Fin2A (x , y) z = x
 A×A→Fin2A (x , y) (s z) = y

 Fin2A→A×A : (Fin 2 → A) → A × A
 Fin2A→A×A u = u z , u (s z)

 Fin2A~A×A : {A : Type α} → Fin2A→A×A ∘ A×A→Fin2A ≡ id
 Fin2A~A×A = refl

 A×A~Fin2A-ptws : ∀ u → (A×A→Fin2A (Fin2A→A×A u)) ≈ u
 A×A~Fin2A-ptws u z = refl
 A×A~Fin2A-ptws u (s z) = refl

 A→A→Fin2A : A → A → Fin 2 → A
 A→A→Fin2A x y z = x
 A→A→Fin2A x y (s _) = y

 A→A→Fin2A' : A → A → Fin 2 → A
 A→A→Fin2A' x y = u
  where
  u : Fin 2 → A
  u z = x
  u (s z) = y

 A→A→Fin2A-ptws-agree : (x y : A) → ∀ i → (A→A→Fin2A x y) i ≡ (A→A→Fin2A' x y) i
 A→A→Fin2A-ptws-agree x y z = refl
 A→A→Fin2A-ptws-agree x y (s z) = refl

 A→A~Fin2A-ptws : (v : Fin 2 → A) → ∀ i → A→A→Fin2A (v z) (v (s z)) i ≡ v i
 A→A~Fin2A-ptws v z = refl
 A→A~Fin2A-ptws v (s z) = refl

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

 open Fin renaming (zero to z ; suc to s)

 lemma : (u : Fin 2 → A) → u ≈ (λ {z → u z ; (s z) → u (s z)})
 lemma u z = refl
 lemma u (s z) = refl

 CurryFin2 : ((Fin 2 → A) → B) → A → A → B
 CurryFin2 f x y = f (A→A→Fin2A x y)

 UncurryFin2 : (A → A → B) → ((Fin 2 → A) → B)
 UncurryFin2 f u = f (u z) (u (s z))

 CurryFin2~UncurryFin2 : CurryFin2 ∘ UncurryFin2 ≡ id
 CurryFin2~UncurryFin2 = refl

 open ≡-Reasoning

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

<span style="float:left;">[← Base.Overture.Inverses](Base.Overture.Inverses.html)</span>
<span style="float:right;">[Base.Relations →](Base.Relations.html)</span>

{% include UALib.Links.md %}

