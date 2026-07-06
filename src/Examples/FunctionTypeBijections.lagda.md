---
layout: default
title : "Examples.FunctionTypeBijections module"
date : "2026-05-10"
author: "the agda-algebras development team"
---

### N-ary function encodings

This is the [Examples.FunctionTypeBijections][] module of the [Agda Universal Algebra Library][].

This module is illustrative rather than load-bearing.  It investigates three competing encodings of n-ary functions on a type — the curried form `A → A → B`, the product form `A × A → B`, and the `Fin`-indexed form `(Fin n → A) → B` — and surfaces a subtle phenomenon: while `A × A → B` and `A → A → B` are bijective up to definitional equality (`Curry` and `Uncurry` are mutually inverse on the nose), the `Fin`-indexed encoding does not enjoy a definitional bijection with either of the other two.  The obstruction is η-expansion failure for function types out of `Fin n`: the equation `(λ {z → u z; (s z) → u (s z)}) ≈ u` holds only pointwise, not definitionally.

This phenomenon is directly relevant to the universal-algebra core, where n-ary operations are encoded as `(Fin n → A) → A`.  Algebraists who reach for the "obvious" curried form `A → ⋯ → A → A` and expect to recover the canonical encoding by `refl` will find this module a useful cautionary example.

The content was relocated here under #310 from `Legacy.Base.Functions.Transformers`; nothing in the canonical `Setoid/`, `Classical/`, or planned `Cubical/` development of the library depends on it.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.FunctionTypeBijections where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; _×_ )
open import Data.Fin.Base   using ( Fin )
open import Function.Base   using ( _∘_ ; id )
open import Level           using ( _⊔_ ; Level )

open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; refl )

-- Imports from agda-algebras ----------------------------------------------------
open import Overture using ( _≈_ )

private variable a b : Level
```

#### Bijections of nondependent function types

The first piece of infrastructure is the type of bijections between two types, in two flavors: the definitional flavor (`Bijection`, where the round-trip composites are required to be `_≡_`-equal to `id`) and the pointwise flavor (`PointwiseBijection`, where pointwise equality `_≈_` suffices).  The investigation below turns on the gap between these two notions.

```agda
record Bijection (A : Type a)(B : Type b) : Type (a ⊔ b) where
  field
    to       : A → B
    from     : B → A
    to-from  : to ∘ from ≡ id
    from-to  : from ∘ to ≡ id

∣_∣=∣_∣ : (A : Type a)(B : Type b) → Type (a ⊔ b)
∣ A ∣=∣ B ∣ = Bijection A B

record PointwiseBijection (A : Type a)(B : Type b) : Type (a ⊔ b) where
  field
    to       : A → B
    from     : B → A
    to-from  : to ∘ from ≈ id
    from-to  : from ∘ to ≈ id

∣_∣≈∣_∣ : (A : Type a)(B : Type b) → Type (a ⊔ b)
∣ A ∣≈∣ B ∣ = PointwiseBijection A B

uncurry₀ : {A : Type a} → A → A → (A × A)
uncurry₀ x y = x , y

module _ {A : Type a} {B : Type b} where

  Curry : ((A × A) → B) → A → A → B
  Curry f x y = f (uncurry₀ x y)

  Uncurry : (A → A → B) → A × A → B
  Uncurry f (x , y) = f x y
```

The product and curried forms enjoy a *definitional* bijection — the round-trip composites reduce to `id` on the nose.

```agda
  A×A→B≅A→A→B : ∣ (A × A → B) ∣=∣ (A → A → B) ∣
  A×A→B≅A→A→B = record  { to = Curry ; from = Uncurry
                        ; to-from = refl ; from-to = refl }
```

#### Fin-indexed encodings

We now introduce the `Fin`-indexed encoding `Fin 2 → A` and transformations between it, the product form `A × A`, and the curried form `A → A`.  The asymmetric behavior of these transformations under definitional equality is the central pedagogical content of the module.

```agda
module _ {A : Type a} where
  open Fin renaming (zero to z ; suc to s)

  A×A→Fin2A : A × A → Fin 2 → A
  A×A→Fin2A (x , y) z = x
  A×A→Fin2A (x , y) (s z) = y

  Fin2A→A×A : (Fin 2 → A) → A × A
  Fin2A→A×A u = u z , u (s z)

  Fin2A~A×A : {A : Type a} → Fin2A→A×A ∘ A×A→Fin2A ≡ id
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
```

#### Failed bijections

We can establish that `CurryFin2 ∘ UncurryFin2 ≡ id` reduces to `refl`, but the reverse composition `UncurryFin2 ∘ CurryFin2` does *not*: it would require reducing `λ {z → u z; (s z) → u (s z)}` to `u`, which is η-expansion of a function out of `Fin 2`, and Agda's definitional equality does not include this reduction.  Hence no definitional bijection between `(Fin 2 → A) → B` and `A → A → B`; only a pointwise one.

```agda
module _ {A : Type a} {B : Type b} where
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

  CurryFin3 : {A : Type a} → ((Fin 3 → A) → B) → A → A → A → B
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
```

The symmetric statement `A×A→B-to-Fin2A→B ∘ Fin2A→B-to-A×A→B ≡ id` fails for the same η-expansion reason: it would require `λ u → (λ {z → u z; (s z) → u (s z)}) ≡ u`, which Agda does not reduce.
