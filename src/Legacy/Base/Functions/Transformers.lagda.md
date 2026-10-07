---
layout: default
title : "Legacy.Base.Functions.Transformers module"
date : "2021-07-26"
author: "the agda-algebras development team"
---

### <a id="type-transformers">Type Transformers</a>

This is the [Legacy.Base.Functions.Transformers][] module of the [agda-algebras][] library.

> **Deprecation notice (v3.0, #310)**.  This module has been relocated to [Examples.FunctionTypeBijections][].  The content here is retained for one minor-version cycle so v2.x consumers can migrate; it is scheduled for removal in v3.1.  Please update your imports to `open import Examples.FunctionTypeBijections`.

Here we define functions for translating from one type to another.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Legacy.Base.Functions.Transformers where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; _×_ )
open import Data.Fin.Base   using ( Fin )
open import Function.Base   using ( _∘_ ; id )
open import Level           using ( _⊔_ ; Level )

open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; refl ; module ≡-Reasoning )

-- Imports from agda-algebras ----------------------------------------------------
open import Overture using ( _≈_ )

private variable a b : Level
```

#### <a id="bijections-of-nondependent-function-types">Bijections of nondependent function types</a>

In set theory, these would simply be bijections between sets, or "set isomorphisms."

```agda
record Bijection (A : Type a)(B : Type b) : Type (a ⊔ b) where
 field
  to       : A → B
  from     : B → A
  to-from  : to ∘ from ≡ id
  from-to  : from ∘ to ≡ id

{-# WARNING_ON_USAGE Bijection "Bijection is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.Bijection (or Function.Bundles.Bijection from stdlib for setoid-flavored bijections)." #-}

∣_∣=∣_∣ : (A : Type a)(B : Type b) → Type (a ⊔ b)
∣ A ∣=∣ B ∣ = Bijection A B

{-# WARNING_ON_USAGE ∣_∣=∣_∣ "∣_∣=∣_∣ is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.∣_∣=∣_∣." #-}

record PointwiseBijection (A : Type a)(B : Type b) : Type (a ⊔ b) where
 field
  to       : A → B
  from     : B → A
  to-from  : to ∘ from ≈ id
  from-to  : from ∘ to ≈ id

{-# WARNING_ON_USAGE PointwiseBijection "PointwiseBijection is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.PointwiseBijection." #-}

∣_∣≈∣_∣ : (A : Type a)(B : Type b) → Type (a ⊔ b)
∣ A ∣≈∣ B ∣ = PointwiseBijection A B

{-# WARNING_ON_USAGE ∣_∣≈∣_∣ "∣_∣≈∣_∣ is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.∣_∣≈∣_∣." #-}

uncurry₀ : {A : Type a} → A → A → (A × A)
uncurry₀ x y = x , y

module _ {A : Type a} {B : Type b} where

 Curry : ((A × A) → B) → A → A → B
 Curry f x y = f (uncurry₀ x y)

 Uncurry : (A → A → B) → A × A → B
 Uncurry f (x , y) = f x y

 A×A→B≅A→A→B : ∣ (A × A → B) ∣=∣ (A → A → B) ∣
 A×A→B≅A→A→B = record  { to = Curry ; from = Uncurry
                       ; to-from = refl ; from-to = refl }

{-# WARNING_ON_USAGE Curry "Curry is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.Curry, or stdlib's Function.Base.curry." #-}
{-# WARNING_ON_USAGE Uncurry "Uncurry is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.Uncurry, or stdlib's Function.Base.uncurry." #-}
```


#### <a id="non-bijective-transformations">Non-bijective transformations</a>

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

Somehow we cannot establish a bijection between the two seemingly isomorphic
function types, `(Fin 2 → A) → B` and `A × A → B`, nor between the types
`(Fin 2 → A) → B` and `A → A → B`.

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

 open ≡-Reasoning

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

{-# WARNING_ON_USAGE CurryFin2 "CurryFin2 is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.CurryFin2." #-}
{-# WARNING_ON_USAGE UncurryFin2 "UncurryFin2 is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.UncurryFin2." #-}
{-# WARNING_ON_USAGE CurryFin3 "CurryFin3 is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.CurryFin3." #-}
{-# WARNING_ON_USAGE UncurryFin3 "UncurryFin3 is deprecated as of agda-algebras v3.0.  Use Examples.FunctionTypeBijections.UncurryFin3." #-}
```
