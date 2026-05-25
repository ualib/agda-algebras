---
layout: default
file: "src/Classical/Small/Structures/CommutativeSemigroup.lagda.md"
title: "Classical.Small.Structures.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.CommutativeSemigroup where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Classical.Structures.CommutativeSemigroup as Polymorphic

CommutativeSemigroup : Type (suc 0ℓ)
CommutativeSemigroup = Polymorphic.CommutativeSemigroup 0ℓ 0ℓ

fromCommSemigroupEqs : (A : Type 0ℓ) (_·_ : A → A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a b → a · b ≡ b · a)
  → CommutativeSemigroup
fromCommSemigroupEqs = Polymorphic.fromCommSemigroupEqs
```
