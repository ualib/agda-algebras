---
layout: default
file: "src/Classical/Theories/CommutativeMonoid.lagda.md"
title: "Classical.Theories.CommutativeMonoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### <a id="classical-theories-commutativemonoid">The equational theory of commutative monoids</a>

This is the [Classical.Theories.CommutativeMonoid][] module of the [Agda Universal Algebra Library][].

Adds commutativity to the monoid theory over the same `Sig-Monoid` signature.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.CommutativeMonoid where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

open import Classical.Signatures.Monoid            using ( Sig-Monoid ; ∙-Op ; ε-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity ; Commutative )
open import Overture.Terms {𝑆 = Sig-Monoid}        using ( Term )

data Eq-CommutativeMonoid : Type where
  assoc idˡ idʳ comm : Eq-CommutativeMonoid

Th-CommutativeMonoid : Eq-CommutativeMonoid → Term (Fin 3) × Term (Fin 3)
Th-CommutativeMonoid assoc = Associative   ∙-Op      refl 0F 1F 2F
Th-CommutativeMonoid idˡ   = LeftIdentity  ∙-Op ε-Op refl refl 0F
Th-CommutativeMonoid idʳ   = RightIdentity ∙-Op ε-Op refl refl 0F
Th-CommutativeMonoid comm  = Commutative   ∙-Op      refl 0F 1F
```

--------------------------------------

{% include UALib.Links.md %}
