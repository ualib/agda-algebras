---
layout: default
file: "src/Classical/Theories/CommutativeRing.lagda.md"
title: "Classical.Theories.CommutativeRing module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### The equational theory of commutative rings

This is the [Classical.Theories.CommutativeRing][] module of the [Agda Universal Algebra Library][].

Adds multiplicative commutativity to the ring theory over the same `Sig-Ring`
signature, exactly as `Th-CommutativeMonoid` adds it to `Th-Monoid` and
`Th-AbelianGroup` adds it to `Th-Group`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.CommutativeRing where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

open import Classical.Signatures.Ring              using ( Sig-Ring ; +-Op ; 0-Op ; -Op ; ·-Op ; 1-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity
                                                         ; LeftInverse ; RightInverse ; Commutative
                                                         ; DistributesOverˡ ; DistributesOverʳ )
open import Overture.Terms {𝑆 = Sig-Ring}          using ( Term )

data Eq-CommutativeRing : Type where
  +-assoc +-idˡ +-idʳ +-invˡ +-invʳ +-comm : Eq-CommutativeRing
  ·-assoc ·-idˡ ·-idʳ ·-comm               : Eq-CommutativeRing
  distribˡ distribʳ                        : Eq-CommutativeRing

Th-CommutativeRing : Eq-CommutativeRing → Term (Fin 3) × Term (Fin 3)
Th-CommutativeRing +-assoc  = Associative     +-Op           refl           0F 1F 2F
Th-CommutativeRing +-idˡ    = LeftIdentity    +-Op 0-Op      refl refl      0F
Th-CommutativeRing +-idʳ    = RightIdentity   +-Op 0-Op      refl refl      0F
Th-CommutativeRing +-invˡ   = LeftInverse     +-Op -Op 0-Op  refl refl refl 0F
Th-CommutativeRing +-invʳ   = RightInverse    +-Op -Op 0-Op  refl refl refl 0F
Th-CommutativeRing +-comm   = Commutative     +-Op           refl           0F 1F
Th-CommutativeRing ·-assoc  = Associative     ·-Op           refl           0F 1F 2F
Th-CommutativeRing ·-idˡ    = LeftIdentity    ·-Op 1-Op      refl refl      0F
Th-CommutativeRing ·-idʳ    = RightIdentity   ·-Op 1-Op      refl refl      0F
Th-CommutativeRing ·-comm   = Commutative     ·-Op           refl           0F 1F
Th-CommutativeRing distribˡ = DistributesOverˡ ·-Op +-Op     refl refl      0F 1F 2F
Th-CommutativeRing distribʳ = DistributesOverʳ ·-Op +-Op     refl refl      0F 1F 2F
```

--------------------------------------

{% include UALib.Links.md %}
