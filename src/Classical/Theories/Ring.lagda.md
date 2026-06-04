---
layout: default
file: "src/Classical/Theories/Ring.lagda.md"
title: "Classical.Theories.Ring module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### The equational theory of rings

This is the [Classical.Theories.Ring][] module of the [Agda Universal Algebra Library][].

`Th-Ring` has eleven equations, composed from the generic builders of
[`Classical.Equations`][] applied to `Sig-Ring`'s symbols, in three groups:

+  the **abelian-group** equations on the additive triple `(+-Op, 0-Op, -Op)` —
   associativity, left/right identity, left/right inverse, and commutativity (six);
+  the **monoid** equations on the multiplicative pair `(·-Op, 1-Op)` —
   associativity and left/right identity (three);
+  the two **distributivity** equations tying multiplication over addition together
   (`DistributesOverˡ`, `DistributesOverʳ`).

Constructor names hyphenate the operation as a prefix (`+-assoc`, `·-idˡ`, …) so the
operation governing each equation is visible at every use site.  This is the first
theory in the [`Classical/`][Classical] tree to compose two separate single-operation
sub-theories plus the cross-operation distributivity laws; the additive sub-theory is
exactly `Th-AbelianGroup` re-spelled over `Sig-Ring`'s additive symbols, and the
multiplicative sub-theory is exactly `Th-Monoid` re-spelled over its multiplicative
symbols, which is what makes the two forgetful reducts of
`Classical.Structures.Ring` discharge cleanly.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Ring where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Ring              using ( Sig-Ring ; +-Op ; 0-Op ; -Op ; ·-Op ; 1-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity
                                                         ; LeftInverse ; RightInverse ; Commutative
                                                         ; DistributesOverˡ ; DistributesOverʳ )
open import Overture.Terms {𝑆 = Sig-Ring}          using ( Term )

data Eq-Ring : Type where
  +-assoc +-idˡ +-idʳ +-invˡ +-invʳ +-comm : Eq-Ring
  ·-assoc ·-idˡ ·-idʳ                      : Eq-Ring
  distribˡ distribʳ                        : Eq-Ring

Th-Ring : Eq-Ring → Term (Fin 3) × Term (Fin 3)
Th-Ring +-assoc  = Associative     +-Op           refl           0F 1F 2F
Th-Ring +-idˡ    = LeftIdentity    +-Op 0-Op      refl refl      0F
Th-Ring +-idʳ    = RightIdentity   +-Op 0-Op      refl refl      0F
Th-Ring +-invˡ   = LeftInverse     +-Op -Op 0-Op  refl refl refl 0F
Th-Ring +-invʳ   = RightInverse    +-Op -Op 0-Op  refl refl refl 0F
Th-Ring +-comm   = Commutative     +-Op           refl           0F 1F
Th-Ring ·-assoc  = Associative     ·-Op           refl           0F 1F 2F
Th-Ring ·-idˡ    = LeftIdentity    ·-Op 1-Op      refl refl      0F
Th-Ring ·-idʳ    = RightIdentity   ·-Op 1-Op      refl refl      0F
Th-Ring distribˡ = DistributesOverˡ ·-Op +-Op     refl refl      0F 1F 2F
Th-Ring distribʳ = DistributesOverʳ ·-Op +-Op     refl refl      0F 1F 2F
```

--------------------------------------

<span style="float:left;">[← Classical.Theories.Group](Classical.Theories.Group.html)</span>

{% include UALib.Links.md %}
