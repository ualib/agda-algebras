---
layout: default
file: "src/Classical/Theories/AbelianGroup.lagda.md"
title: "Classical.Theories.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### <a id="classical-theories-abeliangroup">The equational theory of abelian groups</a>

This is the [Classical.Theories.AbelianGroup][] module of the [Agda Universal Algebra Library][].

Adds commutativity to the group theory over the same `Sig-Group` signature, exactly
as `Th-CommutativeMonoid` adds it to `Th-Monoid`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.AbelianGroup where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

open import Classical.Signatures.Group             using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity
                                                         ; LeftInverse ; RightInverse ; Commutative )
open import Overture.Terms {𝑆 = Sig-Group}         using ( Term )

data Eq-AbelianGroup : Type where
  assoc idˡ idʳ invˡ invʳ comm : Eq-AbelianGroup

Th-AbelianGroup : Eq-AbelianGroup → Term (Fin 3) × Term (Fin 3)
Th-AbelianGroup assoc = Associative   ∙-Op             refl           0F 1F 2F
Th-AbelianGroup idˡ   = LeftIdentity  ∙-Op ε-Op        refl refl      0F
Th-AbelianGroup idʳ   = RightIdentity ∙-Op ε-Op        refl refl      0F
Th-AbelianGroup invˡ  = LeftInverse   ∙-Op ⁻¹-Op ε-Op  refl refl refl 0F
Th-AbelianGroup invʳ  = RightInverse  ∙-Op ⁻¹-Op ε-Op  refl refl refl 0F
Th-AbelianGroup comm  = Commutative   ∙-Op             refl           0F 1F
```

--------------------------------------

{% include UALib.Links.md %}
