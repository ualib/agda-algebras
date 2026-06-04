---
layout: default
file: "src/Classical/Theories/Monoid.lagda.md"
title: "Classical.Theories.Monoid module"
date: "2026-05-22"
author: "the agda-algebras development team"
---

### The equational theory of monoids

This is the [Classical.Theories.Monoid][] module of the [Agda Universal Algebra Library][].

`Th-Monoid` has three equations: associativity, left identity, and right
identity, composed from the generic builders of [`Classical.Equations`][] applied
to `Sig-Monoid`'s symbols.  Associativity needs three variables, the identity laws
one each, so the variable carrier is uniformly `Fin 3` (per [ADR-002 v2
§2](../../docs/adr/002-classical-layer-design.md)); the identity equations use
`0F` and ignore `1F`, `2F`.  The codomain is spelled in long form, not `_`, per
§4.  This module's prose carries the same normative weight for the
identity-bearing structures as `Classical.Theories.Semigroup` does for the
associativity-only ones.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Monoid where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Monoid            using ( Sig-Monoid ; ∙-Op ; ε-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity )
open import Overture.Terms {𝑆 = Sig-Monoid}        using ( Term )

data Eq-Monoid : Type where
  assoc idˡ idʳ : Eq-Monoid

Th-Monoid : Eq-Monoid → Term (Fin 3) × Term (Fin 3)
Th-Monoid assoc  = Associative    ∙-Op       refl 0F 1F 2F
Th-Monoid idˡ    = LeftIdentity   ∙-Op ε-Op  refl refl 0F
Th-Monoid idʳ    = RightIdentity  ∙-Op ε-Op  refl refl 0F
```

--------------------------------------

<span style="float:left;">[← Classical.Theories.Semigroup](Classical.Theories.Semigroup.html)</span>
<span style="float:right;">[Classical.Theories.Group →](Classical.Theories.Group.html)</span>

{% include UALib.Links.md %}
