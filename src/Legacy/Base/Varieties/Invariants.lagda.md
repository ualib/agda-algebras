---
layout: default
title : "Legacy.Base.Varieties.Invariants module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "the ualib/agda-algebras development team"
---

### Algebraic invariants

> **Deprecation notice (v3.0, #311)**.  This module has been ported to [Setoid.Varieties.Invariants][].  The content here is retained for one minor-version cycle so v2.x consumers can migrate; it is scheduled for removal in v3.1.  Please update your imports to `open import Setoid.Varieties.Invariants {𝑆}`.

These are properties that are preserved under isomorphism.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Legacy.Base.Homomorphisms   {𝑆 = 𝑆} using ( _≅_ )
open import Legacy.Base.Algebras.Basic  {𝑆 = 𝑆} using ( Algebra )

private variable α ℓ : Level

AlgebraicInvariant : Pred (Algebra α) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩

{-# WARNING_ON_USAGE AlgebraicInvariant "Use Setoid.Varieties.Invariants.AlgebraicInvariant instead. Deprecated under #311; removal planned one minor cycle later." #-}
```
