---
layout: default
file: "src/Classical/Categories/Forgetful.lagda.md"
title: "Classical.Categories.Forgetful module"
date: "2026-06-09"
author: "the agda-algebras development team"
---

### Classical forgetful functors

This is the [Classical.Categories.Forgetful][] module of the [Agda Universal Algebra Library][].

The classical forgetful *projections* of [ADR-002][] §5 become forgetful *functors* simply by
giving them the morphism action — and that action is already supplied, uniformly, by the
reduct functor [`reductF`][Classical.Categories.Reduct].  Each forgetful is `reductF` of the
relevant signature inclusion, reusing the per-structure inclusion data (`X-incl` / `X-κ`).

The inaugural instance is `monoid→semigroupF`.  Since a semigroup is an algebra over
`Sig-Magma` (Semigroup reuses the magma signature), the forgetful from monoids is `reductF`
of the inclusion `Sig-Magma ↪ Sig-Monoid` — packaged from the existing `∙-incl` / `∙-κ` of
[`Classical.Structures.Monoid`][].  Its action on a monoid homomorphism keeps the underlying
setoid map on the nose, as `monoid→semigroupF-keeps-map` records by `refl`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Categories.Forgetful where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using ()             renaming ( Set to Type )
open import Data.Product    using ( proj₁ )
open import Level           using ( Level )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures.Morphisms  using ( SigMorphism ; mkSigMorphism )
open import Setoid.Categories.Functor      using ( Functor )
open import Classical.Categories.Reduct    using ( reductF )
open import Classical.Signatures.Magma     using ( Sig-Magma )
open import Classical.Signatures.Monoid    using ( Sig-Monoid )
open import Classical.Structures.Monoid    using ( ∙-incl ; ∙-κ )

import Setoid.Categories.Algebra as AlgCat

open import Setoid.Algebras.Basic      {𝑆 = Sig-Monoid} using ( Algebra )
open import Setoid.Homomorphisms.Basic {𝑆 = Sig-Monoid} using ( hom )

private variable α ρ : Level
```

The inclusion `Sig-Magma ↪ Sig-Monoid`, as a signature morphism:

```agda
magma↪monoid : SigMorphism Sig-Magma Sig-Monoid
magma↪monoid = mkSigMorphism ∙-incl ∙-κ
```

The forgetful functor on algebras, `reductF` of that inclusion:

```agda
monoid→semigroupF : Functor (AlgCat.Alg {𝑆 = Sig-Monoid} α ρ) (AlgCat.Alg {𝑆 = Sig-Magma} α ρ)
monoid→semigroupF = reductF magma↪monoid
```

Its morphism action keeps the underlying setoid map of a monoid homomorphism unchanged:

```agda
monoid→semigroupF-keeps-map : {𝑴 𝑵 : Algebra α ρ} (f : hom 𝑴 𝑵)
                            → proj₁ (Functor.F₁ monoid→semigroupF f) ≡ proj₁ f
monoid→semigroupF-keeps-map _ = refl
```

--------------------------------------

{% include UALib.Links.md %}
