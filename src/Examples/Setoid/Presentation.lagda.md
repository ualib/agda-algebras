---
layout: default
file: "src/Examples/Setoid/Presentation.lagda.md"
title: "Examples.Setoid.Presentation module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: a structure by generators and relations {#examples-setoid-presentation}

This is the [Examples.Setoid.Presentation][] module of the [Agda Universal Algebra Library][].

A *presentation* `⟨ X ∣ R ⟩`{.AgdaFunction} describes a structure by a set `X` of
generators together with a set `R` of defining relations: the presented structure
is the free algebra on `X` modulo the smallest congruence containing `R`.  In the
relatively-free-algebra machinery of [Setoid.Varieties.SoundAndComplete][] this is
exactly `𝔽[ X ]`{.AgdaFunction} for the equation family `R`, whose carrier equality
is derivable equality from `R`.

We take the smallest interesting presentation over the magma signature
`Sig-Magma`{.AgdaFunction}: one generator `a`{.AgdaFunction} and one relation
making it idempotent, `⟨ a ∣ a · a ≈ a ⟩`{.AgdaFunction} — the *free band on one
generator*.  Idempotence forces every nonempty product of `a`{.AgdaFunction} to
collapse to `a`{.AgdaFunction}; we derive two instances of that collapse from the
single defining relation.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.Presentation where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive                       using () renaming ( Set to Type )
open import Data.Fin.Base                        using ( Fin )
open import Data.Fin.Patterns                    using ( 0F ; 1F )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Magma           using ( Sig-Magma ; ∙-Op )
open import Overture.Terms       {𝑆 = Sig-Magma} using ( Term ; ℊ ; node )
open import Setoid.Algebras      {𝑆 = Sig-Magma} using ( 𝔻[_] )
open import Setoid.Varieties.SoundAndComplete {𝑆 = Sig-Magma}
  using ( Eq ; _≈̇_ ; _⊨_ ; _⊢_▹_≈_ ; module FreeAlgebra )

open import Relation.Binary using ( Setoid )

open _⊢_▹_≈_ using ( hyp ; app ; refl ; trans )
```

#### The presentation `⟨ a ∣ a · a ≈ a ⟩` {#the-presentation}

The single generator is `a = ℊ 0F`{.AgdaFunction} in the one-variable context
`Fin 1`{.AgdaDatatype}; the single relation is idempotence.

```agda
_·_ : {X : Type} → Term X → Term X → Term X
s · t = node ∙-Op λ { 0F → s ; 1F → t }

-- the sole generator
a : Term (Fin 1)
a = ℊ 0F

-- the sole relation:  a · a  ≈̇  a
idem-rel : Eq
idem-rel = (a · a) ≈̇ a

R : Fin 1 → Eq
R _ = idem-rel

open FreeAlgebra R using ( 𝔽[_] )
```

The presented structure is `𝔽[ Fin 1 ]`{.AgdaFunction}; it models its own defining
relation by construction.

```agda
presented-is-idempotent : 𝔽[ Fin 1 ] ⊨ R
presented-is-idempotent = FreeAlgebra.satisfies R
```

#### Consequences of the presentation {#consequences}

The carrier equality of `𝔽[ Fin 1 ]`{.AgdaFunction} is derivable equality, so the
defining relation is available as `hyp`{.AgdaInductiveConstructor} `0F`.  Rewriting
the redex `a · a`{.AgdaFunction} with congruence (`app`{.AgdaInductiveConstructor})
and then once more at the top collapses the two three-fold products to
`a`{.AgdaFunction}.

```agda
open Setoid 𝔻[ 𝔽[ Fin 1 ] ] using ( _≈_ )

-- the defining relation itself
idem : (a · a) ≈ a
idem = hyp 0F

-- (a · a) · a ≈ a   :  reduce the left factor, then the top
collapseˡ : ((a · a) · a) ≈ a
collapseˡ = trans (app λ { 0F → hyp 0F ; 1F → refl }) (hyp 0F)

-- a · (a · a) ≈ a   :  reduce the right factor, then the top
collapseʳ : (a · (a · a)) ≈ a
collapseʳ = trans (app λ { 0F → refl ; 1F → hyp 0F }) (hyp 0F)
```

--------------------------------------

{% include UALib.Links.md %}
