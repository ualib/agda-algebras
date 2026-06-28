---
layout: default
file: "src/Examples/Setoid/FinitarySignatures.lagda.md"
title: "Examples.Setoid.FinitarySignatures module"
date: "2026-06-28"
author: "the agda-algebras development team"
---

### Finiteness witnesses are one-liners

This is the [Examples.Setoid.FinitarySignatures][] module of the [Agda Universal Algebra Library][].

The finitary Jónsson theorem `jonsson-finitary⇒CongruenceDistributiveVariety`
([Setoid.Varieties.MaltsevConditions][]) asks for a witness `Finitary 𝑆`
([Setoid.Congruences.ChainJoin][]) that every operation symbol of `𝑆` has a finite arity.
This module shows that supplying that witness is never a hoop: for the finitary signatures
of ordinary universal algebra it is the identity bijection `↔-id`, written once (per the
signature's shape).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.FinitarySignatures where

open import Agda.Primitive                  using () renaming ( Set to Type )
open import Data.Fin.Base                   using ( Fin )
open import Data.Nat.Base                   using ( ℕ )
open import Data.Product                    using ( _,_ )
open import Function.Construct.Identity     using ( ↔-id )
open import Level                           using ( Level )

open import Setoid.Congruences.ChainJoin    using ( Finitary )
open import Setoid.Varieties.Maltsev        using ( Sig-Maltsev ; m-Op )
```

#### The recommended shape: arities as `Fin (ar f)`

When a signature's arity function has the shape `λ f → Fin (ar f)` — the natural way to write
a finitary signature — every arity *reduces* to a concrete `Fin`, so the finiteness witness is
literally `λ f → _ , ↔-id _`: no case split, no proof obligation.

```agda
module _ {𝓞 : Level}{Op : Type 𝓞}(ar : Op → ℕ) where

  finitary-Fin-arity : Finitary {𝑆 = Op , (λ f → Fin (ar f))}
  finitary-Fin-arity f = ar f , ↔-id _
```

#### Pattern-matched arities

The signatures already in the library (`Sig-Maltsev`, and the `Classical/` structures) define
their arity function by pattern matching on the operation symbol — e.g. `ar-Maltsev m-Op = Fin 3`.
There the witness names the identity bijection once per symbol, still a trivial one-liner.

```agda
finitary-Sig-Maltsev : Finitary {𝑆 = Sig-Maltsev}
finitary-Sig-Maltsev m-Op = _ , ↔-id _
```

So for any finitary algebra, `jonsson-finitary⇒CongruenceDistributiveVariety fin jt` applies
with `fin` one of the witnesses above and `jt` the algebra's Jónsson terms — the finiteness
side condition is discharged, never threaded by hand.

--------------------------------------

{% include UALib.Links.md %}
