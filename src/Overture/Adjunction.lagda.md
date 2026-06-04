---
layout: default
title : "Overture.Adjunction module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "the agda-algebras development team"
---

## Adjunction

This is the [Overture.Adjunction][] module of the [Agda Universal Algebra Library][].

This subtree collects the order-theoretic adjunction infrastructure used across the library: closure operators and closure systems, Galois connections between posets, and residuated pairs.  Every definition is parameterized by `Poset` from stdlib and works with the equivalence carried by the underlying poset; nothing presupposes a setoid algebra or commits to propositional equality.  This equivalence-flavor-agnosticism is why the subtree lives in `Overture/` — it is shared by `Setoid/` (where closure operators induce algebraic closure systems on subuniverses, and Galois connections appear in clone theory) and the planned `Classical/` tree (lattice and order infrastructure, M3-5), and is mechanically portable to `Cubical/` when the long-term port lands.

This module is a Category-A relocation under #305 (M2-7a).  See [`src/Legacy/Base/DEPRECATED.md`](../Legacy/Base/DEPRECATED.md) for the inventory and migration guidance.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Adjunction where

open import Overture.Adjunction.Closure      public
open import Overture.Adjunction.Galois       public
open import Overture.Adjunction.Residuation  public
```

-------------------------------------

<span style="float:left;">[← Overture.Functions](Overture.Functions.html)</span>
<span style="float:right;">[Overture.Adjunction.Closure →](Overture.Adjunction.Closure.html)</span>

{% include UALib.Links.md %}
```
