---
layout: default
title : "Setoid.Complexity module (Agda Universal Algebra Library)"
date : "2026-05-09"
author: "agda-algebras development team"
---

## <a id="types-for-computational-complexity">Types for Computational Complexity</a>

This is the [Setoid.Complexity][] module of the [Agda Universal Algebra Library][].

This subtree collects the setoid-canonical formulation of computational complexity infrastructure used by the library: word and algorithm definitions ([`Setoid.Complexity.Basic`](Setoid.Complexity.Basic.html)) and the relational formulation of CSP, including the Galois connection to polymorphism clones ([`Setoid.Complexity.CSP`](Setoid.Complexity.CSP.html)).

This module is the canonical home for the content previously developed in `Legacy.Base.Complexity.*`, ported under #307 (M2-7c).  See [`src/Legacy/Base/DEPRECATED.md`](../Legacy/Base/DEPRECATED.md) for the inventory and migration guidance.  Substantial extensions — polymorphism clones as a first-class type, the Jeavons Galois connection, Post's lattice, Bulatov–Zhuk — are tracked under #274 (M7-1) and build on this module.

```agda

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Complexity {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Complexity.Basic               public
open import Setoid.Complexity.CSP    {𝑆 = 𝑆}      public
```

--------------------------------

<span style="float:left;">[← Setoid.Varieties](Setoid.Varieties.html)</span>
<span style="float:right;">[Setoid.Complexity.Basic →](Setoid.Complexity.Basic.html)</span>

{% include UALib.Links.md %}
