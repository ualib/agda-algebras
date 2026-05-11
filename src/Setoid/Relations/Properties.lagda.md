---
layout: default
title : "Setoid.Relations.Properties module (The Agda Universal Algebra Library)"
date : "2026-05-10"
author: "the agda-algebras development team"
---

### <a id="properties-of-binary-relations">Properties of binary relations</a>

This is the [Setoid.Relations.Properties][] module of the [Agda Universal Algebra Library][].

The canonical home for elementary properties of binary relations — reflexivity, symmetry, transitivity, antisymmetry, irreflexivity, asymmetry, connex, totality — is `Relation.Binary.Definitions` in the Agda standard library.  Stdlib expresses these properties for `Rel A ℓ = A → A → Type ℓ` (the curried form), and the canonical `Setoid/` tree adopts the same convention: `Setoid.Relations.Discrete` and `Setoid.Relations.Quotients` already import their `Reflexive` / `Transitive` etc. directly from stdlib.

This module exists to give agda-algebras users a stable canonical import path that mirrors `Legacy.Base.Relations.Properties` in the v2.x library and that sits alongside the canonical `Setoid.Relations.{Discrete,Quotients,Continuous}` siblings.  Its content is a thin `public` re-export from stdlib — no new definitions are introduced.  If a genuinely Setoid-flavoured relation property surfaces later (e.g., reflexivity that respects a setoid's `_≈_`), it can be added here without disrupting the canonical import path.

Differences from the legacy module:

+  The legacy module defined its properties for `Pred (A × A) ℓ` (a predicate on the product type); this module uses the stdlib `Rel A ℓ` (the curried form).  The two are interconvertible via `Data.Product.curry` / `Data.Product.uncurry`; the curried form is preferred because the rest of the canonical tree already uses it.
+  The legacy module bundled its own `curry` / `uncurry` definitions; stdlib's `Data.Product.curry` / `Data.Product.uncurry` cover the same ground and are not re-exported here.  Consumers who need the bridge should import from `Data.Product` directly.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations.Properties where

open import Relation.Binary.Definitions public
  using  ( Reflexive    ; Sym         ; Symmetric
         ; Trans        ; TransFlip   ; Transitive
         ; Antisym      ; Antisymmetric
         ; Irreflexive  ; Asymmetric
         ; Connex       ; Total )
```

--------------------------------------

<span style="float:left;">[← Setoid.Relations.Continuous](Setoid.Relations.Continuous.html)</span>
<span style="float:right;">[Setoid.Algebras →](Setoid.Algebras.html)</span>

{% include UALib.Links.md %}
