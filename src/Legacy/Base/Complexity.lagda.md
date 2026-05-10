---
layout: default
title : "Base.Complexity module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

## <a id="types-for-computational-complexity">Types for Computational Complexity</a>

This is the [Base.Complexity][] module of the [Agda Universal Algebra Library][].

> **Deprecated**.  Canonical home is now [`Setoid.Complexity`](Setoid.Complexity.html), ported under #307 (M2-7c).  The legacy modules in this subtree remain in `Legacy.Base.Complexity.*` for one minor cycle to support downstream migration; they will be removed in v3.1.  See [`src/Legacy/Base/DEPRECATED.md`](../DEPRECATED.md) for the migration guidance.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Complexity where

open import Legacy.Base.Complexity.Basic  public
open import Legacy.Base.Complexity.CSP    public
```

--------------------------------

<span style="float:left;">[← Structures.Sigma.Isos](Structures.Sigma.Isos.html)</span>
<span style="float:right;">[Base.Complexity.Basic →](Base.Complexity.Basic.html)</span>

{% include UALib.Links.md %}
