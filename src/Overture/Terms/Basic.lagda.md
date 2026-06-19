---
layout: default
title : "Overture.Terms.Basic module (The Agda Universal Algebra Library)"
date : "2026-06-18"
author: "agda-algebras development team"
---

## Terms over a signature {#terms}

A `Term X` is a finite tree whose leaves are drawn from a type `X` of variable
symbols and whose internal nodes are labelled by operation symbols of the signature
`𝑆`.  Equivalently, `Term` is the W-type for the polynomial functor associated to
`𝑆`, freely adjoined a copy of `X` at the leaves.

This definition presupposes only the signature: no propositional equality on a
carrier, no setoid equivalence, no path type.  It is therefore foundational rather
than setoid-specific, which is why it lives in `Overture/` rather than under
`Setoid/`, `Classical/`, or `Cubical/`.  The Setoid term algebra `𝑻 X` (which equips
`Term X` with an inductive equivalence-of-terms relation `_≐_`) is built on top of
this definition in `Setoid.Terms.Basic`; the planned Cubical analog will sit
similarly.[^1]

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture.Signatures using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )

module Overture.Terms.Basic {𝑆 : Signature 𝓞 𝓥} where
-- Imports from Agda primitives and the standard library.
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level ; suc ; _⊔_ )

private variable χ : Level
```

### The level shorthand `ov`

Throughout the library we package the universe levels of operation symbols (`𝓞`),
arities (`𝓥`), and a separate "carrier-or-variable" level (`χ`) into a single
shorthand `ov χ = 𝓞 ⊔ 𝓥 ⊔ suc χ`.  The `suc` is unavoidable because `Term X` mixes
leaves of type `X : Type χ` with operation symbols of type `Type 𝓞`, so the resulting
tree type sits one universe up.

This shorthand currently appears with the same definition in
`Legacy.Base.Algebras.Basic` and `Setoid.Algebras.Basic`; the three definitions are
definitionally equal.[^2]

```agda
ov : Level → Level
ov χ = 𝓞 ⊔ 𝓥 ⊔ suc χ
```

### The type of terms

Fix a signature `𝑆` and let `X` denote an arbitrary collection of variable symbols,
assumed disjoint from the operation symbols of `𝑆`
(i.e. `X ∩ OperationSymbolsOf 𝑆 = ∅`).

By a *word* in the language of `𝑆`, we mean a nonempty finite sequence of members of
`X ∪ OperationSymbolsOf 𝑆`; we denote concatenation of such sequences by simple
juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`.  We define the sets `𝑇ₙ`
of *words* over `X ∪ OperationSymbolsOf 𝑆` by induction on `n`
(cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀`  and  `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `f t` such that `f : OperationSymbolsOf 𝑆` and `t
: ArityOf 𝑆 f → 𝑇ₙ` (recall `ArityOf 𝑆 f` is the arity of `f`).  The collection of
*terms* in the signature `𝑆` over `X` is then `Term X := ⋃ₙ 𝑇ₙ`.  By an 𝑆-*term* we
mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type suffices
to represent the notion in type theory.  Such a representation is given by the
inductive type below, which encodes each term as a tree with an operation symbol at
each `node` and a variable symbol (the `generator`) at each leaf.

```agda
data Term (X : Type χ) : Type (ov χ) where
  ℊ     : X → Term X                                       -- (ℊ for "generator")
  node  : (f : OperationSymbolsOf 𝑆)(t : ArityOf 𝑆 f → Term X) → Term X

open Term public
```

**Notation**.  The type `X` represents an arbitrary collection of variable symbols;
`ov χ` is the universe-level shorthand defined above.

The bare-types term algebra `𝑻 : (X : Type χ) → Algebra (ov χ)`, which equips `Term
X` with `node` as its interpretation, is *not* relocated here: it depends on the
foundation-specific `Algebra` type, which differs between the bare-types tree
(`Legacy.Base.Algebras.Algebra`) and the canonical Setoid tree
(`Setoid.Algebras.Basic.Algebra`).  The legacy `𝑻` continues to live in
`Legacy.Base.Terms.Basic`; the Setoid term algebra continues to live in
`Setoid.Terms.Basic`.

--------------------------------------

[^1]: This module is a Category-A relocation under #303 (M2-6).  See [`src/Legacy/Base/DEPRECATED.md`](../Legacy/Base/DEPRECATED.md) for the full inventory.

[^2]: Hoisting `ov` to `Overture.Signatures` and removing the duplicates is a small candidate cleanup tracked separately from #303.

<span style="float:left;">[← Overture.Operations](Overture.Operations.html)</span>
<span style="float:right;">[Overture.Relations →](Overture.Relations.html)</span>

{% include UALib.Links.md %}
