---
layout: default
title : "Overture.Signatures module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---


### Signatures

This is the [Overture.Signatures][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Signatures where

-- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------
open import Agda.Primitive  using () renaming ( Set to  Type )
open import Data.Product    using ( Σ-syntax ; proj₁ ; proj₂ )
open import Level           using ( Level ; suc ; _⊔_ )

variable 𝓞 𝓥 : Level
```

The variables `𝓞` and `𝓥` are not private since, throughout the [agda-algebras][] library,
`𝓞` denotes the universe level of *operation symbol* types, while `𝓥` denotes the universe
level of *arity* types.

#### Theoretical background

In [model theory](https://en.wikipedia.org/wiki/Model_theory), the *signature*
`𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a structure consists of three (possibly empty) sets `𝐶`, `𝐹`,
and `𝑅`---called *constant symbols*, *function symbols*, and *relation symbols*,
respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an
*arity* to each symbol.

Often (but not always) `𝑁 = ℕ`, the natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted
notion of an *algebraic signature* (or *signature* for algebraic structures), by
which we mean a pair `𝑆 = (𝐹, ρ)` consisting of a collection `𝐹` of *operation
symbols* and an *arity function* `ρ : 𝐹 → 𝑁` that maps each operation symbol to
its arity; here, 𝑁 denotes the *arity type*.

Heuristically, the arity `ρ 𝑓` of an operation symbol `𝑓 ∈ 𝐹` may be thought of as
the "number of arguments" that `𝑓` takes as "input".

If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-*ary* operation symbol.  In
case `n` is 0 (or 1 or 2 or 3, respectively) we call the function *nullary* (or
*unary* or *binary* or *ternary*, respectively).

If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this
by writing `𝑓 : A`<sup>ρ 𝑓</sup> `→ A`. On the other hand, the arguments of such
an operation form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be
viewed as the graph of the function `a : ρ𝑓 → A`.

When the codomain of `ρ` is `ℕ`, we may view `ρ 𝑓` as the finite set `{0, 1, …, ρ𝑓 - 1}`.

Thus, by identifying the `ρ𝑓`-th power `A`<sup>ρ 𝑓</sup> with the type `ρ 𝑓 → A` of
functions from `{0, 1, …, ρ𝑓 - 1}` to `A`, we identify the type
`A`<sup>ρ f</sup> `→ A` with the function type `(ρ𝑓 → A) → A`.

**Example**.

Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`.

Let `a : m → A` be an `m`-tuple on `A`.

Then `𝑔 a` may be viewed as `𝑔 (a 0, a 1, …, a (m-1))`, which has type `A`.

Suppose further that `𝑓 : (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`.

Let `a : ρ𝑓 → A` be a `ρ𝑓`-tuple on `A`, and let `h : A → B` be a function.

Then the following typing judgments obtain:

`h ∘ a : ρ𝑓 → B` and `𝑓 (h ∘ a) : B`.


#### The signature type

In the [agda-algebras][] library we represent the *signature* of an algebraic
structure using the following type.

```agda
Signature : (𝓞 𝓥 : Level) → Type (suc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)
```

Occasionally it is useful to obtain the universe level of a given signature.

```agda
Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
Level-of-Signature {𝓞}{𝓥} _ = suc (𝓞 ⊔ 𝓥)
```

A signature is a Σ-type, so its two components are recovered by the standard
projections `proj₁` and `proj₂` (from `Data.Product`, re-exported by
[Overture.Basic][]).

Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then

* `proj₁ 𝑆` denotes the set of operation symbols, and
* `proj₂ 𝑆` denotes the arity function.

If `𝑓 : proj₁ 𝑆` is an operation symbol in the signature `𝑆`, then `proj₂ 𝑆 𝑓`
is the arity of `𝑓`.

#### Self-documenting projections

Bare `proj₁` / `proj₂` read opaquely at signature use sites.  The following
long-form aliases are definitionally identical to the projections and are the
canonical way to name a signature's components throughout the library.  See
[ADR-002][] §1 for the rationale and the per-tree policy.

```agda
OperationSymbolsOf : Signature 𝓞 𝓥 → Type 𝓞
OperationSymbolsOf 𝑆 = proj₁ 𝑆

ArityOf : (𝑆 : Signature 𝓞 𝓥) → OperationSymbolsOf 𝑆 → Type 𝓥
ArityOf 𝑆 f = proj₂ 𝑆 f
```

The bracket projections `∣_∣` / `∥_∥` are deprecated as of v3.0 (they carry a
`WARNING_ON_USAGE` in [Overture.Basic][]); new code uses `OperationSymbolsOf` /
`ArityOf` for signature components and `proj₁` / `proj₂` elsewhere.

----------------------

<span style="float:left;">[← Overture.Basic](Overture.Basic.html)</span>
<span style="float:right;">[Overture.Operations →](Overture.Operations.html)</span>


{% include UALib.Links.md %}
