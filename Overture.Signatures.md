---
layout: default
title : "Overture.Signatures module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---


### <a id="signatures">Signatures</a>

This is the [Overture.Signatures][] module of the [Agda Universal Algebra Library][].


<pre class="Agda">

<a id="299" class="Symbol">{-#</a> <a id="303" class="Keyword">OPTIONS</a> <a id="311" class="Pragma">--without-K</a> <a id="323" class="Pragma">--exact-split</a> <a id="337" class="Pragma">--safe</a> <a id="344" class="Symbol">#-}</a>

<a id="349" class="Keyword">module</a> <a id="356" href="Overture.Signatures.html" class="Module">Overture.Signatures</a> <a id="376" class="Keyword">where</a>

<a id="383" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="500" class="Keyword">using</a> <a id="506" class="Symbol">()</a> <a id="509" class="Keyword">renaming</a> <a id="518" class="Symbol">(</a> <a id="520" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="524" class="Symbol">to</a>  <a id="528" class="Primitive">Type</a> <a id="533" class="Symbol">)</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="Data.Product.html" class="Module">Data.Product</a>    <a id="563" class="Keyword">using</a> <a id="569" class="Symbol">(</a> <a id="571" href="Data.Product.Base.html#1244" class="Function">Σ-syntax</a> <a id="580" class="Symbol">)</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="Level.html" class="Module">Level</a>           <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a> <a id="618" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="624" class="Symbol">;</a> <a id="626" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="630" class="Symbol">;</a> <a id="632" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="636" class="Symbol">)</a>

<a id="639" class="Keyword">variable</a> <a id="648" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="650" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="652" class="Symbol">:</a> <a id="654" href="Agda.Primitive.html#742" class="Postulate">Level</a>

</pre>

The variables `𝓞` and `𝓥` are not private since, throughout the [agda-algebras][] library,
`𝓞` denotes the universe level of *operation symbol* types, while `𝓥` denotes the universe
level of *arity* types.

#### <a id="theoretical-background">Theoretical background</a>

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



#### <a id="the-signature-type">The signature type</a>

In the [agda-algebras][] library we represent the *signature* of an algebraic
structure using the following type.

<pre class="Agda">

<a id="Signature"></a><a id="3264" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="3274" class="Symbol">:</a> <a id="3276" class="Symbol">(</a><a id="3277" href="Overture.Signatures.html#3277" class="Bound">𝓞</a> <a id="3279" href="Overture.Signatures.html#3279" class="Bound">𝓥</a> <a id="3281" class="Symbol">:</a> <a id="3283" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3288" class="Symbol">)</a> <a id="3290" class="Symbol">→</a> <a id="3292" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3297" class="Symbol">(</a><a id="3298" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="3302" class="Symbol">(</a><a id="3303" href="Overture.Signatures.html#3277" class="Bound">𝓞</a> <a id="3305" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3307" href="Overture.Signatures.html#3279" class="Bound">𝓥</a><a id="3308" class="Symbol">))</a>
<a id="3311" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="3321" href="Overture.Signatures.html#3321" class="Bound">𝓞</a> <a id="3323" href="Overture.Signatures.html#3323" class="Bound">𝓥</a> <a id="3325" class="Symbol">=</a> <a id="3327" href="Data.Product.Base.html#1244" class="Function">Σ[</a> <a id="3330" href="Overture.Signatures.html#3330" class="Bound">F</a> <a id="3332" href="Data.Product.Base.html#1244" class="Function">∈</a> <a id="3334" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3339" href="Overture.Signatures.html#3321" class="Bound">𝓞</a> <a id="3341" href="Data.Product.Base.html#1244" class="Function">]</a> <a id="3343" class="Symbol">(</a><a id="3344" href="Overture.Signatures.html#3330" class="Bound">F</a> <a id="3346" class="Symbol">→</a> <a id="3348" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3353" href="Overture.Signatures.html#3323" class="Bound">𝓥</a><a id="3354" class="Symbol">)</a>

</pre>

Occasionally it is useful to obtain the universe level of a given signature.

<pre class="Agda">

<a id="Level-of-Signature"></a><a id="3461" href="Overture.Signatures.html#3461" class="Function">Level-of-Signature</a> <a id="3480" class="Symbol">:</a> <a id="3482" class="Symbol">{</a><a id="3483" href="Overture.Signatures.html#3483" class="Bound">𝓞</a> <a id="3485" href="Overture.Signatures.html#3485" class="Bound">𝓥</a> <a id="3487" class="Symbol">:</a> <a id="3489" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3494" class="Symbol">}</a> <a id="3496" class="Symbol">→</a> <a id="3498" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="3508" href="Overture.Signatures.html#3483" class="Bound">𝓞</a> <a id="3510" href="Overture.Signatures.html#3485" class="Bound">𝓥</a> <a id="3512" class="Symbol">→</a> <a id="3514" href="Agda.Primitive.html#742" class="Postulate">Level</a>
<a id="3520" href="Overture.Signatures.html#3461" class="Function">Level-of-Signature</a> <a id="3539" class="Symbol">{</a><a id="3540" href="Overture.Signatures.html#3540" class="Bound">𝓞</a><a id="3541" class="Symbol">}{</a><a id="3543" href="Overture.Signatures.html#3543" class="Bound">𝓥</a><a id="3544" class="Symbol">}</a> <a id="3546" class="Symbol">_</a> <a id="3548" class="Symbol">=</a> <a id="3550" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="3554" class="Symbol">(</a><a id="3555" href="Overture.Signatures.html#3540" class="Bound">𝓞</a> <a id="3557" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3559" href="Overture.Signatures.html#3543" class="Bound">𝓥</a><a id="3560" class="Symbol">)</a>

</pre>

In the [Base.Functions][] module of the [agda-algebras][] library, special syntax
is defined for the first and second projections---namely, `∣_∣` and `∥_∥`, resp.

Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then

* `∣ 𝑆 ∣` denotes the set of operation symbols, and
* `∥ 𝑆 ∥` denotes the arity function.

If `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ 𝑓` is the
arity of `𝑓`.

----------------------

<span style="float:left;">[← Overture.Basic](Overture.Basic.html)</span>
<span style="float:right;">[Overture.Operations →](Overture.Operations.html)</span>


{% include UALib.Links.md %}
