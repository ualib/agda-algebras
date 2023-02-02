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
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="500" class="Keyword">using</a> <a id="506" class="Symbol">()</a> <a id="509" class="Keyword">renaming</a> <a id="518" class="Symbol">(</a> <a id="520" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="524" class="Symbol">to</a>  <a id="528" class="Primitive">Type</a> <a id="533" class="Symbol">)</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="Data.Product.html" class="Module">Data.Product</a>    <a id="563" class="Keyword">using</a> <a id="569" class="Symbol">(</a> <a id="571" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="580" class="Symbol">)</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="Level.html" class="Module">Level</a>           <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a> <a id="618" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="624" class="Symbol">;</a> <a id="626" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="630" class="Symbol">;</a> <a id="632" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="636" class="Symbol">)</a>

<a id="639" class="Keyword">variable</a> <a id="648" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="650" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="652" class="Symbol">:</a> <a id="654" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

The variables `𝓞` and `𝓥` are not private since, throughout the [agda-algebras][] library,
`𝓞` denotes the universe level of *operation symbol* types, while `𝓥` denotes the universe
level of *arity* types.

#### <a id="theoretical-background">Theoretical background</a>

In [model theory](https://en.wikipedia.org/wiki/Model_theory), the *signature*
`𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a structure consists of three (possibly empty) sets `𝐶`, `𝐹`,
and `𝑅`---called *constant symbols*, *function symbols*, and *relation symbols*,
respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an
*arity* to each symbol. Often (but not always) `𝑁 = ℕ`, the natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted
notion of an *algebraic signature* (or *signature* for algebraic structures), by
which we mean a pair `𝑆 = (𝐹, ρ)` consisting of a collection `𝐹` of *operation
symbols* and an *arity function* `ρ : 𝐹 → 𝑁` that maps each operation symbol to
its arity; here, 𝑁 denotes the *arity type*. Heuristically, the arity `ρ 𝑓` of an
operation symbol `𝑓 ∈ 𝐹` may be thought of as the "number of arguments" that `𝑓`
takes as "input".

If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-*ary* operation symbol.  In
case `n` is 0 (or 1 or 2 or 3, respectively) we call the function *nullary* (or
*unary* or *binary* or *ternary*, respectively).

If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this
by writing `𝑓 : A`<sup>ρ 𝑓</sup> `→ A`. On the other hand, the arguments of such
an operation form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be
viewed as the graph of the function `a : ρ𝑓 → A`. When the codomain of `ρ` is `ℕ`,
we may view `ρ 𝑓` as the finite set `{0, 1, …, ρ𝑓 - 1}`. Thus, by identifying the
`ρ𝑓`-th power `A`<sup>ρ 𝑓</sup> with the type `ρ 𝑓 → A` of functions from `{0, 1,
…, ρ𝑓 - 1}` to `A`, we identify the function type `A`<sup>ρ f</sup> `→ A` with the
function (or "functional") type `(ρ𝑓 → A) → A`.

**Example**. Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`, and
`a : m → A` is an `m`-tuple on `A`. Then `𝑔 a` may be viewed as
`𝑔 (a 0, a 1, …, a (m-1))`, which has type `A`. Suppose further that
`𝑓 : (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`, let `a : ρ𝑓 → A` be a
`ρ𝑓`-tuple on `A`, and let `h : A → B` be a function.  Then the following
typing judgments obtain: `h ∘ a : ρ𝑓 → B` and we `𝑓 (h ∘ a) : B`.

#### <a id="the-signature-type">The signature type</a>

In the [agda-algebras][] library we represent the *signature* of an algebraic
structure using the following type.

<pre class="Agda">

<a id="Signature"></a><a id="3282" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="3292" class="Symbol">:</a> <a id="3294" class="Symbol">(</a><a id="3295" href="Overture.Signatures.html#3295" class="Bound">𝓞</a> <a id="3297" href="Overture.Signatures.html#3297" class="Bound">𝓥</a> <a id="3299" class="Symbol">:</a> <a id="3301" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3306" class="Symbol">)</a> <a id="3308" class="Symbol">→</a> <a id="3310" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3315" class="Symbol">(</a><a id="3316" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3320" class="Symbol">(</a><a id="3321" href="Overture.Signatures.html#3295" class="Bound">𝓞</a> <a id="3323" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3325" href="Overture.Signatures.html#3297" class="Bound">𝓥</a><a id="3326" class="Symbol">))</a>
<a id="3329" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="3339" href="Overture.Signatures.html#3339" class="Bound">𝓞</a> <a id="3341" href="Overture.Signatures.html#3341" class="Bound">𝓥</a> <a id="3343" class="Symbol">=</a> <a id="3345" href="Data.Product.html#916" class="Function">Σ[</a> <a id="3348" href="Overture.Signatures.html#3348" class="Bound">F</a> <a id="3350" href="Data.Product.html#916" class="Function">∈</a> <a id="3352" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3357" href="Overture.Signatures.html#3339" class="Bound">𝓞</a> <a id="3359" href="Data.Product.html#916" class="Function">]</a> <a id="3361" class="Symbol">(</a><a id="3362" href="Overture.Signatures.html#3348" class="Bound">F</a> <a id="3364" class="Symbol">→</a> <a id="3366" href="Overture.Signatures.html#528" class="Primitive">Type</a> <a id="3371" href="Overture.Signatures.html#3341" class="Bound">𝓥</a><a id="3372" class="Symbol">)</a>

<a id="Level-of-Signature"></a><a id="3375" href="Overture.Signatures.html#3375" class="Function">Level-of-Signature</a> <a id="3394" class="Symbol">:</a> <a id="3396" class="Symbol">{</a><a id="3397" href="Overture.Signatures.html#3397" class="Bound">𝓞</a> <a id="3399" href="Overture.Signatures.html#3399" class="Bound">𝓥</a> <a id="3401" class="Symbol">:</a> <a id="3403" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3408" class="Symbol">}</a> <a id="3410" class="Symbol">→</a> <a id="3412" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="3422" href="Overture.Signatures.html#3397" class="Bound">𝓞</a> <a id="3424" href="Overture.Signatures.html#3399" class="Bound">𝓥</a> <a id="3426" class="Symbol">→</a> <a id="3428" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3434" href="Overture.Signatures.html#3375" class="Function">Level-of-Signature</a> <a id="3453" class="Symbol">{</a><a id="3454" href="Overture.Signatures.html#3454" class="Bound">𝓞</a><a id="3455" class="Symbol">}{</a><a id="3457" href="Overture.Signatures.html#3457" class="Bound">𝓥</a><a id="3458" class="Symbol">}</a> <a id="3460" class="Symbol">_</a> <a id="3462" class="Symbol">=</a> <a id="3464" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3468" class="Symbol">(</a><a id="3469" href="Overture.Signatures.html#3454" class="Bound">𝓞</a> <a id="3471" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3473" href="Overture.Signatures.html#3457" class="Bound">𝓥</a><a id="3474" class="Symbol">)</a>

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
