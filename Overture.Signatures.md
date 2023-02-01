---
layout: default
title : "Overture.Signatures module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---


### <a id="signatures">Signatures</a>

This is the Overture.Signatures`_ module of the `Agda Universal Algebra Library`_.


<pre class="Agda">

<a id="296" class="Symbol">{-#</a> <a id="300" class="Keyword">OPTIONS</a> <a id="308" class="Pragma">--without-K</a> <a id="320" class="Pragma">--exact-split</a> <a id="334" class="Pragma">--safe</a> <a id="341" class="Symbol">#-}</a>

<a id="346" class="Keyword">module</a> <a id="353" href="Overture.Signatures.html" class="Module">Overture.Signatures</a> <a id="373" class="Keyword">where</a>

<a id="380" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------</a>
<a id="469" class="Keyword">open</a> <a id="474" class="Keyword">import</a> <a id="481" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="497" class="Keyword">using</a> <a id="503" class="Symbol">()</a> <a id="506" class="Keyword">renaming</a> <a id="515" class="Symbol">(</a> <a id="517" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="521" class="Symbol">to</a>  <a id="525" class="Primitive">Type</a> <a id="530" class="Symbol">)</a>
<a id="532" class="Keyword">open</a> <a id="537" class="Keyword">import</a> <a id="544" href="Data.Product.html" class="Module">Data.Product</a>    <a id="560" class="Keyword">using</a> <a id="566" class="Symbol">(</a> <a id="568" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="577" class="Symbol">)</a>
<a id="579" class="Keyword">open</a> <a id="584" class="Keyword">import</a> <a id="591" href="Level.html" class="Module">Level</a>           <a id="607" class="Keyword">using</a> <a id="613" class="Symbol">(</a> <a id="615" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="621" class="Symbol">;</a> <a id="623" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="627" class="Symbol">;</a> <a id="629" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="633" class="Symbol">)</a>

<a id="636" class="Keyword">variable</a> <a id="645" href="Overture.Signatures.html#645" class="Generalizable">𝓞</a> <a id="647" href="Overture.Signatures.html#647" class="Generalizable">𝓥</a> <a id="649" class="Symbol">:</a> <a id="651" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

The variables `𝓞` and `𝓥` are not private since, as mentioned earlier, throughout
the [agda-algebras][] library `𝓞` denotes the universe level of *operation symbol*
types, while `𝓥` denotes the universe level of *arity* types.

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

<a id="Signature"></a><a id="3300" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="3310" class="Symbol">:</a> <a id="3312" class="Symbol">(</a><a id="3313" href="Overture.Signatures.html#3313" class="Bound">𝓞</a> <a id="3315" href="Overture.Signatures.html#3315" class="Bound">𝓥</a> <a id="3317" class="Symbol">:</a> <a id="3319" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3324" class="Symbol">)</a> <a id="3326" class="Symbol">→</a> <a id="3328" href="Overture.Signatures.html#525" class="Primitive">Type</a> <a id="3333" class="Symbol">(</a><a id="3334" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3338" class="Symbol">(</a><a id="3339" href="Overture.Signatures.html#3313" class="Bound">𝓞</a> <a id="3341" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3343" href="Overture.Signatures.html#3315" class="Bound">𝓥</a><a id="3344" class="Symbol">))</a>
<a id="3347" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="3357" href="Overture.Signatures.html#3357" class="Bound">𝓞</a> <a id="3359" href="Overture.Signatures.html#3359" class="Bound">𝓥</a> <a id="3361" class="Symbol">=</a> <a id="3363" href="Data.Product.html#916" class="Function">Σ[</a> <a id="3366" href="Overture.Signatures.html#3366" class="Bound">F</a> <a id="3368" href="Data.Product.html#916" class="Function">∈</a> <a id="3370" href="Overture.Signatures.html#525" class="Primitive">Type</a> <a id="3375" href="Overture.Signatures.html#3357" class="Bound">𝓞</a> <a id="3377" href="Data.Product.html#916" class="Function">]</a> <a id="3379" class="Symbol">(</a><a id="3380" href="Overture.Signatures.html#3366" class="Bound">F</a> <a id="3382" class="Symbol">→</a> <a id="3384" href="Overture.Signatures.html#525" class="Primitive">Type</a> <a id="3389" href="Overture.Signatures.html#3359" class="Bound">𝓥</a><a id="3390" class="Symbol">)</a>

<a id="Level-of-Signature"></a><a id="3393" href="Overture.Signatures.html#3393" class="Function">Level-of-Signature</a> <a id="3412" class="Symbol">:</a> <a id="3414" class="Symbol">{</a><a id="3415" href="Overture.Signatures.html#3415" class="Bound">𝓞</a> <a id="3417" href="Overture.Signatures.html#3417" class="Bound">𝓥</a> <a id="3419" class="Symbol">:</a> <a id="3421" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3426" class="Symbol">}</a> <a id="3428" class="Symbol">→</a> <a id="3430" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="3440" href="Overture.Signatures.html#3415" class="Bound">𝓞</a> <a id="3442" href="Overture.Signatures.html#3417" class="Bound">𝓥</a> <a id="3444" class="Symbol">→</a> <a id="3446" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3452" href="Overture.Signatures.html#3393" class="Function">Level-of-Signature</a> <a id="3471" class="Symbol">{</a><a id="3472" href="Overture.Signatures.html#3472" class="Bound">𝓞</a><a id="3473" class="Symbol">}{</a><a id="3475" href="Overture.Signatures.html#3475" class="Bound">𝓥</a><a id="3476" class="Symbol">}</a> <a id="3478" class="Symbol">_</a> <a id="3480" class="Symbol">=</a> <a id="3482" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3486" class="Symbol">(</a><a id="3487" href="Overture.Signatures.html#3472" class="Bound">𝓞</a> <a id="3489" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3491" href="Overture.Signatures.html#3475" class="Bound">𝓥</a><a id="3492" class="Symbol">)</a>

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
