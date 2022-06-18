---
layout: default
title : "Overture.Signatures module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

<pre class="Agda">

<a id="171" class="Symbol">{-#</a> <a id="175" class="Keyword">OPTIONS</a> <a id="183" class="Pragma">--without-K</a> <a id="195" class="Pragma">--exact-split</a> <a id="209" class="Pragma">--safe</a> <a id="216" class="Symbol">#-}</a>

<a id="221" class="Keyword">module</a> <a id="228" href="Overture.Signatures.html" class="Module">Overture.Signatures</a> <a id="248" class="Keyword">where</a>

<a id="255" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="372" class="Keyword">using</a> <a id="378" class="Symbol">()</a> <a id="381" class="Keyword">renaming</a> <a id="390" class="Symbol">(</a> <a id="392" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="396" class="Symbol">to</a>  <a id="400" class="Primitive">Type</a> <a id="405" class="Symbol">)</a>
<a id="407" class="Keyword">open</a> <a id="412" class="Keyword">import</a> <a id="419" href="Data.Product.html" class="Module">Data.Product</a>    <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a> <a id="443" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="452" class="Symbol">)</a>
<a id="454" class="Keyword">open</a> <a id="459" class="Keyword">import</a> <a id="466" href="Level.html" class="Module">Level</a>           <a id="482" class="Keyword">using</a> <a id="488" class="Symbol">(</a> <a id="490" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="496" class="Symbol">;</a> <a id="498" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="502" class="Symbol">;</a> <a id="504" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="508" class="Symbol">)</a>

<a id="511" class="Keyword">variable</a> <a id="520" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="522" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a> <a id="524" class="Symbol">:</a> <a id="526" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

The variables `𝓞` and `𝓥` are not private since, as mentioned earlier, throughout
the [agda-algebras][] library `𝓞` denotes the universe level of *operation symbol*
types, while `𝓥` denotes the universe level of *arity* types.


### <a id="signatures-of-an-algebra">Signatures of an algebra</a>

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

#### <a id="signature-type">Signature type</a>

In the [agda-algebras][] library we represent the *signature* of an algebraic
structure using the following type.

<pre class="Agda">

<a id="Signature"></a><a id="3171" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="3181" class="Symbol">:</a> <a id="3183" class="Symbol">(</a><a id="3184" href="Overture.Signatures.html#3184" class="Bound">𝓞</a> <a id="3186" href="Overture.Signatures.html#3186" class="Bound">𝓥</a> <a id="3188" class="Symbol">:</a> <a id="3190" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3195" class="Symbol">)</a> <a id="3197" class="Symbol">→</a> <a id="3199" href="Overture.Signatures.html#400" class="Primitive">Type</a> <a id="3204" class="Symbol">(</a><a id="3205" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3209" class="Symbol">(</a><a id="3210" href="Overture.Signatures.html#3184" class="Bound">𝓞</a> <a id="3212" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3214" href="Overture.Signatures.html#3186" class="Bound">𝓥</a><a id="3215" class="Symbol">))</a>
<a id="3218" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="3228" href="Overture.Signatures.html#3228" class="Bound">𝓞</a> <a id="3230" href="Overture.Signatures.html#3230" class="Bound">𝓥</a> <a id="3232" class="Symbol">=</a> <a id="3234" href="Data.Product.html#916" class="Function">Σ[</a> <a id="3237" href="Overture.Signatures.html#3237" class="Bound">F</a> <a id="3239" href="Data.Product.html#916" class="Function">∈</a> <a id="3241" href="Overture.Signatures.html#400" class="Primitive">Type</a> <a id="3246" href="Overture.Signatures.html#3228" class="Bound">𝓞</a> <a id="3248" href="Data.Product.html#916" class="Function">]</a> <a id="3250" class="Symbol">(</a><a id="3251" href="Overture.Signatures.html#3237" class="Bound">F</a> <a id="3253" class="Symbol">→</a> <a id="3255" href="Overture.Signatures.html#400" class="Primitive">Type</a> <a id="3260" href="Overture.Signatures.html#3230" class="Bound">𝓥</a><a id="3261" class="Symbol">)</a>

<a id="Level-of-Signature"></a><a id="3264" href="Overture.Signatures.html#3264" class="Function">Level-of-Signature</a> <a id="3283" class="Symbol">:</a> <a id="3285" class="Symbol">{</a><a id="3286" href="Overture.Signatures.html#3286" class="Bound">𝓞</a> <a id="3288" href="Overture.Signatures.html#3288" class="Bound">𝓥</a> <a id="3290" class="Symbol">:</a> <a id="3292" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3297" class="Symbol">}</a> <a id="3299" class="Symbol">→</a> <a id="3301" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="3311" href="Overture.Signatures.html#3286" class="Bound">𝓞</a> <a id="3313" href="Overture.Signatures.html#3288" class="Bound">𝓥</a> <a id="3315" class="Symbol">→</a> <a id="3317" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3323" href="Overture.Signatures.html#3264" class="Function">Level-of-Signature</a> <a id="3342" class="Symbol">{</a><a id="3343" href="Overture.Signatures.html#3343" class="Bound">𝓞</a><a id="3344" class="Symbol">}{</a><a id="3346" href="Overture.Signatures.html#3346" class="Bound">𝓥</a><a id="3347" class="Symbol">}</a> <a id="3349" class="Symbol">_</a> <a id="3351" class="Symbol">=</a> <a id="3353" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3357" class="Symbol">(</a><a id="3358" href="Overture.Signatures.html#3343" class="Bound">𝓞</a> <a id="3360" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3362" href="Overture.Signatures.html#3346" class="Bound">𝓥</a><a id="3363" class="Symbol">)</a>

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
