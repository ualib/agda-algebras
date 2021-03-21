---
layout: default
title : Prelude.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This is the [UALib.Prelude.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="297" class="Symbol">{-#</a> <a id="301" class="Keyword">OPTIONS</a> <a id="309" class="Pragma">--without-K</a> <a id="321" class="Pragma">--exact-split</a> <a id="335" class="Pragma">--safe</a> <a id="342" class="Symbol">#-}</a>

<a id="347" class="Keyword">module</a> <a id="354" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="368" class="Keyword">where</a>

<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a> <a id="404" class="Keyword">public</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Prelude.Lifts.html#fn1)</sup>

```agda
𝓤 ̇ : 𝓤 ⁺ ̇,   𝓤 ⁺ ̇ : 𝓤 ⁺ ⁺ ̇,  etc.
```

This means that the universe `𝓤 ̇` has type `𝓤 ⁺ ̇`, and  `𝓤 ⁺ ̇` has type  `𝓤 ⁺ ⁺ ̇`, and so on.  It is important to note, however, this does *not* imply that  `𝓤 ̇ : 𝓤 ⁺ ⁺ ̇`. In other words, Agda's universe hierarchy is *noncummulative*. This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand, a noncummulative hierarchy can sometimes make for a nonfun proof assistant. Specifically, in certain situations, the noncummulativity makes it unduly difficult to convince Agda that a program or proof is correct.

Presently, we will describe general lifting and lowering functions that help us overcome this technical issue. Later (in the [Lifts of Algebras](Algebras.Algebras.html#lifts-of-algebras) section) we provide some domain-specific analogs of these tools. We will prove some nice properties that make these effective mechanisms for resolving universe level problems when working with algebra types.

#### <a id="lifting-and-lowering">Lifting and lowering</a>

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
𝓤 != 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

There are some general "lifting and lowering" tools that make these situations easier to deal with. These must be applied with some care to avoid making the type theory inconsistent. In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the `Level` module of the [Agda Standard Library][], is defined as follows.

<pre class="Agda">

<a id="2582" class="Keyword">record</a> <a id="Lift"></a><a id="2589" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="2594" class="Symbol">{</a><a id="2595" href="Prelude.Lifts.html#2595" class="Bound">𝓦</a> <a id="2597" href="Prelude.Lifts.html#2597" class="Bound">𝓤</a> <a id="2599" class="Symbol">:</a> <a id="2601" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2609" class="Symbol">}</a> <a id="2611" class="Symbol">(</a><a id="2612" href="Prelude.Lifts.html#2612" class="Bound">A</a> <a id="2614" class="Symbol">:</a> <a id="2616" href="Prelude.Lifts.html#2597" class="Bound">𝓤</a> <a id="2618" href="Universes.html#403" class="Function Operator">̇</a><a id="2619" class="Symbol">)</a> <a id="2621" class="Symbol">:</a> <a id="2623" href="Prelude.Lifts.html#2597" class="Bound">𝓤</a> <a id="2625" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2627" href="Prelude.Lifts.html#2595" class="Bound">𝓦</a> <a id="2629" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2632" class="Keyword">where</a>
 <a id="2639" class="Keyword">constructor</a> <a id="lift"></a><a id="2651" href="Prelude.Lifts.html#2651" class="InductiveConstructor">lift</a>
 <a id="2657" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2663" href="Prelude.Lifts.html#2663" class="Field">lower</a> <a id="2669" class="Symbol">:</a> <a id="2671" href="Prelude.Lifts.html#2612" class="Bound">A</a>
<a id="2673" class="Keyword">open</a> <a id="2678" href="Prelude.Lifts.html#2589" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3111" href="Prelude.Lifts.html#3111" class="Function">lift∼lower</a> <a id="3122" class="Symbol">:</a> <a id="3124" class="Symbol">{</a><a id="3125" href="Prelude.Lifts.html#3125" class="Bound">𝓦</a> <a id="3127" href="Prelude.Lifts.html#3127" class="Bound">𝓤</a> <a id="3129" class="Symbol">:</a> <a id="3131" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3139" class="Symbol">}{</a><a id="3141" href="Prelude.Lifts.html#3141" class="Bound">A</a> <a id="3143" class="Symbol">:</a> <a id="3145" href="Prelude.Lifts.html#3127" class="Bound">𝓤</a> <a id="3147" href="Universes.html#403" class="Function Operator">̇</a><a id="3148" class="Symbol">}</a> <a id="3150" class="Symbol">→</a> <a id="3152" href="Prelude.Lifts.html#2651" class="InductiveConstructor">lift</a> <a id="3157" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3159" href="Prelude.Lifts.html#2663" class="Field">lower</a> <a id="3165" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3167" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3170" class="Symbol">(</a><a id="3171" href="Prelude.Lifts.html#2589" class="Record">Lift</a><a id="3175" class="Symbol">{</a><a id="3176" href="Prelude.Lifts.html#3125" class="Bound">𝓦</a><a id="3177" class="Symbol">}</a> <a id="3179" href="Prelude.Lifts.html#3141" class="Bound">A</a><a id="3180" class="Symbol">)</a>
<a id="3182" href="Prelude.Lifts.html#3111" class="Function">lift∼lower</a> <a id="3193" class="Symbol">=</a> <a id="3195" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3201" href="Prelude.Lifts.html#3201" class="Function">lower∼lift</a> <a id="3212" class="Symbol">:</a> <a id="3214" class="Symbol">{</a><a id="3215" href="Prelude.Lifts.html#3215" class="Bound">𝓦</a> <a id="3217" href="Prelude.Lifts.html#3217" class="Bound">𝓤</a> <a id="3219" class="Symbol">:</a> <a id="3221" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3229" class="Symbol">}{</a><a id="3231" href="Prelude.Lifts.html#3231" class="Bound">A</a> <a id="3233" class="Symbol">:</a> <a id="3235" href="Prelude.Lifts.html#3217" class="Bound">𝓤</a> <a id="3237" href="Universes.html#403" class="Function Operator">̇</a><a id="3238" class="Symbol">}</a> <a id="3240" class="Symbol">→</a> <a id="3242" href="Prelude.Lifts.html#2663" class="Field">lower</a><a id="3247" class="Symbol">{</a><a id="3248" href="Prelude.Lifts.html#3215" class="Bound">𝓦</a><a id="3249" class="Symbol">}{</a><a id="3251" href="Prelude.Lifts.html#3217" class="Bound">𝓤</a><a id="3252" class="Symbol">}</a> <a id="3254" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3256" href="Prelude.Lifts.html#2651" class="InductiveConstructor">lift</a> <a id="3261" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3263" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3266" href="Prelude.Lifts.html#3231" class="Bound">A</a>
<a id="3268" href="Prelude.Lifts.html#3201" class="Function">lower∼lift</a> <a id="3279" class="Symbol">=</a> <a id="3281" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<sup>1</sup><span class="footnote" id="fn1">Recall, from the [Prelude.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
