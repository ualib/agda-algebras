---
layout: default
title : Prelude.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This section presents the [UALib.Prelude.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="311" class="Symbol">{-#</a> <a id="315" class="Keyword">OPTIONS</a> <a id="323" class="Pragma">--without-K</a> <a id="335" class="Pragma">--exact-split</a> <a id="349" class="Pragma">--safe</a> <a id="356" class="Symbol">#-}</a>

<a id="361" class="Keyword">module</a> <a id="368" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="382" class="Keyword">where</a>

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a> <a id="418" class="Keyword">public</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:

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

<a id="2558" class="Keyword">record</a> <a id="Lift"></a><a id="2565" href="Prelude.Lifts.html#2565" class="Record">Lift</a> <a id="2570" class="Symbol">{</a><a id="2571" href="Prelude.Lifts.html#2571" class="Bound">𝓦</a> <a id="2573" href="Prelude.Lifts.html#2573" class="Bound">𝓤</a> <a id="2575" class="Symbol">:</a> <a id="2577" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2585" class="Symbol">}</a> <a id="2587" class="Symbol">(</a><a id="2588" href="Prelude.Lifts.html#2588" class="Bound">A</a> <a id="2590" class="Symbol">:</a> <a id="2592" href="Prelude.Lifts.html#2573" class="Bound">𝓤</a> <a id="2594" href="Universes.html#403" class="Function Operator">̇</a><a id="2595" class="Symbol">)</a> <a id="2597" class="Symbol">:</a> <a id="2599" href="Prelude.Lifts.html#2573" class="Bound">𝓤</a> <a id="2601" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2603" href="Prelude.Lifts.html#2571" class="Bound">𝓦</a> <a id="2605" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2608" class="Keyword">where</a>
 <a id="2615" class="Keyword">constructor</a> <a id="lift"></a><a id="2627" href="Prelude.Lifts.html#2627" class="InductiveConstructor">lift</a>
 <a id="2633" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2639" href="Prelude.Lifts.html#2639" class="Field">lower</a> <a id="2645" class="Symbol">:</a> <a id="2647" href="Prelude.Lifts.html#2588" class="Bound">A</a>
<a id="2649" class="Keyword">open</a> <a id="2654" href="Prelude.Lifts.html#2565" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3087" href="Prelude.Lifts.html#3087" class="Function">lift∼lower</a> <a id="3098" class="Symbol">:</a> <a id="3100" class="Symbol">{</a><a id="3101" href="Prelude.Lifts.html#3101" class="Bound">𝓦</a> <a id="3103" href="Prelude.Lifts.html#3103" class="Bound">𝓤</a> <a id="3105" class="Symbol">:</a> <a id="3107" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3115" class="Symbol">}{</a><a id="3117" href="Prelude.Lifts.html#3117" class="Bound">A</a> <a id="3119" class="Symbol">:</a> <a id="3121" href="Prelude.Lifts.html#3103" class="Bound">𝓤</a> <a id="3123" href="Universes.html#403" class="Function Operator">̇</a><a id="3124" class="Symbol">}</a> <a id="3126" class="Symbol">→</a> <a id="3128" href="Prelude.Lifts.html#2627" class="InductiveConstructor">lift</a> <a id="3133" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3135" href="Prelude.Lifts.html#2639" class="Field">lower</a> <a id="3141" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3143" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3146" class="Symbol">(</a><a id="3147" href="Prelude.Lifts.html#2565" class="Record">Lift</a><a id="3151" class="Symbol">{</a><a id="3152" href="Prelude.Lifts.html#3101" class="Bound">𝓦</a><a id="3153" class="Symbol">}</a> <a id="3155" href="Prelude.Lifts.html#3117" class="Bound">A</a><a id="3156" class="Symbol">)</a>
<a id="3158" href="Prelude.Lifts.html#3087" class="Function">lift∼lower</a> <a id="3169" class="Symbol">=</a> <a id="3171" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3177" href="Prelude.Lifts.html#3177" class="Function">lower∼lift</a> <a id="3188" class="Symbol">:</a> <a id="3190" class="Symbol">{</a><a id="3191" href="Prelude.Lifts.html#3191" class="Bound">𝓦</a> <a id="3193" href="Prelude.Lifts.html#3193" class="Bound">𝓤</a> <a id="3195" class="Symbol">:</a> <a id="3197" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3205" class="Symbol">}{</a><a id="3207" href="Prelude.Lifts.html#3207" class="Bound">A</a> <a id="3209" class="Symbol">:</a> <a id="3211" href="Prelude.Lifts.html#3193" class="Bound">𝓤</a> <a id="3213" href="Universes.html#403" class="Function Operator">̇</a><a id="3214" class="Symbol">}</a> <a id="3216" class="Symbol">→</a> <a id="3218" href="Prelude.Lifts.html#2639" class="Field">lower</a><a id="3223" class="Symbol">{</a><a id="3224" href="Prelude.Lifts.html#3191" class="Bound">𝓦</a><a id="3225" class="Symbol">}{</a><a id="3227" href="Prelude.Lifts.html#3193" class="Bound">𝓤</a><a id="3228" class="Symbol">}</a> <a id="3230" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3232" href="Prelude.Lifts.html#2627" class="InductiveConstructor">lift</a> <a id="3237" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3239" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3242" href="Prelude.Lifts.html#3207" class="Bound">A</a>
<a id="3244" href="Prelude.Lifts.html#3177" class="Function">lower∼lift</a> <a id="3255" class="Symbol">=</a> <a id="3257" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Evidently, the proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
