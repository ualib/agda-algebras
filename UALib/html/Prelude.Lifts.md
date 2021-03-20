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

<a id="2544" class="Keyword">record</a> <a id="Lift"></a><a id="2551" href="Prelude.Lifts.html#2551" class="Record">Lift</a> <a id="2556" class="Symbol">{</a><a id="2557" href="Prelude.Lifts.html#2557" class="Bound">𝓦</a> <a id="2559" href="Prelude.Lifts.html#2559" class="Bound">𝓤</a> <a id="2561" class="Symbol">:</a> <a id="2563" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2571" class="Symbol">}</a> <a id="2573" class="Symbol">(</a><a id="2574" href="Prelude.Lifts.html#2574" class="Bound">A</a> <a id="2576" class="Symbol">:</a> <a id="2578" href="Prelude.Lifts.html#2559" class="Bound">𝓤</a> <a id="2580" href="Universes.html#403" class="Function Operator">̇</a><a id="2581" class="Symbol">)</a> <a id="2583" class="Symbol">:</a> <a id="2585" href="Prelude.Lifts.html#2559" class="Bound">𝓤</a> <a id="2587" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2589" href="Prelude.Lifts.html#2557" class="Bound">𝓦</a> <a id="2591" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2594" class="Keyword">where</a>
 <a id="2601" class="Keyword">constructor</a> <a id="lift"></a><a id="2613" href="Prelude.Lifts.html#2613" class="InductiveConstructor">lift</a>
 <a id="2619" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2625" href="Prelude.Lifts.html#2625" class="Field">lower</a> <a id="2631" class="Symbol">:</a> <a id="2633" href="Prelude.Lifts.html#2574" class="Bound">A</a>
<a id="2635" class="Keyword">open</a> <a id="2640" href="Prelude.Lifts.html#2551" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3073" href="Prelude.Lifts.html#3073" class="Function">lift∼lower</a> <a id="3084" class="Symbol">:</a> <a id="3086" class="Symbol">{</a><a id="3087" href="Prelude.Lifts.html#3087" class="Bound">𝓦</a> <a id="3089" href="Prelude.Lifts.html#3089" class="Bound">𝓤</a> <a id="3091" class="Symbol">:</a> <a id="3093" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3101" class="Symbol">}{</a><a id="3103" href="Prelude.Lifts.html#3103" class="Bound">A</a> <a id="3105" class="Symbol">:</a> <a id="3107" href="Prelude.Lifts.html#3089" class="Bound">𝓤</a> <a id="3109" href="Universes.html#403" class="Function Operator">̇</a><a id="3110" class="Symbol">}</a> <a id="3112" class="Symbol">→</a> <a id="3114" href="Prelude.Lifts.html#2613" class="InductiveConstructor">lift</a> <a id="3119" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3121" href="Prelude.Lifts.html#2625" class="Field">lower</a> <a id="3127" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3129" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3132" class="Symbol">(</a><a id="3133" href="Prelude.Lifts.html#2551" class="Record">Lift</a><a id="3137" class="Symbol">{</a><a id="3138" href="Prelude.Lifts.html#3087" class="Bound">𝓦</a><a id="3139" class="Symbol">}</a> <a id="3141" href="Prelude.Lifts.html#3103" class="Bound">A</a><a id="3142" class="Symbol">)</a>
<a id="3144" href="Prelude.Lifts.html#3073" class="Function">lift∼lower</a> <a id="3155" class="Symbol">=</a> <a id="3157" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3163" href="Prelude.Lifts.html#3163" class="Function">lower∼lift</a> <a id="3174" class="Symbol">:</a> <a id="3176" class="Symbol">{</a><a id="3177" href="Prelude.Lifts.html#3177" class="Bound">𝓦</a> <a id="3179" href="Prelude.Lifts.html#3179" class="Bound">𝓤</a> <a id="3181" class="Symbol">:</a> <a id="3183" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3191" class="Symbol">}{</a><a id="3193" href="Prelude.Lifts.html#3193" class="Bound">A</a> <a id="3195" class="Symbol">:</a> <a id="3197" href="Prelude.Lifts.html#3179" class="Bound">𝓤</a> <a id="3199" href="Universes.html#403" class="Function Operator">̇</a><a id="3200" class="Symbol">}</a> <a id="3202" class="Symbol">→</a> <a id="3204" href="Prelude.Lifts.html#2625" class="Field">lower</a><a id="3209" class="Symbol">{</a><a id="3210" href="Prelude.Lifts.html#3177" class="Bound">𝓦</a><a id="3211" class="Symbol">}{</a><a id="3213" href="Prelude.Lifts.html#3179" class="Bound">𝓤</a><a id="3214" class="Symbol">}</a> <a id="3216" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3218" href="Prelude.Lifts.html#2613" class="InductiveConstructor">lift</a> <a id="3223" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3225" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3228" href="Prelude.Lifts.html#3193" class="Bound">A</a>
<a id="3230" href="Prelude.Lifts.html#3163" class="Function">lower∼lift</a> <a id="3241" class="Symbol">=</a> <a id="3243" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
