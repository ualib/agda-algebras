---
layout: default
title : Overture.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This is the [Overture.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="293" class="Symbol">{-#</a> <a id="297" class="Keyword">OPTIONS</a> <a id="305" class="Pragma">--without-K</a> <a id="317" class="Pragma">--exact-split</a> <a id="331" class="Pragma">--safe</a> <a id="338" class="Symbol">#-}</a>

<a id="343" class="Keyword">module</a> <a id="350" href="Overture.Lifts.html" class="Module">Overture.Lifts</a> <a id="365" class="Keyword">where</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="Overture.Inverses.html" class="Module">Overture.Inverses</a> <a id="402" class="Keyword">public</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

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

<a id="2581" class="Keyword">record</a> <a id="Lift"></a><a id="2588" href="Overture.Lifts.html#2588" class="Record">Lift</a> <a id="2593" class="Symbol">{</a><a id="2594" href="Overture.Lifts.html#2594" class="Bound">𝓦</a> <a id="2596" href="Overture.Lifts.html#2596" class="Bound">𝓤</a> <a id="2598" class="Symbol">:</a> <a id="2600" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2608" class="Symbol">}</a> <a id="2610" class="Symbol">(</a><a id="2611" href="Overture.Lifts.html#2611" class="Bound">A</a> <a id="2613" class="Symbol">:</a> <a id="2615" href="Overture.Lifts.html#2596" class="Bound">𝓤</a> <a id="2617" href="Universes.html#403" class="Function Operator">̇</a><a id="2618" class="Symbol">)</a> <a id="2620" class="Symbol">:</a> <a id="2622" href="Overture.Lifts.html#2596" class="Bound">𝓤</a> <a id="2624" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2626" href="Overture.Lifts.html#2594" class="Bound">𝓦</a> <a id="2628" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2631" class="Keyword">where</a>
 <a id="2638" class="Keyword">constructor</a> <a id="lift"></a><a id="2650" href="Overture.Lifts.html#2650" class="InductiveConstructor">lift</a>
 <a id="2656" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2662" href="Overture.Lifts.html#2662" class="Field">lower</a> <a id="2668" class="Symbol">:</a> <a id="2670" href="Overture.Lifts.html#2611" class="Bound">A</a>
<a id="2672" class="Keyword">open</a> <a id="2677" href="Overture.Lifts.html#2588" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3110" href="Overture.Lifts.html#3110" class="Function">lift∼lower</a> <a id="3121" class="Symbol">:</a> <a id="3123" class="Symbol">{</a><a id="3124" href="Overture.Lifts.html#3124" class="Bound">𝓦</a> <a id="3126" href="Overture.Lifts.html#3126" class="Bound">𝓤</a> <a id="3128" class="Symbol">:</a> <a id="3130" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3138" class="Symbol">}{</a><a id="3140" href="Overture.Lifts.html#3140" class="Bound">A</a> <a id="3142" class="Symbol">:</a> <a id="3144" href="Overture.Lifts.html#3126" class="Bound">𝓤</a> <a id="3146" href="Universes.html#403" class="Function Operator">̇</a><a id="3147" class="Symbol">}</a> <a id="3149" class="Symbol">→</a> <a id="3151" href="Overture.Lifts.html#2650" class="InductiveConstructor">lift</a> <a id="3156" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3158" href="Overture.Lifts.html#2662" class="Field">lower</a> <a id="3164" href="Overture.Equality.html#2564" class="Datatype Operator">≡</a> <a id="3166" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3169" class="Symbol">(</a><a id="3170" href="Overture.Lifts.html#2588" class="Record">Lift</a><a id="3174" class="Symbol">{</a><a id="3175" href="Overture.Lifts.html#3124" class="Bound">𝓦</a><a id="3176" class="Symbol">}</a> <a id="3178" href="Overture.Lifts.html#3140" class="Bound">A</a><a id="3179" class="Symbol">)</a>
<a id="3181" href="Overture.Lifts.html#3110" class="Function">lift∼lower</a> <a id="3192" class="Symbol">=</a> <a id="3194" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3200" href="Overture.Lifts.html#3200" class="Function">lower∼lift</a> <a id="3211" class="Symbol">:</a> <a id="3213" class="Symbol">{</a><a id="3214" href="Overture.Lifts.html#3214" class="Bound">𝓦</a> <a id="3216" href="Overture.Lifts.html#3216" class="Bound">𝓤</a> <a id="3218" class="Symbol">:</a> <a id="3220" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3228" class="Symbol">}{</a><a id="3230" href="Overture.Lifts.html#3230" class="Bound">A</a> <a id="3232" class="Symbol">:</a> <a id="3234" href="Overture.Lifts.html#3216" class="Bound">𝓤</a> <a id="3236" href="Universes.html#403" class="Function Operator">̇</a><a id="3237" class="Symbol">}</a> <a id="3239" class="Symbol">→</a> <a id="3241" href="Overture.Lifts.html#2662" class="Field">lower</a><a id="3246" class="Symbol">{</a><a id="3247" href="Overture.Lifts.html#3214" class="Bound">𝓦</a><a id="3248" class="Symbol">}{</a><a id="3250" href="Overture.Lifts.html#3216" class="Bound">𝓤</a><a id="3251" class="Symbol">}</a> <a id="3253" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3255" href="Overture.Lifts.html#2650" class="InductiveConstructor">lift</a> <a id="3260" href="Overture.Equality.html#2564" class="Datatype Operator">≡</a> <a id="3262" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3265" href="Overture.Lifts.html#3230" class="Bound">A</a>
<a id="3267" href="Overture.Lifts.html#3200" class="Function">lower∼lift</a> <a id="3278" class="Symbol">=</a> <a id="3280" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<sup>1</sup><span class="footnote" id="fn1">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


<p></p>

[← Overture.Inverses](Overture.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
