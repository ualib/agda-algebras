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

This means that the universe `𝓤 ̇` has type `𝓤 ⁺ ̇`, and  `𝓤 ⁺ ̇` has type  `𝓤 ⁺ ⁺ ̇`, and so on.  It is important to note, however, this does *not* imply that  `𝓤 ̇ : 𝓤 ⁺ ⁺ ̇`. In other words, Agda's universe hierarchy is *noncumulative*. This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand, a noncumulative hierarchy can sometimes make for a nonfun proof assistant. Specifically, in certain situations, the noncumulativity makes it unduly difficult to convince Agda that a program or proof is correct.

#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
𝓤 != 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].

<pre class="Agda">

<a id="2460" class="Keyword">record</a> <a id="Lift"></a><a id="2467" href="Overture.Lifts.html#2467" class="Record">Lift</a> <a id="2472" class="Symbol">{</a><a id="2473" href="Overture.Lifts.html#2473" class="Bound">𝓦</a> <a id="2475" href="Overture.Lifts.html#2475" class="Bound">𝓤</a> <a id="2477" class="Symbol">:</a> <a id="2479" href="Universes.html#205" class="Postulate">Universe</a><a id="2487" class="Symbol">}</a> <a id="2489" class="Symbol">(</a><a id="2490" href="Overture.Lifts.html#2490" class="Bound">A</a> <a id="2492" class="Symbol">:</a> <a id="2494" href="Overture.Lifts.html#2475" class="Bound">𝓤</a> <a id="2496" href="Universes.html#403" class="Function Operator">̇</a><a id="2497" class="Symbol">)</a> <a id="2499" class="Symbol">:</a> <a id="2501" href="Overture.Lifts.html#2475" class="Bound">𝓤</a> <a id="2503" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2505" href="Overture.Lifts.html#2473" class="Bound">𝓦</a> <a id="2507" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2510" class="Keyword">where</a>
 <a id="2517" class="Keyword">constructor</a> <a id="lift"></a><a id="2529" href="Overture.Lifts.html#2529" class="InductiveConstructor">lift</a>
 <a id="2535" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2541" href="Overture.Lifts.html#2541" class="Field">lower</a> <a id="2547" class="Symbol">:</a> <a id="2549" href="Overture.Lifts.html#2490" class="Bound">A</a>
<a id="2551" class="Keyword">open</a> <a id="2556" href="Overture.Lifts.html#2467" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="2989" href="Overture.Lifts.html#2989" class="Function">lift∼lower</a> <a id="3000" class="Symbol">:</a> <a id="3002" class="Symbol">{</a><a id="3003" href="Overture.Lifts.html#3003" class="Bound">𝓦</a> <a id="3005" href="Overture.Lifts.html#3005" class="Bound">𝓤</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="Universes.html#205" class="Postulate">Universe</a><a id="3017" class="Symbol">}{</a><a id="3019" href="Overture.Lifts.html#3019" class="Bound">A</a> <a id="3021" class="Symbol">:</a> <a id="3023" href="Overture.Lifts.html#3005" class="Bound">𝓤</a> <a id="3025" href="Universes.html#403" class="Function Operator">̇</a><a id="3026" class="Symbol">}</a> <a id="3028" class="Symbol">→</a> <a id="3030" href="Overture.Lifts.html#2529" class="InductiveConstructor">lift</a> <a id="3035" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3037" href="Overture.Lifts.html#2541" class="Field">lower</a> <a id="3043" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3045" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3048" class="Symbol">(</a><a id="3049" href="Overture.Lifts.html#2467" class="Record">Lift</a><a id="3053" class="Symbol">{</a><a id="3054" href="Overture.Lifts.html#3003" class="Bound">𝓦</a><a id="3055" class="Symbol">}</a> <a id="3057" href="Overture.Lifts.html#3019" class="Bound">A</a><a id="3058" class="Symbol">)</a>
<a id="3060" href="Overture.Lifts.html#2989" class="Function">lift∼lower</a> <a id="3071" class="Symbol">=</a> <a id="3073" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3079" href="Overture.Lifts.html#3079" class="Function">lower∼lift</a> <a id="3090" class="Symbol">:</a> <a id="3092" class="Symbol">{</a><a id="3093" href="Overture.Lifts.html#3093" class="Bound">𝓦</a> <a id="3095" href="Overture.Lifts.html#3095" class="Bound">𝓤</a> <a id="3097" class="Symbol">:</a> <a id="3099" href="Universes.html#205" class="Postulate">Universe</a><a id="3107" class="Symbol">}{</a><a id="3109" href="Overture.Lifts.html#3109" class="Bound">A</a> <a id="3111" class="Symbol">:</a> <a id="3113" href="Overture.Lifts.html#3095" class="Bound">𝓤</a> <a id="3115" href="Universes.html#403" class="Function Operator">̇</a><a id="3116" class="Symbol">}</a> <a id="3118" class="Symbol">→</a> <a id="3120" href="Overture.Lifts.html#2541" class="Field">lower</a><a id="3125" class="Symbol">{</a><a id="3126" href="Overture.Lifts.html#3093" class="Bound">𝓦</a><a id="3127" class="Symbol">}{</a><a id="3129" href="Overture.Lifts.html#3095" class="Bound">𝓤</a><a id="3130" class="Symbol">}</a> <a id="3132" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3134" href="Overture.Lifts.html#2529" class="InductiveConstructor">lift</a> <a id="3139" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3141" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3144" href="Overture.Lifts.html#3109" class="Bound">A</a>
<a id="3146" href="Overture.Lifts.html#3079" class="Function">lower∼lift</a> <a id="3157" class="Symbol">=</a> <a id="3159" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.

---------------

<sup>1</sup><span class="footnote" id="fn1">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


<p></p>

[← Overture.Inverses](Overture.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
