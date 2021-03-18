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

#### The noncumulative hierarchy

The hierarchy of universe levels in Agda looks like this:

𝓤₀ : 𝓤₁, &nbsp; 𝓤₁ : 𝓤₂, &nbsp; 𝓤₂ : 𝓤₃, …

This means that the type level of 𝓤₀ is 𝓤₁, and for each `n` The type level of 𝓤ₙ is 𝓤ₙ₊₁.

It is important to note, however, this does *not* imply that 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃, and so on.  In other words, Agda's universe hierarchy is **noncummulative**.  This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand (in this author's experience) a noncummulative hierarchy can sometimes make for a nonfun proof assistant.

Fortunately, there are ways to overcome this technical issue. We describe general lifting and lowering functions below, and then later, in the section on [Lifts of algebras](https://ualib.gitlab.io/Algebras.Algebras.html#lifts-of-algebras), we'll see the domain-specific analogs of these tools which turn out to have some nice properties that make them very effective for resolving universe level problems when working with algebra datatypes.

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

<a id="2464" class="Keyword">record</a> <a id="Lift"></a><a id="2471" href="Prelude.Lifts.html#2471" class="Record">Lift</a> <a id="2476" class="Symbol">{</a><a id="2477" href="Prelude.Lifts.html#2477" class="Bound">𝓦</a> <a id="2479" href="Prelude.Lifts.html#2479" class="Bound">𝓤</a> <a id="2481" class="Symbol">:</a> <a id="2483" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2491" class="Symbol">}</a> <a id="2493" class="Symbol">(</a><a id="2494" href="Prelude.Lifts.html#2494" class="Bound">X</a> <a id="2496" class="Symbol">:</a> <a id="2498" href="Prelude.Lifts.html#2479" class="Bound">𝓤</a> <a id="2500" href="Universes.html#403" class="Function Operator">̇</a><a id="2501" class="Symbol">)</a> <a id="2503" class="Symbol">:</a> <a id="2505" href="Prelude.Lifts.html#2479" class="Bound">𝓤</a> <a id="2507" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2509" href="Prelude.Lifts.html#2477" class="Bound">𝓦</a> <a id="2511" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2514" class="Keyword">where</a>
 <a id="2521" class="Keyword">constructor</a> <a id="lift"></a><a id="2533" href="Prelude.Lifts.html#2533" class="InductiveConstructor">lift</a>
 <a id="2539" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2545" href="Prelude.Lifts.html#2545" class="Field">lower</a> <a id="2551" class="Symbol">:</a> <a id="2553" href="Prelude.Lifts.html#2494" class="Bound">X</a>
<a id="2555" class="Keyword">open</a> <a id="2560" href="Prelude.Lifts.html#2471" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="2993" href="Prelude.Lifts.html#2993" class="Function">lift∼lower</a> <a id="3004" class="Symbol">:</a> <a id="3006" class="Symbol">{</a><a id="3007" href="Prelude.Lifts.html#3007" class="Bound">𝓦</a> <a id="3009" href="Prelude.Lifts.html#3009" class="Bound">𝓧</a> <a id="3011" class="Symbol">:</a> <a id="3013" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3021" class="Symbol">}{</a><a id="3023" href="Prelude.Lifts.html#3023" class="Bound">X</a> <a id="3025" class="Symbol">:</a> <a id="3027" href="Prelude.Lifts.html#3009" class="Bound">𝓧</a> <a id="3029" href="Universes.html#403" class="Function Operator">̇</a><a id="3030" class="Symbol">}</a> <a id="3032" class="Symbol">→</a> <a id="3034" href="Prelude.Lifts.html#2533" class="InductiveConstructor">lift</a> <a id="3039" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3041" href="Prelude.Lifts.html#2545" class="Field">lower</a> <a id="3047" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="3049" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3052" class="Symbol">(</a><a id="3053" href="Prelude.Lifts.html#2471" class="Record">Lift</a><a id="3057" class="Symbol">{</a><a id="3058" href="Prelude.Lifts.html#3007" class="Bound">𝓦</a><a id="3059" class="Symbol">}</a> <a id="3061" href="Prelude.Lifts.html#3023" class="Bound">X</a><a id="3062" class="Symbol">)</a>
<a id="3064" href="Prelude.Lifts.html#2993" class="Function">lift∼lower</a> <a id="3075" class="Symbol">=</a> <a id="3077" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3083" href="Prelude.Lifts.html#3083" class="Function">lower∼lift</a> <a id="3094" class="Symbol">:</a> <a id="3096" class="Symbol">{</a><a id="3097" href="Prelude.Lifts.html#3097" class="Bound">𝓦</a> <a id="3099" href="Prelude.Lifts.html#3099" class="Bound">𝓧</a> <a id="3101" class="Symbol">:</a> <a id="3103" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3111" class="Symbol">}{</a><a id="3113" href="Prelude.Lifts.html#3113" class="Bound">X</a> <a id="3115" class="Symbol">:</a> <a id="3117" href="Prelude.Lifts.html#3099" class="Bound">𝓧</a> <a id="3119" href="Universes.html#403" class="Function Operator">̇</a><a id="3120" class="Symbol">}</a> <a id="3122" class="Symbol">→</a> <a id="3124" href="Prelude.Lifts.html#2545" class="Field">lower</a><a id="3129" class="Symbol">{</a><a id="3130" href="Prelude.Lifts.html#3097" class="Bound">𝓦</a><a id="3131" class="Symbol">}{</a><a id="3133" href="Prelude.Lifts.html#3099" class="Bound">𝓧</a><a id="3134" class="Symbol">}</a> <a id="3136" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3138" href="Prelude.Lifts.html#2533" class="InductiveConstructor">lift</a> <a id="3143" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="3145" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3148" href="Prelude.Lifts.html#3113" class="Bound">X</a>
<a id="3150" href="Prelude.Lifts.html#3083" class="Function">lower∼lift</a> <a id="3161" class="Symbol">=</a> <a id="3163" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Evidently, the proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
