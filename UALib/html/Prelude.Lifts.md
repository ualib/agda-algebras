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

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="424" class="Keyword">public</a>

</pre>

#### The noncumulative hierarchy

The hierarchy of universe levels in Agda looks like this:

𝓤₀ : 𝓤₁, &nbsp; 𝓤₁ : 𝓤₂, &nbsp; 𝓤₂ : 𝓤₃, …

This means that the type level of 𝓤₀ is 𝓤₁, and for each `n` The type level of 𝓤ₙ is 𝓤ₙ₊₁.

It is important to note, however, this does *not* imply that 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃, and so on.  In other words, Agda's universe hierarchy is **noncummulative**.  This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand (in this author's experience) a noncummulative hierarchy can sometimes make for a nonfun proof assistant.

Luckily, there are ways to overcome this technical issue, and we describe some such techniques we developed specifically for our domain.

#### Lifting and lowering

Let us be more concrete about what is at issue here by giving an example. Agda will often complain with errors like the following:

```
Birkhoff.lagda:498,20-23
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)
when checking that the expression SP𝒦 has type
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346
```

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda` file, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the [Agda Standard Library][] (in the `Level` module), is defined as follows.

<pre class="Agda">

<a id="2405" class="Keyword">record</a> <a id="Lift"></a><a id="2412" href="Prelude.Lifts.html#2412" class="Record">Lift</a> <a id="2417" class="Symbol">{</a><a id="2418" href="Prelude.Lifts.html#2418" class="Bound">𝓤</a> <a id="2420" href="Prelude.Lifts.html#2420" class="Bound">𝓦</a> <a id="2422" class="Symbol">:</a> <a id="2424" href="universes.html#551" class="Postulate">Universe</a><a id="2432" class="Symbol">}</a> <a id="2434" class="Symbol">(</a><a id="2435" href="Prelude.Lifts.html#2435" class="Bound">X</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="Prelude.Lifts.html#2418" class="Bound">𝓤</a> <a id="2441" href="universes.html#758" class="Function Operator">̇</a><a id="2442" class="Symbol">)</a> <a id="2444" class="Symbol">:</a> <a id="2446" href="Prelude.Lifts.html#2418" class="Bound">𝓤</a> <a id="2448" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2450" href="Prelude.Lifts.html#2420" class="Bound">𝓦</a> <a id="2452" href="universes.html#758" class="Function Operator">̇</a>  <a id="2455" class="Keyword">where</a>
 <a id="2462" class="Keyword">constructor</a> <a id="lift"></a><a id="2474" href="Prelude.Lifts.html#2474" class="InductiveConstructor">lift</a>
 <a id="2480" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2486" href="Prelude.Lifts.html#2486" class="Field">lower</a> <a id="2492" class="Symbol">:</a> <a id="2494" href="Prelude.Lifts.html#2435" class="Bound">X</a>
<a id="2496" class="Keyword">open</a> <a id="2501" href="Prelude.Lifts.html#2412" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2585" href="Prelude.Lifts.html#2585" class="Function">lift-dom</a> <a id="2594" class="Symbol">:</a> <a id="2596" class="Symbol">{</a><a id="2597" href="Prelude.Lifts.html#2597" class="Bound">𝓧</a> <a id="2599" href="Prelude.Lifts.html#2599" class="Bound">𝓨</a> <a id="2601" href="Prelude.Lifts.html#2601" class="Bound">𝓦</a> <a id="2603" class="Symbol">:</a> <a id="2605" href="universes.html#551" class="Postulate">Universe</a><a id="2613" class="Symbol">}{</a><a id="2615" href="Prelude.Lifts.html#2615" class="Bound">X</a> <a id="2617" class="Symbol">:</a> <a id="2619" href="Prelude.Lifts.html#2597" class="Bound">𝓧</a> <a id="2621" href="universes.html#758" class="Function Operator">̇</a><a id="2622" class="Symbol">}{</a><a id="2624" href="Prelude.Lifts.html#2624" class="Bound">Y</a> <a id="2626" class="Symbol">:</a> <a id="2628" href="Prelude.Lifts.html#2599" class="Bound">𝓨</a> <a id="2630" href="universes.html#758" class="Function Operator">̇</a><a id="2631" class="Symbol">}</a> <a id="2633" class="Symbol">→</a> <a id="2635" class="Symbol">(</a><a id="2636" href="Prelude.Lifts.html#2615" class="Bound">X</a> <a id="2638" class="Symbol">→</a> <a id="2640" href="Prelude.Lifts.html#2624" class="Bound">Y</a><a id="2641" class="Symbol">)</a> <a id="2643" class="Symbol">→</a> <a id="2645" class="Symbol">(</a><a id="2646" href="Prelude.Lifts.html#2412" class="Record">Lift</a><a id="2650" class="Symbol">{</a><a id="2651" href="Prelude.Lifts.html#2597" class="Bound">𝓧</a><a id="2652" class="Symbol">}{</a><a id="2654" href="Prelude.Lifts.html#2601" class="Bound">𝓦</a><a id="2655" class="Symbol">}</a> <a id="2657" href="Prelude.Lifts.html#2615" class="Bound">X</a> <a id="2659" class="Symbol">→</a> <a id="2661" href="Prelude.Lifts.html#2624" class="Bound">Y</a><a id="2662" class="Symbol">)</a>
<a id="2664" href="Prelude.Lifts.html#2585" class="Function">lift-dom</a> <a id="2673" href="Prelude.Lifts.html#2673" class="Bound">f</a> <a id="2675" class="Symbol">=</a> <a id="2677" class="Symbol">λ</a> <a id="2679" href="Prelude.Lifts.html#2679" class="Bound">x</a> <a id="2681" class="Symbol">→</a> <a id="2683" class="Symbol">(</a><a id="2684" href="Prelude.Lifts.html#2673" class="Bound">f</a> <a id="2686" class="Symbol">(</a><a id="2687" href="Prelude.Lifts.html#2486" class="Field">lower</a> <a id="2693" href="Prelude.Lifts.html#2679" class="Bound">x</a><a id="2694" class="Symbol">))</a>

<a id="lift-cod"></a><a id="2698" href="Prelude.Lifts.html#2698" class="Function">lift-cod</a> <a id="2707" class="Symbol">:</a> <a id="2709" class="Symbol">{</a><a id="2710" href="Prelude.Lifts.html#2710" class="Bound">𝓧</a> <a id="2712" href="Prelude.Lifts.html#2712" class="Bound">𝓨</a> <a id="2714" href="Prelude.Lifts.html#2714" class="Bound">𝓦</a> <a id="2716" class="Symbol">:</a> <a id="2718" href="universes.html#551" class="Postulate">Universe</a><a id="2726" class="Symbol">}{</a><a id="2728" href="Prelude.Lifts.html#2728" class="Bound">X</a> <a id="2730" class="Symbol">:</a> <a id="2732" href="Prelude.Lifts.html#2710" class="Bound">𝓧</a> <a id="2734" href="universes.html#758" class="Function Operator">̇</a><a id="2735" class="Symbol">}{</a><a id="2737" href="Prelude.Lifts.html#2737" class="Bound">Y</a> <a id="2739" class="Symbol">:</a> <a id="2741" href="Prelude.Lifts.html#2712" class="Bound">𝓨</a> <a id="2743" href="universes.html#758" class="Function Operator">̇</a><a id="2744" class="Symbol">}</a> <a id="2746" class="Symbol">→</a> <a id="2748" class="Symbol">(</a><a id="2749" href="Prelude.Lifts.html#2728" class="Bound">X</a> <a id="2751" class="Symbol">→</a> <a id="2753" href="Prelude.Lifts.html#2737" class="Bound">Y</a><a id="2754" class="Symbol">)</a> <a id="2756" class="Symbol">→</a> <a id="2758" class="Symbol">(</a><a id="2759" href="Prelude.Lifts.html#2728" class="Bound">X</a> <a id="2761" class="Symbol">→</a> <a id="2763" href="Prelude.Lifts.html#2412" class="Record">Lift</a><a id="2767" class="Symbol">{</a><a id="2768" href="Prelude.Lifts.html#2712" class="Bound">𝓨</a><a id="2769" class="Symbol">}{</a><a id="2771" href="Prelude.Lifts.html#2714" class="Bound">𝓦</a><a id="2772" class="Symbol">}</a> <a id="2774" href="Prelude.Lifts.html#2737" class="Bound">Y</a><a id="2775" class="Symbol">)</a>
<a id="2777" href="Prelude.Lifts.html#2698" class="Function">lift-cod</a> <a id="2786" href="Prelude.Lifts.html#2786" class="Bound">f</a> <a id="2788" class="Symbol">=</a> <a id="2790" class="Symbol">λ</a> <a id="2792" href="Prelude.Lifts.html#2792" class="Bound">x</a> <a id="2794" class="Symbol">→</a> <a id="2796" href="Prelude.Lifts.html#2474" class="InductiveConstructor">lift</a> <a id="2801" class="Symbol">(</a><a id="2802" href="Prelude.Lifts.html#2786" class="Bound">f</a> <a id="2804" href="Prelude.Lifts.html#2792" class="Bound">x</a><a id="2805" class="Symbol">)</a>

<a id="lift-fun"></a><a id="2808" href="Prelude.Lifts.html#2808" class="Function">lift-fun</a> <a id="2817" class="Symbol">:</a> <a id="2819" class="Symbol">{</a><a id="2820" href="Prelude.Lifts.html#2820" class="Bound">𝓧</a> <a id="2822" href="Prelude.Lifts.html#2822" class="Bound">𝓨</a> <a id="2824" href="Prelude.Lifts.html#2824" class="Bound">𝓦</a> <a id="2826" href="Prelude.Lifts.html#2826" class="Bound">𝓩</a> <a id="2828" class="Symbol">:</a> <a id="2830" href="universes.html#551" class="Postulate">Universe</a><a id="2838" class="Symbol">}{</a><a id="2840" href="Prelude.Lifts.html#2840" class="Bound">X</a> <a id="2842" class="Symbol">:</a> <a id="2844" href="Prelude.Lifts.html#2820" class="Bound">𝓧</a> <a id="2846" href="universes.html#758" class="Function Operator">̇</a><a id="2847" class="Symbol">}{</a><a id="2849" href="Prelude.Lifts.html#2849" class="Bound">Y</a> <a id="2851" class="Symbol">:</a> <a id="2853" href="Prelude.Lifts.html#2822" class="Bound">𝓨</a> <a id="2855" href="universes.html#758" class="Function Operator">̇</a><a id="2856" class="Symbol">}</a> <a id="2858" class="Symbol">→</a> <a id="2860" class="Symbol">(</a><a id="2861" href="Prelude.Lifts.html#2840" class="Bound">X</a> <a id="2863" class="Symbol">→</a> <a id="2865" href="Prelude.Lifts.html#2849" class="Bound">Y</a><a id="2866" class="Symbol">)</a> <a id="2868" class="Symbol">→</a> <a id="2870" class="Symbol">(</a><a id="2871" href="Prelude.Lifts.html#2412" class="Record">Lift</a><a id="2875" class="Symbol">{</a><a id="2876" href="Prelude.Lifts.html#2820" class="Bound">𝓧</a><a id="2877" class="Symbol">}{</a><a id="2879" href="Prelude.Lifts.html#2824" class="Bound">𝓦</a><a id="2880" class="Symbol">}</a> <a id="2882" href="Prelude.Lifts.html#2840" class="Bound">X</a> <a id="2884" class="Symbol">→</a> <a id="2886" href="Prelude.Lifts.html#2412" class="Record">Lift</a><a id="2890" class="Symbol">{</a><a id="2891" href="Prelude.Lifts.html#2822" class="Bound">𝓨</a><a id="2892" class="Symbol">}{</a><a id="2894" href="Prelude.Lifts.html#2826" class="Bound">𝓩</a><a id="2895" class="Symbol">}</a> <a id="2897" href="Prelude.Lifts.html#2849" class="Bound">Y</a><a id="2898" class="Symbol">)</a>
<a id="2900" href="Prelude.Lifts.html#2808" class="Function">lift-fun</a> <a id="2909" href="Prelude.Lifts.html#2909" class="Bound">f</a> <a id="2911" class="Symbol">=</a> <a id="2913" class="Symbol">λ</a> <a id="2915" href="Prelude.Lifts.html#2915" class="Bound">x</a> <a id="2917" class="Symbol">→</a> <a id="2919" href="Prelude.Lifts.html#2474" class="InductiveConstructor">lift</a> <a id="2924" class="Symbol">(</a><a id="2925" href="Prelude.Lifts.html#2909" class="Bound">f</a> <a id="2927" class="Symbol">(</a><a id="2928" href="Prelude.Lifts.html#2486" class="Field">lower</a> <a id="2934" href="Prelude.Lifts.html#2915" class="Bound">x</a><a id="2935" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3037" href="Prelude.Lifts.html#3037" class="Function">lower∼lift</a> <a id="3048" class="Symbol">:</a> <a id="3050" class="Symbol">{</a><a id="3051" href="Prelude.Lifts.html#3051" class="Bound">𝓧</a> <a id="3053" href="Prelude.Lifts.html#3053" class="Bound">𝓦</a> <a id="3055" class="Symbol">:</a> <a id="3057" href="universes.html#551" class="Postulate">Universe</a><a id="3065" class="Symbol">}{</a><a id="3067" href="Prelude.Lifts.html#3067" class="Bound">X</a> <a id="3069" class="Symbol">:</a> <a id="3071" href="Prelude.Lifts.html#3051" class="Bound">𝓧</a> <a id="3073" href="universes.html#758" class="Function Operator">̇</a><a id="3074" class="Symbol">}</a> <a id="3076" class="Symbol">→</a> <a id="3078" href="Prelude.Lifts.html#2486" class="Field">lower</a><a id="3083" class="Symbol">{</a><a id="3084" href="Prelude.Lifts.html#3051" class="Bound">𝓧</a><a id="3085" class="Symbol">}{</a><a id="3087" href="Prelude.Lifts.html#3053" class="Bound">𝓦</a><a id="3088" class="Symbol">}</a> <a id="3090" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3092" href="Prelude.Lifts.html#2474" class="InductiveConstructor">lift</a> <a id="3097" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="3099" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3102" href="Prelude.Lifts.html#3067" class="Bound">X</a>
<a id="3104" href="Prelude.Lifts.html#3037" class="Function">lower∼lift</a> <a id="3115" class="Symbol">=</a> <a id="3117" href="Prelude.Equality.html#1961" class="InductiveConstructor">refl</a> <a id="3122" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3125" href="Prelude.Lifts.html#3125" class="Function">lift∼lower</a> <a id="3136" class="Symbol">:</a> <a id="3138" class="Symbol">{</a><a id="3139" href="Prelude.Lifts.html#3139" class="Bound">𝓧</a> <a id="3141" href="Prelude.Lifts.html#3141" class="Bound">𝓦</a> <a id="3143" class="Symbol">:</a> <a id="3145" href="universes.html#551" class="Postulate">Universe</a><a id="3153" class="Symbol">}{</a><a id="3155" href="Prelude.Lifts.html#3155" class="Bound">X</a> <a id="3157" class="Symbol">:</a> <a id="3159" href="Prelude.Lifts.html#3139" class="Bound">𝓧</a> <a id="3161" href="universes.html#758" class="Function Operator">̇</a><a id="3162" class="Symbol">}</a> <a id="3164" class="Symbol">→</a> <a id="3166" href="Prelude.Lifts.html#2474" class="InductiveConstructor">lift</a> <a id="3171" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3173" href="Prelude.Lifts.html#2486" class="Field">lower</a> <a id="3179" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="3181" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3184" class="Symbol">(</a><a id="3185" href="Prelude.Lifts.html#2412" class="Record">Lift</a><a id="3189" class="Symbol">{</a><a id="3190" href="Prelude.Lifts.html#3139" class="Bound">𝓧</a><a id="3191" class="Symbol">}{</a><a id="3193" href="Prelude.Lifts.html#3141" class="Bound">𝓦</a><a id="3194" class="Symbol">}</a> <a id="3196" href="Prelude.Lifts.html#3155" class="Bound">X</a><a id="3197" class="Symbol">)</a>
<a id="3199" href="Prelude.Lifts.html#3125" class="Function">lift∼lower</a> <a id="3210" class="Symbol">=</a> <a id="3212" href="Prelude.Equality.html#1961" class="InductiveConstructor">refl</a> <a id="3217" class="Symbol">_</a>

</pre>


---------------

[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
