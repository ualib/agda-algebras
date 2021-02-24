---
layout: default
title : UALib.Prelude.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This section presents the [UALib.Prelude.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="317" class="Symbol">{-#</a> <a id="321" class="Keyword">OPTIONS</a> <a id="329" class="Pragma">--without-K</a> <a id="341" class="Pragma">--exact-split</a> <a id="355" class="Pragma">--safe</a> <a id="362" class="Symbol">#-}</a>

<a id="367" class="Keyword">module</a> <a id="374" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="388" class="Keyword">where</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="430" class="Keyword">public</a>

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

<a id="2411" class="Keyword">record</a> <a id="Lift"></a><a id="2418" href="Prelude.Lifts.html#2418" class="Record">Lift</a> <a id="2423" class="Symbol">{</a><a id="2424" href="Prelude.Lifts.html#2424" class="Bound">𝓤</a> <a id="2426" href="Prelude.Lifts.html#2426" class="Bound">𝓦</a> <a id="2428" class="Symbol">:</a> <a id="2430" href="universes.html#551" class="Postulate">Universe</a><a id="2438" class="Symbol">}</a> <a id="2440" class="Symbol">(</a><a id="2441" href="Prelude.Lifts.html#2441" class="Bound">X</a> <a id="2443" class="Symbol">:</a> <a id="2445" href="Prelude.Lifts.html#2424" class="Bound">𝓤</a> <a id="2447" href="universes.html#758" class="Function Operator">̇</a><a id="2448" class="Symbol">)</a> <a id="2450" class="Symbol">:</a> <a id="2452" href="Prelude.Lifts.html#2424" class="Bound">𝓤</a> <a id="2454" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2456" href="Prelude.Lifts.html#2426" class="Bound">𝓦</a> <a id="2458" href="universes.html#758" class="Function Operator">̇</a>  <a id="2461" class="Keyword">where</a>
 <a id="2468" class="Keyword">constructor</a> <a id="lift"></a><a id="2480" href="Prelude.Lifts.html#2480" class="InductiveConstructor">lift</a>
 <a id="2486" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2492" href="Prelude.Lifts.html#2492" class="Field">lower</a> <a id="2498" class="Symbol">:</a> <a id="2500" href="Prelude.Lifts.html#2441" class="Bound">X</a>
<a id="2502" class="Keyword">open</a> <a id="2507" href="Prelude.Lifts.html#2418" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2591" href="Prelude.Lifts.html#2591" class="Function">lift-dom</a> <a id="2600" class="Symbol">:</a> <a id="2602" class="Symbol">{</a><a id="2603" href="Prelude.Lifts.html#2603" class="Bound">𝓧</a> <a id="2605" href="Prelude.Lifts.html#2605" class="Bound">𝓨</a> <a id="2607" href="Prelude.Lifts.html#2607" class="Bound">𝓦</a> <a id="2609" class="Symbol">:</a> <a id="2611" href="universes.html#551" class="Postulate">Universe</a><a id="2619" class="Symbol">}{</a><a id="2621" href="Prelude.Lifts.html#2621" class="Bound">X</a> <a id="2623" class="Symbol">:</a> <a id="2625" href="Prelude.Lifts.html#2603" class="Bound">𝓧</a> <a id="2627" href="universes.html#758" class="Function Operator">̇</a><a id="2628" class="Symbol">}{</a><a id="2630" href="Prelude.Lifts.html#2630" class="Bound">Y</a> <a id="2632" class="Symbol">:</a> <a id="2634" href="Prelude.Lifts.html#2605" class="Bound">𝓨</a> <a id="2636" href="universes.html#758" class="Function Operator">̇</a><a id="2637" class="Symbol">}</a> <a id="2639" class="Symbol">→</a> <a id="2641" class="Symbol">(</a><a id="2642" href="Prelude.Lifts.html#2621" class="Bound">X</a> <a id="2644" class="Symbol">→</a> <a id="2646" href="Prelude.Lifts.html#2630" class="Bound">Y</a><a id="2647" class="Symbol">)</a> <a id="2649" class="Symbol">→</a> <a id="2651" class="Symbol">(</a><a id="2652" href="Prelude.Lifts.html#2418" class="Record">Lift</a><a id="2656" class="Symbol">{</a><a id="2657" href="Prelude.Lifts.html#2603" class="Bound">𝓧</a><a id="2658" class="Symbol">}{</a><a id="2660" href="Prelude.Lifts.html#2607" class="Bound">𝓦</a><a id="2661" class="Symbol">}</a> <a id="2663" href="Prelude.Lifts.html#2621" class="Bound">X</a> <a id="2665" class="Symbol">→</a> <a id="2667" href="Prelude.Lifts.html#2630" class="Bound">Y</a><a id="2668" class="Symbol">)</a>
<a id="2670" href="Prelude.Lifts.html#2591" class="Function">lift-dom</a> <a id="2679" href="Prelude.Lifts.html#2679" class="Bound">f</a> <a id="2681" class="Symbol">=</a> <a id="2683" class="Symbol">λ</a> <a id="2685" href="Prelude.Lifts.html#2685" class="Bound">x</a> <a id="2687" class="Symbol">→</a> <a id="2689" class="Symbol">(</a><a id="2690" href="Prelude.Lifts.html#2679" class="Bound">f</a> <a id="2692" class="Symbol">(</a><a id="2693" href="Prelude.Lifts.html#2492" class="Field">lower</a> <a id="2699" href="Prelude.Lifts.html#2685" class="Bound">x</a><a id="2700" class="Symbol">))</a>

<a id="lift-cod"></a><a id="2704" href="Prelude.Lifts.html#2704" class="Function">lift-cod</a> <a id="2713" class="Symbol">:</a> <a id="2715" class="Symbol">{</a><a id="2716" href="Prelude.Lifts.html#2716" class="Bound">𝓧</a> <a id="2718" href="Prelude.Lifts.html#2718" class="Bound">𝓨</a> <a id="2720" href="Prelude.Lifts.html#2720" class="Bound">𝓦</a> <a id="2722" class="Symbol">:</a> <a id="2724" href="universes.html#551" class="Postulate">Universe</a><a id="2732" class="Symbol">}{</a><a id="2734" href="Prelude.Lifts.html#2734" class="Bound">X</a> <a id="2736" class="Symbol">:</a> <a id="2738" href="Prelude.Lifts.html#2716" class="Bound">𝓧</a> <a id="2740" href="universes.html#758" class="Function Operator">̇</a><a id="2741" class="Symbol">}{</a><a id="2743" href="Prelude.Lifts.html#2743" class="Bound">Y</a> <a id="2745" class="Symbol">:</a> <a id="2747" href="Prelude.Lifts.html#2718" class="Bound">𝓨</a> <a id="2749" href="universes.html#758" class="Function Operator">̇</a><a id="2750" class="Symbol">}</a> <a id="2752" class="Symbol">→</a> <a id="2754" class="Symbol">(</a><a id="2755" href="Prelude.Lifts.html#2734" class="Bound">X</a> <a id="2757" class="Symbol">→</a> <a id="2759" href="Prelude.Lifts.html#2743" class="Bound">Y</a><a id="2760" class="Symbol">)</a> <a id="2762" class="Symbol">→</a> <a id="2764" class="Symbol">(</a><a id="2765" href="Prelude.Lifts.html#2734" class="Bound">X</a> <a id="2767" class="Symbol">→</a> <a id="2769" href="Prelude.Lifts.html#2418" class="Record">Lift</a><a id="2773" class="Symbol">{</a><a id="2774" href="Prelude.Lifts.html#2718" class="Bound">𝓨</a><a id="2775" class="Symbol">}{</a><a id="2777" href="Prelude.Lifts.html#2720" class="Bound">𝓦</a><a id="2778" class="Symbol">}</a> <a id="2780" href="Prelude.Lifts.html#2743" class="Bound">Y</a><a id="2781" class="Symbol">)</a>
<a id="2783" href="Prelude.Lifts.html#2704" class="Function">lift-cod</a> <a id="2792" href="Prelude.Lifts.html#2792" class="Bound">f</a> <a id="2794" class="Symbol">=</a> <a id="2796" class="Symbol">λ</a> <a id="2798" href="Prelude.Lifts.html#2798" class="Bound">x</a> <a id="2800" class="Symbol">→</a> <a id="2802" href="Prelude.Lifts.html#2480" class="InductiveConstructor">lift</a> <a id="2807" class="Symbol">(</a><a id="2808" href="Prelude.Lifts.html#2792" class="Bound">f</a> <a id="2810" href="Prelude.Lifts.html#2798" class="Bound">x</a><a id="2811" class="Symbol">)</a>

<a id="lift-fun"></a><a id="2814" href="Prelude.Lifts.html#2814" class="Function">lift-fun</a> <a id="2823" class="Symbol">:</a> <a id="2825" class="Symbol">{</a><a id="2826" href="Prelude.Lifts.html#2826" class="Bound">𝓧</a> <a id="2828" href="Prelude.Lifts.html#2828" class="Bound">𝓨</a> <a id="2830" href="Prelude.Lifts.html#2830" class="Bound">𝓦</a> <a id="2832" href="Prelude.Lifts.html#2832" class="Bound">𝓩</a> <a id="2834" class="Symbol">:</a> <a id="2836" href="universes.html#551" class="Postulate">Universe</a><a id="2844" class="Symbol">}{</a><a id="2846" href="Prelude.Lifts.html#2846" class="Bound">X</a> <a id="2848" class="Symbol">:</a> <a id="2850" href="Prelude.Lifts.html#2826" class="Bound">𝓧</a> <a id="2852" href="universes.html#758" class="Function Operator">̇</a><a id="2853" class="Symbol">}{</a><a id="2855" href="Prelude.Lifts.html#2855" class="Bound">Y</a> <a id="2857" class="Symbol">:</a> <a id="2859" href="Prelude.Lifts.html#2828" class="Bound">𝓨</a> <a id="2861" href="universes.html#758" class="Function Operator">̇</a><a id="2862" class="Symbol">}</a> <a id="2864" class="Symbol">→</a> <a id="2866" class="Symbol">(</a><a id="2867" href="Prelude.Lifts.html#2846" class="Bound">X</a> <a id="2869" class="Symbol">→</a> <a id="2871" href="Prelude.Lifts.html#2855" class="Bound">Y</a><a id="2872" class="Symbol">)</a> <a id="2874" class="Symbol">→</a> <a id="2876" class="Symbol">(</a><a id="2877" href="Prelude.Lifts.html#2418" class="Record">Lift</a><a id="2881" class="Symbol">{</a><a id="2882" href="Prelude.Lifts.html#2826" class="Bound">𝓧</a><a id="2883" class="Symbol">}{</a><a id="2885" href="Prelude.Lifts.html#2830" class="Bound">𝓦</a><a id="2886" class="Symbol">}</a> <a id="2888" href="Prelude.Lifts.html#2846" class="Bound">X</a> <a id="2890" class="Symbol">→</a> <a id="2892" href="Prelude.Lifts.html#2418" class="Record">Lift</a><a id="2896" class="Symbol">{</a><a id="2897" href="Prelude.Lifts.html#2828" class="Bound">𝓨</a><a id="2898" class="Symbol">}{</a><a id="2900" href="Prelude.Lifts.html#2832" class="Bound">𝓩</a><a id="2901" class="Symbol">}</a> <a id="2903" href="Prelude.Lifts.html#2855" class="Bound">Y</a><a id="2904" class="Symbol">)</a>
<a id="2906" href="Prelude.Lifts.html#2814" class="Function">lift-fun</a> <a id="2915" href="Prelude.Lifts.html#2915" class="Bound">f</a> <a id="2917" class="Symbol">=</a> <a id="2919" class="Symbol">λ</a> <a id="2921" href="Prelude.Lifts.html#2921" class="Bound">x</a> <a id="2923" class="Symbol">→</a> <a id="2925" href="Prelude.Lifts.html#2480" class="InductiveConstructor">lift</a> <a id="2930" class="Symbol">(</a><a id="2931" href="Prelude.Lifts.html#2915" class="Bound">f</a> <a id="2933" class="Symbol">(</a><a id="2934" href="Prelude.Lifts.html#2492" class="Field">lower</a> <a id="2940" href="Prelude.Lifts.html#2921" class="Bound">x</a><a id="2941" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3043" href="Prelude.Lifts.html#3043" class="Function">lower∼lift</a> <a id="3054" class="Symbol">:</a> <a id="3056" class="Symbol">{</a><a id="3057" href="Prelude.Lifts.html#3057" class="Bound">𝓧</a> <a id="3059" href="Prelude.Lifts.html#3059" class="Bound">𝓦</a> <a id="3061" class="Symbol">:</a> <a id="3063" href="universes.html#551" class="Postulate">Universe</a><a id="3071" class="Symbol">}{</a><a id="3073" href="Prelude.Lifts.html#3073" class="Bound">X</a> <a id="3075" class="Symbol">:</a> <a id="3077" href="Prelude.Lifts.html#3057" class="Bound">𝓧</a> <a id="3079" href="universes.html#758" class="Function Operator">̇</a><a id="3080" class="Symbol">}</a> <a id="3082" class="Symbol">→</a> <a id="3084" href="Prelude.Lifts.html#2492" class="Field">lower</a><a id="3089" class="Symbol">{</a><a id="3090" href="Prelude.Lifts.html#3057" class="Bound">𝓧</a><a id="3091" class="Symbol">}{</a><a id="3093" href="Prelude.Lifts.html#3059" class="Bound">𝓦</a><a id="3094" class="Symbol">}</a> <a id="3096" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3098" href="Prelude.Lifts.html#2480" class="InductiveConstructor">lift</a> <a id="3103" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="3105" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3108" href="Prelude.Lifts.html#3073" class="Bound">X</a>
<a id="3110" href="Prelude.Lifts.html#3043" class="Function">lower∼lift</a> <a id="3121" class="Symbol">=</a> <a id="3123" href="Prelude.Equality.html#1961" class="InductiveConstructor">refl</a> <a id="3128" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3131" href="Prelude.Lifts.html#3131" class="Function">lift∼lower</a> <a id="3142" class="Symbol">:</a> <a id="3144" class="Symbol">{</a><a id="3145" href="Prelude.Lifts.html#3145" class="Bound">𝓧</a> <a id="3147" href="Prelude.Lifts.html#3147" class="Bound">𝓦</a> <a id="3149" class="Symbol">:</a> <a id="3151" href="universes.html#551" class="Postulate">Universe</a><a id="3159" class="Symbol">}{</a><a id="3161" href="Prelude.Lifts.html#3161" class="Bound">X</a> <a id="3163" class="Symbol">:</a> <a id="3165" href="Prelude.Lifts.html#3145" class="Bound">𝓧</a> <a id="3167" href="universes.html#758" class="Function Operator">̇</a><a id="3168" class="Symbol">}</a> <a id="3170" class="Symbol">→</a> <a id="3172" href="Prelude.Lifts.html#2480" class="InductiveConstructor">lift</a> <a id="3177" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3179" href="Prelude.Lifts.html#2492" class="Field">lower</a> <a id="3185" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="3187" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3190" class="Symbol">(</a><a id="3191" href="Prelude.Lifts.html#2418" class="Record">Lift</a><a id="3195" class="Symbol">{</a><a id="3196" href="Prelude.Lifts.html#3145" class="Bound">𝓧</a><a id="3197" class="Symbol">}{</a><a id="3199" href="Prelude.Lifts.html#3147" class="Bound">𝓦</a><a id="3200" class="Symbol">}</a> <a id="3202" href="Prelude.Lifts.html#3161" class="Bound">X</a><a id="3203" class="Symbol">)</a>
<a id="3205" href="Prelude.Lifts.html#3131" class="Function">lift∼lower</a> <a id="3216" class="Symbol">=</a> <a id="3218" href="Prelude.Equality.html#1961" class="InductiveConstructor">refl</a> <a id="3223" class="Symbol">_</a>

</pre>


---------------

[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
