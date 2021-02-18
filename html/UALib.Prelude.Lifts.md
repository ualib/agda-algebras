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

<a id="367" class="Keyword">module</a> <a id="374" href="UALib.Prelude.Lifts.html" class="Module">UALib.Prelude.Lifts</a> <a id="394" class="Keyword">where</a>

<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="UALib.Prelude.Extensionality.html" class="Module">UALib.Prelude.Extensionality</a> <a id="442" class="Keyword">public</a>

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

<a id="2423" class="Keyword">record</a> <a id="Lift"></a><a id="2430" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a> <a id="2435" class="Symbol">{</a><a id="2436" href="UALib.Prelude.Lifts.html#2436" class="Bound">𝓤</a> <a id="2438" href="UALib.Prelude.Lifts.html#2438" class="Bound">𝓦</a> <a id="2440" class="Symbol">:</a> <a id="2442" href="universes.html#551" class="Postulate">Universe</a><a id="2450" class="Symbol">}</a> <a id="2452" class="Symbol">(</a><a id="2453" href="UALib.Prelude.Lifts.html#2453" class="Bound">X</a> <a id="2455" class="Symbol">:</a> <a id="2457" href="UALib.Prelude.Lifts.html#2436" class="Bound">𝓤</a> <a id="2459" href="universes.html#758" class="Function Operator">̇</a><a id="2460" class="Symbol">)</a> <a id="2462" class="Symbol">:</a> <a id="2464" href="UALib.Prelude.Lifts.html#2436" class="Bound">𝓤</a> <a id="2466" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2468" href="UALib.Prelude.Lifts.html#2438" class="Bound">𝓦</a> <a id="2470" href="universes.html#758" class="Function Operator">̇</a>  <a id="2473" class="Keyword">where</a>
 <a id="2480" class="Keyword">constructor</a> <a id="lift"></a><a id="2492" href="UALib.Prelude.Lifts.html#2492" class="InductiveConstructor">lift</a>
 <a id="2498" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2504" href="UALib.Prelude.Lifts.html#2504" class="Field">lower</a> <a id="2510" class="Symbol">:</a> <a id="2512" href="UALib.Prelude.Lifts.html#2453" class="Bound">X</a>
<a id="2514" class="Keyword">open</a> <a id="2519" href="UALib.Prelude.Lifts.html#2430" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2603" href="UALib.Prelude.Lifts.html#2603" class="Function">lift-dom</a> <a id="2612" class="Symbol">:</a> <a id="2614" class="Symbol">{</a><a id="2615" href="UALib.Prelude.Lifts.html#2615" class="Bound">𝓧</a> <a id="2617" href="UALib.Prelude.Lifts.html#2617" class="Bound">𝓨</a> <a id="2619" href="UALib.Prelude.Lifts.html#2619" class="Bound">𝓦</a> <a id="2621" class="Symbol">:</a> <a id="2623" href="universes.html#551" class="Postulate">Universe</a><a id="2631" class="Symbol">}{</a><a id="2633" href="UALib.Prelude.Lifts.html#2633" class="Bound">X</a> <a id="2635" class="Symbol">:</a> <a id="2637" href="UALib.Prelude.Lifts.html#2615" class="Bound">𝓧</a> <a id="2639" href="universes.html#758" class="Function Operator">̇</a><a id="2640" class="Symbol">}{</a><a id="2642" href="UALib.Prelude.Lifts.html#2642" class="Bound">Y</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="UALib.Prelude.Lifts.html#2617" class="Bound">𝓨</a> <a id="2648" href="universes.html#758" class="Function Operator">̇</a><a id="2649" class="Symbol">}</a> <a id="2651" class="Symbol">→</a> <a id="2653" class="Symbol">(</a><a id="2654" href="UALib.Prelude.Lifts.html#2633" class="Bound">X</a> <a id="2656" class="Symbol">→</a> <a id="2658" href="UALib.Prelude.Lifts.html#2642" class="Bound">Y</a><a id="2659" class="Symbol">)</a> <a id="2661" class="Symbol">→</a> <a id="2663" class="Symbol">(</a><a id="2664" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a><a id="2668" class="Symbol">{</a><a id="2669" href="UALib.Prelude.Lifts.html#2615" class="Bound">𝓧</a><a id="2670" class="Symbol">}{</a><a id="2672" href="UALib.Prelude.Lifts.html#2619" class="Bound">𝓦</a><a id="2673" class="Symbol">}</a> <a id="2675" href="UALib.Prelude.Lifts.html#2633" class="Bound">X</a> <a id="2677" class="Symbol">→</a> <a id="2679" href="UALib.Prelude.Lifts.html#2642" class="Bound">Y</a><a id="2680" class="Symbol">)</a>
<a id="2682" href="UALib.Prelude.Lifts.html#2603" class="Function">lift-dom</a> <a id="2691" href="UALib.Prelude.Lifts.html#2691" class="Bound">f</a> <a id="2693" class="Symbol">=</a> <a id="2695" class="Symbol">λ</a> <a id="2697" href="UALib.Prelude.Lifts.html#2697" class="Bound">x</a> <a id="2699" class="Symbol">→</a> <a id="2701" class="Symbol">(</a><a id="2702" href="UALib.Prelude.Lifts.html#2691" class="Bound">f</a> <a id="2704" class="Symbol">(</a><a id="2705" href="UALib.Prelude.Lifts.html#2504" class="Field">lower</a> <a id="2711" href="UALib.Prelude.Lifts.html#2697" class="Bound">x</a><a id="2712" class="Symbol">))</a>

<a id="lift-cod"></a><a id="2716" href="UALib.Prelude.Lifts.html#2716" class="Function">lift-cod</a> <a id="2725" class="Symbol">:</a> <a id="2727" class="Symbol">{</a><a id="2728" href="UALib.Prelude.Lifts.html#2728" class="Bound">𝓧</a> <a id="2730" href="UALib.Prelude.Lifts.html#2730" class="Bound">𝓨</a> <a id="2732" href="UALib.Prelude.Lifts.html#2732" class="Bound">𝓦</a> <a id="2734" class="Symbol">:</a> <a id="2736" href="universes.html#551" class="Postulate">Universe</a><a id="2744" class="Symbol">}{</a><a id="2746" href="UALib.Prelude.Lifts.html#2746" class="Bound">X</a> <a id="2748" class="Symbol">:</a> <a id="2750" href="UALib.Prelude.Lifts.html#2728" class="Bound">𝓧</a> <a id="2752" href="universes.html#758" class="Function Operator">̇</a><a id="2753" class="Symbol">}{</a><a id="2755" href="UALib.Prelude.Lifts.html#2755" class="Bound">Y</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="UALib.Prelude.Lifts.html#2730" class="Bound">𝓨</a> <a id="2761" href="universes.html#758" class="Function Operator">̇</a><a id="2762" class="Symbol">}</a> <a id="2764" class="Symbol">→</a> <a id="2766" class="Symbol">(</a><a id="2767" href="UALib.Prelude.Lifts.html#2746" class="Bound">X</a> <a id="2769" class="Symbol">→</a> <a id="2771" href="UALib.Prelude.Lifts.html#2755" class="Bound">Y</a><a id="2772" class="Symbol">)</a> <a id="2774" class="Symbol">→</a> <a id="2776" class="Symbol">(</a><a id="2777" href="UALib.Prelude.Lifts.html#2746" class="Bound">X</a> <a id="2779" class="Symbol">→</a> <a id="2781" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a><a id="2785" class="Symbol">{</a><a id="2786" href="UALib.Prelude.Lifts.html#2730" class="Bound">𝓨</a><a id="2787" class="Symbol">}{</a><a id="2789" href="UALib.Prelude.Lifts.html#2732" class="Bound">𝓦</a><a id="2790" class="Symbol">}</a> <a id="2792" href="UALib.Prelude.Lifts.html#2755" class="Bound">Y</a><a id="2793" class="Symbol">)</a>
<a id="2795" href="UALib.Prelude.Lifts.html#2716" class="Function">lift-cod</a> <a id="2804" href="UALib.Prelude.Lifts.html#2804" class="Bound">f</a> <a id="2806" class="Symbol">=</a> <a id="2808" class="Symbol">λ</a> <a id="2810" href="UALib.Prelude.Lifts.html#2810" class="Bound">x</a> <a id="2812" class="Symbol">→</a> <a id="2814" href="UALib.Prelude.Lifts.html#2492" class="InductiveConstructor">lift</a> <a id="2819" class="Symbol">(</a><a id="2820" href="UALib.Prelude.Lifts.html#2804" class="Bound">f</a> <a id="2822" href="UALib.Prelude.Lifts.html#2810" class="Bound">x</a><a id="2823" class="Symbol">)</a>

<a id="lift-fun"></a><a id="2826" href="UALib.Prelude.Lifts.html#2826" class="Function">lift-fun</a> <a id="2835" class="Symbol">:</a> <a id="2837" class="Symbol">{</a><a id="2838" href="UALib.Prelude.Lifts.html#2838" class="Bound">𝓧</a> <a id="2840" href="UALib.Prelude.Lifts.html#2840" class="Bound">𝓨</a> <a id="2842" href="UALib.Prelude.Lifts.html#2842" class="Bound">𝓦</a> <a id="2844" href="UALib.Prelude.Lifts.html#2844" class="Bound">𝓩</a> <a id="2846" class="Symbol">:</a> <a id="2848" href="universes.html#551" class="Postulate">Universe</a><a id="2856" class="Symbol">}{</a><a id="2858" href="UALib.Prelude.Lifts.html#2858" class="Bound">X</a> <a id="2860" class="Symbol">:</a> <a id="2862" href="UALib.Prelude.Lifts.html#2838" class="Bound">𝓧</a> <a id="2864" href="universes.html#758" class="Function Operator">̇</a><a id="2865" class="Symbol">}{</a><a id="2867" href="UALib.Prelude.Lifts.html#2867" class="Bound">Y</a> <a id="2869" class="Symbol">:</a> <a id="2871" href="UALib.Prelude.Lifts.html#2840" class="Bound">𝓨</a> <a id="2873" href="universes.html#758" class="Function Operator">̇</a><a id="2874" class="Symbol">}</a> <a id="2876" class="Symbol">→</a> <a id="2878" class="Symbol">(</a><a id="2879" href="UALib.Prelude.Lifts.html#2858" class="Bound">X</a> <a id="2881" class="Symbol">→</a> <a id="2883" href="UALib.Prelude.Lifts.html#2867" class="Bound">Y</a><a id="2884" class="Symbol">)</a> <a id="2886" class="Symbol">→</a> <a id="2888" class="Symbol">(</a><a id="2889" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a><a id="2893" class="Symbol">{</a><a id="2894" href="UALib.Prelude.Lifts.html#2838" class="Bound">𝓧</a><a id="2895" class="Symbol">}{</a><a id="2897" href="UALib.Prelude.Lifts.html#2842" class="Bound">𝓦</a><a id="2898" class="Symbol">}</a> <a id="2900" href="UALib.Prelude.Lifts.html#2858" class="Bound">X</a> <a id="2902" class="Symbol">→</a> <a id="2904" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a><a id="2908" class="Symbol">{</a><a id="2909" href="UALib.Prelude.Lifts.html#2840" class="Bound">𝓨</a><a id="2910" class="Symbol">}{</a><a id="2912" href="UALib.Prelude.Lifts.html#2844" class="Bound">𝓩</a><a id="2913" class="Symbol">}</a> <a id="2915" href="UALib.Prelude.Lifts.html#2867" class="Bound">Y</a><a id="2916" class="Symbol">)</a>
<a id="2918" href="UALib.Prelude.Lifts.html#2826" class="Function">lift-fun</a> <a id="2927" href="UALib.Prelude.Lifts.html#2927" class="Bound">f</a> <a id="2929" class="Symbol">=</a> <a id="2931" class="Symbol">λ</a> <a id="2933" href="UALib.Prelude.Lifts.html#2933" class="Bound">x</a> <a id="2935" class="Symbol">→</a> <a id="2937" href="UALib.Prelude.Lifts.html#2492" class="InductiveConstructor">lift</a> <a id="2942" class="Symbol">(</a><a id="2943" href="UALib.Prelude.Lifts.html#2927" class="Bound">f</a> <a id="2945" class="Symbol">(</a><a id="2946" href="UALib.Prelude.Lifts.html#2504" class="Field">lower</a> <a id="2952" href="UALib.Prelude.Lifts.html#2933" class="Bound">x</a><a id="2953" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3055" href="UALib.Prelude.Lifts.html#3055" class="Function">lower∼lift</a> <a id="3066" class="Symbol">:</a> <a id="3068" class="Symbol">{</a><a id="3069" href="UALib.Prelude.Lifts.html#3069" class="Bound">𝓧</a> <a id="3071" href="UALib.Prelude.Lifts.html#3071" class="Bound">𝓦</a> <a id="3073" class="Symbol">:</a> <a id="3075" href="universes.html#551" class="Postulate">Universe</a><a id="3083" class="Symbol">}{</a><a id="3085" href="UALib.Prelude.Lifts.html#3085" class="Bound">X</a> <a id="3087" class="Symbol">:</a> <a id="3089" href="UALib.Prelude.Lifts.html#3069" class="Bound">𝓧</a> <a id="3091" href="universes.html#758" class="Function Operator">̇</a><a id="3092" class="Symbol">}</a> <a id="3094" class="Symbol">→</a> <a id="3096" href="UALib.Prelude.Lifts.html#2504" class="Field">lower</a><a id="3101" class="Symbol">{</a><a id="3102" href="UALib.Prelude.Lifts.html#3069" class="Bound">𝓧</a><a id="3103" class="Symbol">}{</a><a id="3105" href="UALib.Prelude.Lifts.html#3071" class="Bound">𝓦</a><a id="3106" class="Symbol">}</a> <a id="3108" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3110" href="UALib.Prelude.Lifts.html#2492" class="InductiveConstructor">lift</a> <a id="3115" href="UALib.Prelude.Preliminaries.html#5654" class="Datatype Operator">≡</a> <a id="3117" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3120" href="UALib.Prelude.Lifts.html#3085" class="Bound">X</a>
<a id="3122" href="UALib.Prelude.Lifts.html#3055" class="Function">lower∼lift</a> <a id="3133" class="Symbol">=</a> <a id="3135" href="UALib.Prelude.Preliminaries.html#5690" class="InductiveConstructor">refl</a> <a id="3140" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3143" href="UALib.Prelude.Lifts.html#3143" class="Function">lift∼lower</a> <a id="3154" class="Symbol">:</a> <a id="3156" class="Symbol">{</a><a id="3157" href="UALib.Prelude.Lifts.html#3157" class="Bound">𝓧</a> <a id="3159" href="UALib.Prelude.Lifts.html#3159" class="Bound">𝓦</a> <a id="3161" class="Symbol">:</a> <a id="3163" href="universes.html#551" class="Postulate">Universe</a><a id="3171" class="Symbol">}{</a><a id="3173" href="UALib.Prelude.Lifts.html#3173" class="Bound">X</a> <a id="3175" class="Symbol">:</a> <a id="3177" href="UALib.Prelude.Lifts.html#3157" class="Bound">𝓧</a> <a id="3179" href="universes.html#758" class="Function Operator">̇</a><a id="3180" class="Symbol">}</a> <a id="3182" class="Symbol">→</a> <a id="3184" href="UALib.Prelude.Lifts.html#2492" class="InductiveConstructor">lift</a> <a id="3189" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3191" href="UALib.Prelude.Lifts.html#2504" class="Field">lower</a> <a id="3197" href="UALib.Prelude.Preliminaries.html#5654" class="Datatype Operator">≡</a> <a id="3199" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3202" class="Symbol">(</a><a id="3203" href="UALib.Prelude.Lifts.html#2430" class="Record">Lift</a><a id="3207" class="Symbol">{</a><a id="3208" href="UALib.Prelude.Lifts.html#3157" class="Bound">𝓧</a><a id="3209" class="Symbol">}{</a><a id="3211" href="UALib.Prelude.Lifts.html#3159" class="Bound">𝓦</a><a id="3212" class="Symbol">}</a> <a id="3214" href="UALib.Prelude.Lifts.html#3173" class="Bound">X</a><a id="3215" class="Symbol">)</a>
<a id="3217" href="UALib.Prelude.Lifts.html#3143" class="Function">lift∼lower</a> <a id="3228" class="Symbol">=</a> <a id="3230" href="UALib.Prelude.Preliminaries.html#5690" class="InductiveConstructor">refl</a> <a id="3235" class="Symbol">_</a>

</pre>


---------------

[← UALib.Prelude.Extensionality](UALib.Prelude.Extensionality.html)
<span style="float:right;">[UALib.Relations →](UALib.Relations.html)</span>

{% include UALib.Links.md %}
