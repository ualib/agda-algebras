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

<samp>
Birkhoff.lagda:498,20-23 <br>
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺) <br>
when checking that the expression SP𝒦 has type <br>
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346 <br>
</samp>

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda` file, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the [Agda Standard Library][] (in the `Level` module), is defined as follows.

<pre class="Agda">

<a id="2432" class="Keyword">record</a> <a id="Lift"></a><a id="2439" href="Prelude.Lifts.html#2439" class="Record">Lift</a> <a id="2444" class="Symbol">{</a><a id="2445" href="Prelude.Lifts.html#2445" class="Bound">𝓤</a> <a id="2447" href="Prelude.Lifts.html#2447" class="Bound">𝓦</a> <a id="2449" class="Symbol">:</a> <a id="2451" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2459" class="Symbol">}</a> <a id="2461" class="Symbol">(</a><a id="2462" href="Prelude.Lifts.html#2462" class="Bound">X</a> <a id="2464" class="Symbol">:</a> <a id="2466" href="Prelude.Lifts.html#2445" class="Bound">𝓤</a> <a id="2468" href="Universes.html#403" class="Function Operator">̇</a><a id="2469" class="Symbol">)</a> <a id="2471" class="Symbol">:</a> <a id="2473" href="Prelude.Lifts.html#2445" class="Bound">𝓤</a> <a id="2475" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2477" href="Prelude.Lifts.html#2447" class="Bound">𝓦</a> <a id="2479" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2482" class="Keyword">where</a>
 <a id="2489" class="Keyword">constructor</a> <a id="lift"></a><a id="2501" href="Prelude.Lifts.html#2501" class="InductiveConstructor">lift</a>
 <a id="2507" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2513" href="Prelude.Lifts.html#2513" class="Field">lower</a> <a id="2519" class="Symbol">:</a> <a id="2521" href="Prelude.Lifts.html#2462" class="Bound">X</a>
<a id="2523" class="Keyword">open</a> <a id="2528" href="Prelude.Lifts.html#2439" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2612" href="Prelude.Lifts.html#2612" class="Function">lift-dom</a> <a id="2621" class="Symbol">:</a> <a id="2623" class="Symbol">{</a><a id="2624" href="Prelude.Lifts.html#2624" class="Bound">𝓧</a> <a id="2626" href="Prelude.Lifts.html#2626" class="Bound">𝓨</a> <a id="2628" href="Prelude.Lifts.html#2628" class="Bound">𝓦</a> <a id="2630" class="Symbol">:</a> <a id="2632" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2640" class="Symbol">}{</a><a id="2642" href="Prelude.Lifts.html#2642" class="Bound">X</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="Prelude.Lifts.html#2624" class="Bound">𝓧</a> <a id="2648" href="Universes.html#403" class="Function Operator">̇</a><a id="2649" class="Symbol">}{</a><a id="2651" href="Prelude.Lifts.html#2651" class="Bound">Y</a> <a id="2653" class="Symbol">:</a> <a id="2655" href="Prelude.Lifts.html#2626" class="Bound">𝓨</a> <a id="2657" href="Universes.html#403" class="Function Operator">̇</a><a id="2658" class="Symbol">}</a> <a id="2660" class="Symbol">→</a> <a id="2662" class="Symbol">(</a><a id="2663" href="Prelude.Lifts.html#2642" class="Bound">X</a> <a id="2665" class="Symbol">→</a> <a id="2667" href="Prelude.Lifts.html#2651" class="Bound">Y</a><a id="2668" class="Symbol">)</a> <a id="2670" class="Symbol">→</a> <a id="2672" class="Symbol">(</a><a id="2673" href="Prelude.Lifts.html#2439" class="Record">Lift</a><a id="2677" class="Symbol">{</a><a id="2678" href="Prelude.Lifts.html#2624" class="Bound">𝓧</a><a id="2679" class="Symbol">}{</a><a id="2681" href="Prelude.Lifts.html#2628" class="Bound">𝓦</a><a id="2682" class="Symbol">}</a> <a id="2684" href="Prelude.Lifts.html#2642" class="Bound">X</a> <a id="2686" class="Symbol">→</a> <a id="2688" href="Prelude.Lifts.html#2651" class="Bound">Y</a><a id="2689" class="Symbol">)</a>
<a id="2691" href="Prelude.Lifts.html#2612" class="Function">lift-dom</a> <a id="2700" href="Prelude.Lifts.html#2700" class="Bound">f</a> <a id="2702" class="Symbol">=</a> <a id="2704" class="Symbol">λ</a> <a id="2706" href="Prelude.Lifts.html#2706" class="Bound">x</a> <a id="2708" class="Symbol">→</a> <a id="2710" class="Symbol">(</a><a id="2711" href="Prelude.Lifts.html#2700" class="Bound">f</a> <a id="2713" class="Symbol">(</a><a id="2714" href="Prelude.Lifts.html#2513" class="Field">lower</a> <a id="2720" href="Prelude.Lifts.html#2706" class="Bound">x</a><a id="2721" class="Symbol">))</a>

<a id="lift-cod"></a><a id="2725" href="Prelude.Lifts.html#2725" class="Function">lift-cod</a> <a id="2734" class="Symbol">:</a> <a id="2736" class="Symbol">{</a><a id="2737" href="Prelude.Lifts.html#2737" class="Bound">𝓧</a> <a id="2739" href="Prelude.Lifts.html#2739" class="Bound">𝓨</a> <a id="2741" href="Prelude.Lifts.html#2741" class="Bound">𝓦</a> <a id="2743" class="Symbol">:</a> <a id="2745" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2753" class="Symbol">}{</a><a id="2755" href="Prelude.Lifts.html#2755" class="Bound">X</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="Prelude.Lifts.html#2737" class="Bound">𝓧</a> <a id="2761" href="Universes.html#403" class="Function Operator">̇</a><a id="2762" class="Symbol">}{</a><a id="2764" href="Prelude.Lifts.html#2764" class="Bound">Y</a> <a id="2766" class="Symbol">:</a> <a id="2768" href="Prelude.Lifts.html#2739" class="Bound">𝓨</a> <a id="2770" href="Universes.html#403" class="Function Operator">̇</a><a id="2771" class="Symbol">}</a> <a id="2773" class="Symbol">→</a> <a id="2775" class="Symbol">(</a><a id="2776" href="Prelude.Lifts.html#2755" class="Bound">X</a> <a id="2778" class="Symbol">→</a> <a id="2780" href="Prelude.Lifts.html#2764" class="Bound">Y</a><a id="2781" class="Symbol">)</a> <a id="2783" class="Symbol">→</a> <a id="2785" class="Symbol">(</a><a id="2786" href="Prelude.Lifts.html#2755" class="Bound">X</a> <a id="2788" class="Symbol">→</a> <a id="2790" href="Prelude.Lifts.html#2439" class="Record">Lift</a><a id="2794" class="Symbol">{</a><a id="2795" href="Prelude.Lifts.html#2739" class="Bound">𝓨</a><a id="2796" class="Symbol">}{</a><a id="2798" href="Prelude.Lifts.html#2741" class="Bound">𝓦</a><a id="2799" class="Symbol">}</a> <a id="2801" href="Prelude.Lifts.html#2764" class="Bound">Y</a><a id="2802" class="Symbol">)</a>
<a id="2804" href="Prelude.Lifts.html#2725" class="Function">lift-cod</a> <a id="2813" href="Prelude.Lifts.html#2813" class="Bound">f</a> <a id="2815" class="Symbol">=</a> <a id="2817" class="Symbol">λ</a> <a id="2819" href="Prelude.Lifts.html#2819" class="Bound">x</a> <a id="2821" class="Symbol">→</a> <a id="2823" href="Prelude.Lifts.html#2501" class="InductiveConstructor">lift</a> <a id="2828" class="Symbol">(</a><a id="2829" href="Prelude.Lifts.html#2813" class="Bound">f</a> <a id="2831" href="Prelude.Lifts.html#2819" class="Bound">x</a><a id="2832" class="Symbol">)</a>

<a id="lift-fun"></a><a id="2835" href="Prelude.Lifts.html#2835" class="Function">lift-fun</a> <a id="2844" class="Symbol">:</a> <a id="2846" class="Symbol">{</a><a id="2847" href="Prelude.Lifts.html#2847" class="Bound">𝓧</a> <a id="2849" href="Prelude.Lifts.html#2849" class="Bound">𝓨</a> <a id="2851" href="Prelude.Lifts.html#2851" class="Bound">𝓦</a> <a id="2853" href="Prelude.Lifts.html#2853" class="Bound">𝓩</a> <a id="2855" class="Symbol">:</a> <a id="2857" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2865" class="Symbol">}{</a><a id="2867" href="Prelude.Lifts.html#2867" class="Bound">X</a> <a id="2869" class="Symbol">:</a> <a id="2871" href="Prelude.Lifts.html#2847" class="Bound">𝓧</a> <a id="2873" href="Universes.html#403" class="Function Operator">̇</a><a id="2874" class="Symbol">}{</a><a id="2876" href="Prelude.Lifts.html#2876" class="Bound">Y</a> <a id="2878" class="Symbol">:</a> <a id="2880" href="Prelude.Lifts.html#2849" class="Bound">𝓨</a> <a id="2882" href="Universes.html#403" class="Function Operator">̇</a><a id="2883" class="Symbol">}</a> <a id="2885" class="Symbol">→</a> <a id="2887" class="Symbol">(</a><a id="2888" href="Prelude.Lifts.html#2867" class="Bound">X</a> <a id="2890" class="Symbol">→</a> <a id="2892" href="Prelude.Lifts.html#2876" class="Bound">Y</a><a id="2893" class="Symbol">)</a> <a id="2895" class="Symbol">→</a> <a id="2897" class="Symbol">(</a><a id="2898" href="Prelude.Lifts.html#2439" class="Record">Lift</a><a id="2902" class="Symbol">{</a><a id="2903" href="Prelude.Lifts.html#2847" class="Bound">𝓧</a><a id="2904" class="Symbol">}{</a><a id="2906" href="Prelude.Lifts.html#2851" class="Bound">𝓦</a><a id="2907" class="Symbol">}</a> <a id="2909" href="Prelude.Lifts.html#2867" class="Bound">X</a> <a id="2911" class="Symbol">→</a> <a id="2913" href="Prelude.Lifts.html#2439" class="Record">Lift</a><a id="2917" class="Symbol">{</a><a id="2918" href="Prelude.Lifts.html#2849" class="Bound">𝓨</a><a id="2919" class="Symbol">}{</a><a id="2921" href="Prelude.Lifts.html#2853" class="Bound">𝓩</a><a id="2922" class="Symbol">}</a> <a id="2924" href="Prelude.Lifts.html#2876" class="Bound">Y</a><a id="2925" class="Symbol">)</a>
<a id="2927" href="Prelude.Lifts.html#2835" class="Function">lift-fun</a> <a id="2936" href="Prelude.Lifts.html#2936" class="Bound">f</a> <a id="2938" class="Symbol">=</a> <a id="2940" class="Symbol">λ</a> <a id="2942" href="Prelude.Lifts.html#2942" class="Bound">x</a> <a id="2944" class="Symbol">→</a> <a id="2946" href="Prelude.Lifts.html#2501" class="InductiveConstructor">lift</a> <a id="2951" class="Symbol">(</a><a id="2952" href="Prelude.Lifts.html#2936" class="Bound">f</a> <a id="2954" class="Symbol">(</a><a id="2955" href="Prelude.Lifts.html#2513" class="Field">lower</a> <a id="2961" href="Prelude.Lifts.html#2942" class="Bound">x</a><a id="2962" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3064" href="Prelude.Lifts.html#3064" class="Function">lower∼lift</a> <a id="3075" class="Symbol">:</a> <a id="3077" class="Symbol">{</a><a id="3078" href="Prelude.Lifts.html#3078" class="Bound">𝓧</a> <a id="3080" href="Prelude.Lifts.html#3080" class="Bound">𝓦</a> <a id="3082" class="Symbol">:</a> <a id="3084" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3092" class="Symbol">}{</a><a id="3094" href="Prelude.Lifts.html#3094" class="Bound">X</a> <a id="3096" class="Symbol">:</a> <a id="3098" href="Prelude.Lifts.html#3078" class="Bound">𝓧</a> <a id="3100" href="Universes.html#403" class="Function Operator">̇</a><a id="3101" class="Symbol">}</a> <a id="3103" class="Symbol">→</a> <a id="3105" href="Prelude.Lifts.html#2513" class="Field">lower</a><a id="3110" class="Symbol">{</a><a id="3111" href="Prelude.Lifts.html#3078" class="Bound">𝓧</a><a id="3112" class="Symbol">}{</a><a id="3114" href="Prelude.Lifts.html#3080" class="Bound">𝓦</a><a id="3115" class="Symbol">}</a> <a id="3117" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3119" href="Prelude.Lifts.html#2501" class="InductiveConstructor">lift</a> <a id="3124" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3126" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3129" href="Prelude.Lifts.html#3094" class="Bound">X</a>
<a id="3131" href="Prelude.Lifts.html#3064" class="Function">lower∼lift</a> <a id="3142" class="Symbol">=</a> <a id="3144" href="Prelude.Equality.html#1754" class="InductiveConstructor">refl</a> <a id="3149" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3152" href="Prelude.Lifts.html#3152" class="Function">lift∼lower</a> <a id="3163" class="Symbol">:</a> <a id="3165" class="Symbol">{</a><a id="3166" href="Prelude.Lifts.html#3166" class="Bound">𝓧</a> <a id="3168" href="Prelude.Lifts.html#3168" class="Bound">𝓦</a> <a id="3170" class="Symbol">:</a> <a id="3172" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3180" class="Symbol">}{</a><a id="3182" href="Prelude.Lifts.html#3182" class="Bound">X</a> <a id="3184" class="Symbol">:</a> <a id="3186" href="Prelude.Lifts.html#3166" class="Bound">𝓧</a> <a id="3188" href="Universes.html#403" class="Function Operator">̇</a><a id="3189" class="Symbol">}</a> <a id="3191" class="Symbol">→</a> <a id="3193" href="Prelude.Lifts.html#2501" class="InductiveConstructor">lift</a> <a id="3198" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3200" href="Prelude.Lifts.html#2513" class="Field">lower</a> <a id="3206" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3208" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3211" class="Symbol">(</a><a id="3212" href="Prelude.Lifts.html#2439" class="Record">Lift</a><a id="3216" class="Symbol">{</a><a id="3217" href="Prelude.Lifts.html#3166" class="Bound">𝓧</a><a id="3218" class="Symbol">}{</a><a id="3220" href="Prelude.Lifts.html#3168" class="Bound">𝓦</a><a id="3221" class="Symbol">}</a> <a id="3223" href="Prelude.Lifts.html#3182" class="Bound">X</a><a id="3224" class="Symbol">)</a>
<a id="3226" href="Prelude.Lifts.html#3152" class="Function">lift∼lower</a> <a id="3237" class="Symbol">=</a> <a id="3239" href="Prelude.Equality.html#1754" class="InductiveConstructor">refl</a> <a id="3244" class="Symbol">_</a>

</pre>


---------------

[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
