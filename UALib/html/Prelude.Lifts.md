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

Luckily, there are ways to overcome this technical issue. We describe general lifting and lowering functions below, and then later, in the section on [Lifts of algebras](https://ualib.gitlab.io/Algebras.Algebras.html#lifts-of-algebras), we'll see the domain-specific analogs of these tools which turn out to have some nice properties that make them very effective for resolving universe level problems when working with algebra datatypes.

#### Lifting and lowering

Let us be more concrete about what is at issue here by giving an example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺) <br>
when checking that the expression SP𝒦 has type <br>
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346 <br>
</samp>

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the `Level` module of the [Agda Standard Library][], is defined as follows.

<pre class="Agda">

<a id="2721" class="Keyword">record</a> <a id="Lift"></a><a id="2728" href="Prelude.Lifts.html#2728" class="Record">Lift</a> <a id="2733" class="Symbol">{</a><a id="2734" href="Prelude.Lifts.html#2734" class="Bound">𝓦</a> <a id="2736" href="Prelude.Lifts.html#2736" class="Bound">𝓤</a> <a id="2738" class="Symbol">:</a> <a id="2740" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2748" class="Symbol">}</a> <a id="2750" class="Symbol">(</a><a id="2751" href="Prelude.Lifts.html#2751" class="Bound">X</a> <a id="2753" class="Symbol">:</a> <a id="2755" href="Prelude.Lifts.html#2736" class="Bound">𝓤</a> <a id="2757" href="Universes.html#403" class="Function Operator">̇</a><a id="2758" class="Symbol">)</a> <a id="2760" class="Symbol">:</a> <a id="2762" href="Prelude.Lifts.html#2736" class="Bound">𝓤</a> <a id="2764" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2766" href="Prelude.Lifts.html#2734" class="Bound">𝓦</a> <a id="2768" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2771" class="Keyword">where</a>
 <a id="2778" class="Keyword">constructor</a> <a id="lift"></a><a id="2790" href="Prelude.Lifts.html#2790" class="InductiveConstructor">lift</a>
 <a id="2796" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2802" href="Prelude.Lifts.html#2802" class="Field">lower</a> <a id="2808" class="Symbol">:</a> <a id="2810" href="Prelude.Lifts.html#2751" class="Bound">X</a>
<a id="2812" class="Keyword">open</a> <a id="2817" href="Prelude.Lifts.html#2728" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="2901" class="Keyword">module</a> <a id="2908" href="Prelude.Lifts.html#2908" class="Module">_</a> <a id="2910" class="Symbol">{</a><a id="2911" href="Prelude.Lifts.html#2911" class="Bound">𝓦</a> <a id="2913" href="Prelude.Lifts.html#2913" class="Bound">𝓧</a> <a id="2915" href="Prelude.Lifts.html#2915" class="Bound">𝓨</a> <a id="2917" class="Symbol">:</a> <a id="2919" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2927" class="Symbol">}</a> <a id="2929" class="Keyword">where</a>

 <a id="2937" href="Prelude.Lifts.html#2937" class="Function">lift-dom</a> <a id="2946" class="Symbol">:</a> <a id="2948" class="Symbol">{</a><a id="2949" href="Prelude.Lifts.html#2949" class="Bound">X</a> <a id="2951" class="Symbol">:</a> <a id="2953" href="Prelude.Lifts.html#2913" class="Bound">𝓧</a> <a id="2955" href="Universes.html#403" class="Function Operator">̇</a><a id="2956" class="Symbol">}{</a><a id="2958" href="Prelude.Lifts.html#2958" class="Bound">Y</a> <a id="2960" class="Symbol">:</a> <a id="2962" href="Prelude.Lifts.html#2915" class="Bound">𝓨</a> <a id="2964" href="Universes.html#403" class="Function Operator">̇</a><a id="2965" class="Symbol">}</a> <a id="2967" class="Symbol">→</a> <a id="2969" class="Symbol">(</a><a id="2970" href="Prelude.Lifts.html#2949" class="Bound">X</a> <a id="2972" class="Symbol">→</a> <a id="2974" href="Prelude.Lifts.html#2958" class="Bound">Y</a><a id="2975" class="Symbol">)</a> <a id="2977" class="Symbol">→</a> <a id="2979" class="Symbol">(</a><a id="2980" href="Prelude.Lifts.html#2728" class="Record">Lift</a><a id="2984" class="Symbol">{</a><a id="2985" href="Prelude.Lifts.html#2911" class="Bound">𝓦</a><a id="2986" class="Symbol">}{</a><a id="2988" href="Prelude.Lifts.html#2913" class="Bound">𝓧</a><a id="2989" class="Symbol">}</a> <a id="2991" href="Prelude.Lifts.html#2949" class="Bound">X</a> <a id="2993" class="Symbol">→</a> <a id="2995" href="Prelude.Lifts.html#2958" class="Bound">Y</a><a id="2996" class="Symbol">)</a>
 <a id="2999" href="Prelude.Lifts.html#2937" class="Function">lift-dom</a> <a id="3008" href="Prelude.Lifts.html#3008" class="Bound">f</a> <a id="3010" class="Symbol">=</a> <a id="3012" class="Symbol">λ</a> <a id="3014" href="Prelude.Lifts.html#3014" class="Bound">x</a> <a id="3016" class="Symbol">→</a> <a id="3018" class="Symbol">(</a><a id="3019" href="Prelude.Lifts.html#3008" class="Bound">f</a> <a id="3021" class="Symbol">(</a><a id="3022" href="Prelude.Lifts.html#2802" class="Field">lower</a> <a id="3028" href="Prelude.Lifts.html#3014" class="Bound">x</a><a id="3029" class="Symbol">))</a>

 <a id="3034" href="Prelude.Lifts.html#3034" class="Function">lift-cod</a> <a id="3043" class="Symbol">:</a> <a id="3045" class="Symbol">{</a><a id="3046" href="Prelude.Lifts.html#3046" class="Bound">X</a> <a id="3048" class="Symbol">:</a> <a id="3050" href="Prelude.Lifts.html#2913" class="Bound">𝓧</a> <a id="3052" href="Universes.html#403" class="Function Operator">̇</a><a id="3053" class="Symbol">}{</a><a id="3055" href="Prelude.Lifts.html#3055" class="Bound">Y</a> <a id="3057" class="Symbol">:</a> <a id="3059" href="Prelude.Lifts.html#2915" class="Bound">𝓨</a> <a id="3061" href="Universes.html#403" class="Function Operator">̇</a><a id="3062" class="Symbol">}</a> <a id="3064" class="Symbol">→</a> <a id="3066" class="Symbol">(</a><a id="3067" href="Prelude.Lifts.html#3046" class="Bound">X</a> <a id="3069" class="Symbol">→</a> <a id="3071" href="Prelude.Lifts.html#3055" class="Bound">Y</a><a id="3072" class="Symbol">)</a> <a id="3074" class="Symbol">→</a> <a id="3076" class="Symbol">(</a><a id="3077" href="Prelude.Lifts.html#3046" class="Bound">X</a> <a id="3079" class="Symbol">→</a> <a id="3081" href="Prelude.Lifts.html#2728" class="Record">Lift</a><a id="3085" class="Symbol">{</a><a id="3086" href="Prelude.Lifts.html#2911" class="Bound">𝓦</a><a id="3087" class="Symbol">}{</a><a id="3089" href="Prelude.Lifts.html#2915" class="Bound">𝓨</a><a id="3090" class="Symbol">}</a> <a id="3092" href="Prelude.Lifts.html#3055" class="Bound">Y</a><a id="3093" class="Symbol">)</a>
 <a id="3096" href="Prelude.Lifts.html#3034" class="Function">lift-cod</a> <a id="3105" href="Prelude.Lifts.html#3105" class="Bound">f</a> <a id="3107" class="Symbol">=</a> <a id="3109" class="Symbol">λ</a> <a id="3111" href="Prelude.Lifts.html#3111" class="Bound">x</a> <a id="3113" class="Symbol">→</a> <a id="3115" href="Prelude.Lifts.html#2790" class="InductiveConstructor">lift</a> <a id="3120" class="Symbol">(</a><a id="3121" href="Prelude.Lifts.html#3105" class="Bound">f</a> <a id="3123" href="Prelude.Lifts.html#3111" class="Bound">x</a><a id="3124" class="Symbol">)</a>


<a id="3128" class="Keyword">module</a> <a id="3135" href="Prelude.Lifts.html#3135" class="Module">_</a> <a id="3137" class="Symbol">{</a><a id="3138" href="Prelude.Lifts.html#3138" class="Bound">𝓦</a> <a id="3140" href="Prelude.Lifts.html#3140" class="Bound">𝓩</a> <a id="3142" href="Prelude.Lifts.html#3142" class="Bound">𝓧</a> <a id="3144" href="Prelude.Lifts.html#3144" class="Bound">𝓨</a> <a id="3146" class="Symbol">:</a> <a id="3148" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3156" class="Symbol">}</a> <a id="3158" class="Keyword">where</a>

 <a id="3166" href="Prelude.Lifts.html#3166" class="Function">lift-fun</a> <a id="3175" class="Symbol">:</a> <a id="3177" class="Symbol">{</a><a id="3178" href="Prelude.Lifts.html#3178" class="Bound">X</a> <a id="3180" class="Symbol">:</a> <a id="3182" href="Prelude.Lifts.html#3142" class="Bound">𝓧</a> <a id="3184" href="Universes.html#403" class="Function Operator">̇</a><a id="3185" class="Symbol">}{</a><a id="3187" href="Prelude.Lifts.html#3187" class="Bound">Y</a> <a id="3189" class="Symbol">:</a> <a id="3191" href="Prelude.Lifts.html#3144" class="Bound">𝓨</a> <a id="3193" href="Universes.html#403" class="Function Operator">̇</a><a id="3194" class="Symbol">}</a> <a id="3196" class="Symbol">→</a> <a id="3198" class="Symbol">(</a><a id="3199" href="Prelude.Lifts.html#3178" class="Bound">X</a> <a id="3201" class="Symbol">→</a> <a id="3203" href="Prelude.Lifts.html#3187" class="Bound">Y</a><a id="3204" class="Symbol">)</a> <a id="3206" class="Symbol">→</a> <a id="3208" class="Symbol">(</a><a id="3209" href="Prelude.Lifts.html#2728" class="Record">Lift</a><a id="3213" class="Symbol">{</a><a id="3214" href="Prelude.Lifts.html#3138" class="Bound">𝓦</a><a id="3215" class="Symbol">}{</a><a id="3217" href="Prelude.Lifts.html#3142" class="Bound">𝓧</a><a id="3218" class="Symbol">}</a> <a id="3220" href="Prelude.Lifts.html#3178" class="Bound">X</a> <a id="3222" class="Symbol">→</a> <a id="3224" href="Prelude.Lifts.html#2728" class="Record">Lift</a><a id="3228" class="Symbol">{</a><a id="3229" href="Prelude.Lifts.html#3140" class="Bound">𝓩</a><a id="3230" class="Symbol">}{</a><a id="3232" href="Prelude.Lifts.html#3144" class="Bound">𝓨</a><a id="3233" class="Symbol">}</a> <a id="3235" href="Prelude.Lifts.html#3187" class="Bound">Y</a><a id="3236" class="Symbol">)</a>
 <a id="3239" href="Prelude.Lifts.html#3166" class="Function">lift-fun</a> <a id="3248" href="Prelude.Lifts.html#3248" class="Bound">f</a> <a id="3250" class="Symbol">=</a> <a id="3252" class="Symbol">λ</a> <a id="3254" href="Prelude.Lifts.html#3254" class="Bound">x</a> <a id="3256" class="Symbol">→</a> <a id="3258" href="Prelude.Lifts.html#2790" class="InductiveConstructor">lift</a> <a id="3263" class="Symbol">(</a><a id="3264" href="Prelude.Lifts.html#3248" class="Bound">f</a> <a id="3266" class="Symbol">(</a><a id="3267" href="Prelude.Lifts.html#2802" class="Field">lower</a> <a id="3273" href="Prelude.Lifts.html#3254" class="Bound">x</a><a id="3274" class="Symbol">))</a>

</pre>

For example, `lift-dom` takes a function `f` defined on the domain `X : 𝓧 ̇` and returns a function defined on the domain `Lift{𝓦}{𝓧} X : 𝓧 ⊔ 𝓦 ̇`, whose type lives in the universe `𝓧 ⊔ 𝓦`.

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that `lift` and `lower` compose to the identity. Later, there will be some situations that require these facts, so we formalize them and their (trivial) proofs.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3867" href="Prelude.Lifts.html#3867" class="Function">lower∼lift</a> <a id="3878" class="Symbol">:</a> <a id="3880" class="Symbol">{</a><a id="3881" href="Prelude.Lifts.html#3881" class="Bound">𝓦</a> <a id="3883" href="Prelude.Lifts.html#3883" class="Bound">𝓧</a> <a id="3885" class="Symbol">:</a> <a id="3887" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3895" class="Symbol">}{</a><a id="3897" href="Prelude.Lifts.html#3897" class="Bound">X</a> <a id="3899" class="Symbol">:</a> <a id="3901" href="Prelude.Lifts.html#3883" class="Bound">𝓧</a> <a id="3903" href="Universes.html#403" class="Function Operator">̇</a><a id="3904" class="Symbol">}</a> <a id="3906" class="Symbol">→</a> <a id="3908" href="Prelude.Lifts.html#2802" class="Field">lower</a><a id="3913" class="Symbol">{</a><a id="3914" href="Prelude.Lifts.html#3881" class="Bound">𝓦</a><a id="3915" class="Symbol">}{</a><a id="3917" href="Prelude.Lifts.html#3883" class="Bound">𝓧</a><a id="3918" class="Symbol">}</a> <a id="3920" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3922" href="Prelude.Lifts.html#2790" class="InductiveConstructor">lift</a> <a id="3927" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3929" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3932" href="Prelude.Lifts.html#3897" class="Bound">X</a>
<a id="3934" href="Prelude.Lifts.html#3867" class="Function">lower∼lift</a> <a id="3945" class="Symbol">=</a> <a id="3947" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

<a id="lift∼lower"></a><a id="3953" href="Prelude.Lifts.html#3953" class="Function">lift∼lower</a> <a id="3964" class="Symbol">:</a> <a id="3966" class="Symbol">{</a><a id="3967" href="Prelude.Lifts.html#3967" class="Bound">𝓦</a> <a id="3969" href="Prelude.Lifts.html#3969" class="Bound">𝓧</a> <a id="3971" class="Symbol">:</a> <a id="3973" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3981" class="Symbol">}{</a><a id="3983" href="Prelude.Lifts.html#3983" class="Bound">X</a> <a id="3985" class="Symbol">:</a> <a id="3987" href="Prelude.Lifts.html#3969" class="Bound">𝓧</a> <a id="3989" href="Universes.html#403" class="Function Operator">̇</a><a id="3990" class="Symbol">}</a> <a id="3992" class="Symbol">→</a> <a id="3994" href="Prelude.Lifts.html#2790" class="InductiveConstructor">lift</a> <a id="3999" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="4001" href="Prelude.Lifts.html#2802" class="Field">lower</a> <a id="4007" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="4009" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="4012" class="Symbol">(</a><a id="4013" href="Prelude.Lifts.html#2728" class="Record">Lift</a><a id="4017" class="Symbol">{</a><a id="4018" href="Prelude.Lifts.html#3967" class="Bound">𝓦</a><a id="4019" class="Symbol">}{</a><a id="4021" href="Prelude.Lifts.html#3969" class="Bound">𝓧</a><a id="4022" class="Symbol">}</a> <a id="4024" href="Prelude.Lifts.html#3983" class="Bound">X</a><a id="4025" class="Symbol">)</a>
<a id="4027" href="Prelude.Lifts.html#3953" class="Function">lift∼lower</a> <a id="4038" class="Symbol">=</a> <a id="4040" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
