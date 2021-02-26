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

Luckily, there are ways to overcome this technical issue. We describe general lifting and lowering functions below, and then later, in the section on [Lifts of algebras](https://ualib.gitlab.io/Algebras.Algebras.html#lifts-of-algebras), we'll see the domain-specific analogs of these tools which turn out to have some nice properties that make them very effective for resolving universe level problems when working with algebra datatypes.

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

<a id="2734" class="Keyword">record</a> <a id="Lift"></a><a id="2741" href="Prelude.Lifts.html#2741" class="Record">Lift</a> <a id="2746" class="Symbol">{</a><a id="2747" href="Prelude.Lifts.html#2747" class="Bound">𝓤</a> <a id="2749" href="Prelude.Lifts.html#2749" class="Bound">𝓦</a> <a id="2751" class="Symbol">:</a> <a id="2753" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2761" class="Symbol">}</a> <a id="2763" class="Symbol">(</a><a id="2764" href="Prelude.Lifts.html#2764" class="Bound">X</a> <a id="2766" class="Symbol">:</a> <a id="2768" href="Prelude.Lifts.html#2747" class="Bound">𝓤</a> <a id="2770" href="Universes.html#403" class="Function Operator">̇</a><a id="2771" class="Symbol">)</a> <a id="2773" class="Symbol">:</a> <a id="2775" href="Prelude.Lifts.html#2747" class="Bound">𝓤</a> <a id="2777" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2779" href="Prelude.Lifts.html#2749" class="Bound">𝓦</a> <a id="2781" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2784" class="Keyword">where</a>
 <a id="2791" class="Keyword">constructor</a> <a id="lift"></a><a id="2803" href="Prelude.Lifts.html#2803" class="InductiveConstructor">lift</a>
 <a id="2809" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2815" href="Prelude.Lifts.html#2815" class="Field">lower</a> <a id="2821" class="Symbol">:</a> <a id="2823" href="Prelude.Lifts.html#2764" class="Bound">X</a>
<a id="2825" class="Keyword">open</a> <a id="2830" href="Prelude.Lifts.html#2741" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2914" href="Prelude.Lifts.html#2914" class="Function">lift-dom</a> <a id="2923" class="Symbol">:</a> <a id="2925" class="Symbol">{</a><a id="2926" href="Prelude.Lifts.html#2926" class="Bound">𝓧</a> <a id="2928" href="Prelude.Lifts.html#2928" class="Bound">𝓨</a> <a id="2930" href="Prelude.Lifts.html#2930" class="Bound">𝓦</a> <a id="2932" class="Symbol">:</a> <a id="2934" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2942" class="Symbol">}{</a><a id="2944" href="Prelude.Lifts.html#2944" class="Bound">X</a> <a id="2946" class="Symbol">:</a> <a id="2948" href="Prelude.Lifts.html#2926" class="Bound">𝓧</a> <a id="2950" href="Universes.html#403" class="Function Operator">̇</a><a id="2951" class="Symbol">}{</a><a id="2953" href="Prelude.Lifts.html#2953" class="Bound">Y</a> <a id="2955" class="Symbol">:</a> <a id="2957" href="Prelude.Lifts.html#2928" class="Bound">𝓨</a> <a id="2959" href="Universes.html#403" class="Function Operator">̇</a><a id="2960" class="Symbol">}</a> <a id="2962" class="Symbol">→</a> <a id="2964" class="Symbol">(</a><a id="2965" href="Prelude.Lifts.html#2944" class="Bound">X</a> <a id="2967" class="Symbol">→</a> <a id="2969" href="Prelude.Lifts.html#2953" class="Bound">Y</a><a id="2970" class="Symbol">)</a> <a id="2972" class="Symbol">→</a> <a id="2974" class="Symbol">(</a><a id="2975" href="Prelude.Lifts.html#2741" class="Record">Lift</a><a id="2979" class="Symbol">{</a><a id="2980" href="Prelude.Lifts.html#2926" class="Bound">𝓧</a><a id="2981" class="Symbol">}{</a><a id="2983" href="Prelude.Lifts.html#2930" class="Bound">𝓦</a><a id="2984" class="Symbol">}</a> <a id="2986" href="Prelude.Lifts.html#2944" class="Bound">X</a> <a id="2988" class="Symbol">→</a> <a id="2990" href="Prelude.Lifts.html#2953" class="Bound">Y</a><a id="2991" class="Symbol">)</a>
<a id="2993" href="Prelude.Lifts.html#2914" class="Function">lift-dom</a> <a id="3002" href="Prelude.Lifts.html#3002" class="Bound">f</a> <a id="3004" class="Symbol">=</a> <a id="3006" class="Symbol">λ</a> <a id="3008" href="Prelude.Lifts.html#3008" class="Bound">x</a> <a id="3010" class="Symbol">→</a> <a id="3012" class="Symbol">(</a><a id="3013" href="Prelude.Lifts.html#3002" class="Bound">f</a> <a id="3015" class="Symbol">(</a><a id="3016" href="Prelude.Lifts.html#2815" class="Field">lower</a> <a id="3022" href="Prelude.Lifts.html#3008" class="Bound">x</a><a id="3023" class="Symbol">))</a>

<a id="lift-cod"></a><a id="3027" href="Prelude.Lifts.html#3027" class="Function">lift-cod</a> <a id="3036" class="Symbol">:</a> <a id="3038" class="Symbol">{</a><a id="3039" href="Prelude.Lifts.html#3039" class="Bound">𝓧</a> <a id="3041" href="Prelude.Lifts.html#3041" class="Bound">𝓨</a> <a id="3043" href="Prelude.Lifts.html#3043" class="Bound">𝓦</a> <a id="3045" class="Symbol">:</a> <a id="3047" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3055" class="Symbol">}{</a><a id="3057" href="Prelude.Lifts.html#3057" class="Bound">X</a> <a id="3059" class="Symbol">:</a> <a id="3061" href="Prelude.Lifts.html#3039" class="Bound">𝓧</a> <a id="3063" href="Universes.html#403" class="Function Operator">̇</a><a id="3064" class="Symbol">}{</a><a id="3066" href="Prelude.Lifts.html#3066" class="Bound">Y</a> <a id="3068" class="Symbol">:</a> <a id="3070" href="Prelude.Lifts.html#3041" class="Bound">𝓨</a> <a id="3072" href="Universes.html#403" class="Function Operator">̇</a><a id="3073" class="Symbol">}</a> <a id="3075" class="Symbol">→</a> <a id="3077" class="Symbol">(</a><a id="3078" href="Prelude.Lifts.html#3057" class="Bound">X</a> <a id="3080" class="Symbol">→</a> <a id="3082" href="Prelude.Lifts.html#3066" class="Bound">Y</a><a id="3083" class="Symbol">)</a> <a id="3085" class="Symbol">→</a> <a id="3087" class="Symbol">(</a><a id="3088" href="Prelude.Lifts.html#3057" class="Bound">X</a> <a id="3090" class="Symbol">→</a> <a id="3092" href="Prelude.Lifts.html#2741" class="Record">Lift</a><a id="3096" class="Symbol">{</a><a id="3097" href="Prelude.Lifts.html#3041" class="Bound">𝓨</a><a id="3098" class="Symbol">}{</a><a id="3100" href="Prelude.Lifts.html#3043" class="Bound">𝓦</a><a id="3101" class="Symbol">}</a> <a id="3103" href="Prelude.Lifts.html#3066" class="Bound">Y</a><a id="3104" class="Symbol">)</a>
<a id="3106" href="Prelude.Lifts.html#3027" class="Function">lift-cod</a> <a id="3115" href="Prelude.Lifts.html#3115" class="Bound">f</a> <a id="3117" class="Symbol">=</a> <a id="3119" class="Symbol">λ</a> <a id="3121" href="Prelude.Lifts.html#3121" class="Bound">x</a> <a id="3123" class="Symbol">→</a> <a id="3125" href="Prelude.Lifts.html#2803" class="InductiveConstructor">lift</a> <a id="3130" class="Symbol">(</a><a id="3131" href="Prelude.Lifts.html#3115" class="Bound">f</a> <a id="3133" href="Prelude.Lifts.html#3121" class="Bound">x</a><a id="3134" class="Symbol">)</a>

<a id="lift-fun"></a><a id="3137" href="Prelude.Lifts.html#3137" class="Function">lift-fun</a> <a id="3146" class="Symbol">:</a> <a id="3148" class="Symbol">{</a><a id="3149" href="Prelude.Lifts.html#3149" class="Bound">𝓧</a> <a id="3151" href="Prelude.Lifts.html#3151" class="Bound">𝓨</a> <a id="3153" href="Prelude.Lifts.html#3153" class="Bound">𝓦</a> <a id="3155" href="Prelude.Lifts.html#3155" class="Bound">𝓩</a> <a id="3157" class="Symbol">:</a> <a id="3159" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3167" class="Symbol">}{</a><a id="3169" href="Prelude.Lifts.html#3169" class="Bound">X</a> <a id="3171" class="Symbol">:</a> <a id="3173" href="Prelude.Lifts.html#3149" class="Bound">𝓧</a> <a id="3175" href="Universes.html#403" class="Function Operator">̇</a><a id="3176" class="Symbol">}{</a><a id="3178" href="Prelude.Lifts.html#3178" class="Bound">Y</a> <a id="3180" class="Symbol">:</a> <a id="3182" href="Prelude.Lifts.html#3151" class="Bound">𝓨</a> <a id="3184" href="Universes.html#403" class="Function Operator">̇</a><a id="3185" class="Symbol">}</a> <a id="3187" class="Symbol">→</a> <a id="3189" class="Symbol">(</a><a id="3190" href="Prelude.Lifts.html#3169" class="Bound">X</a> <a id="3192" class="Symbol">→</a> <a id="3194" href="Prelude.Lifts.html#3178" class="Bound">Y</a><a id="3195" class="Symbol">)</a> <a id="3197" class="Symbol">→</a> <a id="3199" class="Symbol">(</a><a id="3200" href="Prelude.Lifts.html#2741" class="Record">Lift</a><a id="3204" class="Symbol">{</a><a id="3205" href="Prelude.Lifts.html#3149" class="Bound">𝓧</a><a id="3206" class="Symbol">}{</a><a id="3208" href="Prelude.Lifts.html#3153" class="Bound">𝓦</a><a id="3209" class="Symbol">}</a> <a id="3211" href="Prelude.Lifts.html#3169" class="Bound">X</a> <a id="3213" class="Symbol">→</a> <a id="3215" href="Prelude.Lifts.html#2741" class="Record">Lift</a><a id="3219" class="Symbol">{</a><a id="3220" href="Prelude.Lifts.html#3151" class="Bound">𝓨</a><a id="3221" class="Symbol">}{</a><a id="3223" href="Prelude.Lifts.html#3155" class="Bound">𝓩</a><a id="3224" class="Symbol">}</a> <a id="3226" href="Prelude.Lifts.html#3178" class="Bound">Y</a><a id="3227" class="Symbol">)</a>
<a id="3229" href="Prelude.Lifts.html#3137" class="Function">lift-fun</a> <a id="3238" href="Prelude.Lifts.html#3238" class="Bound">f</a> <a id="3240" class="Symbol">=</a> <a id="3242" class="Symbol">λ</a> <a id="3244" href="Prelude.Lifts.html#3244" class="Bound">x</a> <a id="3246" class="Symbol">→</a> <a id="3248" href="Prelude.Lifts.html#2803" class="InductiveConstructor">lift</a> <a id="3253" class="Symbol">(</a><a id="3254" href="Prelude.Lifts.html#3238" class="Bound">f</a> <a id="3256" class="Symbol">(</a><a id="3257" href="Prelude.Lifts.html#2815" class="Field">lower</a> <a id="3263" href="Prelude.Lifts.html#3244" class="Bound">x</a><a id="3264" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3366" href="Prelude.Lifts.html#3366" class="Function">lower∼lift</a> <a id="3377" class="Symbol">:</a> <a id="3379" class="Symbol">{</a><a id="3380" href="Prelude.Lifts.html#3380" class="Bound">𝓧</a> <a id="3382" href="Prelude.Lifts.html#3382" class="Bound">𝓦</a> <a id="3384" class="Symbol">:</a> <a id="3386" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3394" class="Symbol">}{</a><a id="3396" href="Prelude.Lifts.html#3396" class="Bound">X</a> <a id="3398" class="Symbol">:</a> <a id="3400" href="Prelude.Lifts.html#3380" class="Bound">𝓧</a> <a id="3402" href="Universes.html#403" class="Function Operator">̇</a><a id="3403" class="Symbol">}</a> <a id="3405" class="Symbol">→</a> <a id="3407" href="Prelude.Lifts.html#2815" class="Field">lower</a><a id="3412" class="Symbol">{</a><a id="3413" href="Prelude.Lifts.html#3380" class="Bound">𝓧</a><a id="3414" class="Symbol">}{</a><a id="3416" href="Prelude.Lifts.html#3382" class="Bound">𝓦</a><a id="3417" class="Symbol">}</a> <a id="3419" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3421" href="Prelude.Lifts.html#2803" class="InductiveConstructor">lift</a> <a id="3426" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3428" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3431" href="Prelude.Lifts.html#3396" class="Bound">X</a>
<a id="3433" href="Prelude.Lifts.html#3366" class="Function">lower∼lift</a> <a id="3444" class="Symbol">=</a> <a id="3446" href="Prelude.Equality.html#1638" class="InductiveConstructor">refl</a> <a id="3451" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3454" href="Prelude.Lifts.html#3454" class="Function">lift∼lower</a> <a id="3465" class="Symbol">:</a> <a id="3467" class="Symbol">{</a><a id="3468" href="Prelude.Lifts.html#3468" class="Bound">𝓧</a> <a id="3470" href="Prelude.Lifts.html#3470" class="Bound">𝓦</a> <a id="3472" class="Symbol">:</a> <a id="3474" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3482" class="Symbol">}{</a><a id="3484" href="Prelude.Lifts.html#3484" class="Bound">X</a> <a id="3486" class="Symbol">:</a> <a id="3488" href="Prelude.Lifts.html#3468" class="Bound">𝓧</a> <a id="3490" href="Universes.html#403" class="Function Operator">̇</a><a id="3491" class="Symbol">}</a> <a id="3493" class="Symbol">→</a> <a id="3495" href="Prelude.Lifts.html#2803" class="InductiveConstructor">lift</a> <a id="3500" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3502" href="Prelude.Lifts.html#2815" class="Field">lower</a> <a id="3508" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3510" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3513" class="Symbol">(</a><a id="3514" href="Prelude.Lifts.html#2741" class="Record">Lift</a><a id="3518" class="Symbol">{</a><a id="3519" href="Prelude.Lifts.html#3468" class="Bound">𝓧</a><a id="3520" class="Symbol">}{</a><a id="3522" href="Prelude.Lifts.html#3470" class="Bound">𝓦</a><a id="3523" class="Symbol">}</a> <a id="3525" href="Prelude.Lifts.html#3484" class="Bound">X</a><a id="3526" class="Symbol">)</a>
<a id="3528" href="Prelude.Lifts.html#3454" class="Function">lift∼lower</a> <a id="3539" class="Symbol">=</a> <a id="3541" href="Prelude.Equality.html#1638" class="InductiveConstructor">refl</a> <a id="3546" class="Symbol">_</a>

</pre>


---------------

[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
