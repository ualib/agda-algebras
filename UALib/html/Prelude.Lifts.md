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

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda` file, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the [Agda Standard Library][] (in the `Level` module), is defined as follows.

<pre class="Agda">

<a id="2728" class="Keyword">record</a> <a id="Lift"></a><a id="2735" href="Prelude.Lifts.html#2735" class="Record">Lift</a> <a id="2740" class="Symbol">{</a><a id="2741" href="Prelude.Lifts.html#2741" class="Bound">𝓦</a> <a id="2743" href="Prelude.Lifts.html#2743" class="Bound">𝓤</a> <a id="2745" class="Symbol">:</a> <a id="2747" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2755" class="Symbol">}</a> <a id="2757" class="Symbol">(</a><a id="2758" href="Prelude.Lifts.html#2758" class="Bound">X</a> <a id="2760" class="Symbol">:</a> <a id="2762" href="Prelude.Lifts.html#2743" class="Bound">𝓤</a> <a id="2764" href="Universes.html#403" class="Function Operator">̇</a><a id="2765" class="Symbol">)</a> <a id="2767" class="Symbol">:</a> <a id="2769" href="Prelude.Lifts.html#2743" class="Bound">𝓤</a> <a id="2771" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2773" href="Prelude.Lifts.html#2741" class="Bound">𝓦</a> <a id="2775" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2778" class="Keyword">where</a>
 <a id="2785" class="Keyword">constructor</a> <a id="lift"></a><a id="2797" href="Prelude.Lifts.html#2797" class="InductiveConstructor">lift</a>
 <a id="2803" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2809" href="Prelude.Lifts.html#2809" class="Field">lower</a> <a id="2815" class="Symbol">:</a> <a id="2817" href="Prelude.Lifts.html#2758" class="Bound">X</a>
<a id="2819" class="Keyword">open</a> <a id="2824" href="Prelude.Lifts.html#2735" class="Module">Lift</a>

</pre>

Next, we give various ways to lift function types.

<pre class="Agda">

<a id="lift-dom"></a><a id="2908" href="Prelude.Lifts.html#2908" class="Function">lift-dom</a> <a id="2917" class="Symbol">:</a> <a id="2919" class="Symbol">{</a><a id="2920" href="Prelude.Lifts.html#2920" class="Bound">𝓦</a> <a id="2922" href="Prelude.Lifts.html#2922" class="Bound">𝓧</a> <a id="2924" href="Prelude.Lifts.html#2924" class="Bound">𝓨</a> <a id="2926" class="Symbol">:</a> <a id="2928" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2936" class="Symbol">}{</a><a id="2938" href="Prelude.Lifts.html#2938" class="Bound">X</a> <a id="2940" class="Symbol">:</a> <a id="2942" href="Prelude.Lifts.html#2922" class="Bound">𝓧</a> <a id="2944" href="Universes.html#403" class="Function Operator">̇</a><a id="2945" class="Symbol">}{</a><a id="2947" href="Prelude.Lifts.html#2947" class="Bound">Y</a> <a id="2949" class="Symbol">:</a> <a id="2951" href="Prelude.Lifts.html#2924" class="Bound">𝓨</a> <a id="2953" href="Universes.html#403" class="Function Operator">̇</a><a id="2954" class="Symbol">}</a> <a id="2956" class="Symbol">→</a> <a id="2958" class="Symbol">(</a><a id="2959" href="Prelude.Lifts.html#2938" class="Bound">X</a> <a id="2961" class="Symbol">→</a> <a id="2963" href="Prelude.Lifts.html#2947" class="Bound">Y</a><a id="2964" class="Symbol">)</a> <a id="2966" class="Symbol">→</a> <a id="2968" class="Symbol">(</a><a id="2969" href="Prelude.Lifts.html#2735" class="Record">Lift</a><a id="2973" class="Symbol">{</a><a id="2974" href="Prelude.Lifts.html#2920" class="Bound">𝓦</a><a id="2975" class="Symbol">}{</a><a id="2977" href="Prelude.Lifts.html#2922" class="Bound">𝓧</a><a id="2978" class="Symbol">}</a> <a id="2980" href="Prelude.Lifts.html#2938" class="Bound">X</a> <a id="2982" class="Symbol">→</a> <a id="2984" href="Prelude.Lifts.html#2947" class="Bound">Y</a><a id="2985" class="Symbol">)</a>
<a id="2987" href="Prelude.Lifts.html#2908" class="Function">lift-dom</a> <a id="2996" href="Prelude.Lifts.html#2996" class="Bound">f</a> <a id="2998" class="Symbol">=</a> <a id="3000" class="Symbol">λ</a> <a id="3002" href="Prelude.Lifts.html#3002" class="Bound">x</a> <a id="3004" class="Symbol">→</a> <a id="3006" class="Symbol">(</a><a id="3007" href="Prelude.Lifts.html#2996" class="Bound">f</a> <a id="3009" class="Symbol">(</a><a id="3010" href="Prelude.Lifts.html#2809" class="Field">lower</a> <a id="3016" href="Prelude.Lifts.html#3002" class="Bound">x</a><a id="3017" class="Symbol">))</a>

<a id="lift-cod"></a><a id="3021" href="Prelude.Lifts.html#3021" class="Function">lift-cod</a> <a id="3030" class="Symbol">:</a> <a id="3032" class="Symbol">{</a><a id="3033" href="Prelude.Lifts.html#3033" class="Bound">𝓦</a> <a id="3035" href="Prelude.Lifts.html#3035" class="Bound">𝓧</a> <a id="3037" href="Prelude.Lifts.html#3037" class="Bound">𝓨</a> <a id="3039" class="Symbol">:</a> <a id="3041" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3049" class="Symbol">}{</a><a id="3051" href="Prelude.Lifts.html#3051" class="Bound">X</a> <a id="3053" class="Symbol">:</a> <a id="3055" href="Prelude.Lifts.html#3035" class="Bound">𝓧</a> <a id="3057" href="Universes.html#403" class="Function Operator">̇</a><a id="3058" class="Symbol">}{</a><a id="3060" href="Prelude.Lifts.html#3060" class="Bound">Y</a> <a id="3062" class="Symbol">:</a> <a id="3064" href="Prelude.Lifts.html#3037" class="Bound">𝓨</a> <a id="3066" href="Universes.html#403" class="Function Operator">̇</a><a id="3067" class="Symbol">}</a> <a id="3069" class="Symbol">→</a> <a id="3071" class="Symbol">(</a><a id="3072" href="Prelude.Lifts.html#3051" class="Bound">X</a> <a id="3074" class="Symbol">→</a> <a id="3076" href="Prelude.Lifts.html#3060" class="Bound">Y</a><a id="3077" class="Symbol">)</a> <a id="3079" class="Symbol">→</a> <a id="3081" class="Symbol">(</a><a id="3082" href="Prelude.Lifts.html#3051" class="Bound">X</a> <a id="3084" class="Symbol">→</a> <a id="3086" href="Prelude.Lifts.html#2735" class="Record">Lift</a><a id="3090" class="Symbol">{</a><a id="3091" href="Prelude.Lifts.html#3033" class="Bound">𝓦</a><a id="3092" class="Symbol">}{</a><a id="3094" href="Prelude.Lifts.html#3037" class="Bound">𝓨</a><a id="3095" class="Symbol">}</a> <a id="3097" href="Prelude.Lifts.html#3060" class="Bound">Y</a><a id="3098" class="Symbol">)</a>
<a id="3100" href="Prelude.Lifts.html#3021" class="Function">lift-cod</a> <a id="3109" href="Prelude.Lifts.html#3109" class="Bound">f</a> <a id="3111" class="Symbol">=</a> <a id="3113" class="Symbol">λ</a> <a id="3115" href="Prelude.Lifts.html#3115" class="Bound">x</a> <a id="3117" class="Symbol">→</a> <a id="3119" href="Prelude.Lifts.html#2797" class="InductiveConstructor">lift</a> <a id="3124" class="Symbol">(</a><a id="3125" href="Prelude.Lifts.html#3109" class="Bound">f</a> <a id="3127" href="Prelude.Lifts.html#3115" class="Bound">x</a><a id="3128" class="Symbol">)</a>

<a id="lift-fun"></a><a id="3131" href="Prelude.Lifts.html#3131" class="Function">lift-fun</a> <a id="3140" class="Symbol">:</a> <a id="3142" class="Symbol">{</a><a id="3143" href="Prelude.Lifts.html#3143" class="Bound">𝓦</a> <a id="3145" href="Prelude.Lifts.html#3145" class="Bound">𝓩</a> <a id="3147" href="Prelude.Lifts.html#3147" class="Bound">𝓧</a> <a id="3149" href="Prelude.Lifts.html#3149" class="Bound">𝓨</a> <a id="3151" class="Symbol">:</a> <a id="3153" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3161" class="Symbol">}{</a><a id="3163" href="Prelude.Lifts.html#3163" class="Bound">X</a> <a id="3165" class="Symbol">:</a> <a id="3167" href="Prelude.Lifts.html#3147" class="Bound">𝓧</a> <a id="3169" href="Universes.html#403" class="Function Operator">̇</a><a id="3170" class="Symbol">}{</a><a id="3172" href="Prelude.Lifts.html#3172" class="Bound">Y</a> <a id="3174" class="Symbol">:</a> <a id="3176" href="Prelude.Lifts.html#3149" class="Bound">𝓨</a> <a id="3178" href="Universes.html#403" class="Function Operator">̇</a><a id="3179" class="Symbol">}</a> <a id="3181" class="Symbol">→</a> <a id="3183" class="Symbol">(</a><a id="3184" href="Prelude.Lifts.html#3163" class="Bound">X</a> <a id="3186" class="Symbol">→</a> <a id="3188" href="Prelude.Lifts.html#3172" class="Bound">Y</a><a id="3189" class="Symbol">)</a> <a id="3191" class="Symbol">→</a> <a id="3193" class="Symbol">(</a><a id="3194" href="Prelude.Lifts.html#2735" class="Record">Lift</a><a id="3198" class="Symbol">{</a><a id="3199" href="Prelude.Lifts.html#3143" class="Bound">𝓦</a><a id="3200" class="Symbol">}{</a><a id="3202" href="Prelude.Lifts.html#3147" class="Bound">𝓧</a><a id="3203" class="Symbol">}</a> <a id="3205" href="Prelude.Lifts.html#3163" class="Bound">X</a> <a id="3207" class="Symbol">→</a> <a id="3209" href="Prelude.Lifts.html#2735" class="Record">Lift</a><a id="3213" class="Symbol">{</a><a id="3214" href="Prelude.Lifts.html#3145" class="Bound">𝓩</a><a id="3215" class="Symbol">}{</a><a id="3217" href="Prelude.Lifts.html#3149" class="Bound">𝓨</a><a id="3218" class="Symbol">}</a> <a id="3220" href="Prelude.Lifts.html#3172" class="Bound">Y</a><a id="3221" class="Symbol">)</a>
<a id="3223" href="Prelude.Lifts.html#3131" class="Function">lift-fun</a> <a id="3232" href="Prelude.Lifts.html#3232" class="Bound">f</a> <a id="3234" class="Symbol">=</a> <a id="3236" class="Symbol">λ</a> <a id="3238" href="Prelude.Lifts.html#3238" class="Bound">x</a> <a id="3240" class="Symbol">→</a> <a id="3242" href="Prelude.Lifts.html#2797" class="InductiveConstructor">lift</a> <a id="3247" class="Symbol">(</a><a id="3248" href="Prelude.Lifts.html#3232" class="Bound">f</a> <a id="3250" class="Symbol">(</a><a id="3251" href="Prelude.Lifts.html#2809" class="Field">lower</a> <a id="3257" href="Prelude.Lifts.html#3238" class="Bound">x</a><a id="3258" class="Symbol">))</a>

</pre>

We will also need to know that lift and lower compose to the identity.

<pre class="Agda">

<a id="lower∼lift"></a><a id="3360" href="Prelude.Lifts.html#3360" class="Function">lower∼lift</a> <a id="3371" class="Symbol">:</a> <a id="3373" class="Symbol">{</a><a id="3374" href="Prelude.Lifts.html#3374" class="Bound">𝓦</a> <a id="3376" href="Prelude.Lifts.html#3376" class="Bound">𝓧</a> <a id="3378" class="Symbol">:</a> <a id="3380" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3388" class="Symbol">}{</a><a id="3390" href="Prelude.Lifts.html#3390" class="Bound">X</a> <a id="3392" class="Symbol">:</a> <a id="3394" href="Prelude.Lifts.html#3376" class="Bound">𝓧</a> <a id="3396" href="Universes.html#403" class="Function Operator">̇</a><a id="3397" class="Symbol">}</a> <a id="3399" class="Symbol">→</a> <a id="3401" href="Prelude.Lifts.html#2809" class="Field">lower</a><a id="3406" class="Symbol">{</a><a id="3407" href="Prelude.Lifts.html#3374" class="Bound">𝓦</a><a id="3408" class="Symbol">}{</a><a id="3410" href="Prelude.Lifts.html#3376" class="Bound">𝓧</a><a id="3411" class="Symbol">}</a> <a id="3413" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3415" href="Prelude.Lifts.html#2797" class="InductiveConstructor">lift</a> <a id="3420" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3422" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3425" href="Prelude.Lifts.html#3390" class="Bound">X</a>
<a id="3427" href="Prelude.Lifts.html#3360" class="Function">lower∼lift</a> <a id="3438" class="Symbol">=</a> <a id="3440" href="Prelude.Equality.html#1266" class="InductiveConstructor">refl</a> <a id="3445" class="Symbol">_</a>

<a id="lift∼lower"></a><a id="3448" href="Prelude.Lifts.html#3448" class="Function">lift∼lower</a> <a id="3459" class="Symbol">:</a> <a id="3461" class="Symbol">{</a><a id="3462" href="Prelude.Lifts.html#3462" class="Bound">𝓦</a> <a id="3464" href="Prelude.Lifts.html#3464" class="Bound">𝓧</a> <a id="3466" class="Symbol">:</a> <a id="3468" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3476" class="Symbol">}{</a><a id="3478" href="Prelude.Lifts.html#3478" class="Bound">X</a> <a id="3480" class="Symbol">:</a> <a id="3482" href="Prelude.Lifts.html#3464" class="Bound">𝓧</a> <a id="3484" href="Universes.html#403" class="Function Operator">̇</a><a id="3485" class="Symbol">}</a> <a id="3487" class="Symbol">→</a> <a id="3489" href="Prelude.Lifts.html#2797" class="InductiveConstructor">lift</a> <a id="3494" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3496" href="Prelude.Lifts.html#2809" class="Field">lower</a> <a id="3502" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3504" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3507" class="Symbol">(</a><a id="3508" href="Prelude.Lifts.html#2735" class="Record">Lift</a><a id="3512" class="Symbol">{</a><a id="3513" href="Prelude.Lifts.html#3462" class="Bound">𝓦</a><a id="3514" class="Symbol">}{</a><a id="3516" href="Prelude.Lifts.html#3464" class="Bound">𝓧</a><a id="3517" class="Symbol">}</a> <a id="3519" href="Prelude.Lifts.html#3478" class="Bound">X</a><a id="3520" class="Symbol">)</a>
<a id="3522" href="Prelude.Lifts.html#3448" class="Function">lift∼lower</a> <a id="3533" class="Symbol">=</a> <a id="3535" href="Prelude.Equality.html#1266" class="InductiveConstructor">refl</a> <a id="3540" class="Symbol">_</a>

</pre>


---------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
