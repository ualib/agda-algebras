---
layout: default
title : Overture.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This is the [Overture.Equality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="266" class="Symbol">{-#</a> <a id="270" class="Keyword">OPTIONS</a> <a id="278" class="Pragma">--without-K</a> <a id="290" class="Pragma">--exact-split</a> <a id="304" class="Pragma">--safe</a> <a id="311" class="Symbol">#-}</a>

<a id="316" class="Keyword">module</a> <a id="323" href="Overture.Equality.html" class="Module">Overture.Equality</a> <a id="341" class="Keyword">where</a>

<a id="348" class="Keyword">open</a> <a id="353" class="Keyword">import</a> <a id="360" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="383" class="Keyword">public</a>

</pre>

#### <a id="definitional-equality">Definitional equality</a>

Here we discuss what is probably the most important type in [MLTT][]. It is called *definitional equality*. This concept is easily understood, at least heuristically, with the following slogan:

*Definitional equality is the substitution-preserving equivalence relation generated by definitions.*

We will make this precise below, but first let us quote from a primary source.

In [An Intuitionistic Theory of Types: Predicative Part](https://www.sciencedirect.com/science/article/pii/S0049237X08719451), Per Martin-Löf offers the following definition (italics added):<sup>[1](Overture.Equality.html#fn1)</sup>

"*Definitional equality* is defined to be the equivalence relation, that is, reflexive, symmetric and transitive relation, which is generated by the principles that a definiendum is always definitionally equal to its definiens and that definitional equality is preserved under substitution."<sup>[2](Overture.Equality.html#fn2)

To be sure we understand what this means, let `:=` denote the relation with respect to which `x` is related to `y` (denoted `x := y`) if and only if `y` *is the definition of* `x`.  Then the definitional equality relation `≡` is the reflexive, symmetric, transitive, substitutive closure of `:=`. By *subsitutive closure* we mean closure under the following *substitution rule*.


```agda
    {A : 𝓤 ̇} {B : A → 𝓦 ̇} {x y : A}   x ≡ y
    ------------------------------------------
                B x ≡ B y
```

The datatype we use to represent definitional equality is imported from the Identity-Type module of the [Type Topology][] library, but apart from superficial syntactic differences, it is equivalent to the identity type used in all other Agda libraries we know of.  We repeat the definition here for easy reference.

<pre class="Agda">

<a id="2249" class="Keyword">module</a> <a id="hide-refl"></a><a id="2256" href="Overture.Equality.html#2256" class="Module">hide-refl</a> <a id="2266" class="Keyword">where</a>

 <a id="2274" class="Keyword">data</a> <a id="hide-refl._≡_"></a><a id="2279" href="Overture.Equality.html#2279" class="Datatype Operator">_≡_</a> <a id="2283" class="Symbol">{</a><a id="2284" href="Overture.Equality.html#2284" class="Bound">A</a> <a id="2286" class="Symbol">:</a> <a id="2288" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2290" href="Universes.html#403" class="Function Operator">̇</a><a id="2291" class="Symbol">}</a> <a id="2293" class="Symbol">:</a> <a id="2295" href="Overture.Equality.html#2284" class="Bound">A</a> <a id="2297" class="Symbol">→</a> <a id="2299" href="Overture.Equality.html#2284" class="Bound">A</a> <a id="2301" class="Symbol">→</a> <a id="2303" href="Overture.Equality.html#2288" class="Bound">𝓤</a> <a id="2305" href="Universes.html#403" class="Function Operator">̇</a> <a id="2307" class="Keyword">where</a> <a id="hide-refl._≡_.refl"></a><a id="2313" href="Overture.Equality.html#2313" class="InductiveConstructor">refl</a> <a id="2318" class="Symbol">:</a> <a id="2320" class="Symbol">{</a><a id="2321" href="Overture.Equality.html#2321" class="Bound">x</a> <a id="2323" class="Symbol">:</a> <a id="2325" href="Overture.Equality.html#2284" class="Bound">A</a><a id="2326" class="Symbol">}</a> <a id="2328" class="Symbol">→</a> <a id="2330" href="Overture.Equality.html#2321" class="Bound">x</a> <a id="2332" href="Overture.Equality.html#2279" class="Datatype Operator">≡</a> <a id="2334" href="Overture.Equality.html#2321" class="Bound">x</a>

<a id="2337" class="Keyword">open</a> <a id="2342" class="Keyword">import</a> <a id="2349" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="2363" class="Keyword">renaming</a> <a id="2372" class="Symbol">(</a><a id="2373" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="2377" class="Symbol">to</a> <a id="2380" class="Keyword">infix</a> <a id="2386" class="Number">0</a> <a id="_≡_"></a><a id="2388" href="Overture.Equality.html#2388" class="Datatype Operator">_≡_</a><a id="2391" class="Symbol">)</a> <a id="2393" class="Keyword">public</a>

</pre>

Whenever we need to complete a proof by simply asserting that `x` is definitionally equal to itself, we invoke `refl`.  If we need to make explicit the implicit argument `x`, then we use `refl {x = x}`.

Of course `≡` is an equivalence relation and the formal proof of this fact is trivial. We don't need to prove reflexivity since it is the defining property of `≡`.  Here are the (trivial) proofs of symmetry and transitivity of `≡`.

<pre class="Agda">

<a id="≡-symmetric"></a><a id="2864" href="Overture.Equality.html#2864" class="Function">≡-symmetric</a> <a id="2876" class="Symbol">:</a> <a id="2878" class="Symbol">{</a><a id="2879" href="Overture.Equality.html#2879" class="Bound">A</a> <a id="2881" class="Symbol">:</a> <a id="2883" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2885" href="Universes.html#403" class="Function Operator">̇</a><a id="2886" class="Symbol">}(</a><a id="2888" href="Overture.Equality.html#2888" class="Bound">x</a> <a id="2890" href="Overture.Equality.html#2890" class="Bound">y</a> <a id="2892" class="Symbol">:</a> <a id="2894" href="Overture.Equality.html#2879" class="Bound">A</a><a id="2895" class="Symbol">)</a> <a id="2897" class="Symbol">→</a> <a id="2899" href="Overture.Equality.html#2888" class="Bound">x</a> <a id="2901" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="2903" href="Overture.Equality.html#2890" class="Bound">y</a> <a id="2905" class="Symbol">→</a> <a id="2907" href="Overture.Equality.html#2890" class="Bound">y</a> <a id="2909" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="2911" href="Overture.Equality.html#2888" class="Bound">x</a>
<a id="2913" href="Overture.Equality.html#2864" class="Function">≡-symmetric</a> <a id="2925" class="Symbol">_</a> <a id="2927" class="Symbol">_</a> <a id="2929" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2934" class="Symbol">=</a> <a id="2936" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="≡-sym"></a><a id="2942" href="Overture.Equality.html#2942" class="Function">≡-sym</a> <a id="2948" class="Symbol">:</a> <a id="2950" class="Symbol">{</a><a id="2951" href="Overture.Equality.html#2951" class="Bound">A</a> <a id="2953" class="Symbol">:</a> <a id="2955" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2957" href="Universes.html#403" class="Function Operator">̇</a><a id="2958" class="Symbol">}{</a><a id="2960" href="Overture.Equality.html#2960" class="Bound">x</a> <a id="2962" href="Overture.Equality.html#2962" class="Bound">y</a> <a id="2964" class="Symbol">:</a> <a id="2966" href="Overture.Equality.html#2951" class="Bound">A</a><a id="2967" class="Symbol">}</a> <a id="2969" class="Symbol">→</a> <a id="2971" href="Overture.Equality.html#2960" class="Bound">x</a> <a id="2973" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="2975" href="Overture.Equality.html#2962" class="Bound">y</a> <a id="2977" class="Symbol">→</a> <a id="2979" href="Overture.Equality.html#2962" class="Bound">y</a> <a id="2981" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="2983" href="Overture.Equality.html#2960" class="Bound">x</a>
<a id="2985" href="Overture.Equality.html#2942" class="Function">≡-sym</a> <a id="2991" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2996" class="Symbol">=</a> <a id="2998" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="≡-transitive"></a><a id="3004" href="Overture.Equality.html#3004" class="Function">≡-transitive</a> <a id="3017" class="Symbol">:</a> <a id="3019" class="Symbol">{</a><a id="3020" href="Overture.Equality.html#3020" class="Bound">A</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3026" href="Universes.html#403" class="Function Operator">̇</a><a id="3027" class="Symbol">}(</a><a id="3029" href="Overture.Equality.html#3029" class="Bound">x</a> <a id="3031" href="Overture.Equality.html#3031" class="Bound">y</a> <a id="3033" href="Overture.Equality.html#3033" class="Bound">z</a> <a id="3035" class="Symbol">:</a> <a id="3037" href="Overture.Equality.html#3020" class="Bound">A</a><a id="3038" class="Symbol">)</a> <a id="3040" class="Symbol">→</a> <a id="3042" href="Overture.Equality.html#3029" class="Bound">x</a> <a id="3044" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3046" href="Overture.Equality.html#3031" class="Bound">y</a> <a id="3048" class="Symbol">→</a> <a id="3050" href="Overture.Equality.html#3031" class="Bound">y</a> <a id="3052" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3054" href="Overture.Equality.html#3033" class="Bound">z</a> <a id="3056" class="Symbol">→</a> <a id="3058" href="Overture.Equality.html#3029" class="Bound">x</a> <a id="3060" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3062" href="Overture.Equality.html#3033" class="Bound">z</a>
<a id="3064" href="Overture.Equality.html#3004" class="Function">≡-transitive</a> <a id="3077" class="Symbol">_</a> <a id="3079" class="Symbol">_</a> <a id="3081" class="Symbol">_</a> <a id="3083" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="3088" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="3093" class="Symbol">=</a> <a id="3095" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

<a id="≡-trans"></a><a id="3101" href="Overture.Equality.html#3101" class="Function">≡-trans</a> <a id="3109" class="Symbol">:</a> <a id="3111" class="Symbol">{</a><a id="3112" href="Overture.Equality.html#3112" class="Bound">A</a> <a id="3114" class="Symbol">:</a> <a id="3116" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3118" href="Universes.html#403" class="Function Operator">̇</a><a id="3119" class="Symbol">}{</a><a id="3121" href="Overture.Equality.html#3121" class="Bound">x</a> <a id="3123" href="Overture.Equality.html#3123" class="Bound">y</a> <a id="3125" href="Overture.Equality.html#3125" class="Bound">z</a> <a id="3127" class="Symbol">:</a> <a id="3129" href="Overture.Equality.html#3112" class="Bound">A</a><a id="3130" class="Symbol">}</a> <a id="3132" class="Symbol">→</a> <a id="3134" href="Overture.Equality.html#3121" class="Bound">x</a> <a id="3136" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3138" href="Overture.Equality.html#3123" class="Bound">y</a> <a id="3140" class="Symbol">→</a> <a id="3142" href="Overture.Equality.html#3123" class="Bound">y</a> <a id="3144" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3146" href="Overture.Equality.html#3125" class="Bound">z</a> <a id="3148" class="Symbol">→</a> <a id="3150" href="Overture.Equality.html#3121" class="Bound">x</a> <a id="3152" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3154" href="Overture.Equality.html#3125" class="Bound">z</a>
<a id="3156" href="Overture.Equality.html#3101" class="Function">≡-trans</a> <a id="3164" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="3169" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="3174" class="Symbol">=</a> <a id="3176" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The only difference between `≡-symmetric` and `≡-sym` (respectively, `≡-transitive` and `≡-trans`) is that the latter has fewer explicit arguments, which is sometimes convenient.

We prove that `≡` obeys the substitution rule (subst) in the next subsection (see the definition of `ap` below), but first we define some syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.<sup>[3](Overture.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="3663" class="Keyword">module</a> <a id="hide-sym-trans"></a><a id="3670" href="Overture.Equality.html#3670" class="Module">hide-sym-trans</a> <a id="3685" class="Symbol">{</a><a id="3686" href="Overture.Equality.html#3686" class="Bound">A</a> <a id="3688" class="Symbol">:</a> <a id="3690" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3692" href="Universes.html#403" class="Function Operator">̇</a><a id="3693" class="Symbol">}</a> <a id="3695" class="Keyword">where</a>

 <a id="hide-sym-trans._⁻¹"></a><a id="3703" href="Overture.Equality.html#3703" class="Function Operator">_⁻¹</a> <a id="3707" class="Symbol">:</a> <a id="3709" class="Symbol">{</a><a id="3710" href="Overture.Equality.html#3710" class="Bound">x</a> <a id="3712" href="Overture.Equality.html#3712" class="Bound">y</a> <a id="3714" class="Symbol">:</a> <a id="3716" href="Overture.Equality.html#3686" class="Bound">A</a><a id="3717" class="Symbol">}</a> <a id="3719" class="Symbol">→</a> <a id="3721" href="Overture.Equality.html#3710" class="Bound">x</a> <a id="3723" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3725" href="Overture.Equality.html#3712" class="Bound">y</a> <a id="3727" class="Symbol">→</a> <a id="3729" href="Overture.Equality.html#3712" class="Bound">y</a> <a id="3731" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3733" href="Overture.Equality.html#3710" class="Bound">x</a>
 <a id="3736" href="Overture.Equality.html#3736" class="Bound">p</a> <a id="3738" href="Overture.Equality.html#3703" class="Function Operator">⁻¹</a> <a id="3741" class="Symbol">=</a> <a id="3743" href="Overture.Equality.html#2942" class="Function">≡-sym</a> <a id="3749" href="Overture.Equality.html#3736" class="Bound">p</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-sym p` we can use the more intuitive `p ⁻¹` . Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

 <a id="hide-sym-trans._∙_"></a><a id="4008" href="Overture.Equality.html#4008" class="Function Operator">_∙_</a> <a id="4012" class="Symbol">:</a> <a id="4014" class="Symbol">{</a><a id="4015" href="Overture.Equality.html#4015" class="Bound">x</a> <a id="4017" href="Overture.Equality.html#4017" class="Bound">y</a> <a id="4019" href="Overture.Equality.html#4019" class="Bound">z</a> <a id="4021" class="Symbol">:</a> <a id="4023" href="Overture.Equality.html#3686" class="Bound">A</a><a id="4024" class="Symbol">}</a> <a id="4026" class="Symbol">→</a> <a id="4028" href="Overture.Equality.html#4015" class="Bound">x</a> <a id="4030" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="4032" href="Overture.Equality.html#4017" class="Bound">y</a> <a id="4034" class="Symbol">→</a> <a id="4036" href="Overture.Equality.html#4017" class="Bound">y</a> <a id="4038" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="4040" href="Overture.Equality.html#4019" class="Bound">z</a> <a id="4042" class="Symbol">→</a> <a id="4044" href="Overture.Equality.html#4015" class="Bound">x</a> <a id="4046" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="4048" href="Overture.Equality.html#4019" class="Bound">z</a>
 <a id="4051" href="Overture.Equality.html#4051" class="Bound">p</a> <a id="4053" href="Overture.Equality.html#4008" class="Function Operator">∙</a> <a id="4055" href="Overture.Equality.html#4055" class="Bound">q</a> <a id="4057" class="Symbol">=</a> <a id="4059" href="Overture.Equality.html#3101" class="Function">≡-trans</a> <a id="4067" href="Overture.Equality.html#4051" class="Bound">p</a> <a id="4069" href="Overture.Equality.html#4055" class="Bound">q</a>

</pre>

As usual, we import the original definitions from the [Type Topology][] library.

<pre class="Agda">

<a id="4180" class="Keyword">open</a> <a id="4185" class="Keyword">import</a> <a id="4192" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="4201" class="Keyword">using</a> <a id="4207" class="Symbol">(</a><a id="4208" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="4211" class="Symbol">;</a> <a id="4213" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="4216" class="Symbol">)</a> <a id="4218" class="Keyword">public</a>

</pre>

#### <a id="transport">Transport</a>

Alonzo Church characterized equality by declaring two things equal iff no property (predicate) can distinguish them.<sup>[4](Overture.Equality.html#fn4)</sup>  In other terms, `x` and `y` are equal iff for all `P` we have `P x → P y`.  One direction of this implication is sometimes called *substitution* or *transport* or *transport along an identity*.  It asserts that *if* two objects are equal and one of them satisfies a predicate, then so does the other. A type representing this notion is defined in the `MGS-MLTT` module of the [Type Topology][] library as follows.<sup>[3](Preliminaries.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="4912" class="Keyword">module</a> <a id="hide-id-transport"></a><a id="4919" href="Overture.Equality.html#4919" class="Module">hide-id-transport</a> <a id="4937" class="Keyword">where</a>

 <a id="hide-id-transport.𝑖𝑑"></a><a id="4945" href="Overture.Equality.html#4945" class="Function">𝑖𝑑</a> <a id="4948" class="Symbol">:</a> <a id="4950" class="Symbol">(</a><a id="4951" href="Overture.Equality.html#4951" class="Bound">A</a> <a id="4953" class="Symbol">:</a> <a id="4955" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4957" href="Universes.html#403" class="Function Operator">̇</a> <a id="4959" class="Symbol">)</a> <a id="4961" class="Symbol">→</a> <a id="4963" href="Overture.Equality.html#4951" class="Bound">A</a> <a id="4965" class="Symbol">→</a> <a id="4967" href="Overture.Equality.html#4951" class="Bound">A</a>
 <a id="4970" href="Overture.Equality.html#4945" class="Function">𝑖𝑑</a> <a id="4973" href="Overture.Equality.html#4973" class="Bound">A</a> <a id="4975" class="Symbol">=</a> <a id="4977" class="Symbol">λ</a> <a id="4979" href="Overture.Equality.html#4979" class="Bound">x</a> <a id="4981" class="Symbol">→</a> <a id="4983" href="Overture.Equality.html#4979" class="Bound">x</a>

 <a id="hide-id-transport.transport"></a><a id="4987" href="Overture.Equality.html#4987" class="Function">transport</a> <a id="4997" class="Symbol">:</a> <a id="4999" class="Symbol">{</a><a id="5000" href="Overture.Equality.html#5000" class="Bound">A</a> <a id="5002" class="Symbol">:</a> <a id="5004" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5006" href="Universes.html#403" class="Function Operator">̇</a><a id="5007" class="Symbol">}(</a><a id="5009" href="Overture.Equality.html#5009" class="Bound">B</a> <a id="5011" class="Symbol">:</a> <a id="5013" href="Overture.Equality.html#5000" class="Bound">A</a> <a id="5015" class="Symbol">→</a> <a id="5017" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5019" href="Universes.html#403" class="Function Operator">̇</a><a id="5020" class="Symbol">){</a><a id="5022" href="Overture.Equality.html#5022" class="Bound">x</a> <a id="5024" href="Overture.Equality.html#5024" class="Bound">y</a> <a id="5026" class="Symbol">:</a> <a id="5028" href="Overture.Equality.html#5000" class="Bound">A</a><a id="5029" class="Symbol">}</a> <a id="5031" class="Symbol">→</a> <a id="5033" href="Overture.Equality.html#5022" class="Bound">x</a> <a id="5035" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="5037" href="Overture.Equality.html#5024" class="Bound">y</a> <a id="5039" class="Symbol">→</a> <a id="5041" href="Overture.Equality.html#5009" class="Bound">B</a> <a id="5043" href="Overture.Equality.html#5022" class="Bound">x</a> <a id="5045" class="Symbol">→</a> <a id="5047" href="Overture.Equality.html#5009" class="Bound">B</a> <a id="5049" href="Overture.Equality.html#5024" class="Bound">y</a>
 <a id="5052" href="Overture.Equality.html#4987" class="Function">transport</a> <a id="5062" href="Overture.Equality.html#5062" class="Bound">B</a> <a id="5064" class="Symbol">(</a><a id="5065" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5070" class="Symbol">{</a><a id="5071" class="Argument">x</a> <a id="5073" class="Symbol">=</a> <a id="5075" href="Overture.Equality.html#5075" class="Bound">x</a><a id="5076" class="Symbol">})</a> <a id="5079" class="Symbol">=</a> <a id="5081" href="Overture.Equality.html#4945" class="Function">𝑖𝑑</a> <a id="5084" class="Symbol">(</a><a id="5085" href="Overture.Equality.html#5062" class="Bound">B</a> <a id="5087" href="Overture.Equality.html#5075" class="Bound">x</a><a id="5088" class="Symbol">)</a>

<a id="5091" class="Keyword">open</a> <a id="5096" class="Keyword">import</a> <a id="5103" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5112" class="Keyword">using</a> <a id="5118" class="Symbol">(</a><a id="5119" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="5121" class="Symbol">;</a> <a id="5123" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="5132" class="Symbol">)</a> <a id="5134" class="Keyword">public</a>

</pre>

As usual, we display definitions of existing types (here, `𝑖𝑑` and `transport`) in a hidden module and then imported their original definition from [Type Topology][].

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `a b : X` of the domain, and an identity proof `p : a ≡ b`, then we obtain a proof of `f a ≡ f b` by simply applying the `ap` function like so, `ap f p : f a ≡ f b`. Escardó defines `ap` in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="5766" class="Keyword">module</a> <a id="hide-ap"></a><a id="5773" href="Overture.Equality.html#5773" class="Module">hide-ap</a> <a id="5781" class="Symbol">{</a><a id="5782" href="Overture.Equality.html#5782" class="Bound">A</a> <a id="5784" class="Symbol">:</a> <a id="5786" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5788" href="Universes.html#403" class="Function Operator">̇</a><a id="5789" class="Symbol">}{</a><a id="5791" href="Overture.Equality.html#5791" class="Bound">B</a> <a id="5793" class="Symbol">:</a> <a id="5795" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5797" href="Universes.html#403" class="Function Operator">̇</a><a id="5798" class="Symbol">}</a> <a id="5800" class="Keyword">where</a>

 <a id="hide-ap.ap"></a><a id="5808" href="Overture.Equality.html#5808" class="Function">ap</a> <a id="5811" class="Symbol">:</a> <a id="5813" class="Symbol">(</a><a id="5814" href="Overture.Equality.html#5814" class="Bound">f</a> <a id="5816" class="Symbol">:</a> <a id="5818" href="Overture.Equality.html#5782" class="Bound">A</a> <a id="5820" class="Symbol">→</a> <a id="5822" href="Overture.Equality.html#5791" class="Bound">B</a><a id="5823" class="Symbol">){</a><a id="5825" href="Overture.Equality.html#5825" class="Bound">x</a> <a id="5827" href="Overture.Equality.html#5827" class="Bound">y</a> <a id="5829" class="Symbol">:</a> <a id="5831" href="Overture.Equality.html#5782" class="Bound">A</a><a id="5832" class="Symbol">}</a> <a id="5834" class="Symbol">→</a> <a id="5836" href="Overture.Equality.html#5825" class="Bound">x</a> <a id="5838" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="5840" href="Overture.Equality.html#5827" class="Bound">y</a> <a id="5842" class="Symbol">→</a> <a id="5844" href="Overture.Equality.html#5814" class="Bound">f</a> <a id="5846" href="Overture.Equality.html#5825" class="Bound">x</a> <a id="5848" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="5850" href="Overture.Equality.html#5814" class="Bound">f</a> <a id="5852" href="Overture.Equality.html#5827" class="Bound">y</a>
 <a id="5855" href="Overture.Equality.html#5808" class="Function">ap</a> <a id="5858" href="Overture.Equality.html#5858" class="Bound">f</a> <a id="5860" class="Symbol">{</a><a id="5861" href="Overture.Equality.html#5861" class="Bound">x</a><a id="5862" class="Symbol">}</a> <a id="5864" href="Overture.Equality.html#5864" class="Bound">p</a> <a id="5866" class="Symbol">=</a> <a id="5868" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5878" class="Symbol">(λ</a> <a id="5881" href="Overture.Equality.html#5881" class="Bound">-</a> <a id="5883" class="Symbol">→</a> <a id="5885" href="Overture.Equality.html#5858" class="Bound">f</a> <a id="5887" href="Overture.Equality.html#5861" class="Bound">x</a> <a id="5889" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="5891" href="Overture.Equality.html#5858" class="Bound">f</a> <a id="5893" href="Overture.Equality.html#5881" class="Bound">-</a><a id="5894" class="Symbol">)</a> <a id="5896" href="Overture.Equality.html#5864" class="Bound">p</a> <a id="5898" class="Symbol">(</a><a id="5899" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5904" class="Symbol">{</a><a id="5905" class="Argument">x</a> <a id="5907" class="Symbol">=</a> <a id="5909" href="Overture.Equality.html#5858" class="Bound">f</a> <a id="5911" href="Overture.Equality.html#5861" class="Bound">x</a><a id="5912" class="Symbol">})</a>

<a id="5916" class="Keyword">open</a> <a id="5921" class="Keyword">import</a> <a id="5928" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5937" class="Keyword">using</a> <a id="5943" class="Symbol">(</a><a id="5944" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="5946" class="Symbol">)</a> <a id="5948" class="Keyword">public</a>

</pre>

Here's a useful variation of `ap` that we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][] (transcribed into TypeTopology/UALib notation of course).

<pre class="Agda">

<a id="cong-app"></a><a id="6167" href="Overture.Equality.html#6167" class="Function">cong-app</a> <a id="6176" class="Symbol">:</a> <a id="6178" class="Symbol">{</a><a id="6179" href="Overture.Equality.html#6179" class="Bound">A</a> <a id="6181" class="Symbol">:</a> <a id="6183" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6185" href="Universes.html#403" class="Function Operator">̇</a><a id="6186" class="Symbol">}{</a><a id="6188" href="Overture.Equality.html#6188" class="Bound">B</a> <a id="6190" class="Symbol">:</a> <a id="6192" href="Overture.Equality.html#6179" class="Bound">A</a> <a id="6194" class="Symbol">→</a> <a id="6196" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6198" href="Universes.html#403" class="Function Operator">̇</a><a id="6199" class="Symbol">}{</a><a id="6201" href="Overture.Equality.html#6201" class="Bound">f</a> <a id="6203" href="Overture.Equality.html#6203" class="Bound">g</a> <a id="6205" class="Symbol">:</a> <a id="6207" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6209" href="Overture.Equality.html#6188" class="Bound">B</a><a id="6210" class="Symbol">}</a> <a id="6212" class="Symbol">→</a> <a id="6214" href="Overture.Equality.html#6201" class="Bound">f</a> <a id="6216" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="6218" href="Overture.Equality.html#6203" class="Bound">g</a> <a id="6220" class="Symbol">→</a> <a id="6222" class="Symbol">∀</a> <a id="6224" href="Overture.Equality.html#6224" class="Bound">x</a> <a id="6226" class="Symbol">→</a> <a id="6228" href="Overture.Equality.html#6201" class="Bound">f</a> <a id="6230" href="Overture.Equality.html#6224" class="Bound">x</a> <a id="6232" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="6234" href="Overture.Equality.html#6203" class="Bound">g</a> <a id="6236" href="Overture.Equality.html#6224" class="Bound">x</a>
<a id="6238" href="Overture.Equality.html#6167" class="Function">cong-app</a> <a id="6247" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6252" class="Symbol">_</a> <a id="6254" class="Symbol">=</a> <a id="6256" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>





-------------------------------------


<sup>1</sup><span class="footnote" id="fn1"> Per Martin-Löf, *An intuitionistic theory of types: predicative part*, Logic Colloquium '73 (Bristol, 1973), 73--118, Studies in Logic and the Foundations of Mathematics, Vol. 80, 1975.</span>

<sup>2</sup><span class="footnote" id="fn2"> The *definiendum* is the left-hand side of a defining equation, the *definiens* is the right-hand side. For readers who have never generated an equivalence relation: the *reflexive closure* of `R ⊆ A × A `is the union of `R` and all pairs of the form `(a , a)`; the *symmetric closure* is the union of `R` and its inverse `{(y , x) : (x , y) ∈ R}`; we leave it to the reader to come up with the correct definition of transitive closure.</span>

<sup>3</sup><span class="footnote" id="fn3"> **Unicode Hints** ([agda2-mode][]). `\^-\^1 ↝ ⁻¹`; `\Mii\Mid ↝ 𝑖𝑑`; `\. ↝ ∙`. In general, for information about a character, place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>



<sup>4</sup><span class="footnote" id="fn4"> Alonzo Church, "A Formulation of the Simple Theory of Types," *Journal of Symbolic Logic*, (2)5:56--68, 1940 [JSOR link](http://www.jstor.org/stable/2266170). See also [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).</span>

<br>
<br>

[← Overture.Preliminaries ](Overture.Preliminaries.html)
<span style="float:right;">[Overture.Extensionality →](Overture.Extensionality.html)</span>

{% include UALib.Links.md %}

