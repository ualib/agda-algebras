---
layout: default
title : Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="unary-relations">Discrete Relations</a>

This is the [Relations.Discrete][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="289" class="Symbol">{-#</a> <a id="293" class="Keyword">OPTIONS</a> <a id="301" class="Pragma">--without-K</a> <a id="313" class="Pragma">--exact-split</a> <a id="327" class="Pragma">--safe</a> <a id="334" class="Symbol">#-}</a>

<a id="339" class="Keyword">module</a> <a id="346" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="365" class="Keyword">where</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="Overture.Lifts.html" class="Module">Overture.Lifts</a> <a id="399" class="Keyword">public</a>

</pre>

In this module we define types that represent *unary* and *binary relations*.  We refer to these as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* we introduce in the next module ([Relations.Continuous][]). We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).


#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : 𝓤 ̇`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="Pred"></a><a id="1534" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1543" href="Universes.html#403" class="Function Operator">̇</a> <a id="1545" class="Symbol">→</a> <a id="1547" class="Symbol">(</a><a id="1548" href="Relations.Discrete.html#1548" class="Bound">𝓦</a> <a id="1550" class="Symbol">:</a> <a id="1552" href="Universes.html#205" class="Postulate">Universe</a><a id="1560" class="Symbol">)</a> <a id="1562" class="Symbol">→</a> <a id="1564" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1566" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1568" href="Relations.Discrete.html#1548" class="Bound">𝓦</a> <a id="1570" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="1572" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1574" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="1579" href="Relations.Discrete.html#1579" class="Bound">A</a> <a id="1581" href="Relations.Discrete.html#1581" class="Bound">𝓦</a> <a id="1583" class="Symbol">=</a> <a id="1585" href="Relations.Discrete.html#1579" class="Bound">A</a> <a id="1587" class="Symbol">→</a> <a id="1589" href="Relations.Discrete.html#1581" class="Bound">𝓦</a> <a id="1591" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `𝓤 ̇`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

Like the [Agda Standard Library][], the [UALib][] includes types that represent the *element inclusion* and *subset inclusion* relations from set theory. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The definition of `∈` is standard. Nonetheless, here it is.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="_∈_"></a><a id="2402" href="Relations.Discrete.html#2402" class="Function Operator">_∈_</a> <a id="2406" class="Symbol">:</a> <a id="2408" class="Symbol">{</a><a id="2409" href="Relations.Discrete.html#2409" class="Bound">A</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2415" href="Universes.html#403" class="Function Operator">̇</a><a id="2416" class="Symbol">}</a> <a id="2418" class="Symbol">→</a> <a id="2420" href="Relations.Discrete.html#2409" class="Bound">A</a> <a id="2422" class="Symbol">→</a> <a id="2424" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="2429" href="Relations.Discrete.html#2409" class="Bound">A</a> <a id="2431" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2433" class="Symbol">→</a> <a id="2435" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2437" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2439" href="Relations.Discrete.html#2439" class="Bound">x</a> <a id="2441" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="2443" href="Relations.Discrete.html#2443" class="Bound">P</a> <a id="2445" class="Symbol">=</a> <a id="2447" href="Relations.Discrete.html#2443" class="Bound">P</a> <a id="2449" href="Relations.Discrete.html#2439" class="Bound">x</a>

</pre>

The "subset" relation is denoted, as usual, with the `⊆` symbol.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="_⊆_"></a><a id="2587" href="Relations.Discrete.html#2587" class="Function Operator">_⊆_</a> <a id="2591" class="Symbol">:</a> <a id="2593" class="Symbol">{</a><a id="2594" href="Relations.Discrete.html#2594" class="Bound">A</a> <a id="2596" class="Symbol">:</a> <a id="2598" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2600" href="Universes.html#403" class="Function Operator">̇</a> <a id="2602" class="Symbol">}</a> <a id="2604" class="Symbol">→</a> <a id="2606" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="2611" href="Relations.Discrete.html#2594" class="Bound">A</a> <a id="2613" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2615" class="Symbol">→</a> <a id="2617" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="2622" href="Relations.Discrete.html#2594" class="Bound">A</a> <a id="2624" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="2626" class="Symbol">→</a> <a id="2628" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2630" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2632" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2634" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2636" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="2638" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2640" href="Relations.Discrete.html#2640" class="Bound">P</a> <a id="2642" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="2644" href="Relations.Discrete.html#2644" class="Bound">Q</a> <a id="2646" class="Symbol">=</a> <a id="2648" class="Symbol">∀</a> <a id="2650" class="Symbol">{</a><a id="2651" href="Relations.Discrete.html#2651" class="Bound">x</a><a id="2652" class="Symbol">}</a> <a id="2654" class="Symbol">→</a> <a id="2656" href="Relations.Discrete.html#2651" class="Bound">x</a> <a id="2658" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="2660" href="Relations.Discrete.html#2640" class="Bound">P</a> <a id="2662" class="Symbol">→</a> <a id="2664" href="Relations.Discrete.html#2651" class="Bound">x</a> <a id="2666" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="2668" href="Relations.Discrete.html#2644" class="Bound">Q</a>

<a id="2671" class="Keyword">infix</a> <a id="2677" class="Number">4</a> <a id="2679" href="Relations.Discrete.html#2587" class="Function Operator">_⊆_</a>


</pre>




#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later. The first is an inductive type representing *disjoint union*.<sup>[2](Relations.Discrete#fn2)</sup>

<pre class="Agda">
<a id="2937" class="Keyword">infixr</a> <a id="2944" class="Number">1</a> <a id="2946" href="Relations.Discrete.html#2960" class="Datatype Operator">_⊎_</a> <a id="2950" href="Relations.Discrete.html#3131" class="Function Operator">_∪_</a>

<a id="2955" class="Keyword">data</a> <a id="_⊎_"></a><a id="2960" href="Relations.Discrete.html#2960" class="Datatype Operator">_⊎_</a> <a id="2964" class="Symbol">(</a><a id="2965" href="Relations.Discrete.html#2965" class="Bound">A</a> <a id="2967" class="Symbol">:</a> <a id="2969" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2971" href="Universes.html#403" class="Function Operator">̇</a><a id="2972" class="Symbol">)</a> <a id="2974" class="Symbol">(</a><a id="2975" href="Relations.Discrete.html#2975" class="Bound">B</a> <a id="2977" class="Symbol">:</a> <a id="2979" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2981" href="Universes.html#403" class="Function Operator">̇</a><a id="2982" class="Symbol">)</a> <a id="2984" class="Symbol">:</a> <a id="2986" href="Relations.Discrete.html#2969" class="Bound">𝓤</a> <a id="2988" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2990" href="Relations.Discrete.html#2979" class="Bound">𝓦</a> <a id="2992" href="Universes.html#403" class="Function Operator">̇</a> <a id="2994" class="Keyword">where</a>
 <a id="_⊎_.inj₁"></a><a id="3001" href="Relations.Discrete.html#3001" class="InductiveConstructor">inj₁</a> <a id="3006" class="Symbol">:</a> <a id="3008" class="Symbol">(</a><a id="3009" href="Relations.Discrete.html#3009" class="Bound">x</a> <a id="3011" class="Symbol">:</a> <a id="3013" href="Relations.Discrete.html#2965" class="Bound">A</a><a id="3014" class="Symbol">)</a> <a id="3016" class="Symbol">→</a> <a id="3018" href="Relations.Discrete.html#2965" class="Bound">A</a> <a id="3020" href="Relations.Discrete.html#2960" class="Datatype Operator">⊎</a> <a id="3022" href="Relations.Discrete.html#2975" class="Bound">B</a>
 <a id="_⊎_.inj₂"></a><a id="3025" href="Relations.Discrete.html#3025" class="InductiveConstructor">inj₂</a> <a id="3030" class="Symbol">:</a> <a id="3032" class="Symbol">(</a><a id="3033" href="Relations.Discrete.html#3033" class="Bound">y</a> <a id="3035" class="Symbol">:</a> <a id="3037" href="Relations.Discrete.html#2975" class="Bound">B</a><a id="3038" class="Symbol">)</a> <a id="3040" class="Symbol">→</a> <a id="3042" href="Relations.Discrete.html#2965" class="Bound">A</a> <a id="3044" href="Relations.Discrete.html#2960" class="Datatype Operator">⊎</a> <a id="3046" href="Relations.Discrete.html#2975" class="Bound">B</a>

</pre>

And this can be used to represent *union*, as follows.

<pre class="Agda">

<a id="_∪_"></a><a id="3131" href="Relations.Discrete.html#3131" class="Function Operator">_∪_</a> <a id="3135" class="Symbol">:</a> <a id="3137" class="Symbol">{</a><a id="3138" href="Relations.Discrete.html#3138" class="Bound">A</a> <a id="3140" class="Symbol">:</a> <a id="3142" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3144" href="Universes.html#403" class="Function Operator">̇</a><a id="3145" class="Symbol">}</a> <a id="3147" class="Symbol">→</a> <a id="3149" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3154" href="Relations.Discrete.html#3138" class="Bound">A</a> <a id="3156" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3158" class="Symbol">→</a> <a id="3160" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3165" href="Relations.Discrete.html#3138" class="Bound">A</a> <a id="3167" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="3169" class="Symbol">→</a> <a id="3171" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3176" href="Relations.Discrete.html#3138" class="Bound">A</a> <a id="3178" class="Symbol">(</a><a id="3179" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3181" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3183" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a><a id="3184" class="Symbol">)</a>
<a id="3186" href="Relations.Discrete.html#3186" class="Bound">P</a> <a id="3188" href="Relations.Discrete.html#3131" class="Function Operator">∪</a> <a id="3190" href="Relations.Discrete.html#3190" class="Bound">Q</a> <a id="3192" class="Symbol">=</a> <a id="3194" class="Symbol">λ</a> <a id="3196" href="Relations.Discrete.html#3196" class="Bound">x</a> <a id="3198" class="Symbol">→</a> <a id="3200" href="Relations.Discrete.html#3196" class="Bound">x</a> <a id="3202" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="3204" href="Relations.Discrete.html#3186" class="Bound">P</a> <a id="3206" href="Relations.Discrete.html#2960" class="Datatype Operator">⊎</a> <a id="3208" href="Relations.Discrete.html#3196" class="Bound">x</a> <a id="3210" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="3212" href="Relations.Discrete.html#3190" class="Bound">Q</a>


</pre>

Next we define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

<pre class="Agda">

<a id="Im_⊆_"></a><a id="3393" href="Relations.Discrete.html#3393" class="Function Operator">Im_⊆_</a> <a id="3399" class="Symbol">:</a> <a id="3401" class="Symbol">{</a><a id="3402" href="Relations.Discrete.html#3402" class="Bound">A</a> <a id="3404" class="Symbol">:</a> <a id="3406" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3408" href="Universes.html#403" class="Function Operator">̇</a><a id="3409" class="Symbol">}{</a><a id="3411" href="Relations.Discrete.html#3411" class="Bound">B</a> <a id="3413" class="Symbol">:</a> <a id="3415" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3417" href="Universes.html#403" class="Function Operator">̇</a><a id="3418" class="Symbol">}</a> <a id="3420" class="Symbol">→</a> <a id="3422" class="Symbol">(</a><a id="3423" href="Relations.Discrete.html#3402" class="Bound">A</a> <a id="3425" class="Symbol">→</a> <a id="3427" href="Relations.Discrete.html#3411" class="Bound">B</a><a id="3428" class="Symbol">)</a> <a id="3430" class="Symbol">→</a> <a id="3432" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3437" href="Relations.Discrete.html#3411" class="Bound">B</a> <a id="3439" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="3441" class="Symbol">→</a> <a id="3443" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3445" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3447" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="3449" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3451" href="Relations.Discrete.html#3393" class="Function Operator">Im</a> <a id="3454" href="Relations.Discrete.html#3454" class="Bound">f</a> <a id="3456" href="Relations.Discrete.html#3393" class="Function Operator">⊆</a> <a id="3458" href="Relations.Discrete.html#3458" class="Bound">S</a> <a id="3460" class="Symbol">=</a> <a id="3462" class="Symbol">∀</a> <a id="3464" href="Relations.Discrete.html#3464" class="Bound">x</a> <a id="3466" class="Symbol">→</a> <a id="3468" href="Relations.Discrete.html#3454" class="Bound">f</a> <a id="3470" href="Relations.Discrete.html#3464" class="Bound">x</a> <a id="3472" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="3474" href="Relations.Discrete.html#3458" class="Bound">S</a>

</pre>


The *empty set* is naturally represented by the *empty type*, `𝟘`.<sup>[2](Relations.Discrete#fn2), [4](Relations.Discrete#fn4)</sup>

<pre class="Agda">

<a id="3639" class="Keyword">open</a> <a id="3644" class="Keyword">import</a> <a id="3651" href="Empty-Type.html" class="Module">Empty-Type</a> <a id="3662" class="Keyword">using</a> <a id="3668" class="Symbol">(</a><a id="3669" href="Empty-Type.html#125" class="Datatype">𝟘</a><a id="3670" class="Symbol">)</a>

<a id="∅"></a><a id="3673" href="Relations.Discrete.html#3673" class="Function">∅</a> <a id="3675" class="Symbol">:</a> <a id="3677" class="Symbol">{</a><a id="3678" href="Relations.Discrete.html#3678" class="Bound">A</a> <a id="3680" class="Symbol">:</a> <a id="3682" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3684" href="Universes.html#403" class="Function Operator">̇</a><a id="3685" class="Symbol">}</a> <a id="3687" class="Symbol">→</a> <a id="3689" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3694" href="Relations.Discrete.html#3678" class="Bound">A</a> <a id="3696" href="Universes.html#158" class="Primitive">𝓤₀</a>
<a id="3699" href="Relations.Discrete.html#3673" class="Function">∅</a> <a id="3701" class="Symbol">_</a> <a id="3703" class="Symbol">=</a> <a id="3705" href="Empty-Type.html#125" class="Datatype">𝟘</a>

</pre>


Before closing our little predicates toolbox, let's insert a type that provides a natural way to encode *singletons*.

<pre class="Agda">

<a id="｛_｝"></a><a id="3854" href="Relations.Discrete.html#3854" class="Function Operator">｛_｝</a> <a id="3858" class="Symbol">:</a> <a id="3860" class="Symbol">{</a><a id="3861" href="Relations.Discrete.html#3861" class="Bound">A</a> <a id="3863" class="Symbol">:</a> <a id="3865" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3867" href="Universes.html#403" class="Function Operator">̇</a><a id="3868" class="Symbol">}</a> <a id="3870" class="Symbol">→</a> <a id="3872" href="Relations.Discrete.html#3861" class="Bound">A</a> <a id="3874" class="Symbol">→</a> <a id="3876" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="3881" href="Relations.Discrete.html#3861" class="Bound">A</a> <a id="3883" class="Symbol">_</a>
<a id="3885" href="Relations.Discrete.html#3854" class="Function Operator">｛</a> <a id="3887" href="Relations.Discrete.html#3887" class="Bound">x</a> <a id="3889" href="Relations.Discrete.html#3854" class="Function Operator">｝</a> <a id="3891" class="Symbol">=</a> <a id="3893" href="Relations.Discrete.html#3887" class="Bound">x</a> <a id="3895" href="Overture.Equality.html#2419" class="Datatype Operator">≡_</a>

</pre>


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → 𝓦 ̇` (for some universe 𝓦). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → 𝓦 ̇`, while a binary relation should have type `A → (A → 𝓦 ̇)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

<pre class="Agda">

<a id="REL"></a><a id="4618" href="Relations.Discrete.html#4618" class="Function">REL</a> <a id="4622" class="Symbol">:</a> <a id="4624" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4626" href="Universes.html#403" class="Function Operator">̇</a> <a id="4628" class="Symbol">→</a> <a id="4630" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4632" href="Universes.html#403" class="Function Operator">̇</a> <a id="4634" class="Symbol">→</a> <a id="4636" class="Symbol">(</a><a id="4637" href="Relations.Discrete.html#4637" class="Bound">𝓩</a> <a id="4639" class="Symbol">:</a> <a id="4641" href="Universes.html#205" class="Postulate">Universe</a><a id="4649" class="Symbol">)</a> <a id="4651" class="Symbol">→</a> <a id="4653" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4655" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4657" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4659" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4661" href="Relations.Discrete.html#4637" class="Bound">𝓩</a> <a id="4663" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4665" href="Universes.html#403" class="Function Operator">̇</a>
<a id="4667" href="Relations.Discrete.html#4618" class="Function">REL</a> <a id="4671" href="Relations.Discrete.html#4671" class="Bound">A</a> <a id="4673" href="Relations.Discrete.html#4673" class="Bound">B</a> <a id="4675" href="Relations.Discrete.html#4675" class="Bound">𝓩</a> <a id="4677" class="Symbol">=</a> <a id="4679" href="Relations.Discrete.html#4671" class="Bound">A</a> <a id="4681" class="Symbol">→</a> <a id="4683" href="Relations.Discrete.html#4673" class="Bound">B</a> <a id="4685" class="Symbol">→</a> <a id="4687" href="Relations.Discrete.html#4675" class="Bound">𝓩</a> <a id="4689" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

In the special case, where `𝓦 ≡ 𝓤` and `B ≡ A`, we have

<pre class="Agda">

<a id="Rel"></a><a id="4775" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="4779" class="Symbol">:</a> <a id="4781" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4783" href="Universes.html#403" class="Function Operator">̇</a> <a id="4785" class="Symbol">→</a> <a id="4787" class="Symbol">(</a><a id="4788" href="Relations.Discrete.html#4788" class="Bound">𝓩</a> <a id="4790" class="Symbol">:</a> <a id="4792" href="Universes.html#205" class="Postulate">Universe</a><a id="4800" class="Symbol">)</a> <a id="4802" class="Symbol">→</a> <a id="4804" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4806" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4808" href="Relations.Discrete.html#4788" class="Bound">𝓩</a> <a id="4810" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4812" href="Universes.html#403" class="Function Operator">̇</a>
<a id="4814" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="4818" href="Relations.Discrete.html#4818" class="Bound">A</a> <a id="4820" href="Relations.Discrete.html#4820" class="Bound">𝓩</a> <a id="4822" class="Symbol">=</a> <a id="4824" href="Relations.Discrete.html#4618" class="Function">REL</a> <a id="4828" href="Relations.Discrete.html#4818" class="Bound">A</a> <a id="4830" href="Relations.Discrete.html#4818" class="Bound">A</a> <a id="4832" href="Relations.Discrete.html#4820" class="Bound">𝓩</a>

</pre>


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


<pre class="Agda">

<a id="5275" class="Keyword">module</a> <a id="5282" href="Relations.Discrete.html#5282" class="Module">_</a> <a id="5284" class="Symbol">{</a><a id="5285" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5287" class="Symbol">:</a> <a id="5289" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5291" href="Universes.html#403" class="Function Operator">̇</a><a id="5292" class="Symbol">}{</a><a id="5294" href="Relations.Discrete.html#5294" class="Bound">B</a> <a id="5296" class="Symbol">:</a> <a id="5298" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5300" href="Universes.html#403" class="Function Operator">̇</a><a id="5301" class="Symbol">}</a> <a id="5303" class="Keyword">where</a>

 <a id="5311" href="Relations.Discrete.html#5311" class="Function">ker</a> <a id="5315" class="Symbol">:</a> <a id="5317" class="Symbol">(</a><a id="5318" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5320" class="Symbol">→</a> <a id="5322" href="Relations.Discrete.html#5294" class="Bound">B</a><a id="5323" class="Symbol">)</a> <a id="5325" class="Symbol">→</a> <a id="5327" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="5331" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5333" href="Relations.Discrete.html#5298" class="Bound">𝓦</a>
 <a id="5336" href="Relations.Discrete.html#5311" class="Function">ker</a> <a id="5340" href="Relations.Discrete.html#5340" class="Bound">g</a> <a id="5342" href="Relations.Discrete.html#5342" class="Bound">x</a> <a id="5344" href="Relations.Discrete.html#5344" class="Bound">y</a> <a id="5346" class="Symbol">=</a> <a id="5348" href="Relations.Discrete.html#5340" class="Bound">g</a> <a id="5350" href="Relations.Discrete.html#5342" class="Bound">x</a> <a id="5352" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5354" href="Relations.Discrete.html#5340" class="Bound">g</a> <a id="5356" href="Relations.Discrete.html#5344" class="Bound">y</a>

 <a id="5360" href="Relations.Discrete.html#5360" class="Function">kernel</a> <a id="5367" class="Symbol">:</a> <a id="5369" class="Symbol">(</a><a id="5370" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5372" class="Symbol">→</a> <a id="5374" href="Relations.Discrete.html#5294" class="Bound">B</a><a id="5375" class="Symbol">)</a> <a id="5377" class="Symbol">→</a> <a id="5379" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="5384" class="Symbol">(</a><a id="5385" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5387" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5389" href="Relations.Discrete.html#5285" class="Bound">A</a><a id="5390" class="Symbol">)</a> <a id="5392" href="Relations.Discrete.html#5298" class="Bound">𝓦</a>
 <a id="5395" href="Relations.Discrete.html#5360" class="Function">kernel</a> <a id="5402" href="Relations.Discrete.html#5402" class="Bound">g</a> <a id="5404" class="Symbol">(</a><a id="5405" href="Relations.Discrete.html#5405" class="Bound">x</a> <a id="5407" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5409" href="Relations.Discrete.html#5409" class="Bound">y</a><a id="5410" class="Symbol">)</a> <a id="5412" class="Symbol">=</a> <a id="5414" href="Relations.Discrete.html#5402" class="Bound">g</a> <a id="5416" href="Relations.Discrete.html#5405" class="Bound">x</a> <a id="5418" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5420" href="Relations.Discrete.html#5402" class="Bound">g</a> <a id="5422" href="Relations.Discrete.html#5409" class="Bound">y</a>

 <a id="5426" href="Relations.Discrete.html#5426" class="Function">ker-sigma</a> <a id="5436" class="Symbol">:</a> <a id="5438" class="Symbol">(</a><a id="5439" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5441" class="Symbol">→</a> <a id="5443" href="Relations.Discrete.html#5294" class="Bound">B</a><a id="5444" class="Symbol">)</a> <a id="5446" class="Symbol">→</a> <a id="5448" href="Relations.Discrete.html#5289" class="Bound">𝓤</a> <a id="5450" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5452" href="Relations.Discrete.html#5298" class="Bound">𝓦</a> <a id="5454" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5457" href="Relations.Discrete.html#5426" class="Function">ker-sigma</a> <a id="5467" href="Relations.Discrete.html#5467" class="Bound">g</a> <a id="5469" class="Symbol">=</a> <a id="5471" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5473" href="Relations.Discrete.html#5473" class="Bound">x</a> <a id="5475" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5477" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5479" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5481" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5483" href="Relations.Discrete.html#5483" class="Bound">y</a> <a id="5485" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5487" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5489" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5491" href="Relations.Discrete.html#5467" class="Bound">g</a> <a id="5493" href="Relations.Discrete.html#5473" class="Bound">x</a> <a id="5495" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5497" href="Relations.Discrete.html#5467" class="Bound">g</a> <a id="5499" href="Relations.Discrete.html#5483" class="Bound">y</a>

 <a id="5503" href="Relations.Discrete.html#5503" class="Function">ker-sigma&#39;</a> <a id="5514" class="Symbol">:</a> <a id="5516" class="Symbol">(</a><a id="5517" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5519" class="Symbol">→</a> <a id="5521" href="Relations.Discrete.html#5294" class="Bound">B</a><a id="5522" class="Symbol">)</a> <a id="5524" class="Symbol">→</a> <a id="5526" href="Relations.Discrete.html#5289" class="Bound">𝓤</a> <a id="5528" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5530" href="Relations.Discrete.html#5298" class="Bound">𝓦</a> <a id="5532" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5535" href="Relations.Discrete.html#5503" class="Function">ker-sigma&#39;</a> <a id="5546" href="Relations.Discrete.html#5546" class="Bound">g</a> <a id="5548" class="Symbol">=</a> <a id="5550" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5552" href="Relations.Discrete.html#5552" class="Bound">(x</a> <a id="5555" href="Relations.Discrete.html#5552" class="Bound">,</a> <a id="5557" href="Relations.Discrete.html#5552" class="Bound">y)</a> <a id="5560" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5562" class="Symbol">(</a><a id="5563" href="Relations.Discrete.html#5285" class="Bound">A</a> <a id="5565" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5567" href="Relations.Discrete.html#5285" class="Bound">A</a><a id="5568" class="Symbol">)</a> <a id="5570" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5572" href="Relations.Discrete.html#5546" class="Bound">g</a> <a id="5574" href="Relations.Discrete.html#5553" class="Bound">x</a> <a id="5576" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5578" href="Relations.Discrete.html#5546" class="Bound">g</a> <a id="5580" href="Relations.Discrete.html#5557" class="Bound">y</a>

</pre>


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.<sup>[2](Relations.Discrete#fn2)</sup>

<pre class="Agda">

<a id="5807" class="Keyword">module</a> <a id="5814" href="Relations.Discrete.html#5814" class="Module">_</a> <a id="5816" class="Symbol">{</a><a id="5817" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="5819" class="Symbol">:</a> <a id="5821" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5823" href="Universes.html#403" class="Function Operator">̇</a> <a id="5825" class="Symbol">}</a> <a id="5827" class="Keyword">where</a>

 <a id="5835" href="Relations.Discrete.html#5835" class="Function">𝟎</a> <a id="5837" class="Symbol">:</a> <a id="5839" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="5843" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="5845" href="Relations.Discrete.html#5821" class="Bound">𝓤</a>
 <a id="5848" href="Relations.Discrete.html#5835" class="Function">𝟎</a> <a id="5850" href="Relations.Discrete.html#5850" class="Bound">x</a> <a id="5852" href="Relations.Discrete.html#5852" class="Bound">y</a> <a id="5854" class="Symbol">=</a> <a id="5856" href="Relations.Discrete.html#5850" class="Bound">x</a> <a id="5858" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5860" href="Relations.Discrete.html#5852" class="Bound">y</a>

 <a id="5864" href="Relations.Discrete.html#5864" class="Function">𝟎-pred</a> <a id="5871" class="Symbol">:</a> <a id="5873" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="5878" class="Symbol">(</a><a id="5879" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="5881" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5883" href="Relations.Discrete.html#5817" class="Bound">A</a><a id="5884" class="Symbol">)</a> <a id="5886" href="Relations.Discrete.html#5821" class="Bound">𝓤</a>
 <a id="5889" href="Relations.Discrete.html#5864" class="Function">𝟎-pred</a> <a id="5896" class="Symbol">(</a><a id="5897" href="Relations.Discrete.html#5897" class="Bound">x</a> <a id="5899" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5901" href="Relations.Discrete.html#5901" class="Bound">y</a><a id="5902" class="Symbol">)</a> <a id="5904" class="Symbol">=</a> <a id="5906" href="Relations.Discrete.html#5897" class="Bound">x</a> <a id="5908" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5910" href="Relations.Discrete.html#5901" class="Bound">y</a>

 <a id="5914" href="Relations.Discrete.html#5914" class="Function">𝟎-sigma</a> <a id="5922" class="Symbol">:</a> <a id="5924" href="Relations.Discrete.html#5821" class="Bound">𝓤</a> <a id="5926" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5929" href="Relations.Discrete.html#5914" class="Function">𝟎-sigma</a> <a id="5937" class="Symbol">=</a> <a id="5939" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5941" href="Relations.Discrete.html#5941" class="Bound">x</a> <a id="5943" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5945" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="5947" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5949" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5951" href="Relations.Discrete.html#5951" class="Bound">y</a> <a id="5953" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5955" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="5957" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5959" href="Relations.Discrete.html#5941" class="Bound">x</a> <a id="5961" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5963" href="Relations.Discrete.html#5951" class="Bound">y</a>

 <a id="5967" href="Relations.Discrete.html#5967" class="Function">𝟎-sigma&#39;</a> <a id="5976" class="Symbol">:</a> <a id="5978" href="Relations.Discrete.html#5821" class="Bound">𝓤</a> <a id="5980" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5983" href="Relations.Discrete.html#5967" class="Function">𝟎-sigma&#39;</a> <a id="5992" class="Symbol">=</a> <a id="5994" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5996" href="Relations.Discrete.html#5996" class="Bound">(x</a> <a id="5999" href="Relations.Discrete.html#5996" class="Bound">,</a> <a id="6001" href="Relations.Discrete.html#5996" class="Bound">y)</a> <a id="6004" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="6006" class="Symbol">(</a><a id="6007" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="6009" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="6011" href="Relations.Discrete.html#5817" class="Bound">A</a><a id="6012" class="Symbol">)</a> <a id="6014" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="6016" href="Relations.Discrete.html#5997" class="Bound">x</a> <a id="6018" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="6020" href="Relations.Discrete.html#6001" class="Bound">y</a>

</pre>

The *total relation* over `A`, which in set theory is the full Cartesian product `A × A`, could be represented using the one-element type from the `Unit-Type` module of [Type Topology][], as follows.

<pre class="Agda">

 <a id="6251" class="Keyword">open</a> <a id="6256" class="Keyword">import</a> <a id="6263" href="Unit-Type.html" class="Module">Unit-Type</a> <a id="6273" class="Keyword">using</a> <a id="6279" class="Symbol">(</a><a id="6280" href="Unit-Type.html#124" class="Datatype">𝟙</a><a id="6281" class="Symbol">)</a>

 <a id="6285" href="Relations.Discrete.html#6285" class="Function">𝟏</a> <a id="6287" class="Symbol">:</a> <a id="6289" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="6293" href="Relations.Discrete.html#5817" class="Bound">A</a> <a id="6295" href="Universes.html#158" class="Primitive">𝓤₀</a>
 <a id="6299" href="Relations.Discrete.html#6285" class="Function">𝟏</a> <a id="6301" href="Relations.Discrete.html#6301" class="Bound">a</a> <a id="6303" href="Relations.Discrete.html#6303" class="Bound">b</a> <a id="6305" class="Symbol">=</a> <a id="6307" href="Unit-Type.html#124" class="Datatype">𝟙</a>
</pre>



#### <a id="implication">Implication</a>

We define the following types representing *implication* for binary relations. (These are borrowed from the [Agda Standard Library][]; we merely translate them into [Type Topology][]/[UALib][] notation.)

<pre class="Agda">

<a id="_on_"></a><a id="6584" href="Relations.Discrete.html#6584" class="Function Operator">_on_</a> <a id="6589" class="Symbol">:</a> <a id="6591" class="Symbol">{</a><a id="6592" href="Relations.Discrete.html#6592" class="Bound">A</a> <a id="6594" class="Symbol">:</a> <a id="6596" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6598" href="Universes.html#403" class="Function Operator">̇</a><a id="6599" class="Symbol">}{</a><a id="6601" href="Relations.Discrete.html#6601" class="Bound">B</a> <a id="6603" class="Symbol">:</a> <a id="6605" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6607" href="Universes.html#403" class="Function Operator">̇</a><a id="6608" class="Symbol">}{</a><a id="6610" href="Relations.Discrete.html#6610" class="Bound">C</a> <a id="6612" class="Symbol">:</a> <a id="6614" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="6616" href="Universes.html#403" class="Function Operator">̇</a><a id="6617" class="Symbol">}</a> <a id="6619" class="Symbol">→</a> <a id="6621" class="Symbol">(</a><a id="6622" href="Relations.Discrete.html#6601" class="Bound">B</a> <a id="6624" class="Symbol">→</a> <a id="6626" href="Relations.Discrete.html#6601" class="Bound">B</a> <a id="6628" class="Symbol">→</a> <a id="6630" href="Relations.Discrete.html#6610" class="Bound">C</a><a id="6631" class="Symbol">)</a> <a id="6633" class="Symbol">→</a> <a id="6635" class="Symbol">(</a><a id="6636" href="Relations.Discrete.html#6592" class="Bound">A</a> <a id="6638" class="Symbol">→</a> <a id="6640" href="Relations.Discrete.html#6601" class="Bound">B</a><a id="6641" class="Symbol">)</a> <a id="6643" class="Symbol">→</a> <a id="6645" class="Symbol">(</a><a id="6646" href="Relations.Discrete.html#6592" class="Bound">A</a> <a id="6648" class="Symbol">→</a> <a id="6650" href="Relations.Discrete.html#6592" class="Bound">A</a> <a id="6652" class="Symbol">→</a> <a id="6654" href="Relations.Discrete.html#6610" class="Bound">C</a><a id="6655" class="Symbol">)</a>
<a id="6657" href="Relations.Discrete.html#6657" class="Bound">R</a> <a id="6659" href="Relations.Discrete.html#6584" class="Function Operator">on</a> <a id="6662" href="Relations.Discrete.html#6662" class="Bound">g</a> <a id="6664" class="Symbol">=</a> <a id="6666" class="Symbol">λ</a> <a id="6668" href="Relations.Discrete.html#6668" class="Bound">x</a> <a id="6670" href="Relations.Discrete.html#6670" class="Bound">y</a> <a id="6672" class="Symbol">→</a> <a id="6674" href="Relations.Discrete.html#6657" class="Bound">R</a> <a id="6676" class="Symbol">(</a><a id="6677" href="Relations.Discrete.html#6662" class="Bound">g</a> <a id="6679" href="Relations.Discrete.html#6668" class="Bound">x</a><a id="6680" class="Symbol">)</a> <a id="6682" class="Symbol">(</a><a id="6683" href="Relations.Discrete.html#6662" class="Bound">g</a> <a id="6685" href="Relations.Discrete.html#6670" class="Bound">y</a><a id="6686" class="Symbol">)</a>

<a id="_⇒_"></a><a id="6689" href="Relations.Discrete.html#6689" class="Function Operator">_⇒_</a> <a id="6693" class="Symbol">:</a> <a id="6695" class="Symbol">{</a><a id="6696" href="Relations.Discrete.html#6696" class="Bound">A</a> <a id="6698" class="Symbol">:</a> <a id="6700" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6702" href="Universes.html#403" class="Function Operator">̇</a><a id="6703" class="Symbol">}{</a><a id="6705" href="Relations.Discrete.html#6705" class="Bound">B</a> <a id="6707" class="Symbol">:</a> <a id="6709" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6711" href="Universes.html#403" class="Function Operator">̇</a><a id="6712" class="Symbol">}</a> <a id="6714" class="Symbol">→</a> <a id="6716" href="Relations.Discrete.html#4618" class="Function">REL</a> <a id="6720" href="Relations.Discrete.html#6696" class="Bound">A</a> <a id="6722" href="Relations.Discrete.html#6705" class="Bound">B</a> <a id="6724" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6726" class="Symbol">→</a> <a id="6728" href="Relations.Discrete.html#4618" class="Function">REL</a> <a id="6732" href="Relations.Discrete.html#6696" class="Bound">A</a> <a id="6734" href="Relations.Discrete.html#6705" class="Bound">B</a> <a id="6736" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6738" class="Symbol">→</a> <a id="6740" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6742" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6744" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6746" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6748" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6750" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6752" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6754" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6756" href="Relations.Discrete.html#6756" class="Bound">P</a> <a id="6758" href="Relations.Discrete.html#6689" class="Function Operator">⇒</a> <a id="6760" href="Relations.Discrete.html#6760" class="Bound">Q</a> <a id="6762" class="Symbol">=</a> <a id="6764" class="Symbol">∀</a> <a id="6766" class="Symbol">{</a><a id="6767" href="Relations.Discrete.html#6767" class="Bound">i</a> <a id="6769" href="Relations.Discrete.html#6769" class="Bound">j</a><a id="6770" class="Symbol">}</a> <a id="6772" class="Symbol">→</a> <a id="6774" href="Relations.Discrete.html#6756" class="Bound">P</a> <a id="6776" href="Relations.Discrete.html#6767" class="Bound">i</a> <a id="6778" href="Relations.Discrete.html#6769" class="Bound">j</a> <a id="6780" class="Symbol">→</a> <a id="6782" href="Relations.Discrete.html#6760" class="Bound">Q</a> <a id="6784" href="Relations.Discrete.html#6767" class="Bound">i</a> <a id="6786" href="Relations.Discrete.html#6769" class="Bound">j</a>

<a id="6789" class="Keyword">infixr</a> <a id="6796" class="Number">4</a> <a id="6798" href="Relations.Discrete.html#6689" class="Function Operator">_⇒_</a>

</pre>

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.

<pre class="Agda">

<a id="_=[_]⇒_"></a><a id="6912" href="Relations.Discrete.html#6912" class="Function Operator">_=[_]⇒_</a> <a id="6920" class="Symbol">:</a> <a id="6922" class="Symbol">{</a><a id="6923" href="Relations.Discrete.html#6923" class="Bound">A</a> <a id="6925" class="Symbol">:</a> <a id="6927" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6929" href="Universes.html#403" class="Function Operator">̇</a><a id="6930" class="Symbol">}{</a><a id="6932" href="Relations.Discrete.html#6932" class="Bound">B</a> <a id="6934" class="Symbol">:</a> <a id="6936" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6938" href="Universes.html#403" class="Function Operator">̇</a><a id="6939" class="Symbol">}</a> <a id="6941" class="Symbol">→</a> <a id="6943" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="6947" href="Relations.Discrete.html#6923" class="Bound">A</a> <a id="6949" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6951" class="Symbol">→</a> <a id="6953" class="Symbol">(</a><a id="6954" href="Relations.Discrete.html#6923" class="Bound">A</a> <a id="6956" class="Symbol">→</a> <a id="6958" href="Relations.Discrete.html#6932" class="Bound">B</a><a id="6959" class="Symbol">)</a> <a id="6961" class="Symbol">→</a> <a id="6963" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="6967" href="Relations.Discrete.html#6932" class="Bound">B</a> <a id="6969" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6971" class="Symbol">→</a> <a id="6973" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6975" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6977" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6979" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6981" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6983" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6985" href="Relations.Discrete.html#6985" class="Bound">P</a> <a id="6987" href="Relations.Discrete.html#6912" class="Function Operator">=[</a> <a id="6990" href="Relations.Discrete.html#6990" class="Bound">g</a> <a id="6992" href="Relations.Discrete.html#6912" class="Function Operator">]⇒</a> <a id="6995" href="Relations.Discrete.html#6995" class="Bound">Q</a> <a id="6997" class="Symbol">=</a> <a id="6999" href="Relations.Discrete.html#6985" class="Bound">P</a> <a id="7001" href="Relations.Discrete.html#6689" class="Function Operator">⇒</a> <a id="7003" class="Symbol">(</a><a id="7004" href="Relations.Discrete.html#6995" class="Bound">Q</a> <a id="7006" href="Relations.Discrete.html#6584" class="Function Operator">on</a> <a id="7009" href="Relations.Discrete.html#6990" class="Bound">g</a><a id="7010" class="Symbol">)</a>

<a id="7013" class="Keyword">infixr</a> <a id="7020" class="Number">4</a> <a id="7022" href="Relations.Discrete.html#6912" class="Function Operator">_=[_]⇒_</a>

</pre>


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

<pre class="Agda">

<a id="7738" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="7763" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="7766" class="Symbol">:</a> <a id="7768" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7770" href="Universes.html#403" class="Function Operator">̇</a> <a id="7772" class="Symbol">→</a> <a id="7774" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7776" href="Universes.html#403" class="Function Operator">̇</a> <a id="7778" class="Symbol">→</a> <a id="7780" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7782" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7784" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7786" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7788" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="7791" href="Relations.Discrete.html#7791" class="Bound">I</a> <a id="7793" href="Relations.Discrete.html#7793" class="Bound">A</a> <a id="7795" class="Symbol">=</a> <a id="7797" class="Symbol">(</a><a id="7798" href="Relations.Discrete.html#7791" class="Bound">I</a> <a id="7800" class="Symbol">→</a> <a id="7802" href="Relations.Discrete.html#7793" class="Bound">A</a><a id="7803" class="Symbol">)</a> <a id="7805" class="Symbol">→</a> <a id="7807" href="Relations.Discrete.html#7793" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

<pre class="Agda">

<a id="π"></a><a id="8177" href="Relations.Discrete.html#8177" class="Function">π</a> <a id="8179" class="Symbol">:</a> <a id="8181" class="Symbol">{</a><a id="8182" href="Relations.Discrete.html#8182" class="Bound">I</a> <a id="8184" class="Symbol">:</a> <a id="8186" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8188" href="Universes.html#403" class="Function Operator">̇</a> <a id="8190" class="Symbol">}</a> <a id="8192" class="Symbol">{</a><a id="8193" href="Relations.Discrete.html#8193" class="Bound">A</a> <a id="8195" class="Symbol">:</a> <a id="8197" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8199" href="Universes.html#403" class="Function Operator">̇</a> <a id="8201" class="Symbol">}</a> <a id="8203" class="Symbol">→</a> <a id="8205" href="Relations.Discrete.html#8182" class="Bound">I</a> <a id="8207" class="Symbol">→</a> <a id="8209" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="8212" href="Relations.Discrete.html#8182" class="Bound">I</a> <a id="8214" href="Relations.Discrete.html#8193" class="Bound">A</a>
<a id="8216" href="Relations.Discrete.html#8177" class="Function">π</a> <a id="8218" href="Relations.Discrete.html#8218" class="Bound">i</a> <a id="8220" href="Relations.Discrete.html#8220" class="Bound">x</a> <a id="8222" class="Symbol">=</a> <a id="8224" href="Relations.Discrete.html#8220" class="Bound">x</a> <a id="8226" href="Relations.Discrete.html#8218" class="Bound">i</a>

</pre>

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A 𝓦` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (v i)` &nbsp; `→` &nbsp; `R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UALib][].

<pre class="Agda">

<a id="eval-rel"></a><a id="8645" href="Relations.Discrete.html#8645" class="Function">eval-rel</a> <a id="8654" class="Symbol">:</a> <a id="8656" class="Symbol">{</a><a id="8657" href="Relations.Discrete.html#8657" class="Bound">A</a> <a id="8659" class="Symbol">:</a> <a id="8661" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8663" href="Universes.html#403" class="Function Operator">̇</a><a id="8664" class="Symbol">}{</a><a id="8666" href="Relations.Discrete.html#8666" class="Bound">I</a> <a id="8668" class="Symbol">:</a> <a id="8670" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8672" href="Universes.html#403" class="Function Operator">̇</a><a id="8673" class="Symbol">}</a> <a id="8675" class="Symbol">→</a> <a id="8677" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="8681" href="Relations.Discrete.html#8657" class="Bound">A</a> <a id="8683" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8685" class="Symbol">→</a> <a id="8687" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="8691" class="Symbol">(</a><a id="8692" href="Relations.Discrete.html#8666" class="Bound">I</a> <a id="8694" class="Symbol">→</a> <a id="8696" href="Relations.Discrete.html#8657" class="Bound">A</a><a id="8697" class="Symbol">)(</a><a id="8699" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8701" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8703" href="Universes.html#264" class="Generalizable">𝓦</a><a id="8704" class="Symbol">)</a>
<a id="8706" href="Relations.Discrete.html#8645" class="Function">eval-rel</a> <a id="8715" href="Relations.Discrete.html#8715" class="Bound">R</a> <a id="8717" href="Relations.Discrete.html#8717" class="Bound">u</a> <a id="8719" href="Relations.Discrete.html#8719" class="Bound">v</a> <a id="8721" class="Symbol">=</a> <a id="8723" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8725" href="Relations.Discrete.html#8725" class="Bound">i</a> <a id="8727" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8729" class="Symbol">_</a> <a id="8731" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8733" href="Relations.Discrete.html#8715" class="Bound">R</a> <a id="8735" class="Symbol">(</a><a id="8736" href="Relations.Discrete.html#8717" class="Bound">u</a> <a id="8738" href="Relations.Discrete.html#8725" class="Bound">i</a><a id="8739" class="Symbol">)</a> <a id="8741" class="Symbol">(</a><a id="8742" href="Relations.Discrete.html#8719" class="Bound">v</a> <a id="8744" href="Relations.Discrete.html#8725" class="Bound">i</a><a id="8745" class="Symbol">)</a>

<a id="_|:_"></a><a id="8748" href="Relations.Discrete.html#8748" class="Function Operator">_|:_</a> <a id="8753" class="Symbol">:</a> <a id="8755" class="Symbol">{</a><a id="8756" href="Relations.Discrete.html#8756" class="Bound">A</a> <a id="8758" class="Symbol">:</a> <a id="8760" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8762" href="Universes.html#403" class="Function Operator">̇</a><a id="8763" class="Symbol">}{</a><a id="8765" href="Relations.Discrete.html#8765" class="Bound">I</a> <a id="8767" class="Symbol">:</a> <a id="8769" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8771" href="Universes.html#403" class="Function Operator">̇</a><a id="8772" class="Symbol">}</a> <a id="8774" class="Symbol">→</a> <a id="8776" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="8779" href="Relations.Discrete.html#8765" class="Bound">I</a> <a id="8781" href="Relations.Discrete.html#8756" class="Bound">A</a> <a id="8783" class="Symbol">→</a> <a id="8785" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="8789" href="Relations.Discrete.html#8756" class="Bound">A</a> <a id="8791" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8793" class="Symbol">→</a> <a id="8795" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8797" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8799" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8801" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8803" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8805" href="Universes.html#403" class="Function Operator">̇</a>
<a id="8807" href="Relations.Discrete.html#8807" class="Bound">f</a> <a id="8809" href="Relations.Discrete.html#8748" class="Function Operator">|:</a> <a id="8812" href="Relations.Discrete.html#8812" class="Bound">R</a>  <a id="8815" class="Symbol">=</a> <a id="8817" class="Symbol">(</a><a id="8818" href="Relations.Discrete.html#8645" class="Function">eval-rel</a> <a id="8827" href="Relations.Discrete.html#8812" class="Bound">R</a><a id="8828" class="Symbol">)</a> <a id="8830" href="Relations.Discrete.html#6912" class="Function Operator">=[</a> <a id="8833" href="Relations.Discrete.html#8807" class="Bound">f</a> <a id="8835" href="Relations.Discrete.html#6912" class="Function Operator">]⇒</a> <a id="8838" href="Relations.Discrete.html#8812" class="Bound">R</a>

</pre>

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

In case it helps the reader, we note that instead of using the slick implication notation, we could have defined the `|:` relation more explicitly, like so.

<pre class="Agda">

<a id="compatible-fun"></a><a id="9153" href="Relations.Discrete.html#9153" class="Function">compatible-fun</a> <a id="9168" class="Symbol">:</a> <a id="9170" class="Symbol">{</a><a id="9171" href="Relations.Discrete.html#9171" class="Bound">A</a> <a id="9173" class="Symbol">:</a> <a id="9175" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="9177" href="Universes.html#403" class="Function Operator">̇</a><a id="9178" class="Symbol">}{</a><a id="9180" href="Relations.Discrete.html#9180" class="Bound">I</a> <a id="9182" class="Symbol">:</a> <a id="9184" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="9186" href="Universes.html#403" class="Function Operator">̇</a><a id="9187" class="Symbol">}</a> <a id="9189" class="Symbol">→</a> <a id="9191" class="Symbol">(</a><a id="9192" href="Relations.Discrete.html#9192" class="Bound">f</a> <a id="9194" class="Symbol">:</a> <a id="9196" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="9199" href="Relations.Discrete.html#9180" class="Bound">I</a> <a id="9201" href="Relations.Discrete.html#9171" class="Bound">A</a><a id="9202" class="Symbol">)(</a><a id="9204" href="Relations.Discrete.html#9204" class="Bound">R</a> <a id="9206" class="Symbol">:</a> <a id="9208" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="9212" href="Relations.Discrete.html#9171" class="Bound">A</a> <a id="9214" href="Universes.html#264" class="Generalizable">𝓦</a><a id="9215" class="Symbol">)</a> <a id="9217" class="Symbol">→</a> <a id="9219" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="9221" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9223" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="9225" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9227" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="9229" href="Universes.html#403" class="Function Operator">̇</a>
<a id="9231" href="Relations.Discrete.html#9153" class="Function">compatible-fun</a> <a id="9246" href="Relations.Discrete.html#9246" class="Bound">f</a> <a id="9248" href="Relations.Discrete.html#9248" class="Bound">R</a>  <a id="9251" class="Symbol">=</a> <a id="9253" class="Symbol">∀</a> <a id="9255" href="Relations.Discrete.html#9255" class="Bound">u</a> <a id="9257" href="Relations.Discrete.html#9257" class="Bound">v</a> <a id="9259" class="Symbol">→</a> <a id="9261" class="Symbol">(</a><a id="9262" href="Relations.Discrete.html#8645" class="Function">eval-rel</a> <a id="9271" href="Relations.Discrete.html#9248" class="Bound">R</a><a id="9272" class="Symbol">)</a> <a id="9274" href="Relations.Discrete.html#9255" class="Bound">u</a> <a id="9276" href="Relations.Discrete.html#9257" class="Bound">v</a> <a id="9278" class="Symbol">→</a> <a id="9280" href="Relations.Discrete.html#9248" class="Bound">R</a> <a id="9282" class="Symbol">(</a><a id="9283" href="Relations.Discrete.html#9246" class="Bound">f</a> <a id="9285" href="Relations.Discrete.html#9255" class="Bound">u</a><a id="9286" class="Symbol">)</a> <a id="9288" class="Symbol">(</a><a id="9289" href="Relations.Discrete.html#9246" class="Bound">f</a> <a id="9291" href="Relations.Discrete.html#9257" class="Bound">v</a><a id="9292" class="Symbol">)</a>

</pre>

However, this is a rare case in which the more elegant syntax used to define `|:` sometimes results in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints** ([agda2-mode][]) `\.=` ↝ `≐`, `\u+` ↝ `⊎`, `\b0` ↝ `𝟘`, `\B0` ↝ `𝟎`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn4">The empty type is defined in the `Empty-Type` module of [Type Topology][] as an inductive type with no constructors: `data 𝟘 {𝓤} : 𝓤 ̇ where -- (empty body)`</span>

<sup>5</sup><span class="footnote" id="fn5">Initially we called the first function `lift-rel` because it "lifts" a binary relation on `A` to a binary relation on tuples of type `I → A`.  However, we renamed it `eval-rel` to avoid confusion with the universe level `Lift` type defined in the [Overture.Lifts][] module, or with `free-lift` ([Terms.Basic][]) which "lifts" a map defined on generators to a map on the thing being generated.</span>

<sup>6</sup><span class="footnote" id="fn6"> The symbol `|:` we use to denote the compatibility relation comes from Cliff Bergman's universal algebra textbook [Bergman (2012)][].

<br>
<br>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}





<!--

#### <a id="the-extensionality-axiom">The axiom of extensionality</a>

In type theory everything is represented as a type and, as we have just seen, this includes subsets.  Equality of types is a nontrivial matter, and thus so is equality of subsets when represented as unary predicates.  Fortunately, it is straightforward to write down the type that represents what we typically means in informal mathematics for two subsets to be equal. In the [UALib][] we denote this type by `≐` and define it as follows.<sup>[2](Relations.Discrete.html#fn2)</sup>

_≐_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓩 → 𝓤 ⊔ 𝓦 ⊔ 𝓩 ̇
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

infix 4 _≐_

Thus, a proof of `P ≐ Q` is a pair `(p , q)` where where `p : P ⊆ Q` and `q : Q ⊆ P` are proofs of the first and second inclusions, respectively. If `P` and `Q` are definitionally equal (i.e., `P ≡ Q`), then both `P ⊆ Q` and `Q ⊆ P` hold, so `P ≐ Q` also holds, as we now confirm.

Pred-≡ : {A : 𝓤 ̇}{P Q : Pred A 𝓦} → P ≡ Q → P ≐ Q
Pred-≡ refl = (λ z → z) , (λ z → z)

The converse is not provable in [MLTT][]. However, we can postulate that it holds as an axiom if we wish.  This is called the *axiom of extensionality* and a type that represents it is the following.
ext-axiom : 𝓤 ̇ → (𝓦 : Universe) →  𝓤 ⊔ 𝓦 ⁺ ̇
ext-axiom A 𝓦 = ∀ (P Q : Pred A 𝓦) → P ≐ Q → P ≡ Q

Note that the type `ext-axiom` does not itself postulate the axiom of extensionality.  It merely says what it is.  If we want to postulate it, we must assume we have a witness, or inhabitant of the type. We could do this in Agda in a number of ways, but probably the easiest is to simply add the witness as a parameter to a module, like so.<sup>[3](Relations.Discrete#fn3)</sup>

module ext-axiom-postulated {A : 𝓤 ̇} {ea : ext-axiom A 𝓦} where

Other notions of extensionality come up often in the [UALib][]; see, for example, [Overture.extensionality][] or [Relations.Truncation][].
-->
