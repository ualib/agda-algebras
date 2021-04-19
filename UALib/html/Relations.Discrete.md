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

#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : 𝓤 ̇`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="Pred"></a><a id="1094" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1103" href="Universes.html#403" class="Function Operator">̇</a> <a id="1105" class="Symbol">→</a> <a id="1107" class="Symbol">(</a><a id="1108" href="Relations.Discrete.html#1108" class="Bound">𝓦</a> <a id="1110" class="Symbol">:</a> <a id="1112" href="Universes.html#205" class="Postulate">Universe</a><a id="1120" class="Symbol">)</a> <a id="1122" class="Symbol">→</a> <a id="1124" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1126" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1128" href="Relations.Discrete.html#1108" class="Bound">𝓦</a> <a id="1130" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="1132" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1134" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="1139" href="Relations.Discrete.html#1139" class="Bound">A</a> <a id="1141" href="Relations.Discrete.html#1141" class="Bound">𝓦</a> <a id="1143" class="Symbol">=</a> <a id="1145" href="Relations.Discrete.html#1139" class="Bound">A</a> <a id="1147" class="Symbol">→</a> <a id="1149" href="Relations.Discrete.html#1141" class="Bound">𝓦</a> <a id="1151" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `𝓤 ̇`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

Like the [Agda Standard Library][], the [UALib][] includes types that represent the *element inclusion* and *subset inclusion* relations from set theory. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The definition of `∈` is standard. Nonetheless, here it is.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="_∈_"></a><a id="1962" href="Relations.Discrete.html#1962" class="Function Operator">_∈_</a> <a id="1966" class="Symbol">:</a> <a id="1968" class="Symbol">{</a><a id="1969" href="Relations.Discrete.html#1969" class="Bound">A</a> <a id="1971" class="Symbol">:</a> <a id="1973" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1975" href="Universes.html#403" class="Function Operator">̇</a><a id="1976" class="Symbol">}</a> <a id="1978" class="Symbol">→</a> <a id="1980" href="Relations.Discrete.html#1969" class="Bound">A</a> <a id="1982" class="Symbol">→</a> <a id="1984" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="1989" href="Relations.Discrete.html#1969" class="Bound">A</a> <a id="1991" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="1993" class="Symbol">→</a> <a id="1995" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="1997" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1999" href="Relations.Discrete.html#1999" class="Bound">x</a> <a id="2001" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="2003" href="Relations.Discrete.html#2003" class="Bound">P</a> <a id="2005" class="Symbol">=</a> <a id="2007" href="Relations.Discrete.html#2003" class="Bound">P</a> <a id="2009" href="Relations.Discrete.html#1999" class="Bound">x</a>

</pre>

The "subset" relation is denoted, as usual, with the `⊆` symbol.<sup>[1](Relations.Discrete.html#fn1)</sup>

<pre class="Agda">

<a id="_⊆_"></a><a id="2147" href="Relations.Discrete.html#2147" class="Function Operator">_⊆_</a> <a id="2151" class="Symbol">:</a> <a id="2153" class="Symbol">{</a><a id="2154" href="Relations.Discrete.html#2154" class="Bound">A</a> <a id="2156" class="Symbol">:</a> <a id="2158" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2160" href="Universes.html#403" class="Function Operator">̇</a> <a id="2162" class="Symbol">}</a> <a id="2164" class="Symbol">→</a> <a id="2166" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2171" href="Relations.Discrete.html#2154" class="Bound">A</a> <a id="2173" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2175" class="Symbol">→</a> <a id="2177" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2182" href="Relations.Discrete.html#2154" class="Bound">A</a> <a id="2184" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="2186" class="Symbol">→</a> <a id="2188" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2190" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2192" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2194" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2196" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="2198" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2200" href="Relations.Discrete.html#2200" class="Bound">P</a> <a id="2202" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="2204" href="Relations.Discrete.html#2204" class="Bound">Q</a> <a id="2206" class="Symbol">=</a> <a id="2208" class="Symbol">∀</a> <a id="2210" class="Symbol">{</a><a id="2211" href="Relations.Discrete.html#2211" class="Bound">x</a><a id="2212" class="Symbol">}</a> <a id="2214" class="Symbol">→</a> <a id="2216" href="Relations.Discrete.html#2211" class="Bound">x</a> <a id="2218" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="2220" href="Relations.Discrete.html#2200" class="Bound">P</a> <a id="2222" class="Symbol">→</a> <a id="2224" href="Relations.Discrete.html#2211" class="Bound">x</a> <a id="2226" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="2228" href="Relations.Discrete.html#2204" class="Bound">Q</a>

<a id="2231" class="Keyword">infix</a> <a id="2237" class="Number">4</a> <a id="2239" href="Relations.Discrete.html#2147" class="Function Operator">_⊆_</a>


</pre>




#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later. The first is an inductive type representing *disjoint union*.<sup>[2](Relations.Discrete#fn2)</sup>

<pre class="Agda">
<a id="2497" class="Keyword">infixr</a> <a id="2504" class="Number">1</a> <a id="2506" href="Relations.Discrete.html#2520" class="Datatype Operator">_⊎_</a> <a id="2510" href="Relations.Discrete.html#2691" class="Function Operator">_∪_</a>

<a id="2515" class="Keyword">data</a> <a id="_⊎_"></a><a id="2520" href="Relations.Discrete.html#2520" class="Datatype Operator">_⊎_</a> <a id="2524" class="Symbol">(</a><a id="2525" href="Relations.Discrete.html#2525" class="Bound">A</a> <a id="2527" class="Symbol">:</a> <a id="2529" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2531" href="Universes.html#403" class="Function Operator">̇</a><a id="2532" class="Symbol">)</a> <a id="2534" class="Symbol">(</a><a id="2535" href="Relations.Discrete.html#2535" class="Bound">B</a> <a id="2537" class="Symbol">:</a> <a id="2539" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2541" href="Universes.html#403" class="Function Operator">̇</a><a id="2542" class="Symbol">)</a> <a id="2544" class="Symbol">:</a> <a id="2546" href="Relations.Discrete.html#2529" class="Bound">𝓤</a> <a id="2548" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2550" href="Relations.Discrete.html#2539" class="Bound">𝓦</a> <a id="2552" href="Universes.html#403" class="Function Operator">̇</a> <a id="2554" class="Keyword">where</a>
 <a id="_⊎_.inj₁"></a><a id="2561" href="Relations.Discrete.html#2561" class="InductiveConstructor">inj₁</a> <a id="2566" class="Symbol">:</a> <a id="2568" class="Symbol">(</a><a id="2569" href="Relations.Discrete.html#2569" class="Bound">x</a> <a id="2571" class="Symbol">:</a> <a id="2573" href="Relations.Discrete.html#2525" class="Bound">A</a><a id="2574" class="Symbol">)</a> <a id="2576" class="Symbol">→</a> <a id="2578" href="Relations.Discrete.html#2525" class="Bound">A</a> <a id="2580" href="Relations.Discrete.html#2520" class="Datatype Operator">⊎</a> <a id="2582" href="Relations.Discrete.html#2535" class="Bound">B</a>
 <a id="_⊎_.inj₂"></a><a id="2585" href="Relations.Discrete.html#2585" class="InductiveConstructor">inj₂</a> <a id="2590" class="Symbol">:</a> <a id="2592" class="Symbol">(</a><a id="2593" href="Relations.Discrete.html#2593" class="Bound">y</a> <a id="2595" class="Symbol">:</a> <a id="2597" href="Relations.Discrete.html#2535" class="Bound">B</a><a id="2598" class="Symbol">)</a> <a id="2600" class="Symbol">→</a> <a id="2602" href="Relations.Discrete.html#2525" class="Bound">A</a> <a id="2604" href="Relations.Discrete.html#2520" class="Datatype Operator">⊎</a> <a id="2606" href="Relations.Discrete.html#2535" class="Bound">B</a>

</pre>

And this can be used to represent *union*, as follows.

<pre class="Agda">

<a id="_∪_"></a><a id="2691" href="Relations.Discrete.html#2691" class="Function Operator">_∪_</a> <a id="2695" class="Symbol">:</a> <a id="2697" class="Symbol">{</a><a id="2698" href="Relations.Discrete.html#2698" class="Bound">A</a> <a id="2700" class="Symbol">:</a> <a id="2702" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2704" href="Universes.html#403" class="Function Operator">̇</a><a id="2705" class="Symbol">}</a> <a id="2707" class="Symbol">→</a> <a id="2709" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2714" href="Relations.Discrete.html#2698" class="Bound">A</a> <a id="2716" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2718" class="Symbol">→</a> <a id="2720" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2725" href="Relations.Discrete.html#2698" class="Bound">A</a> <a id="2727" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="2729" class="Symbol">→</a> <a id="2731" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2736" href="Relations.Discrete.html#2698" class="Bound">A</a> <a id="2738" class="Symbol">(</a><a id="2739" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2741" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2743" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a><a id="2744" class="Symbol">)</a>
<a id="2746" href="Relations.Discrete.html#2746" class="Bound">P</a> <a id="2748" href="Relations.Discrete.html#2691" class="Function Operator">∪</a> <a id="2750" href="Relations.Discrete.html#2750" class="Bound">Q</a> <a id="2752" class="Symbol">=</a> <a id="2754" class="Symbol">λ</a> <a id="2756" href="Relations.Discrete.html#2756" class="Bound">x</a> <a id="2758" class="Symbol">→</a> <a id="2760" href="Relations.Discrete.html#2756" class="Bound">x</a> <a id="2762" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="2764" href="Relations.Discrete.html#2746" class="Bound">P</a> <a id="2766" href="Relations.Discrete.html#2520" class="Datatype Operator">⊎</a> <a id="2768" href="Relations.Discrete.html#2756" class="Bound">x</a> <a id="2770" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="2772" href="Relations.Discrete.html#2750" class="Bound">Q</a>


</pre>

Next we define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

<pre class="Agda">

<a id="Im_⊆_"></a><a id="2953" href="Relations.Discrete.html#2953" class="Function Operator">Im_⊆_</a> <a id="2959" class="Symbol">:</a> <a id="2961" class="Symbol">{</a><a id="2962" href="Relations.Discrete.html#2962" class="Bound">A</a> <a id="2964" class="Symbol">:</a> <a id="2966" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2968" href="Universes.html#403" class="Function Operator">̇</a><a id="2969" class="Symbol">}{</a><a id="2971" href="Relations.Discrete.html#2971" class="Bound">B</a> <a id="2973" class="Symbol">:</a> <a id="2975" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2977" href="Universes.html#403" class="Function Operator">̇</a><a id="2978" class="Symbol">}</a> <a id="2980" class="Symbol">→</a> <a id="2982" class="Symbol">(</a><a id="2983" href="Relations.Discrete.html#2962" class="Bound">A</a> <a id="2985" class="Symbol">→</a> <a id="2987" href="Relations.Discrete.html#2971" class="Bound">B</a><a id="2988" class="Symbol">)</a> <a id="2990" class="Symbol">→</a> <a id="2992" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="2997" href="Relations.Discrete.html#2971" class="Bound">B</a> <a id="2999" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="3001" class="Symbol">→</a> <a id="3003" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3005" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3007" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="3009" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3011" href="Relations.Discrete.html#2953" class="Function Operator">Im</a> <a id="3014" href="Relations.Discrete.html#3014" class="Bound">f</a> <a id="3016" href="Relations.Discrete.html#2953" class="Function Operator">⊆</a> <a id="3018" href="Relations.Discrete.html#3018" class="Bound">S</a> <a id="3020" class="Symbol">=</a> <a id="3022" class="Symbol">∀</a> <a id="3024" href="Relations.Discrete.html#3024" class="Bound">x</a> <a id="3026" class="Symbol">→</a> <a id="3028" href="Relations.Discrete.html#3014" class="Bound">f</a> <a id="3030" href="Relations.Discrete.html#3024" class="Bound">x</a> <a id="3032" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="3034" href="Relations.Discrete.html#3018" class="Bound">S</a>

</pre>


The *empty set* is naturally represented by the *empty type*, `𝟘`.<sup>[2](Relations.Discrete#fn2), [4](Relations.Discrete#fn4)</sup>

<pre class="Agda">

<a id="3199" class="Keyword">open</a> <a id="3204" class="Keyword">import</a> <a id="3211" href="Empty-Type.html" class="Module">Empty-Type</a> <a id="3222" class="Keyword">using</a> <a id="3228" class="Symbol">(</a><a id="3229" href="Empty-Type.html#125" class="Datatype">𝟘</a><a id="3230" class="Symbol">)</a>

<a id="∅"></a><a id="3233" href="Relations.Discrete.html#3233" class="Function">∅</a> <a id="3235" class="Symbol">:</a> <a id="3237" class="Symbol">{</a><a id="3238" href="Relations.Discrete.html#3238" class="Bound">A</a> <a id="3240" class="Symbol">:</a> <a id="3242" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3244" href="Universes.html#403" class="Function Operator">̇</a><a id="3245" class="Symbol">}</a> <a id="3247" class="Symbol">→</a> <a id="3249" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="3254" href="Relations.Discrete.html#3238" class="Bound">A</a> <a id="3256" href="Universes.html#158" class="Primitive">𝓤₀</a>
<a id="3259" href="Relations.Discrete.html#3233" class="Function">∅</a> <a id="3261" class="Symbol">_</a> <a id="3263" class="Symbol">=</a> <a id="3265" href="Empty-Type.html#125" class="Datatype">𝟘</a>

</pre>


Before closing our little predicates toolbox, let's insert a type that provides a natural way to encode *singletons*.

<pre class="Agda">

<a id="｛_｝"></a><a id="3414" href="Relations.Discrete.html#3414" class="Function Operator">｛_｝</a> <a id="3418" class="Symbol">:</a> <a id="3420" class="Symbol">{</a><a id="3421" href="Relations.Discrete.html#3421" class="Bound">A</a> <a id="3423" class="Symbol">:</a> <a id="3425" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3427" href="Universes.html#403" class="Function Operator">̇</a><a id="3428" class="Symbol">}</a> <a id="3430" class="Symbol">→</a> <a id="3432" href="Relations.Discrete.html#3421" class="Bound">A</a> <a id="3434" class="Symbol">→</a> <a id="3436" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="3441" href="Relations.Discrete.html#3421" class="Bound">A</a> <a id="3443" class="Symbol">_</a>
<a id="3445" href="Relations.Discrete.html#3414" class="Function Operator">｛</a> <a id="3447" href="Relations.Discrete.html#3447" class="Bound">x</a> <a id="3449" href="Relations.Discrete.html#3414" class="Function Operator">｝</a> <a id="3451" class="Symbol">=</a> <a id="3453" href="Relations.Discrete.html#3447" class="Bound">x</a> <a id="3455" href="Identity-Type.html#121" class="Datatype Operator">≡_</a>

</pre>


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → 𝓦 ̇` (for some universe 𝓦). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → 𝓦 ̇`, while a binary relation should have type `A → (A → 𝓦 ̇)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

<pre class="Agda">

<a id="REL"></a><a id="4178" href="Relations.Discrete.html#4178" class="Function">REL</a> <a id="4182" class="Symbol">:</a> <a id="4184" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4186" href="Universes.html#403" class="Function Operator">̇</a> <a id="4188" class="Symbol">→</a> <a id="4190" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4192" href="Universes.html#403" class="Function Operator">̇</a> <a id="4194" class="Symbol">→</a> <a id="4196" class="Symbol">(</a><a id="4197" href="Relations.Discrete.html#4197" class="Bound">𝓩</a> <a id="4199" class="Symbol">:</a> <a id="4201" href="Universes.html#205" class="Postulate">Universe</a><a id="4209" class="Symbol">)</a> <a id="4211" class="Symbol">→</a> <a id="4213" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4215" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4217" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4219" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4221" href="Relations.Discrete.html#4197" class="Bound">𝓩</a> <a id="4223" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4225" href="Universes.html#403" class="Function Operator">̇</a>
<a id="4227" href="Relations.Discrete.html#4178" class="Function">REL</a> <a id="4231" href="Relations.Discrete.html#4231" class="Bound">A</a> <a id="4233" href="Relations.Discrete.html#4233" class="Bound">B</a> <a id="4235" href="Relations.Discrete.html#4235" class="Bound">𝓩</a> <a id="4237" class="Symbol">=</a> <a id="4239" href="Relations.Discrete.html#4231" class="Bound">A</a> <a id="4241" class="Symbol">→</a> <a id="4243" href="Relations.Discrete.html#4233" class="Bound">B</a> <a id="4245" class="Symbol">→</a> <a id="4247" href="Relations.Discrete.html#4235" class="Bound">𝓩</a> <a id="4249" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

In the special case, where `𝓦 ≡ 𝓤` and `B ≡ A`, we have

<pre class="Agda">

<a id="Rel"></a><a id="4335" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="4339" class="Symbol">:</a> <a id="4341" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4343" href="Universes.html#403" class="Function Operator">̇</a> <a id="4345" class="Symbol">→</a> <a id="4347" class="Symbol">(</a><a id="4348" href="Relations.Discrete.html#4348" class="Bound">𝓩</a> <a id="4350" class="Symbol">:</a> <a id="4352" href="Universes.html#205" class="Postulate">Universe</a><a id="4360" class="Symbol">)</a> <a id="4362" class="Symbol">→</a> <a id="4364" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4366" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4368" href="Relations.Discrete.html#4348" class="Bound">𝓩</a> <a id="4370" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4372" href="Universes.html#403" class="Function Operator">̇</a>
<a id="4374" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="4378" href="Relations.Discrete.html#4378" class="Bound">A</a> <a id="4380" href="Relations.Discrete.html#4380" class="Bound">𝓩</a> <a id="4382" class="Symbol">=</a> <a id="4384" href="Relations.Discrete.html#4178" class="Function">REL</a> <a id="4388" href="Relations.Discrete.html#4378" class="Bound">A</a> <a id="4390" href="Relations.Discrete.html#4378" class="Bound">A</a> <a id="4392" href="Relations.Discrete.html#4380" class="Bound">𝓩</a>

</pre>


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


<pre class="Agda">

<a id="4835" class="Keyword">module</a> <a id="4842" href="Relations.Discrete.html#4842" class="Module">_</a> <a id="4844" class="Symbol">{</a><a id="4845" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="4847" class="Symbol">:</a> <a id="4849" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4851" href="Universes.html#403" class="Function Operator">̇</a><a id="4852" class="Symbol">}{</a><a id="4854" href="Relations.Discrete.html#4854" class="Bound">B</a> <a id="4856" class="Symbol">:</a> <a id="4858" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4860" href="Universes.html#403" class="Function Operator">̇</a><a id="4861" class="Symbol">}</a> <a id="4863" class="Keyword">where</a>

 <a id="4871" href="Relations.Discrete.html#4871" class="Function">ker</a> <a id="4875" class="Symbol">:</a> <a id="4877" class="Symbol">(</a><a id="4878" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="4880" class="Symbol">→</a> <a id="4882" href="Relations.Discrete.html#4854" class="Bound">B</a><a id="4883" class="Symbol">)</a> <a id="4885" class="Symbol">→</a> <a id="4887" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="4891" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="4893" href="Relations.Discrete.html#4858" class="Bound">𝓦</a>
 <a id="4896" href="Relations.Discrete.html#4871" class="Function">ker</a> <a id="4900" href="Relations.Discrete.html#4900" class="Bound">g</a> <a id="4902" href="Relations.Discrete.html#4902" class="Bound">x</a> <a id="4904" href="Relations.Discrete.html#4904" class="Bound">y</a> <a id="4906" class="Symbol">=</a> <a id="4908" href="Relations.Discrete.html#4900" class="Bound">g</a> <a id="4910" href="Relations.Discrete.html#4902" class="Bound">x</a> <a id="4912" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4914" href="Relations.Discrete.html#4900" class="Bound">g</a> <a id="4916" href="Relations.Discrete.html#4904" class="Bound">y</a>

 <a id="4920" href="Relations.Discrete.html#4920" class="Function">kernel</a> <a id="4927" class="Symbol">:</a> <a id="4929" class="Symbol">(</a><a id="4930" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="4932" class="Symbol">→</a> <a id="4934" href="Relations.Discrete.html#4854" class="Bound">B</a><a id="4935" class="Symbol">)</a> <a id="4937" class="Symbol">→</a> <a id="4939" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="4944" class="Symbol">(</a><a id="4945" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="4947" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4949" href="Relations.Discrete.html#4845" class="Bound">A</a><a id="4950" class="Symbol">)</a> <a id="4952" href="Relations.Discrete.html#4858" class="Bound">𝓦</a>
 <a id="4955" href="Relations.Discrete.html#4920" class="Function">kernel</a> <a id="4962" href="Relations.Discrete.html#4962" class="Bound">g</a> <a id="4964" class="Symbol">(</a><a id="4965" href="Relations.Discrete.html#4965" class="Bound">x</a> <a id="4967" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4969" href="Relations.Discrete.html#4969" class="Bound">y</a><a id="4970" class="Symbol">)</a> <a id="4972" class="Symbol">=</a> <a id="4974" href="Relations.Discrete.html#4962" class="Bound">g</a> <a id="4976" href="Relations.Discrete.html#4965" class="Bound">x</a> <a id="4978" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4980" href="Relations.Discrete.html#4962" class="Bound">g</a> <a id="4982" href="Relations.Discrete.html#4969" class="Bound">y</a>

 <a id="4986" href="Relations.Discrete.html#4986" class="Function">ker-sigma</a> <a id="4996" class="Symbol">:</a> <a id="4998" class="Symbol">(</a><a id="4999" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="5001" class="Symbol">→</a> <a id="5003" href="Relations.Discrete.html#4854" class="Bound">B</a><a id="5004" class="Symbol">)</a> <a id="5006" class="Symbol">→</a> <a id="5008" href="Relations.Discrete.html#4849" class="Bound">𝓤</a> <a id="5010" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5012" href="Relations.Discrete.html#4858" class="Bound">𝓦</a> <a id="5014" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5017" href="Relations.Discrete.html#4986" class="Function">ker-sigma</a> <a id="5027" href="Relations.Discrete.html#5027" class="Bound">g</a> <a id="5029" class="Symbol">=</a> <a id="5031" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5033" href="Relations.Discrete.html#5033" class="Bound">x</a> <a id="5035" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5037" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="5039" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5041" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5043" href="Relations.Discrete.html#5043" class="Bound">y</a> <a id="5045" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5047" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="5049" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5051" href="Relations.Discrete.html#5027" class="Bound">g</a> <a id="5053" href="Relations.Discrete.html#5033" class="Bound">x</a> <a id="5055" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5057" href="Relations.Discrete.html#5027" class="Bound">g</a> <a id="5059" href="Relations.Discrete.html#5043" class="Bound">y</a>

 <a id="5063" href="Relations.Discrete.html#5063" class="Function">ker-sigma&#39;</a> <a id="5074" class="Symbol">:</a> <a id="5076" class="Symbol">(</a><a id="5077" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="5079" class="Symbol">→</a> <a id="5081" href="Relations.Discrete.html#4854" class="Bound">B</a><a id="5082" class="Symbol">)</a> <a id="5084" class="Symbol">→</a> <a id="5086" href="Relations.Discrete.html#4849" class="Bound">𝓤</a> <a id="5088" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5090" href="Relations.Discrete.html#4858" class="Bound">𝓦</a> <a id="5092" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5095" href="Relations.Discrete.html#5063" class="Function">ker-sigma&#39;</a> <a id="5106" href="Relations.Discrete.html#5106" class="Bound">g</a> <a id="5108" class="Symbol">=</a> <a id="5110" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5112" href="Relations.Discrete.html#5112" class="Bound">(x</a> <a id="5115" href="Relations.Discrete.html#5112" class="Bound">,</a> <a id="5117" href="Relations.Discrete.html#5112" class="Bound">y)</a> <a id="5120" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5122" class="Symbol">(</a><a id="5123" href="Relations.Discrete.html#4845" class="Bound">A</a> <a id="5125" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5127" href="Relations.Discrete.html#4845" class="Bound">A</a><a id="5128" class="Symbol">)</a> <a id="5130" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5132" href="Relations.Discrete.html#5106" class="Bound">g</a> <a id="5134" href="Relations.Discrete.html#5113" class="Bound">x</a> <a id="5136" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5138" href="Relations.Discrete.html#5106" class="Bound">g</a> <a id="5140" href="Relations.Discrete.html#5117" class="Bound">y</a>

</pre>


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.<sup>[2](Relations.Discrete#fn2)</sup>

<pre class="Agda">

<a id="5367" class="Keyword">module</a> <a id="5374" href="Relations.Discrete.html#5374" class="Module">_</a> <a id="5376" class="Symbol">{</a><a id="5377" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5379" class="Symbol">:</a> <a id="5381" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5383" href="Universes.html#403" class="Function Operator">̇</a> <a id="5385" class="Symbol">}</a> <a id="5387" class="Keyword">where</a>

 <a id="5395" href="Relations.Discrete.html#5395" class="Function">𝟎</a> <a id="5397" class="Symbol">:</a> <a id="5399" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="5403" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5405" href="Relations.Discrete.html#5381" class="Bound">𝓤</a>
 <a id="5408" href="Relations.Discrete.html#5395" class="Function">𝟎</a> <a id="5410" href="Relations.Discrete.html#5410" class="Bound">x</a> <a id="5412" href="Relations.Discrete.html#5412" class="Bound">y</a> <a id="5414" class="Symbol">=</a> <a id="5416" href="Relations.Discrete.html#5410" class="Bound">x</a> <a id="5418" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5420" href="Relations.Discrete.html#5412" class="Bound">y</a>

 <a id="5424" href="Relations.Discrete.html#5424" class="Function">𝟎-pred</a> <a id="5431" class="Symbol">:</a> <a id="5433" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="5438" class="Symbol">(</a><a id="5439" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5441" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5443" href="Relations.Discrete.html#5377" class="Bound">A</a><a id="5444" class="Symbol">)</a> <a id="5446" href="Relations.Discrete.html#5381" class="Bound">𝓤</a>
 <a id="5449" href="Relations.Discrete.html#5424" class="Function">𝟎-pred</a> <a id="5456" class="Symbol">(</a><a id="5457" href="Relations.Discrete.html#5457" class="Bound">x</a> <a id="5459" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5461" href="Relations.Discrete.html#5461" class="Bound">y</a><a id="5462" class="Symbol">)</a> <a id="5464" class="Symbol">=</a> <a id="5466" href="Relations.Discrete.html#5457" class="Bound">x</a> <a id="5468" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5470" href="Relations.Discrete.html#5461" class="Bound">y</a>

 <a id="5474" href="Relations.Discrete.html#5474" class="Function">𝟎-sigma</a> <a id="5482" class="Symbol">:</a> <a id="5484" href="Relations.Discrete.html#5381" class="Bound">𝓤</a> <a id="5486" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5489" href="Relations.Discrete.html#5474" class="Function">𝟎-sigma</a> <a id="5497" class="Symbol">=</a> <a id="5499" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5501" href="Relations.Discrete.html#5501" class="Bound">x</a> <a id="5503" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5505" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5507" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5509" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5511" href="Relations.Discrete.html#5511" class="Bound">y</a> <a id="5513" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5515" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5517" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5519" href="Relations.Discrete.html#5501" class="Bound">x</a> <a id="5521" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5523" href="Relations.Discrete.html#5511" class="Bound">y</a>

 <a id="5527" href="Relations.Discrete.html#5527" class="Function">𝟎-sigma&#39;</a> <a id="5536" class="Symbol">:</a> <a id="5538" href="Relations.Discrete.html#5381" class="Bound">𝓤</a> <a id="5540" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5543" href="Relations.Discrete.html#5527" class="Function">𝟎-sigma&#39;</a> <a id="5552" class="Symbol">=</a> <a id="5554" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5556" href="Relations.Discrete.html#5556" class="Bound">(x</a> <a id="5559" href="Relations.Discrete.html#5556" class="Bound">,</a> <a id="5561" href="Relations.Discrete.html#5556" class="Bound">y)</a> <a id="5564" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5566" class="Symbol">(</a><a id="5567" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5569" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5571" href="Relations.Discrete.html#5377" class="Bound">A</a><a id="5572" class="Symbol">)</a> <a id="5574" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5576" href="Relations.Discrete.html#5557" class="Bound">x</a> <a id="5578" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5580" href="Relations.Discrete.html#5561" class="Bound">y</a>

</pre>

The *total relation* over `A`, which in set theory is the full Cartesian product `A × A`, could be represented using the one-element type from the `Unit-Type` module of [Type Topology][], as follows.

<pre class="Agda">

 <a id="5811" class="Keyword">open</a> <a id="5816" class="Keyword">import</a> <a id="5823" href="Unit-Type.html" class="Module">Unit-Type</a> <a id="5833" class="Keyword">using</a> <a id="5839" class="Symbol">(</a><a id="5840" href="Unit-Type.html#124" class="Datatype">𝟙</a><a id="5841" class="Symbol">)</a>

 <a id="5845" href="Relations.Discrete.html#5845" class="Function">𝟏</a> <a id="5847" class="Symbol">:</a> <a id="5849" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="5853" href="Relations.Discrete.html#5377" class="Bound">A</a> <a id="5855" href="Universes.html#158" class="Primitive">𝓤₀</a>
 <a id="5859" href="Relations.Discrete.html#5845" class="Function">𝟏</a> <a id="5861" href="Relations.Discrete.html#5861" class="Bound">a</a> <a id="5863" href="Relations.Discrete.html#5863" class="Bound">b</a> <a id="5865" class="Symbol">=</a> <a id="5867" href="Unit-Type.html#124" class="Datatype">𝟙</a>
</pre>



#### <a id="implication">Implication</a>

We define the following types representing *implication* for binary relations. (These are borrowed from the [Agda Standard Library][]; we merely translate them into [Type Topology][]/[UALib][] notation.)

<pre class="Agda">

<a id="_on_"></a><a id="6144" href="Relations.Discrete.html#6144" class="Function Operator">_on_</a> <a id="6149" class="Symbol">:</a> <a id="6151" class="Symbol">{</a><a id="6152" href="Relations.Discrete.html#6152" class="Bound">A</a> <a id="6154" class="Symbol">:</a> <a id="6156" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6158" href="Universes.html#403" class="Function Operator">̇</a><a id="6159" class="Symbol">}{</a><a id="6161" href="Relations.Discrete.html#6161" class="Bound">B</a> <a id="6163" class="Symbol">:</a> <a id="6165" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6167" href="Universes.html#403" class="Function Operator">̇</a><a id="6168" class="Symbol">}{</a><a id="6170" href="Relations.Discrete.html#6170" class="Bound">C</a> <a id="6172" class="Symbol">:</a> <a id="6174" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="6176" href="Universes.html#403" class="Function Operator">̇</a><a id="6177" class="Symbol">}</a> <a id="6179" class="Symbol">→</a> <a id="6181" class="Symbol">(</a><a id="6182" href="Relations.Discrete.html#6161" class="Bound">B</a> <a id="6184" class="Symbol">→</a> <a id="6186" href="Relations.Discrete.html#6161" class="Bound">B</a> <a id="6188" class="Symbol">→</a> <a id="6190" href="Relations.Discrete.html#6170" class="Bound">C</a><a id="6191" class="Symbol">)</a> <a id="6193" class="Symbol">→</a> <a id="6195" class="Symbol">(</a><a id="6196" href="Relations.Discrete.html#6152" class="Bound">A</a> <a id="6198" class="Symbol">→</a> <a id="6200" href="Relations.Discrete.html#6161" class="Bound">B</a><a id="6201" class="Symbol">)</a> <a id="6203" class="Symbol">→</a> <a id="6205" class="Symbol">(</a><a id="6206" href="Relations.Discrete.html#6152" class="Bound">A</a> <a id="6208" class="Symbol">→</a> <a id="6210" href="Relations.Discrete.html#6152" class="Bound">A</a> <a id="6212" class="Symbol">→</a> <a id="6214" href="Relations.Discrete.html#6170" class="Bound">C</a><a id="6215" class="Symbol">)</a>
<a id="6217" href="Relations.Discrete.html#6217" class="Bound">R</a> <a id="6219" href="Relations.Discrete.html#6144" class="Function Operator">on</a> <a id="6222" href="Relations.Discrete.html#6222" class="Bound">g</a> <a id="6224" class="Symbol">=</a> <a id="6226" class="Symbol">λ</a> <a id="6228" href="Relations.Discrete.html#6228" class="Bound">x</a> <a id="6230" href="Relations.Discrete.html#6230" class="Bound">y</a> <a id="6232" class="Symbol">→</a> <a id="6234" href="Relations.Discrete.html#6217" class="Bound">R</a> <a id="6236" class="Symbol">(</a><a id="6237" href="Relations.Discrete.html#6222" class="Bound">g</a> <a id="6239" href="Relations.Discrete.html#6228" class="Bound">x</a><a id="6240" class="Symbol">)</a> <a id="6242" class="Symbol">(</a><a id="6243" href="Relations.Discrete.html#6222" class="Bound">g</a> <a id="6245" href="Relations.Discrete.html#6230" class="Bound">y</a><a id="6246" class="Symbol">)</a>

<a id="_⇒_"></a><a id="6249" href="Relations.Discrete.html#6249" class="Function Operator">_⇒_</a> <a id="6253" class="Symbol">:</a> <a id="6255" class="Symbol">{</a><a id="6256" href="Relations.Discrete.html#6256" class="Bound">A</a> <a id="6258" class="Symbol">:</a> <a id="6260" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6262" href="Universes.html#403" class="Function Operator">̇</a><a id="6263" class="Symbol">}{</a><a id="6265" href="Relations.Discrete.html#6265" class="Bound">B</a> <a id="6267" class="Symbol">:</a> <a id="6269" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6271" href="Universes.html#403" class="Function Operator">̇</a><a id="6272" class="Symbol">}</a> <a id="6274" class="Symbol">→</a> <a id="6276" href="Relations.Discrete.html#4178" class="Function">REL</a> <a id="6280" href="Relations.Discrete.html#6256" class="Bound">A</a> <a id="6282" href="Relations.Discrete.html#6265" class="Bound">B</a> <a id="6284" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6286" class="Symbol">→</a> <a id="6288" href="Relations.Discrete.html#4178" class="Function">REL</a> <a id="6292" href="Relations.Discrete.html#6256" class="Bound">A</a> <a id="6294" href="Relations.Discrete.html#6265" class="Bound">B</a> <a id="6296" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6298" class="Symbol">→</a> <a id="6300" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6302" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6304" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6306" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6308" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6310" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6312" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6314" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6316" href="Relations.Discrete.html#6316" class="Bound">P</a> <a id="6318" href="Relations.Discrete.html#6249" class="Function Operator">⇒</a> <a id="6320" href="Relations.Discrete.html#6320" class="Bound">Q</a> <a id="6322" class="Symbol">=</a> <a id="6324" class="Symbol">∀</a> <a id="6326" class="Symbol">{</a><a id="6327" href="Relations.Discrete.html#6327" class="Bound">i</a> <a id="6329" href="Relations.Discrete.html#6329" class="Bound">j</a><a id="6330" class="Symbol">}</a> <a id="6332" class="Symbol">→</a> <a id="6334" href="Relations.Discrete.html#6316" class="Bound">P</a> <a id="6336" href="Relations.Discrete.html#6327" class="Bound">i</a> <a id="6338" href="Relations.Discrete.html#6329" class="Bound">j</a> <a id="6340" class="Symbol">→</a> <a id="6342" href="Relations.Discrete.html#6320" class="Bound">Q</a> <a id="6344" href="Relations.Discrete.html#6327" class="Bound">i</a> <a id="6346" href="Relations.Discrete.html#6329" class="Bound">j</a>

<a id="6349" class="Keyword">infixr</a> <a id="6356" class="Number">4</a> <a id="6358" href="Relations.Discrete.html#6249" class="Function Operator">_⇒_</a>

</pre>

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.

<pre class="Agda">

<a id="_=[_]⇒_"></a><a id="6472" href="Relations.Discrete.html#6472" class="Function Operator">_=[_]⇒_</a> <a id="6480" class="Symbol">:</a> <a id="6482" class="Symbol">{</a><a id="6483" href="Relations.Discrete.html#6483" class="Bound">A</a> <a id="6485" class="Symbol">:</a> <a id="6487" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6489" href="Universes.html#403" class="Function Operator">̇</a><a id="6490" class="Symbol">}{</a><a id="6492" href="Relations.Discrete.html#6492" class="Bound">B</a> <a id="6494" class="Symbol">:</a> <a id="6496" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6498" href="Universes.html#403" class="Function Operator">̇</a><a id="6499" class="Symbol">}</a> <a id="6501" class="Symbol">→</a> <a id="6503" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="6507" href="Relations.Discrete.html#6483" class="Bound">A</a> <a id="6509" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6511" class="Symbol">→</a> <a id="6513" class="Symbol">(</a><a id="6514" href="Relations.Discrete.html#6483" class="Bound">A</a> <a id="6516" class="Symbol">→</a> <a id="6518" href="Relations.Discrete.html#6492" class="Bound">B</a><a id="6519" class="Symbol">)</a> <a id="6521" class="Symbol">→</a> <a id="6523" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="6527" href="Relations.Discrete.html#6492" class="Bound">B</a> <a id="6529" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6531" class="Symbol">→</a> <a id="6533" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6535" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6537" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="6539" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6541" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="6543" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6545" href="Relations.Discrete.html#6545" class="Bound">P</a> <a id="6547" href="Relations.Discrete.html#6472" class="Function Operator">=[</a> <a id="6550" href="Relations.Discrete.html#6550" class="Bound">g</a> <a id="6552" href="Relations.Discrete.html#6472" class="Function Operator">]⇒</a> <a id="6555" href="Relations.Discrete.html#6555" class="Bound">Q</a> <a id="6557" class="Symbol">=</a> <a id="6559" href="Relations.Discrete.html#6545" class="Bound">P</a> <a id="6561" href="Relations.Discrete.html#6249" class="Function Operator">⇒</a> <a id="6563" class="Symbol">(</a><a id="6564" href="Relations.Discrete.html#6555" class="Bound">Q</a> <a id="6566" href="Relations.Discrete.html#6144" class="Function Operator">on</a> <a id="6569" href="Relations.Discrete.html#6550" class="Bound">g</a><a id="6570" class="Symbol">)</a>

<a id="6573" class="Keyword">infixr</a> <a id="6580" class="Number">4</a> <a id="6582" href="Relations.Discrete.html#6472" class="Function Operator">_=[_]⇒_</a>

</pre>


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

<pre class="Agda">

<a id="7298" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="7323" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="7326" class="Symbol">:</a> <a id="7328" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7330" href="Universes.html#403" class="Function Operator">̇</a> <a id="7332" class="Symbol">→</a> <a id="7334" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7336" href="Universes.html#403" class="Function Operator">̇</a> <a id="7338" class="Symbol">→</a> <a id="7340" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7342" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7344" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7346" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7348" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="7351" href="Relations.Discrete.html#7351" class="Bound">I</a> <a id="7353" href="Relations.Discrete.html#7353" class="Bound">A</a> <a id="7355" class="Symbol">=</a> <a id="7357" class="Symbol">(</a><a id="7358" href="Relations.Discrete.html#7351" class="Bound">I</a> <a id="7360" class="Symbol">→</a> <a id="7362" href="Relations.Discrete.html#7353" class="Bound">A</a><a id="7363" class="Symbol">)</a> <a id="7365" class="Symbol">→</a> <a id="7367" href="Relations.Discrete.html#7353" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

<pre class="Agda">

<a id="π"></a><a id="7737" href="Relations.Discrete.html#7737" class="Function">π</a> <a id="7739" class="Symbol">:</a> <a id="7741" class="Symbol">{</a><a id="7742" href="Relations.Discrete.html#7742" class="Bound">I</a> <a id="7744" class="Symbol">:</a> <a id="7746" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7748" href="Universes.html#403" class="Function Operator">̇</a> <a id="7750" class="Symbol">}</a> <a id="7752" class="Symbol">{</a><a id="7753" href="Relations.Discrete.html#7753" class="Bound">A</a> <a id="7755" class="Symbol">:</a> <a id="7757" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7759" href="Universes.html#403" class="Function Operator">̇</a> <a id="7761" class="Symbol">}</a> <a id="7763" class="Symbol">→</a> <a id="7765" href="Relations.Discrete.html#7742" class="Bound">I</a> <a id="7767" class="Symbol">→</a> <a id="7769" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="7772" href="Relations.Discrete.html#7742" class="Bound">I</a> <a id="7774" href="Relations.Discrete.html#7753" class="Bound">A</a>
<a id="7776" href="Relations.Discrete.html#7737" class="Function">π</a> <a id="7778" href="Relations.Discrete.html#7778" class="Bound">i</a> <a id="7780" href="Relations.Discrete.html#7780" class="Bound">x</a> <a id="7782" class="Symbol">=</a> <a id="7784" href="Relations.Discrete.html#7780" class="Bound">x</a> <a id="7786" href="Relations.Discrete.html#7778" class="Bound">i</a>

</pre>

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A 𝓦` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (v i)` &nbsp; `→` &nbsp; `R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UALib][].

<pre class="Agda">

<a id="eval-rel"></a><a id="8205" href="Relations.Discrete.html#8205" class="Function">eval-rel</a> <a id="8214" class="Symbol">:</a> <a id="8216" class="Symbol">{</a><a id="8217" href="Relations.Discrete.html#8217" class="Bound">A</a> <a id="8219" class="Symbol">:</a> <a id="8221" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8223" href="Universes.html#403" class="Function Operator">̇</a><a id="8224" class="Symbol">}{</a><a id="8226" href="Relations.Discrete.html#8226" class="Bound">I</a> <a id="8228" class="Symbol">:</a> <a id="8230" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8232" href="Universes.html#403" class="Function Operator">̇</a><a id="8233" class="Symbol">}</a> <a id="8235" class="Symbol">→</a> <a id="8237" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="8241" href="Relations.Discrete.html#8217" class="Bound">A</a> <a id="8243" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8245" class="Symbol">→</a> <a id="8247" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="8251" class="Symbol">(</a><a id="8252" href="Relations.Discrete.html#8226" class="Bound">I</a> <a id="8254" class="Symbol">→</a> <a id="8256" href="Relations.Discrete.html#8217" class="Bound">A</a><a id="8257" class="Symbol">)(</a><a id="8259" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8261" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8263" href="Universes.html#264" class="Generalizable">𝓦</a><a id="8264" class="Symbol">)</a>
<a id="8266" href="Relations.Discrete.html#8205" class="Function">eval-rel</a> <a id="8275" href="Relations.Discrete.html#8275" class="Bound">R</a> <a id="8277" href="Relations.Discrete.html#8277" class="Bound">u</a> <a id="8279" href="Relations.Discrete.html#8279" class="Bound">v</a> <a id="8281" class="Symbol">=</a> <a id="8283" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8285" href="Relations.Discrete.html#8285" class="Bound">i</a> <a id="8287" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8289" class="Symbol">_</a> <a id="8291" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8293" href="Relations.Discrete.html#8275" class="Bound">R</a> <a id="8295" class="Symbol">(</a><a id="8296" href="Relations.Discrete.html#8277" class="Bound">u</a> <a id="8298" href="Relations.Discrete.html#8285" class="Bound">i</a><a id="8299" class="Symbol">)</a> <a id="8301" class="Symbol">(</a><a id="8302" href="Relations.Discrete.html#8279" class="Bound">v</a> <a id="8304" href="Relations.Discrete.html#8285" class="Bound">i</a><a id="8305" class="Symbol">)</a>

<a id="_|:_"></a><a id="8308" href="Relations.Discrete.html#8308" class="Function Operator">_|:_</a> <a id="8313" class="Symbol">:</a> <a id="8315" class="Symbol">{</a><a id="8316" href="Relations.Discrete.html#8316" class="Bound">A</a> <a id="8318" class="Symbol">:</a> <a id="8320" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8322" href="Universes.html#403" class="Function Operator">̇</a><a id="8323" class="Symbol">}{</a><a id="8325" href="Relations.Discrete.html#8325" class="Bound">I</a> <a id="8327" class="Symbol">:</a> <a id="8329" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8331" href="Universes.html#403" class="Function Operator">̇</a><a id="8332" class="Symbol">}</a> <a id="8334" class="Symbol">→</a> <a id="8336" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="8339" href="Relations.Discrete.html#8325" class="Bound">I</a> <a id="8341" href="Relations.Discrete.html#8316" class="Bound">A</a> <a id="8343" class="Symbol">→</a> <a id="8345" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="8349" href="Relations.Discrete.html#8316" class="Bound">A</a> <a id="8351" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8353" class="Symbol">→</a> <a id="8355" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8357" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8359" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8361" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8363" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8365" href="Universes.html#403" class="Function Operator">̇</a>
<a id="8367" href="Relations.Discrete.html#8367" class="Bound">f</a> <a id="8369" href="Relations.Discrete.html#8308" class="Function Operator">|:</a> <a id="8372" href="Relations.Discrete.html#8372" class="Bound">R</a>  <a id="8375" class="Symbol">=</a> <a id="8377" class="Symbol">(</a><a id="8378" href="Relations.Discrete.html#8205" class="Function">eval-rel</a> <a id="8387" href="Relations.Discrete.html#8372" class="Bound">R</a><a id="8388" class="Symbol">)</a> <a id="8390" href="Relations.Discrete.html#6472" class="Function Operator">=[</a> <a id="8393" href="Relations.Discrete.html#8367" class="Bound">f</a> <a id="8395" href="Relations.Discrete.html#6472" class="Function Operator">]⇒</a> <a id="8398" href="Relations.Discrete.html#8372" class="Bound">R</a>

</pre>

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

In case it helps the reader, we note that instead of using the slick implication notation, we could have defined the `|:` relation more explicitly, like so.

<pre class="Agda">

<a id="compatible-fun"></a><a id="8713" href="Relations.Discrete.html#8713" class="Function">compatible-fun</a> <a id="8728" class="Symbol">:</a> <a id="8730" class="Symbol">{</a><a id="8731" href="Relations.Discrete.html#8731" class="Bound">A</a> <a id="8733" class="Symbol">:</a> <a id="8735" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8737" href="Universes.html#403" class="Function Operator">̇</a><a id="8738" class="Symbol">}{</a><a id="8740" href="Relations.Discrete.html#8740" class="Bound">I</a> <a id="8742" class="Symbol">:</a> <a id="8744" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8746" href="Universes.html#403" class="Function Operator">̇</a><a id="8747" class="Symbol">}</a> <a id="8749" class="Symbol">→</a> <a id="8751" class="Symbol">(</a><a id="8752" href="Relations.Discrete.html#8752" class="Bound">f</a> <a id="8754" class="Symbol">:</a> <a id="8756" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="8759" href="Relations.Discrete.html#8740" class="Bound">I</a> <a id="8761" href="Relations.Discrete.html#8731" class="Bound">A</a><a id="8762" class="Symbol">)(</a><a id="8764" href="Relations.Discrete.html#8764" class="Bound">R</a> <a id="8766" class="Symbol">:</a> <a id="8768" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="8772" href="Relations.Discrete.html#8731" class="Bound">A</a> <a id="8774" href="Universes.html#264" class="Generalizable">𝓦</a><a id="8775" class="Symbol">)</a> <a id="8777" class="Symbol">→</a> <a id="8779" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="8781" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8783" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8785" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8787" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8789" href="Universes.html#403" class="Function Operator">̇</a>
<a id="8791" href="Relations.Discrete.html#8713" class="Function">compatible-fun</a> <a id="8806" href="Relations.Discrete.html#8806" class="Bound">f</a> <a id="8808" href="Relations.Discrete.html#8808" class="Bound">R</a>  <a id="8811" class="Symbol">=</a> <a id="8813" class="Symbol">∀</a> <a id="8815" href="Relations.Discrete.html#8815" class="Bound">u</a> <a id="8817" href="Relations.Discrete.html#8817" class="Bound">v</a> <a id="8819" class="Symbol">→</a> <a id="8821" class="Symbol">(</a><a id="8822" href="Relations.Discrete.html#8205" class="Function">eval-rel</a> <a id="8831" href="Relations.Discrete.html#8808" class="Bound">R</a><a id="8832" class="Symbol">)</a> <a id="8834" href="Relations.Discrete.html#8815" class="Bound">u</a> <a id="8836" href="Relations.Discrete.html#8817" class="Bound">v</a> <a id="8838" class="Symbol">→</a> <a id="8840" href="Relations.Discrete.html#8808" class="Bound">R</a> <a id="8842" class="Symbol">(</a><a id="8843" href="Relations.Discrete.html#8806" class="Bound">f</a> <a id="8845" href="Relations.Discrete.html#8815" class="Bound">u</a><a id="8846" class="Symbol">)</a> <a id="8848" class="Symbol">(</a><a id="8849" href="Relations.Discrete.html#8806" class="Bound">f</a> <a id="8851" href="Relations.Discrete.html#8817" class="Bound">v</a><a id="8852" class="Symbol">)</a>

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
