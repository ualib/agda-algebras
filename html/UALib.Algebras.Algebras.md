---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebra-types">Algebra Types</a>

This section presents the [UALib.Algebras.Algebras] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="300" class="Symbol">{-#</a> <a id="304" class="Keyword">OPTIONS</a> <a id="312" class="Pragma">--without-K</a> <a id="324" class="Pragma">--exact-split</a> <a id="338" class="Pragma">--safe</a> <a id="345" class="Symbol">#-}</a>

<a id="350" class="Keyword">module</a> <a id="357" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="381" class="Keyword">where</a>

<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="426" class="Keyword">public</a>

<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="474" class="Keyword">using</a> <a id="480" class="Symbol">(</a><a id="481" href="universes.html#504" class="Primitive">𝓤₀</a><a id="483" class="Symbol">;</a> <a id="485" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="486" class="Symbol">;</a> <a id="488" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="489" class="Symbol">)</a> <a id="491" class="Keyword">public</a>

</pre>

#### Sets (0-groupoids)

Before defining the type of algebras, we need to explain what it means to be a set in univalent mathematics.  A type is defined to be a **set** if there is at most one way for any two of its elements to be equal.

MHE defines this notion (e.g., in the MGS-Embeddings module) as follows:

```agda
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

and explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."

#### The main Algebra type

The first type for representing algebras that we define will put the domain of an algebra in an arbitrary type.  We will call these "∞-algebras" because the universe need not be a set.  After that, we define the type of algebra that we typically think of when doing informal universal algebra, which we call "0-algebras" since their domains are sets.

<pre class="Agda">

<a id="∞-algebra"></a><a id="1461" href="UALib.Algebras.Algebras.html#1461" class="Function">∞-algebra</a> <a id="Algebra"></a><a id="1471" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="1479" class="Symbol">:</a> <a id="1481" class="Symbol">(</a><a id="1482" href="UALib.Algebras.Algebras.html#1482" class="Bound">𝓤</a> <a id="1484" class="Symbol">:</a> <a id="1486" href="universes.html#551" class="Postulate">Universe</a><a id="1494" class="Symbol">)(</a><a id="1496" href="UALib.Algebras.Algebras.html#1496" class="Bound">𝑆</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="1510" href="universes.html#613" class="Generalizable">𝓞</a> <a id="1512" href="universes.html#617" class="Generalizable">𝓥</a><a id="1513" class="Symbol">)</a> <a id="1515" class="Symbol">→</a>  <a id="1518" href="universes.html#613" class="Generalizable">𝓞</a> <a id="1520" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1522" href="universes.html#617" class="Generalizable">𝓥</a> <a id="1524" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1526" href="UALib.Algebras.Algebras.html#1482" class="Bound">𝓤</a> <a id="1528" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1530" href="universes.html#758" class="Function Operator">̇</a>

<a id="1533" href="UALib.Algebras.Algebras.html#1461" class="Function">∞-algebra</a> <a id="1543" href="UALib.Algebras.Algebras.html#1543" class="Bound">𝓤</a>  <a id="1546" href="UALib.Algebras.Algebras.html#1546" class="Bound">𝑆</a> <a id="1548" class="Symbol">=</a> <a id="1550" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1552" href="UALib.Algebras.Algebras.html#1552" class="Bound">A</a> <a id="1554" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1556" href="UALib.Algebras.Algebras.html#1543" class="Bound">𝓤</a> <a id="1558" href="universes.html#758" class="Function Operator">̇</a> <a id="1560" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1562" class="Symbol">((</a><a id="1564" href="UALib.Algebras.Algebras.html#1564" class="Bound">f</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="1570" href="UALib.Algebras.Algebras.html#1546" class="Bound">𝑆</a> <a id="1572" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a><a id="1573" class="Symbol">)</a> <a id="1575" class="Symbol">→</a> <a id="1577" href="UALib.Algebras.Signatures.html#535" class="Function">Op</a> <a id="1580" class="Symbol">(</a><a id="1581" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="1583" href="UALib.Algebras.Algebras.html#1546" class="Bound">𝑆</a> <a id="1585" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="1587" href="UALib.Algebras.Algebras.html#1564" class="Bound">f</a><a id="1588" class="Symbol">)</a> <a id="1590" href="UALib.Algebras.Algebras.html#1552" class="Bound">A</a><a id="1591" class="Symbol">)</a>
<a id="1593" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="1601" class="Symbol">=</a> <a id="1603" href="UALib.Algebras.Algebras.html#1461" class="Function">∞-algebra</a>

</pre>

The type of the `Algebra 𝓤 𝑆` type is `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`. This type is used so often in our library that in some modules (where the signature universe levels 𝓞 𝓥 are already in context) we will define the following shorthand for the universe level:

```agda
OV : Universe → Universe
OV = λ 𝓤 → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
```

so we can now simply type `OV 𝓤` in place of the more laborious `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.

<pre class="Agda">

<a id="2030" class="Keyword">data</a> <a id="monoid-op"></a><a id="2035" href="UALib.Algebras.Algebras.html#2035" class="Datatype">monoid-op</a> <a id="2045" class="Symbol">:</a> <a id="2047" href="universes.html#504" class="Primitive">𝓤₀</a> <a id="2050" href="universes.html#758" class="Function Operator">̇</a> <a id="2052" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2059" href="UALib.Algebras.Algebras.html#2059" class="InductiveConstructor">e</a> <a id="2061" class="Symbol">:</a> <a id="2063" href="UALib.Algebras.Algebras.html#2035" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2074" href="UALib.Algebras.Algebras.html#2074" class="InductiveConstructor">·</a> <a id="2076" class="Symbol">:</a> <a id="2078" href="UALib.Algebras.Algebras.html#2035" class="Datatype">monoid-op</a>

<a id="monoid-sig"></a><a id="2089" href="UALib.Algebras.Algebras.html#2089" class="Function">monoid-sig</a> <a id="2100" class="Symbol">:</a> <a id="2102" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="2112" class="Symbol">_</a> <a id="2114" class="Symbol">_</a>
<a id="2116" href="UALib.Algebras.Algebras.html#2089" class="Function">monoid-sig</a> <a id="2127" class="Symbol">=</a> <a id="2129" href="UALib.Algebras.Algebras.html#2035" class="Datatype">monoid-op</a> <a id="2139" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="2141" class="Symbol">λ</a> <a id="2143" class="Symbol">{</a> <a id="2145" href="UALib.Algebras.Algebras.html#2059" class="InductiveConstructor">e</a> <a id="2147" class="Symbol">→</a> <a id="2149" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2150" class="Symbol">;</a> <a id="2152" href="UALib.Algebras.Algebras.html#2074" class="InductiveConstructor">·</a> <a id="2154" class="Symbol">→</a> <a id="2156" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2158" class="Symbol">}</a>

</pre>

#### Algebras as record types

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="2361" class="Keyword">module</a> <a id="2368" href="UALib.Algebras.Algebras.html#2368" class="Module">_</a> <a id="2370" class="Symbol">{</a><a id="2371" href="UALib.Algebras.Algebras.html#2371" class="Bound">𝓞</a> <a id="2373" href="UALib.Algebras.Algebras.html#2373" class="Bound">𝓥</a> <a id="2375" class="Symbol">:</a> <a id="2377" href="universes.html#551" class="Postulate">Universe</a><a id="2385" class="Symbol">}</a> <a id="2387" class="Keyword">where</a>
 <a id="2394" class="Keyword">record</a> <a id="2401" href="UALib.Algebras.Algebras.html#2401" class="Record">algebra</a> <a id="2409" class="Symbol">(</a><a id="2410" href="UALib.Algebras.Algebras.html#2410" class="Bound">𝓤</a> <a id="2412" class="Symbol">:</a> <a id="2414" href="universes.html#551" class="Postulate">Universe</a><a id="2422" class="Symbol">)</a> <a id="2424" class="Symbol">(</a><a id="2425" href="UALib.Algebras.Algebras.html#2425" class="Bound">𝑆</a> <a id="2427" class="Symbol">:</a> <a id="2429" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="2439" href="UALib.Algebras.Algebras.html#2371" class="Bound">𝓞</a> <a id="2441" href="UALib.Algebras.Algebras.html#2373" class="Bound">𝓥</a><a id="2442" class="Symbol">)</a> <a id="2444" class="Symbol">:</a> <a id="2446" class="Symbol">(</a><a id="2447" href="UALib.Algebras.Algebras.html#2371" class="Bound">𝓞</a> <a id="2449" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2451" href="UALib.Algebras.Algebras.html#2373" class="Bound">𝓥</a> <a id="2453" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2455" href="UALib.Algebras.Algebras.html#2410" class="Bound">𝓤</a><a id="2456" class="Symbol">)</a> <a id="2458" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="2460" href="universes.html#758" class="Function Operator">̇</a> <a id="2462" class="Keyword">where</a>
  <a id="2470" class="Keyword">constructor</a> <a id="2482" href="UALib.Algebras.Algebras.html#2482" class="InductiveConstructor">mkalg</a>
  <a id="2490" class="Keyword">field</a>
   <a id="2499" href="UALib.Algebras.Algebras.html#2499" class="Field">univ</a> <a id="2504" class="Symbol">:</a> <a id="2506" href="UALib.Algebras.Algebras.html#2410" class="Bound">𝓤</a> <a id="2508" href="universes.html#758" class="Function Operator">̇</a>
   <a id="2513" href="UALib.Algebras.Algebras.html#2513" class="Field">op</a> <a id="2516" class="Symbol">:</a> <a id="2518" class="Symbol">(</a><a id="2519" href="UALib.Algebras.Algebras.html#2519" class="Bound">f</a> <a id="2521" class="Symbol">:</a> <a id="2523" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="2525" href="UALib.Algebras.Algebras.html#2425" class="Bound">𝑆</a> <a id="2527" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a><a id="2528" class="Symbol">)</a> <a id="2530" class="Symbol">→</a> <a id="2532" class="Symbol">((</a><a id="2534" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="2536" href="UALib.Algebras.Algebras.html#2425" class="Bound">𝑆</a> <a id="2538" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="2540" href="UALib.Algebras.Algebras.html#2519" class="Bound">f</a><a id="2541" class="Symbol">)</a> <a id="2543" class="Symbol">→</a> <a id="2545" href="UALib.Algebras.Algebras.html#2499" class="Field">univ</a><a id="2549" class="Symbol">)</a> <a id="2551" class="Symbol">→</a> <a id="2553" href="UALib.Algebras.Algebras.html#2499" class="Field">univ</a>


</pre>

(Recall, the type `Signature 𝓞 𝓥` is simply defined as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.)

Of course, we can go back and forth between the two representations of algebras, like so.

<pre class="Agda">

<a id="2783" class="Keyword">module</a> <a id="2790" href="UALib.Algebras.Algebras.html#2790" class="Module">_</a> <a id="2792" class="Symbol">{</a><a id="2793" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="2795" href="UALib.Algebras.Algebras.html#2795" class="Bound">𝓞</a> <a id="2797" href="UALib.Algebras.Algebras.html#2797" class="Bound">𝓥</a> <a id="2799" class="Symbol">:</a> <a id="2801" href="universes.html#551" class="Postulate">Universe</a><a id="2809" class="Symbol">}</a> <a id="2811" class="Symbol">{</a><a id="2812" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a> <a id="2814" class="Symbol">:</a> <a id="2816" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="2826" href="UALib.Algebras.Algebras.html#2795" class="Bound">𝓞</a> <a id="2828" href="UALib.Algebras.Algebras.html#2797" class="Bound">𝓥</a><a id="2829" class="Symbol">}</a> <a id="2831" class="Keyword">where</a>

 <a id="2839" class="Keyword">open</a> <a id="2844" href="UALib.Algebras.Algebras.html#2401" class="Module">algebra</a>

 <a id="2854" href="UALib.Algebras.Algebras.html#2854" class="Function">algebra→Algebra</a> <a id="2870" class="Symbol">:</a> <a id="2872" href="UALib.Algebras.Algebras.html#2401" class="Record">algebra</a> <a id="2880" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="2882" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a> <a id="2884" class="Symbol">→</a> <a id="2886" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="2894" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="2896" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a>
 <a id="2899" href="UALib.Algebras.Algebras.html#2854" class="Function">algebra→Algebra</a> <a id="2915" href="UALib.Algebras.Algebras.html#2915" class="Bound">𝑨</a> <a id="2917" class="Symbol">=</a> <a id="2919" class="Symbol">(</a><a id="2920" href="UALib.Algebras.Algebras.html#2499" class="Field">univ</a> <a id="2925" href="UALib.Algebras.Algebras.html#2915" class="Bound">𝑨</a> <a id="2927" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="2929" href="UALib.Algebras.Algebras.html#2513" class="Field">op</a> <a id="2932" href="UALib.Algebras.Algebras.html#2915" class="Bound">𝑨</a><a id="2933" class="Symbol">)</a>

 <a id="2937" href="UALib.Algebras.Algebras.html#2937" class="Function">Algebra→algebra</a> <a id="2953" class="Symbol">:</a> <a id="2955" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="2963" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="2965" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a> <a id="2967" class="Symbol">→</a> <a id="2969" href="UALib.Algebras.Algebras.html#2401" class="Record">algebra</a> <a id="2977" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="2979" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a>
 <a id="2982" href="UALib.Algebras.Algebras.html#2937" class="Function">Algebra→algebra</a> <a id="2998" href="UALib.Algebras.Algebras.html#2998" class="Bound">𝑨</a> <a id="3000" class="Symbol">=</a> <a id="3002" href="UALib.Algebras.Algebras.html#2482" class="InductiveConstructor">mkalg</a> <a id="3008" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="3010" href="UALib.Algebras.Algebras.html#2998" class="Bound">𝑨</a> <a id="3012" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="3014" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="3016" href="UALib.Algebras.Algebras.html#2998" class="Bound">𝑨</a> <a id="3018" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a>

</pre>

#### Operation interpretation syntax

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

<pre class="Agda">

 <a id="3348" href="UALib.Algebras.Algebras.html#3348" class="Function Operator">_̂_</a> <a id="3352" class="Symbol">:</a> <a id="3354" class="Symbol">(</a><a id="3355" href="UALib.Algebras.Algebras.html#3355" class="Bound">f</a> <a id="3357" class="Symbol">:</a> <a id="3359" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="3361" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a> <a id="3363" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a><a id="3364" class="Symbol">)(</a><a id="3366" href="UALib.Algebras.Algebras.html#3366" class="Bound">𝑨</a> <a id="3368" class="Symbol">:</a> <a id="3370" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="3378" href="UALib.Algebras.Algebras.html#2793" class="Bound">𝓤</a> <a id="3380" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a><a id="3381" class="Symbol">)</a> <a id="3383" class="Symbol">→</a> <a id="3385" class="Symbol">(</a><a id="3386" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="3388" href="UALib.Algebras.Algebras.html#2812" class="Bound">𝑆</a> <a id="3390" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="3392" href="UALib.Algebras.Algebras.html#3355" class="Bound">f</a>  <a id="3395" class="Symbol">→</a>  <a id="3398" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="3400" href="UALib.Algebras.Algebras.html#3366" class="Bound">𝑨</a> <a id="3402" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a><a id="3403" class="Symbol">)</a> <a id="3405" class="Symbol">→</a> <a id="3407" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="3409" href="UALib.Algebras.Algebras.html#3366" class="Bound">𝑨</a> <a id="3411" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a>

 <a id="3415" href="UALib.Algebras.Algebras.html#3415" class="Bound">f</a> <a id="3417" href="UALib.Algebras.Algebras.html#3348" class="Function Operator">̂</a> <a id="3419" href="UALib.Algebras.Algebras.html#3419" class="Bound">𝑨</a> <a id="3421" class="Symbol">=</a> <a id="3423" class="Symbol">λ</a> <a id="3425" href="UALib.Algebras.Algebras.html#3425" class="Bound">x</a> <a id="3427" class="Symbol">→</a> <a id="3429" class="Symbol">(</a><a id="3430" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="3432" href="UALib.Algebras.Algebras.html#3419" class="Bound">𝑨</a> <a id="3434" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="3436" href="UALib.Algebras.Algebras.html#3415" class="Bound">f</a><a id="3437" class="Symbol">)</a> <a id="3439" href="UALib.Algebras.Algebras.html#3425" class="Bound">x</a>

</pre>

-------------------------------------

[Back to Table of Contents ↑](UALib.html#detailed-contents)

-------------------------------

{% include UALib.Links.md %}
