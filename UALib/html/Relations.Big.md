---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Big Relations</a>

This section presents the [UALib.Relations.Big][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `GenRel` to be the type `(I → A) → 𝓦 ̇` and we will call `GenRel` the type of **general relations**.  After that, we define a type that represents relations even more generally.  Specifically, if we are given types `A`, `B`, `C`, etc., we want to represent relations from A to B to C to ….  We define such **dependent relations** [below](Relations.General.html#dependent-relations).

<pre class="Agda">

<a id="1406" class="Symbol">{-#</a> <a id="1410" class="Keyword">OPTIONS</a> <a id="1418" class="Pragma">--without-K</a> <a id="1430" class="Pragma">--exact-split</a> <a id="1444" class="Pragma">--safe</a> <a id="1451" class="Symbol">#-}</a>

<a id="1456" class="Keyword">module</a> <a id="1463" href="Relations.Big.html" class="Module">Relations.Big</a> <a id="1477" class="Keyword">where</a>

<a id="1484" class="Keyword">open</a> <a id="1489" class="Keyword">import</a> <a id="1496" href="Relations.Small.html" class="Module">Relations.Small</a> <a id="1512" class="Keyword">public</a>

</pre>

#### <a id="general-relations">General relations</a>

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="GenRel"></a><a id="2119" href="Relations.Big.html#2119" class="Function">GenRel</a> <a id="2126" class="Symbol">:</a> <a id="2128" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2130" href="Universes.html#403" class="Function Operator">̇</a> <a id="2132" class="Symbol">→</a> <a id="2134" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2136" href="Universes.html#403" class="Function Operator">̇</a> <a id="2138" class="Symbol">→</a> <a id="2140" class="Symbol">(</a><a id="2141" href="Relations.Big.html#2141" class="Bound">𝓦</a> <a id="2143" class="Symbol">:</a> <a id="2145" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2153" class="Symbol">)</a> <a id="2155" class="Symbol">→</a> <a id="2157" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2159" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2161" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2163" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2165" href="Relations.Big.html#2141" class="Bound">𝓦</a> <a id="2167" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="2169" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2171" href="Relations.Big.html#2119" class="Function">GenRel</a> <a id="2178" href="Relations.Big.html#2178" class="Bound">I</a> <a id="2180" href="Relations.Big.html#2180" class="Bound">A</a> <a id="2182" href="Relations.Big.html#2182" class="Bound">𝓦</a> <a id="2184" class="Symbol">=</a> <a id="2186" class="Symbol">(</a><a id="2187" href="Relations.Big.html#2178" class="Bound">I</a> <a id="2189" class="Symbol">→</a> <a id="2191" href="Relations.Big.html#2180" class="Bound">A</a><a id="2192" class="Symbol">)</a> <a id="2194" class="Symbol">→</a> <a id="2196" href="Relations.Big.html#2182" class="Bound">𝓦</a> <a id="2198" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with general relations.

<pre class="Agda">

<a id="2448" class="Keyword">module</a> <a id="2455" href="Relations.Big.html#2455" class="Module">_</a> <a id="2457" class="Symbol">{</a><a id="2458" href="Relations.Big.html#2458" class="Bound">𝓤</a> <a id="2460" href="Relations.Big.html#2460" class="Bound">𝓥</a> <a id="2462" href="Relations.Big.html#2462" class="Bound">𝓦</a> <a id="2464" class="Symbol">:</a> <a id="2466" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2474" class="Symbol">}</a> <a id="2476" class="Symbol">{</a><a id="2477" href="Relations.Big.html#2477" class="Bound">I</a> <a id="2479" href="Relations.Big.html#2479" class="Bound">J</a> <a id="2481" class="Symbol">:</a> <a id="2483" href="Relations.Big.html#2460" class="Bound">𝓥</a> <a id="2485" href="Universes.html#403" class="Function Operator">̇</a><a id="2486" class="Symbol">}</a> <a id="2488" class="Symbol">{</a><a id="2489" href="Relations.Big.html#2489" class="Bound">A</a> <a id="2491" class="Symbol">:</a> <a id="2493" href="Relations.Big.html#2458" class="Bound">𝓤</a> <a id="2495" href="Universes.html#403" class="Function Operator">̇</a><a id="2496" class="Symbol">}</a> <a id="2498" class="Keyword">where</a>

 <a id="2506" href="Relations.Big.html#2506" class="Function">lift-gen-rel</a> <a id="2519" class="Symbol">:</a> <a id="2521" href="Relations.Big.html#2119" class="Function">GenRel</a> <a id="2528" href="Relations.Big.html#2477" class="Bound">I</a> <a id="2530" href="Relations.Big.html#2489" class="Bound">A</a> <a id="2532" href="Relations.Big.html#2462" class="Bound">𝓦</a> <a id="2534" class="Symbol">→</a> <a id="2536" class="Symbol">(</a><a id="2537" href="Relations.Big.html#2477" class="Bound">I</a> <a id="2539" class="Symbol">→</a> <a id="2541" class="Symbol">(</a><a id="2542" href="Relations.Big.html#2479" class="Bound">J</a> <a id="2544" class="Symbol">→</a> <a id="2546" href="Relations.Big.html#2489" class="Bound">A</a><a id="2547" class="Symbol">))</a> <a id="2550" class="Symbol">→</a> <a id="2552" href="Relations.Big.html#2460" class="Bound">𝓥</a> <a id="2554" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2556" href="Relations.Big.html#2462" class="Bound">𝓦</a> <a id="2558" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2561" href="Relations.Big.html#2506" class="Function">lift-gen-rel</a> <a id="2574" href="Relations.Big.html#2574" class="Bound">R</a> <a id="2576" href="Relations.Big.html#2576" class="Bound">𝕒</a> <a id="2578" class="Symbol">=</a> <a id="2580" class="Symbol">∀</a> <a id="2582" class="Symbol">(</a><a id="2583" href="Relations.Big.html#2583" class="Bound">j</a> <a id="2585" class="Symbol">:</a> <a id="2587" href="Relations.Big.html#2479" class="Bound">J</a><a id="2588" class="Symbol">)</a> <a id="2590" class="Symbol">→</a> <a id="2592" href="Relations.Big.html#2574" class="Bound">R</a> <a id="2594" class="Symbol">(λ</a> <a id="2597" href="Relations.Big.html#2597" class="Bound">i</a> <a id="2599" class="Symbol">→</a> <a id="2601" class="Symbol">(</a><a id="2602" href="Relations.Big.html#2576" class="Bound">𝕒</a> <a id="2604" href="Relations.Big.html#2597" class="Bound">i</a><a id="2605" class="Symbol">)</a> <a id="2607" href="Relations.Big.html#2583" class="Bound">j</a><a id="2608" class="Symbol">)</a>

 <a id="2612" href="Relations.Big.html#2612" class="Function">gen-compatible-fun</a> <a id="2631" class="Symbol">:</a> <a id="2633" class="Symbol">(</a><a id="2634" href="Relations.Big.html#2477" class="Bound">I</a> <a id="2636" class="Symbol">→</a> <a id="2638" class="Symbol">(</a><a id="2639" href="Relations.Big.html#2479" class="Bound">J</a> <a id="2641" class="Symbol">→</a> <a id="2643" href="Relations.Big.html#2489" class="Bound">A</a><a id="2644" class="Symbol">)</a> <a id="2646" class="Symbol">→</a> <a id="2648" href="Relations.Big.html#2489" class="Bound">A</a><a id="2649" class="Symbol">)</a> <a id="2651" class="Symbol">→</a> <a id="2653" href="Relations.Big.html#2119" class="Function">GenRel</a> <a id="2660" href="Relations.Big.html#2477" class="Bound">I</a> <a id="2662" href="Relations.Big.html#2489" class="Bound">A</a> <a id="2664" href="Relations.Big.html#2462" class="Bound">𝓦</a> <a id="2666" class="Symbol">→</a> <a id="2668" href="Relations.Big.html#2460" class="Bound">𝓥</a> <a id="2670" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2672" href="Relations.Big.html#2458" class="Bound">𝓤</a> <a id="2674" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2676" href="Relations.Big.html#2462" class="Bound">𝓦</a> <a id="2678" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2681" href="Relations.Big.html#2612" class="Function">gen-compatible-fun</a> <a id="2700" href="Relations.Big.html#2700" class="Bound">𝕗</a> <a id="2702" href="Relations.Big.html#2702" class="Bound">R</a>  <a id="2705" class="Symbol">=</a> <a id="2707" class="Symbol">∀</a> <a id="2709" href="Relations.Big.html#2709" class="Bound">𝕒</a> <a id="2711" class="Symbol">→</a> <a id="2713" class="Symbol">(</a><a id="2714" href="Relations.Big.html#2506" class="Function">lift-gen-rel</a> <a id="2727" href="Relations.Big.html#2702" class="Bound">R</a><a id="2728" class="Symbol">)</a> <a id="2730" href="Relations.Big.html#2709" class="Bound">𝕒</a> <a id="2732" class="Symbol">→</a> <a id="2734" href="Relations.Big.html#2702" class="Bound">R</a> <a id="2736" class="Symbol">(λ</a> <a id="2739" href="Relations.Big.html#2739" class="Bound">i</a> <a id="2741" class="Symbol">→</a> <a id="2743" class="Symbol">(</a><a id="2744" href="Relations.Big.html#2700" class="Bound">𝕗</a> <a id="2746" href="Relations.Big.html#2739" class="Bound">i</a><a id="2747" class="Symbol">)</a> <a id="2749" class="Symbol">(</a><a id="2750" href="Relations.Big.html#2709" class="Bound">𝕒</a> <a id="2752" href="Relations.Big.html#2739" class="Bound">i</a><a id="2753" class="Symbol">))</a>

</pre>

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a general relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each general relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝕒 i 1      𝕒 k 1
𝕒 i 2      𝕒 k 2
𝕒 i 3      𝕒 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝕒 i J      𝕒 k J
```

Now `lift-gen-rel R 𝕒` is defined by `∀ j → R (λ i → (𝕒 i) j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `gen-compatible-fun`.  Here, `𝕗 : I → (J → A) → A` denotes an `I`-tuple of `J`-ary operations on `A`.  That is, for each `i : I`, the function `𝕗 i` takes a `J`-tuple `𝕒 i : J → A` and evaluates to some `(𝕗 i) (𝕒 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝕒 : I → (J → A)` is precisely the type on which the relation `lift-gen-rel R` is defined.


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` may not even be enumerable).

<pre class="Agda">

<a id="DepRel"></a><a id="5318" href="Relations.Big.html#5318" class="Function">DepRel</a> <a id="5325" class="Symbol">:</a> <a id="5327" class="Symbol">(</a><a id="5328" href="Relations.Big.html#5328" class="Bound">I</a> <a id="5330" class="Symbol">:</a> <a id="5332" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="5334" href="Universes.html#403" class="Function Operator">̇</a><a id="5335" class="Symbol">)(</a><a id="5337" href="Relations.Big.html#5337" class="Bound">A</a> <a id="5339" class="Symbol">:</a> <a id="5341" href="Relations.Big.html#5328" class="Bound">I</a> <a id="5343" class="Symbol">→</a> <a id="5345" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5347" href="Universes.html#403" class="Function Operator">̇</a><a id="5348" class="Symbol">)(</a><a id="5350" href="Relations.Big.html#5350" class="Bound">𝓦</a> <a id="5352" class="Symbol">:</a> <a id="5354" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5362" class="Symbol">)</a> <a id="5364" class="Symbol">→</a> <a id="5366" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="5368" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5370" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5372" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5374" href="Relations.Big.html#5350" class="Bound">𝓦</a> <a id="5376" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="5378" href="Universes.html#403" class="Function Operator">̇</a>
<a id="5380" href="Relations.Big.html#5318" class="Function">DepRel</a> <a id="5387" href="Relations.Big.html#5387" class="Bound">I</a> <a id="5389" href="Relations.Big.html#5389" class="Bound">A</a> <a id="5391" href="Relations.Big.html#5391" class="Bound">𝓦</a> <a id="5393" class="Symbol">=</a> <a id="5395" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5397" href="Relations.Big.html#5389" class="Bound">A</a> <a id="5399" class="Symbol">→</a> <a id="5401" href="Relations.Big.html#5391" class="Bound">𝓦</a> <a id="5403" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

Above we made peace with lifts of general relations and what it means for such relations to be compatibile with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="5900" class="Keyword">module</a> <a id="5907" href="Relations.Big.html#5907" class="Module">_</a> <a id="5909" class="Symbol">{</a><a id="5910" href="Relations.Big.html#5910" class="Bound">𝓤</a> <a id="5912" href="Relations.Big.html#5912" class="Bound">𝓥</a> <a id="5914" href="Relations.Big.html#5914" class="Bound">𝓦</a> <a id="5916" class="Symbol">:</a> <a id="5918" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5926" class="Symbol">}</a> <a id="5928" class="Symbol">{</a><a id="5929" href="Relations.Big.html#5929" class="Bound">I</a> <a id="5931" href="Relations.Big.html#5931" class="Bound">J</a> <a id="5933" class="Symbol">:</a> <a id="5935" href="Relations.Big.html#5912" class="Bound">𝓥</a> <a id="5937" href="Universes.html#403" class="Function Operator">̇</a><a id="5938" class="Symbol">}</a> <a id="5940" class="Symbol">{</a><a id="5941" href="Relations.Big.html#5941" class="Bound">A</a> <a id="5943" class="Symbol">:</a> <a id="5945" href="Relations.Big.html#5929" class="Bound">I</a> <a id="5947" class="Symbol">→</a> <a id="5949" href="Relations.Big.html#5910" class="Bound">𝓤</a> <a id="5951" href="Universes.html#403" class="Function Operator">̇</a><a id="5952" class="Symbol">}</a> <a id="5954" class="Keyword">where</a>

 <a id="5962" href="Relations.Big.html#5962" class="Function">lift-dep-rel</a> <a id="5975" class="Symbol">:</a> <a id="5977" href="Relations.Big.html#5318" class="Function">DepRel</a> <a id="5984" href="Relations.Big.html#5929" class="Bound">I</a> <a id="5986" href="Relations.Big.html#5941" class="Bound">A</a> <a id="5988" href="Relations.Big.html#5914" class="Bound">𝓦</a> <a id="5990" class="Symbol">→</a> <a id="5992" class="Symbol">((</a><a id="5994" href="Relations.Big.html#5994" class="Bound">i</a> <a id="5996" class="Symbol">:</a> <a id="5998" href="Relations.Big.html#5929" class="Bound">I</a><a id="5999" class="Symbol">)</a> <a id="6001" class="Symbol">→</a> <a id="6003" class="Symbol">(</a><a id="6004" href="Relations.Big.html#5931" class="Bound">J</a> <a id="6006" class="Symbol">→</a> <a id="6008" class="Symbol">(</a><a id="6009" href="Relations.Big.html#5941" class="Bound">A</a> <a id="6011" href="Relations.Big.html#5994" class="Bound">i</a><a id="6012" class="Symbol">)))</a> <a id="6016" class="Symbol">→</a> <a id="6018" href="Relations.Big.html#5912" class="Bound">𝓥</a> <a id="6020" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6022" href="Relations.Big.html#5914" class="Bound">𝓦</a> <a id="6024" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6027" href="Relations.Big.html#5962" class="Function">lift-dep-rel</a> <a id="6040" href="Relations.Big.html#6040" class="Bound">R</a> <a id="6042" href="Relations.Big.html#6042" class="Bound">𝕒</a> <a id="6044" class="Symbol">=</a> <a id="6046" class="Symbol">∀</a> <a id="6048" class="Symbol">(</a><a id="6049" href="Relations.Big.html#6049" class="Bound">j</a> <a id="6051" class="Symbol">:</a> <a id="6053" href="Relations.Big.html#5931" class="Bound">J</a><a id="6054" class="Symbol">)</a> <a id="6056" class="Symbol">→</a> <a id="6058" href="Relations.Big.html#6040" class="Bound">R</a> <a id="6060" class="Symbol">(λ</a> <a id="6063" href="Relations.Big.html#6063" class="Bound">i</a> <a id="6065" class="Symbol">→</a> <a id="6067" class="Symbol">(</a><a id="6068" href="Relations.Big.html#6042" class="Bound">𝕒</a> <a id="6070" href="Relations.Big.html#6063" class="Bound">i</a><a id="6071" class="Symbol">)</a> <a id="6073" href="Relations.Big.html#6049" class="Bound">j</a><a id="6074" class="Symbol">)</a>

 <a id="6078" href="Relations.Big.html#6078" class="Function">dep-compatible-fun</a> <a id="6097" class="Symbol">:</a> <a id="6099" class="Symbol">((</a><a id="6101" href="Relations.Big.html#6101" class="Bound">i</a> <a id="6103" class="Symbol">:</a> <a id="6105" href="Relations.Big.html#5929" class="Bound">I</a><a id="6106" class="Symbol">)</a> <a id="6108" class="Symbol">→</a> <a id="6110" class="Symbol">(</a><a id="6111" href="Relations.Big.html#5931" class="Bound">J</a> <a id="6113" class="Symbol">→</a> <a id="6115" class="Symbol">(</a><a id="6116" href="Relations.Big.html#5941" class="Bound">A</a> <a id="6118" href="Relations.Big.html#6101" class="Bound">i</a><a id="6119" class="Symbol">))</a> <a id="6122" class="Symbol">→</a> <a id="6124" class="Symbol">(</a><a id="6125" href="Relations.Big.html#5941" class="Bound">A</a> <a id="6127" href="Relations.Big.html#6101" class="Bound">i</a><a id="6128" class="Symbol">))</a> <a id="6131" class="Symbol">→</a> <a id="6133" href="Relations.Big.html#5318" class="Function">DepRel</a> <a id="6140" href="Relations.Big.html#5929" class="Bound">I</a> <a id="6142" href="Relations.Big.html#5941" class="Bound">A</a> <a id="6144" href="Relations.Big.html#5914" class="Bound">𝓦</a> <a id="6146" class="Symbol">→</a> <a id="6148" href="Relations.Big.html#5912" class="Bound">𝓥</a> <a id="6150" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6152" href="Relations.Big.html#5910" class="Bound">𝓤</a> <a id="6154" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6156" href="Relations.Big.html#5914" class="Bound">𝓦</a> <a id="6158" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6161" href="Relations.Big.html#6078" class="Function">dep-compatible-fun</a> <a id="6180" href="Relations.Big.html#6180" class="Bound">𝕗</a> <a id="6182" href="Relations.Big.html#6182" class="Bound">R</a>  <a id="6185" class="Symbol">=</a> <a id="6187" class="Symbol">∀</a> <a id="6189" href="Relations.Big.html#6189" class="Bound">𝕒</a> <a id="6191" class="Symbol">→</a> <a id="6193" class="Symbol">(</a><a id="6194" href="Relations.Big.html#5962" class="Function">lift-dep-rel</a> <a id="6207" href="Relations.Big.html#6182" class="Bound">R</a><a id="6208" class="Symbol">)</a> <a id="6210" href="Relations.Big.html#6189" class="Bound">𝕒</a> <a id="6212" class="Symbol">→</a> <a id="6214" href="Relations.Big.html#6182" class="Bound">R</a> <a id="6216" class="Symbol">(λ</a> <a id="6219" href="Relations.Big.html#6219" class="Bound">i</a> <a id="6221" class="Symbol">→</a> <a id="6223" class="Symbol">(</a><a id="6224" href="Relations.Big.html#6180" class="Bound">𝕗</a> <a id="6226" href="Relations.Big.html#6219" class="Bound">i</a><a id="6227" class="Symbol">)(</a><a id="6229" href="Relations.Big.html#6189" class="Bound">𝕒</a> <a id="6231" href="Relations.Big.html#6219" class="Bound">i</a><a id="6232" class="Symbol">))</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → (J → (A i))`.


--------------------------------------

[← Relations.Small](Relations.Small.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
