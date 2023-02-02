---
layout: default
title : "Base.Algebras.Products module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

### <a id="products-of-algebras-and-product-algebras">Products of Algebras and Product Algebras</a>

This is the [Base.Algebras.Products][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="365" class="Symbol">{-#</a> <a id="369" class="Keyword">OPTIONS</a> <a id="377" class="Pragma">--without-K</a> <a id="389" class="Pragma">--exact-split</a> <a id="403" class="Pragma">--safe</a> <a id="410" class="Symbol">#-}</a>

<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="Overture.html" class="Module">Overture</a> <a id="436" class="Keyword">using</a> <a id="442" class="Symbol">(</a> <a id="444" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="446" class="Symbol">;</a> <a id="448" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="450" class="Symbol">;</a> <a id="452" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="462" class="Symbol">)</a>

<a id="465" class="Keyword">module</a> <a id="472" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a> <a id="495" class="Symbol">{</a><a id="496" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a> <a id="498" class="Symbol">:</a> <a id="500" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="510" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="512" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="513" class="Symbol">}</a> <a id="515" class="Keyword">where</a>

<a id="522" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="604" class="Keyword">open</a> <a id="609" class="Keyword">import</a> <a id="616" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="632" class="Keyword">using</a> <a id="638" class="Symbol">()</a> <a id="641" class="Keyword">renaming</a> <a id="650" class="Symbol">(</a> <a id="652" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="656" class="Symbol">to</a> <a id="659" class="Primitive">Type</a> <a id="664" class="Symbol">)</a>
<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="Data.Product.html" class="Module">Data.Product</a>    <a id="694" class="Keyword">using</a> <a id="700" class="Symbol">(</a> <a id="702" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="706" class="Symbol">;</a> <a id="708" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="710" class="Symbol">;</a> <a id="712" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="721" class="Symbol">)</a>
<a id="723" class="Keyword">open</a> <a id="728" class="Keyword">import</a> <a id="735" href="Level.html" class="Module">Level</a>           <a id="751" class="Keyword">using</a> <a id="757" class="Symbol">(</a> <a id="759" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="765" class="Symbol">;</a> <a id="767" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="771" class="Symbol">;</a> <a id="773" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="777" class="Symbol">)</a>
<a id="779" class="Keyword">open</a> <a id="784" class="Keyword">import</a> <a id="791" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="807" class="Keyword">using</a> <a id="813" class="Symbol">(</a> <a id="815" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="820" class="Symbol">;</a> <a id="822" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="826" class="Symbol">;</a> <a id="828" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="832" class="Symbol">)</a>

<a id="835" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="Overture.html" class="Module">Overture</a>                     <a id="958" class="Keyword">using</a> <a id="964" class="Symbol">(</a><a id="965" href="Overture.Basic.html#4920" class="Function Operator">_⁻¹</a><a id="968" class="Symbol">;</a> <a id="970" href="Overture.Basic.html#5319" class="Function">𝑖𝑑</a><a id="972" class="Symbol">;</a> <a id="974" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a><a id="977" class="Symbol">;</a> <a id="979" href="Overture.Basic.html#4364" class="Function Operator">∥_∥</a><a id="982" class="Symbol">)</a>
<a id="984" class="Keyword">open</a> <a id="989" class="Keyword">import</a> <a id="996" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="1016" class="Symbol">{</a><a id="1017" class="Argument">𝑆</a> <a id="1019" class="Symbol">=</a> <a id="1021" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a><a id="1022" class="Symbol">}</a>  <a id="1025" class="Keyword">using</a> <a id="1031" class="Symbol">(</a> <a id="1033" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="1041" class="Symbol">;</a> <a id="1043" href="Base.Algebras.Basic.html#5783" class="Function Operator">_̂_</a> <a id="1047" class="Symbol">;</a> <a id="1049" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="1057" class="Symbol">)</a>

<a id="1060" class="Keyword">private</a> <a id="1068" class="Keyword">variable</a> <a id="1077" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="1079" href="Base.Algebras.Products.html#1079" class="Generalizable">β</a> <a id="1081" href="Base.Algebras.Products.html#1081" class="Generalizable">ρ</a> <a id="1083" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1085" class="Symbol">:</a> <a id="1087" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the
[agda-algebras](https://github.com/ualib/agda-algebras) library will assume a
fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I :
Type 𝓘` and a family `𝒜 : I → Algebra α`, the *product* `⨅ 𝒜` is the algebra
whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the
algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary
operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such
that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 :=
(i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product
of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1923" href="Base.Algebras.Products.html#1923" class="Function">⨅</a> <a id="1925" class="Symbol">:</a> <a id="1927" class="Symbol">{</a><a id="1928" href="Base.Algebras.Products.html#1928" class="Bound">I</a> <a id="1930" class="Symbol">:</a> <a id="1932" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="1937" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1939" class="Symbol">}(</a><a id="1941" href="Base.Algebras.Products.html#1941" class="Bound">𝒜</a> <a id="1943" class="Symbol">:</a> <a id="1945" href="Base.Algebras.Products.html#1928" class="Bound">I</a> <a id="1947" class="Symbol">→</a> <a id="1949" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="1957" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="1959" class="Symbol">)</a> <a id="1961" class="Symbol">→</a> <a id="1963" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="1971" class="Symbol">(</a><a id="1972" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1974" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1976" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="1977" class="Symbol">)</a>

<a id="1980" href="Base.Algebras.Products.html#1923" class="Function">⨅</a> <a id="1982" class="Symbol">{</a><a id="1983" class="Argument">I</a> <a id="1985" class="Symbol">=</a> <a id="1987" href="Base.Algebras.Products.html#1987" class="Bound">I</a><a id="1988" class="Symbol">}</a> <a id="1990" href="Base.Algebras.Products.html#1990" class="Bound">𝒜</a> <a id="1992" class="Symbol">=</a>  <a id="1995" class="Symbol">(</a> <a id="1997" class="Symbol">∀</a> <a id="1999" class="Symbol">(</a><a id="2000" href="Base.Algebras.Products.html#2000" class="Bound">i</a> <a id="2002" class="Symbol">:</a> <a id="2004" href="Base.Algebras.Products.html#1987" class="Bound">I</a><a id="2005" class="Symbol">)</a> <a id="2007" class="Symbol">→</a> <a id="2009" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="2011" href="Base.Algebras.Products.html#1990" class="Bound">𝒜</a> <a id="2013" href="Base.Algebras.Products.html#2000" class="Bound">i</a> <a id="2015" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="2017" class="Symbol">)</a> <a id="2019" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>        <a id="2028" class="Comment">-- domain of the product algebra</a>
                <a id="2077" class="Symbol">λ</a> <a id="2079" href="Base.Algebras.Products.html#2079" class="Bound">𝑓</a> <a id="2081" href="Base.Algebras.Products.html#2081" class="Bound">𝑎</a> <a id="2083" href="Base.Algebras.Products.html#2083" class="Bound">i</a> <a id="2085" class="Symbol">→</a> <a id="2087" class="Symbol">(</a><a id="2088" href="Base.Algebras.Products.html#2079" class="Bound">𝑓</a> <a id="2090" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="2092" href="Base.Algebras.Products.html#1990" class="Bound">𝒜</a> <a id="2094" href="Base.Algebras.Products.html#2083" class="Bound">i</a><a id="2095" class="Symbol">)</a> <a id="2097" class="Symbol">λ</a> <a id="2099" href="Base.Algebras.Products.html#2099" class="Bound">x</a> <a id="2101" class="Symbol">→</a> <a id="2103" href="Base.Algebras.Products.html#2081" class="Bound">𝑎</a> <a id="2105" href="Base.Algebras.Products.html#2099" class="Bound">x</a> <a id="2107" href="Base.Algebras.Products.html#2083" class="Bound">i</a>  <a id="2110" class="Comment">-- basic operations of the product algebra</a>

</pre>

The type just defined is the one that will be used throughout the
[agda-algebras](https://github.com/ualib/agda-algebras) library whenever the
product of an indexed collection of algebras (of type `Algebra`) is required.
However, for the sake of completeness, here is how one could define a type
representing the product of algebras inhabiting the record type `algebra`. 

<pre class="Agda">

<a id="2553" class="Keyword">open</a> <a id="2558" href="Base.Algebras.Basic.html#4789" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2567" href="Base.Algebras.Products.html#2567" class="Function">⨅&#39;</a> <a id="2570" class="Symbol">:</a> <a id="2572" class="Symbol">{</a><a id="2573" href="Base.Algebras.Products.html#2573" class="Bound">I</a> <a id="2575" class="Symbol">:</a> <a id="2577" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="2582" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="2584" class="Symbol">}(</a><a id="2586" href="Base.Algebras.Products.html#2586" class="Bound">𝒜</a> <a id="2588" class="Symbol">:</a> <a id="2590" href="Base.Algebras.Products.html#2573" class="Bound">I</a> <a id="2592" class="Symbol">→</a> <a id="2594" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="2602" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="2603" class="Symbol">)</a> <a id="2605" class="Symbol">→</a> <a id="2607" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="2615" class="Symbol">(</a><a id="2616" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="2618" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2620" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="2621" class="Symbol">)</a>
<a id="2623" href="Base.Algebras.Products.html#2567" class="Function">⨅&#39;</a> <a id="2626" class="Symbol">{</a><a id="2627" href="Base.Algebras.Products.html#2627" class="Bound">I</a><a id="2628" class="Symbol">}</a> <a id="2630" href="Base.Algebras.Products.html#2630" class="Bound">𝒜</a> <a id="2632" class="Symbol">=</a> <a id="2634" class="Keyword">record</a>  <a id="2642" class="Symbol">{</a> <a id="2644" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a> <a id="2652" class="Symbol">=</a> <a id="2654" class="Symbol">∀</a> <a id="2656" href="Base.Algebras.Products.html#2656" class="Bound">i</a> <a id="2658" class="Symbol">→</a> <a id="2660" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a> <a id="2668" class="Symbol">(</a><a id="2669" href="Base.Algebras.Products.html#2630" class="Bound">𝒜</a> <a id="2671" href="Base.Algebras.Products.html#2656" class="Bound">i</a><a id="2672" class="Symbol">)</a>                         <a id="2698" class="Comment">-- domain</a>
                    <a id="2728" class="Symbol">;</a> <a id="2730" href="Base.Algebras.Basic.html#4885" class="Field">opsymbol</a> <a id="2739" class="Symbol">=</a> <a id="2741" class="Symbol">λ</a> <a id="2743" href="Base.Algebras.Products.html#2743" class="Bound">𝑓</a> <a id="2745" href="Base.Algebras.Products.html#2745" class="Bound">𝑎</a> <a id="2747" href="Base.Algebras.Products.html#2747" class="Bound">i</a> <a id="2749" class="Symbol">→</a> <a id="2751" class="Symbol">(</a><a id="2752" href="Base.Algebras.Basic.html#4885" class="Field">opsymbol</a> <a id="2761" class="Symbol">(</a><a id="2762" href="Base.Algebras.Products.html#2630" class="Bound">𝒜</a> <a id="2764" href="Base.Algebras.Products.html#2747" class="Bound">i</a><a id="2765" class="Symbol">))</a> <a id="2768" href="Base.Algebras.Products.html#2743" class="Bound">𝑓</a> <a id="2770" class="Symbol">λ</a> <a id="2772" href="Base.Algebras.Products.html#2772" class="Bound">x</a> <a id="2774" class="Symbol">→</a> <a id="2776" href="Base.Algebras.Products.html#2745" class="Bound">𝑎</a> <a id="2778" href="Base.Algebras.Products.html#2772" class="Bound">x</a> <a id="2780" href="Base.Algebras.Products.html#2747" class="Bound">i</a> <a id="2782" class="Symbol">}</a>  <a id="2785" class="Comment">-- basic operations</a>
</pre>

**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α` has
type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the
[agda-algebras](https://github.com/ualib/agda-algebras) library that we define
the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3097" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="3100" class="Symbol">:</a> <a id="3102" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3108" class="Symbol">→</a> <a id="3110" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3116" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="3119" href="Base.Algebras.Products.html#3119" class="Bound">α</a> <a id="3121" class="Symbol">=</a> <a id="3123" href="Base.Algebras.Products.html#510" class="Bound">𝓞</a> <a id="3125" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3127" href="Base.Algebras.Products.html#512" class="Bound">𝓥</a> <a id="3129" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3131" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3135" href="Base.Algebras.Products.html#3119" class="Bound">α</a>
</pre>


### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type
`Algebra α`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred
(Algebra α) β`, for some type `β`. Later we will formally state and prove that
the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of
subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns
out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary
(nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not
what we want.  For recall that `Pred (Algebra α) β` is just an alias for the
function type `Algebra α → Type β`, and the semantics of the latter takes `𝒦 𝑨`
(and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α` belongs to `𝒦`.
Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that
maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of
type `(Algebra α) → Type β`) and the type `Algebra α` seems rather nebulous in
that there is no natural indexing class with which to "enumerate" all inhabitants
of `Algebra α` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least
heuristically that is how one can view the type `ℑ` that we now define.

<pre class="Agda">

<a id="4800" class="Keyword">module</a> <a id="4807" href="Base.Algebras.Products.html#4807" class="Module">_</a> <a id="4809" class="Symbol">{</a><a id="4810" href="Base.Algebras.Products.html#4810" class="Bound">𝒦</a> <a id="4812" class="Symbol">:</a> <a id="4814" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4819" class="Symbol">(</a><a id="4820" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="4828" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="4829" class="Symbol">)(</a><a id="4831" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="4834" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="4835" class="Symbol">)}</a> <a id="4838" class="Keyword">where</a>
 <a id="4845" href="Base.Algebras.Products.html#4845" class="Function">ℑ</a> <a id="4847" class="Symbol">:</a> <a id="4849" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="4854" class="Symbol">(</a><a id="4855" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="4858" href="Base.Algebras.Products.html#4828" class="Bound">α</a><a id="4859" class="Symbol">)</a>
 <a id="4862" href="Base.Algebras.Products.html#4845" class="Function">ℑ</a> <a id="4864" class="Symbol">=</a> <a id="4866" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4869" href="Base.Algebras.Products.html#4869" class="Bound">𝑨</a> <a id="4871" href="Data.Product.html#916" class="Function">∈</a> <a id="4873" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="4881" href="Base.Algebras.Products.html#4828" class="Bound">α</a> <a id="4883" href="Data.Product.html#916" class="Function">]</a> <a id="4885" href="Base.Algebras.Products.html#4869" class="Bound">𝑨</a> <a id="4887" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4889" href="Base.Algebras.Products.html#4810" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index
`i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where
`𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function
mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5238" href="Base.Algebras.Products.html#5238" class="Function">𝔄</a> <a id="5240" class="Symbol">:</a> <a id="5242" href="Base.Algebras.Products.html#4845" class="Function">ℑ</a> <a id="5244" class="Symbol">→</a> <a id="5246" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="5254" href="Base.Algebras.Products.html#4828" class="Bound">α</a>
 <a id="5257" href="Base.Algebras.Products.html#5238" class="Function">𝔄</a> <a id="5259" href="Base.Algebras.Products.html#5259" class="Bound">i</a> <a id="5261" class="Symbol">=</a> <a id="5263" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5265" href="Base.Algebras.Products.html#5259" class="Bound">i</a> <a id="5267" href="Overture.Basic.html#4326" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of
𝒦.

<pre class="Agda">

 <a id="5383" href="Base.Algebras.Products.html#5383" class="Function">class-product</a> <a id="5397" class="Symbol">:</a> <a id="5399" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="5407" class="Symbol">(</a><a id="5408" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="5411" href="Base.Algebras.Products.html#4828" class="Bound">α</a><a id="5412" class="Symbol">)</a>
 <a id="5415" href="Base.Algebras.Products.html#5383" class="Function">class-product</a> <a id="5429" class="Symbol">=</a> <a id="5431" href="Base.Algebras.Products.html#1923" class="Function">⨅</a> <a id="5433" href="Base.Algebras.Products.html#5238" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we
can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅
𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Base.Algebras.Basic](Base.Algebras.Basic.html)</span>
<span style="float:right;">[Base.Algebras.Congruences →](Base.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
