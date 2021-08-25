---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---


### <a id="products-of-algebras-and-product-algebras">Products of Algebras and Product Algebras</a>

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="354" class="Symbol">{-#</a> <a id="358" class="Keyword">OPTIONS</a> <a id="366" class="Pragma">--without-K</a> <a id="378" class="Pragma">--exact-split</a> <a id="392" class="Pragma">--safe</a> <a id="399" class="Symbol">#-}</a>


<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a> <a id="440" href="Algebras.Basic.html#1140" class="Generalizable">𝓞</a> <a id="442" class="Symbol">;</a> <a id="444" href="Algebras.Basic.html#1142" class="Generalizable">𝓥</a> <a id="446" class="Symbol">;</a> <a id="448" href="Algebras.Basic.html#3566" class="Function">Signature</a> <a id="458" class="Symbol">)</a>

<a id="461" class="Keyword">module</a> <a id="468" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="486" class="Symbol">{</a><a id="487" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="489" class="Symbol">:</a> <a id="491" href="Algebras.Basic.html#3566" class="Function">Signature</a> <a id="501" href="Algebras.Basic.html#1140" class="Generalizable">𝓞</a> <a id="503" href="Algebras.Basic.html#1142" class="Generalizable">𝓥</a><a id="504" class="Symbol">}</a> <a id="506" class="Keyword">where</a>

<a id="513" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="595" class="Keyword">open</a> <a id="600" class="Keyword">import</a> <a id="607" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="623" class="Keyword">using</a> <a id="629" class="Symbol">(</a> <a id="631" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="636" class="Symbol">;</a> <a id="638" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="642" class="Symbol">;</a> <a id="644" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="650" class="Symbol">)</a> <a id="652" class="Keyword">renaming</a> <a id="661" class="Symbol">(</a> <a id="663" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="667" class="Symbol">to</a> <a id="670" class="Primitive">Type</a> <a id="675" class="Symbol">)</a>
<a id="677" class="Keyword">open</a> <a id="682" class="Keyword">import</a> <a id="689" href="Data.Product.html" class="Module">Data.Product</a>    <a id="705" class="Keyword">using</a> <a id="711" class="Symbol">(</a> <a id="713" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="717" class="Symbol">;</a> <a id="719" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="721" class="Symbol">;</a> <a id="723" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="732" class="Symbol">)</a>
<a id="734" class="Keyword">open</a> <a id="739" class="Keyword">import</a> <a id="746" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="762" class="Keyword">using</a> <a id="768" class="Symbol">(</a> <a id="770" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="775" class="Symbol">;</a> <a id="777" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="781" class="Symbol">;</a> <a id="783" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="787" class="Symbol">)</a>

<a id="790" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="872" class="Keyword">open</a> <a id="877" class="Keyword">import</a> <a id="884" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="907" class="Keyword">using</a> <a id="913" class="Symbol">(</a><a id="914" href="Overture.Preliminaries.html#4931" class="Function Operator">_⁻¹</a><a id="917" class="Symbol">;</a> <a id="919" href="Overture.Preliminaries.html#5330" class="Function">𝑖𝑑</a><a id="921" class="Symbol">;</a> <a id="923" href="Overture.Preliminaries.html#4227" class="Function Operator">∣_∣</a><a id="926" class="Symbol">;</a> <a id="928" href="Overture.Preliminaries.html#4265" class="Function Operator">∥_∥</a><a id="931" class="Symbol">)</a>
<a id="933" class="Keyword">open</a> <a id="938" class="Keyword">import</a> <a id="945" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="968" class="Keyword">using</a> <a id="974" class="Symbol">(</a> <a id="976" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="984" class="Symbol">;</a> <a id="986" href="Algebras.Basic.html#9038" class="Function Operator">_̂_</a> <a id="990" class="Symbol">;</a> <a id="992" href="Algebras.Basic.html#7969" class="Record">algebra</a> <a id="1000" class="Symbol">)</a>

<a id="1003" class="Keyword">private</a> <a id="1011" class="Keyword">variable</a> <a id="1020" href="Algebras.Products.html#1020" class="Generalizable">α</a> <a id="1022" href="Algebras.Products.html#1022" class="Generalizable">β</a> <a id="1024" href="Algebras.Products.html#1024" class="Generalizable">ρ</a> <a id="1026" href="Algebras.Products.html#1026" class="Generalizable">𝓘</a> <a id="1028" class="Symbol">:</a> <a id="1030" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [UniversalAlgebra][] library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1786" href="Algebras.Products.html#1786" class="Function">⨅</a> <a id="1788" class="Symbol">:</a> <a id="1790" class="Symbol">{</a><a id="1791" href="Algebras.Products.html#1791" class="Bound">I</a> <a id="1793" class="Symbol">:</a> <a id="1795" href="Algebras.Products.html#670" class="Primitive">Type</a> <a id="1800" href="Algebras.Products.html#1026" class="Generalizable">𝓘</a> <a id="1802" class="Symbol">}(</a><a id="1804" href="Algebras.Products.html#1804" class="Bound">𝒜</a> <a id="1806" class="Symbol">:</a> <a id="1808" href="Algebras.Products.html#1791" class="Bound">I</a> <a id="1810" class="Symbol">→</a> <a id="1812" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="1820" href="Algebras.Products.html#1020" class="Generalizable">α</a> <a id="1822" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="1824" class="Symbol">)</a> <a id="1826" class="Symbol">→</a> <a id="1828" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="1836" class="Symbol">(</a><a id="1837" href="Algebras.Products.html#1026" class="Generalizable">𝓘</a> <a id="1839" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1841" href="Algebras.Products.html#1020" class="Generalizable">α</a><a id="1842" class="Symbol">)</a> <a id="1844" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="1847" href="Algebras.Products.html#1786" class="Function">⨅</a> <a id="1849" class="Symbol">{</a><a id="1850" class="Argument">I</a> <a id="1852" class="Symbol">=</a> <a id="1854" href="Algebras.Products.html#1854" class="Bound">I</a><a id="1855" class="Symbol">}</a> <a id="1857" href="Algebras.Products.html#1857" class="Bound">𝒜</a> <a id="1859" class="Symbol">=</a> <a id="1861" class="Symbol">(</a> <a id="1863" class="Symbol">∀</a> <a id="1865" class="Symbol">(</a><a id="1866" href="Algebras.Products.html#1866" class="Bound">i</a> <a id="1868" class="Symbol">:</a> <a id="1870" href="Algebras.Products.html#1854" class="Bound">I</a><a id="1871" class="Symbol">)</a> <a id="1873" class="Symbol">→</a> <a id="1875" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a> <a id="1877" href="Algebras.Products.html#1857" class="Bound">𝒜</a> <a id="1879" href="Algebras.Products.html#1866" class="Bound">i</a> <a id="1881" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a> <a id="1883" class="Symbol">)</a> <a id="1885" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1897" class="Comment">-- domain of the product algebra</a>
               <a id="1945" class="Symbol">λ</a> <a id="1947" href="Algebras.Products.html#1947" class="Bound">𝑓</a> <a id="1949" href="Algebras.Products.html#1949" class="Bound">𝑎</a> <a id="1951" href="Algebras.Products.html#1951" class="Bound">i</a> <a id="1953" class="Symbol">→</a> <a id="1955" class="Symbol">(</a><a id="1956" href="Algebras.Products.html#1947" class="Bound">𝑓</a> <a id="1958" href="Algebras.Basic.html#9038" class="Function Operator">̂</a> <a id="1960" href="Algebras.Products.html#1857" class="Bound">𝒜</a> <a id="1962" href="Algebras.Products.html#1951" class="Bound">i</a><a id="1963" class="Symbol">)</a> <a id="1965" class="Symbol">λ</a> <a id="1967" href="Algebras.Products.html#1967" class="Bound">x</a> <a id="1969" class="Symbol">→</a> <a id="1971" href="Algebras.Products.html#1949" class="Bound">𝑎</a> <a id="1973" href="Algebras.Products.html#1967" class="Bound">x</a> <a id="1975" href="Algebras.Products.html#1951" class="Bound">i</a>   <a id="1979" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2472" class="Keyword">open</a> <a id="2477" href="Algebras.Basic.html#7969" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2486" href="Algebras.Products.html#2486" class="Function">⨅&#39;</a> <a id="2489" class="Symbol">:</a> <a id="2491" class="Symbol">{</a><a id="2492" href="Algebras.Products.html#2492" class="Bound">I</a> <a id="2494" class="Symbol">:</a> <a id="2496" href="Algebras.Products.html#670" class="Primitive">Type</a> <a id="2501" href="Algebras.Products.html#1026" class="Generalizable">𝓘</a> <a id="2503" class="Symbol">}(</a><a id="2505" href="Algebras.Products.html#2505" class="Bound">𝒜</a> <a id="2507" class="Symbol">:</a> <a id="2509" href="Algebras.Products.html#2492" class="Bound">I</a> <a id="2511" class="Symbol">→</a> <a id="2513" href="Algebras.Basic.html#7969" class="Record">algebra</a> <a id="2521" href="Algebras.Products.html#1020" class="Generalizable">α</a> <a id="2523" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="2524" class="Symbol">)</a> <a id="2526" class="Symbol">→</a> <a id="2528" href="Algebras.Basic.html#7969" class="Record">algebra</a> <a id="2536" class="Symbol">(</a><a id="2537" href="Algebras.Products.html#1026" class="Generalizable">𝓘</a> <a id="2539" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2541" href="Algebras.Products.html#1020" class="Generalizable">α</a><a id="2542" class="Symbol">)</a> <a id="2544" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="2547" href="Algebras.Products.html#2486" class="Function">⨅&#39;</a> <a id="2550" class="Symbol">{</a><a id="2551" href="Algebras.Products.html#2551" class="Bound">I</a><a id="2552" class="Symbol">}</a> <a id="2554" href="Algebras.Products.html#2554" class="Bound">𝒜</a> <a id="2556" class="Symbol">=</a> <a id="2558" class="Keyword">record</a> <a id="2565" class="Symbol">{</a> <a id="2567" href="Algebras.Basic.html#8067" class="Field">carrier</a> <a id="2575" class="Symbol">=</a> <a id="2577" class="Symbol">∀</a> <a id="2579" href="Algebras.Products.html#2579" class="Bound">i</a> <a id="2581" class="Symbol">→</a> <a id="2583" href="Algebras.Basic.html#8067" class="Field">carrier</a> <a id="2591" class="Symbol">(</a><a id="2592" href="Algebras.Products.html#2554" class="Bound">𝒜</a> <a id="2594" href="Algebras.Products.html#2579" class="Bound">i</a><a id="2595" class="Symbol">)</a> <a id="2597" class="Symbol">;</a>                 <a id="2615" class="Comment">-- domain</a>
                     <a id="2646" href="Algebras.Basic.html#8086" class="Field">opsymbol</a> <a id="2655" class="Symbol">=</a> <a id="2657" class="Symbol">λ</a> <a id="2659" href="Algebras.Products.html#2659" class="Bound">𝑓</a> <a id="2661" href="Algebras.Products.html#2661" class="Bound">𝑎</a> <a id="2663" href="Algebras.Products.html#2663" class="Bound">i</a> <a id="2665" class="Symbol">→</a> <a id="2667" class="Symbol">(</a><a id="2668" href="Algebras.Basic.html#8086" class="Field">opsymbol</a> <a id="2677" class="Symbol">(</a><a id="2678" href="Algebras.Products.html#2554" class="Bound">𝒜</a> <a id="2680" href="Algebras.Products.html#2663" class="Bound">i</a><a id="2681" class="Symbol">))</a> <a id="2684" href="Algebras.Products.html#2659" class="Bound">𝑓</a> <a id="2686" class="Symbol">λ</a> <a id="2688" href="Algebras.Products.html#2688" class="Bound">x</a> <a id="2690" class="Symbol">→</a> <a id="2692" href="Algebras.Products.html#2661" class="Bound">𝑎</a> <a id="2694" href="Algebras.Products.html#2688" class="Bound">x</a> <a id="2696" href="Algebras.Products.html#2663" class="Bound">i</a> <a id="2698" class="Symbol">}</a> <a id="2700" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2982" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="2985" class="Symbol">:</a> <a id="2987" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="2993" class="Symbol">→</a> <a id="2995" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3001" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="3004" href="Algebras.Products.html#3004" class="Bound">α</a> <a id="3006" class="Symbol">=</a> <a id="3008" href="Algebras.Products.html#501" class="Bound">𝓞</a> <a id="3010" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3012" href="Algebras.Products.html#503" class="Bound">𝓥</a> <a id="3014" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3016" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3021" href="Algebras.Products.html#3004" class="Bound">α</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra α 𝑆`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred (Algebra α 𝑆) β`, for some type `β`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not what we want.  For recall that `Pred (Algebra α 𝑆) β` is just an alias for the function type `Algebra α 𝑆 → Type β`, and the semantics of the latter takes `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α 𝑆) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α 𝑆` belongs to `𝒦`.  Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra α 𝑆` belonging to `𝒦`.<sup>[1](Algebras.Product.html#fn1)</sup>

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.<sup>[2](Algebras.Product.html#fn2)</sup>

<pre class="Agda">

<a id="4792" class="Keyword">module</a> <a id="4799" href="Algebras.Products.html#4799" class="Module">_</a> <a id="4801" class="Symbol">{</a><a id="4802" href="Algebras.Products.html#4802" class="Bound">𝒦</a> <a id="4804" class="Symbol">:</a> <a id="4806" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4811" class="Symbol">(</a><a id="4812" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="4820" href="Algebras.Products.html#1020" class="Generalizable">α</a> <a id="4822" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="4823" class="Symbol">)(</a><a id="4825" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="4828" href="Algebras.Products.html#1020" class="Generalizable">α</a><a id="4829" class="Symbol">)}</a> <a id="4832" class="Keyword">where</a>
 <a id="4839" href="Algebras.Products.html#4839" class="Function">ℑ</a> <a id="4841" class="Symbol">:</a> <a id="4843" href="Algebras.Products.html#670" class="Primitive">Type</a> <a id="4848" class="Symbol">(</a><a id="4849" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="4852" href="Algebras.Products.html#4820" class="Bound">α</a><a id="4853" class="Symbol">)</a>
 <a id="4856" href="Algebras.Products.html#4839" class="Function">ℑ</a> <a id="4858" class="Symbol">=</a> <a id="4860" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4863" href="Algebras.Products.html#4863" class="Bound">𝑨</a> <a id="4865" href="Data.Product.html#916" class="Function">∈</a> <a id="4867" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="4875" href="Algebras.Products.html#4820" class="Bound">α</a> <a id="4877" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="4879" href="Data.Product.html#916" class="Function">]</a> <a id="4881" href="Algebras.Products.html#4863" class="Bound">𝑨</a> <a id="4883" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4885" href="Algebras.Products.html#4802" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5234" href="Algebras.Products.html#5234" class="Function">𝔄</a> <a id="5236" class="Symbol">:</a> <a id="5238" href="Algebras.Products.html#4839" class="Function">ℑ</a> <a id="5240" class="Symbol">→</a> <a id="5242" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="5250" href="Algebras.Products.html#4820" class="Bound">α</a> <a id="5252" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5255" href="Algebras.Products.html#5234" class="Function">𝔄</a> <a id="5257" href="Algebras.Products.html#5257" class="Bound">i</a> <a id="5259" class="Symbol">=</a> <a id="5261" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a> <a id="5263" href="Algebras.Products.html#5257" class="Bound">i</a> <a id="5265" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5381" href="Algebras.Products.html#5381" class="Function">class-product</a> <a id="5395" class="Symbol">:</a> <a id="5397" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="5405" class="Symbol">(</a><a id="5406" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="5409" href="Algebras.Products.html#4820" class="Bound">α</a><a id="5410" class="Symbol">)</a> <a id="5412" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5415" href="Algebras.Products.html#5381" class="Function">class-product</a> <a id="5429" class="Symbol">=</a> <a id="5431" href="Algebras.Products.html#1786" class="Function">⨅</a> <a id="5433" href="Algebras.Products.html#5234" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

--------------------------------------------

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
