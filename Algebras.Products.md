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


<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a> <a id="440" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="442" class="Symbol">;</a> <a id="444" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a> <a id="446" class="Symbol">;</a> <a id="448" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="458" class="Symbol">)</a>

<a id="461" class="Keyword">module</a> <a id="468" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="486" class="Symbol">{</a><a id="487" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="489" class="Symbol">:</a> <a id="491" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="501" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="503" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a><a id="504" class="Symbol">}</a> <a id="506" class="Keyword">where</a>

<a id="513" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------------------------------</a>
<a id="605" class="Keyword">open</a> <a id="610" class="Keyword">import</a> <a id="617" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="633" class="Keyword">using</a> <a id="639" class="Symbol">(</a> <a id="641" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="646" class="Symbol">;</a> <a id="648" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="652" class="Symbol">;</a> <a id="654" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="660" class="Symbol">)</a> <a id="662" class="Keyword">renaming</a> <a id="671" class="Symbol">(</a> <a id="673" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="677" class="Symbol">to</a> <a id="680" class="Primitive">Type</a> <a id="685" class="Symbol">)</a>
<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="Data.Product.html" class="Module">Data.Product</a>    <a id="715" class="Keyword">using</a> <a id="721" class="Symbol">(</a> <a id="723" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="727" class="Symbol">;</a> <a id="729" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="731" class="Symbol">;</a> <a id="733" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="742" class="Symbol">)</a>
<a id="744" class="Keyword">open</a> <a id="749" class="Keyword">import</a> <a id="756" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="772" class="Keyword">using</a> <a id="778" class="Symbol">(</a> <a id="780" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="785" class="Symbol">;</a> <a id="787" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="791" class="Symbol">;</a> <a id="793" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="797" class="Symbol">)</a>

<a id="800" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="893" class="Keyword">open</a> <a id="898" class="Keyword">import</a> <a id="905" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="928" class="Keyword">using</a> <a id="934" class="Symbol">(</a><a id="935" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a><a id="938" class="Symbol">;</a> <a id="940" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a><a id="942" class="Symbol">;</a> <a id="944" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a><a id="947" class="Symbol">;</a> <a id="949" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a><a id="952" class="Symbol">)</a>
<a id="954" class="Keyword">open</a> <a id="959" class="Keyword">import</a> <a id="966" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="989" class="Keyword">using</a> <a id="995" class="Symbol">(</a> <a id="997" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1005" class="Symbol">;</a> <a id="1007" href="Algebras.Basic.html#9053" class="Function Operator">_̂_</a> <a id="1011" class="Symbol">;</a> <a id="1013" href="Algebras.Basic.html#7984" class="Record">algebra</a> <a id="1021" class="Symbol">)</a>

<a id="1024" class="Keyword">private</a> <a id="1032" class="Keyword">variable</a> <a id="1041" href="Algebras.Products.html#1041" class="Generalizable">α</a> <a id="1043" href="Algebras.Products.html#1043" class="Generalizable">β</a> <a id="1045" href="Algebras.Products.html#1045" class="Generalizable">ρ</a> <a id="1047" href="Algebras.Products.html#1047" class="Generalizable">𝓘</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [UniversalAlgebra][] library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1807" href="Algebras.Products.html#1807" class="Function">⨅</a> <a id="1809" class="Symbol">:</a> <a id="1811" class="Symbol">{</a><a id="1812" href="Algebras.Products.html#1812" class="Bound">I</a> <a id="1814" class="Symbol">:</a> <a id="1816" href="Algebras.Products.html#680" class="Primitive">Type</a> <a id="1821" href="Algebras.Products.html#1047" class="Generalizable">𝓘</a> <a id="1823" class="Symbol">}(</a><a id="1825" href="Algebras.Products.html#1825" class="Bound">𝒜</a> <a id="1827" class="Symbol">:</a> <a id="1829" href="Algebras.Products.html#1812" class="Bound">I</a> <a id="1831" class="Symbol">→</a> <a id="1833" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1841" href="Algebras.Products.html#1041" class="Generalizable">α</a> <a id="1843" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="1845" class="Symbol">)</a> <a id="1847" class="Symbol">→</a> <a id="1849" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1857" class="Symbol">(</a><a id="1858" href="Algebras.Products.html#1047" class="Generalizable">𝓘</a> <a id="1860" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1862" href="Algebras.Products.html#1041" class="Generalizable">α</a><a id="1863" class="Symbol">)</a> <a id="1865" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="1868" href="Algebras.Products.html#1807" class="Function">⨅</a> <a id="1870" class="Symbol">{</a><a id="1871" class="Argument">I</a> <a id="1873" class="Symbol">=</a> <a id="1875" href="Algebras.Products.html#1875" class="Bound">I</a><a id="1876" class="Symbol">}</a> <a id="1878" href="Algebras.Products.html#1878" class="Bound">𝒜</a> <a id="1880" class="Symbol">=</a> <a id="1882" class="Symbol">(</a> <a id="1884" class="Symbol">∀</a> <a id="1886" class="Symbol">(</a><a id="1887" href="Algebras.Products.html#1887" class="Bound">i</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="Algebras.Products.html#1875" class="Bound">I</a><a id="1892" class="Symbol">)</a> <a id="1894" class="Symbol">→</a> <a id="1896" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1898" href="Algebras.Products.html#1878" class="Bound">𝒜</a> <a id="1900" href="Algebras.Products.html#1887" class="Bound">i</a> <a id="1902" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1904" class="Symbol">)</a> <a id="1906" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1918" class="Comment">-- domain of the product algebra</a>
               <a id="1966" class="Symbol">λ</a> <a id="1968" href="Algebras.Products.html#1968" class="Bound">𝑓</a> <a id="1970" href="Algebras.Products.html#1970" class="Bound">𝑎</a> <a id="1972" href="Algebras.Products.html#1972" class="Bound">i</a> <a id="1974" class="Symbol">→</a> <a id="1976" class="Symbol">(</a><a id="1977" href="Algebras.Products.html#1968" class="Bound">𝑓</a> <a id="1979" href="Algebras.Basic.html#9053" class="Function Operator">̂</a> <a id="1981" href="Algebras.Products.html#1878" class="Bound">𝒜</a> <a id="1983" href="Algebras.Products.html#1972" class="Bound">i</a><a id="1984" class="Symbol">)</a> <a id="1986" class="Symbol">λ</a> <a id="1988" href="Algebras.Products.html#1988" class="Bound">x</a> <a id="1990" class="Symbol">→</a> <a id="1992" href="Algebras.Products.html#1970" class="Bound">𝑎</a> <a id="1994" href="Algebras.Products.html#1988" class="Bound">x</a> <a id="1996" href="Algebras.Products.html#1972" class="Bound">i</a>   <a id="2000" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2493" class="Keyword">open</a> <a id="2498" href="Algebras.Basic.html#7984" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2507" href="Algebras.Products.html#2507" class="Function">⨅&#39;</a> <a id="2510" class="Symbol">:</a> <a id="2512" class="Symbol">{</a><a id="2513" href="Algebras.Products.html#2513" class="Bound">I</a> <a id="2515" class="Symbol">:</a> <a id="2517" href="Algebras.Products.html#680" class="Primitive">Type</a> <a id="2522" href="Algebras.Products.html#1047" class="Generalizable">𝓘</a> <a id="2524" class="Symbol">}(</a><a id="2526" href="Algebras.Products.html#2526" class="Bound">𝒜</a> <a id="2528" class="Symbol">:</a> <a id="2530" href="Algebras.Products.html#2513" class="Bound">I</a> <a id="2532" class="Symbol">→</a> <a id="2534" href="Algebras.Basic.html#7984" class="Record">algebra</a> <a id="2542" href="Algebras.Products.html#1041" class="Generalizable">α</a> <a id="2544" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="2545" class="Symbol">)</a> <a id="2547" class="Symbol">→</a> <a id="2549" href="Algebras.Basic.html#7984" class="Record">algebra</a> <a id="2557" class="Symbol">(</a><a id="2558" href="Algebras.Products.html#1047" class="Generalizable">𝓘</a> <a id="2560" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2562" href="Algebras.Products.html#1041" class="Generalizable">α</a><a id="2563" class="Symbol">)</a> <a id="2565" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="2568" href="Algebras.Products.html#2507" class="Function">⨅&#39;</a> <a id="2571" class="Symbol">{</a><a id="2572" href="Algebras.Products.html#2572" class="Bound">I</a><a id="2573" class="Symbol">}</a> <a id="2575" href="Algebras.Products.html#2575" class="Bound">𝒜</a> <a id="2577" class="Symbol">=</a> <a id="2579" class="Keyword">record</a> <a id="2586" class="Symbol">{</a> <a id="2588" href="Algebras.Basic.html#8082" class="Field">carrier</a> <a id="2596" class="Symbol">=</a> <a id="2598" class="Symbol">∀</a> <a id="2600" href="Algebras.Products.html#2600" class="Bound">i</a> <a id="2602" class="Symbol">→</a> <a id="2604" href="Algebras.Basic.html#8082" class="Field">carrier</a> <a id="2612" class="Symbol">(</a><a id="2613" href="Algebras.Products.html#2575" class="Bound">𝒜</a> <a id="2615" href="Algebras.Products.html#2600" class="Bound">i</a><a id="2616" class="Symbol">)</a> <a id="2618" class="Symbol">;</a>                 <a id="2636" class="Comment">-- domain</a>
                     <a id="2667" href="Algebras.Basic.html#8101" class="Field">opsymbol</a> <a id="2676" class="Symbol">=</a> <a id="2678" class="Symbol">λ</a> <a id="2680" href="Algebras.Products.html#2680" class="Bound">𝑓</a> <a id="2682" href="Algebras.Products.html#2682" class="Bound">𝑎</a> <a id="2684" href="Algebras.Products.html#2684" class="Bound">i</a> <a id="2686" class="Symbol">→</a> <a id="2688" class="Symbol">(</a><a id="2689" href="Algebras.Basic.html#8101" class="Field">opsymbol</a> <a id="2698" class="Symbol">(</a><a id="2699" href="Algebras.Products.html#2575" class="Bound">𝒜</a> <a id="2701" href="Algebras.Products.html#2684" class="Bound">i</a><a id="2702" class="Symbol">))</a> <a id="2705" href="Algebras.Products.html#2680" class="Bound">𝑓</a> <a id="2707" class="Symbol">λ</a> <a id="2709" href="Algebras.Products.html#2709" class="Bound">x</a> <a id="2711" class="Symbol">→</a> <a id="2713" href="Algebras.Products.html#2682" class="Bound">𝑎</a> <a id="2715" href="Algebras.Products.html#2709" class="Bound">x</a> <a id="2717" href="Algebras.Products.html#2684" class="Bound">i</a> <a id="2719" class="Symbol">}</a> <a id="2721" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3003" href="Algebras.Products.html#3003" class="Function">ov</a> <a id="3006" class="Symbol">:</a> <a id="3008" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3014" class="Symbol">→</a> <a id="3016" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3022" href="Algebras.Products.html#3003" class="Function">ov</a> <a id="3025" href="Algebras.Products.html#3025" class="Bound">α</a> <a id="3027" class="Symbol">=</a> <a id="3029" href="Algebras.Products.html#501" class="Bound">𝓞</a> <a id="3031" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3033" href="Algebras.Products.html#503" class="Bound">𝓥</a> <a id="3035" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3037" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3042" href="Algebras.Products.html#3025" class="Bound">α</a>

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

<a id="4813" class="Keyword">module</a> <a id="4820" href="Algebras.Products.html#4820" class="Module">_</a> <a id="4822" class="Symbol">{</a><a id="4823" href="Algebras.Products.html#4823" class="Bound">𝒦</a> <a id="4825" class="Symbol">:</a> <a id="4827" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4832" class="Symbol">(</a><a id="4833" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="4841" href="Algebras.Products.html#1041" class="Generalizable">α</a> <a id="4843" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="4844" class="Symbol">)(</a><a id="4846" href="Algebras.Products.html#3003" class="Function">ov</a> <a id="4849" href="Algebras.Products.html#1041" class="Generalizable">α</a><a id="4850" class="Symbol">)}</a> <a id="4853" class="Keyword">where</a>
 <a id="4860" href="Algebras.Products.html#4860" class="Function">ℑ</a> <a id="4862" class="Symbol">:</a> <a id="4864" href="Algebras.Products.html#680" class="Primitive">Type</a> <a id="4869" class="Symbol">(</a><a id="4870" href="Algebras.Products.html#3003" class="Function">ov</a> <a id="4873" href="Algebras.Products.html#4841" class="Bound">α</a><a id="4874" class="Symbol">)</a>
 <a id="4877" href="Algebras.Products.html#4860" class="Function">ℑ</a> <a id="4879" class="Symbol">=</a> <a id="4881" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4884" href="Algebras.Products.html#4884" class="Bound">𝑨</a> <a id="4886" href="Data.Product.html#916" class="Function">∈</a> <a id="4888" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="4896" href="Algebras.Products.html#4841" class="Bound">α</a> <a id="4898" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="4900" href="Data.Product.html#916" class="Function">]</a> <a id="4902" href="Algebras.Products.html#4884" class="Bound">𝑨</a> <a id="4904" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4906" href="Algebras.Products.html#4823" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5255" href="Algebras.Products.html#5255" class="Function">𝔄</a> <a id="5257" class="Symbol">:</a> <a id="5259" href="Algebras.Products.html#4860" class="Function">ℑ</a> <a id="5261" class="Symbol">→</a> <a id="5263" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="5271" href="Algebras.Products.html#4841" class="Bound">α</a> <a id="5273" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5276" href="Algebras.Products.html#5255" class="Function">𝔄</a> <a id="5278" href="Algebras.Products.html#5278" class="Bound">i</a> <a id="5280" class="Symbol">=</a> <a id="5282" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="5284" href="Algebras.Products.html#5278" class="Bound">i</a> <a id="5286" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5402" href="Algebras.Products.html#5402" class="Function">class-product</a> <a id="5416" class="Symbol">:</a> <a id="5418" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="5426" class="Symbol">(</a><a id="5427" href="Algebras.Products.html#3003" class="Function">ov</a> <a id="5430" href="Algebras.Products.html#4841" class="Bound">α</a><a id="5431" class="Symbol">)</a> <a id="5433" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5436" href="Algebras.Products.html#5402" class="Function">class-product</a> <a id="5450" class="Symbol">=</a> <a id="5452" href="Algebras.Products.html#1807" class="Function">⨅</a> <a id="5454" href="Algebras.Products.html#5255" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

--------------------------------------------

<br>

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
