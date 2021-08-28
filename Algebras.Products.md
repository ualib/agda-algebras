---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---


## <a id="products-of-algebras-and-product-algebras">Products of Algebras and Product Algebras</a>

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="353" class="Symbol">{-#</a> <a id="357" class="Keyword">OPTIONS</a> <a id="365" class="Pragma">--without-K</a> <a id="377" class="Pragma">--exact-split</a> <a id="391" class="Pragma">--safe</a> <a id="398" class="Symbol">#-}</a>


<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="431" class="Keyword">using</a> <a id="437" class="Symbol">(</a> <a id="439" href="Algebras.Basic.html#1139" class="Generalizable">𝓞</a> <a id="441" class="Symbol">;</a> <a id="443" href="Algebras.Basic.html#1141" class="Generalizable">𝓥</a> <a id="445" class="Symbol">;</a> <a id="447" href="Algebras.Basic.html#3865" class="Function">Signature</a> <a id="457" class="Symbol">)</a>

<a id="460" class="Keyword">module</a> <a id="467" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="485" class="Symbol">{</a><a id="486" href="Algebras.Products.html#486" class="Bound">𝑆</a> <a id="488" class="Symbol">:</a> <a id="490" href="Algebras.Basic.html#3865" class="Function">Signature</a> <a id="500" href="Algebras.Basic.html#1139" class="Generalizable">𝓞</a> <a id="502" href="Algebras.Basic.html#1141" class="Generalizable">𝓥</a><a id="503" class="Symbol">}</a> <a id="505" class="Keyword">where</a>

<a id="512" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="622" class="Keyword">using</a> <a id="628" class="Symbol">(</a> <a id="630" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="635" class="Symbol">;</a> <a id="637" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="641" class="Symbol">;</a> <a id="643" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="649" class="Symbol">)</a> <a id="651" class="Keyword">renaming</a> <a id="660" class="Symbol">(</a> <a id="662" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="666" class="Symbol">to</a> <a id="669" class="Primitive">Type</a> <a id="674" class="Symbol">)</a>
<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="Data.Product.html" class="Module">Data.Product</a>    <a id="704" class="Keyword">using</a> <a id="710" class="Symbol">(</a> <a id="712" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="716" class="Symbol">;</a> <a id="718" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="720" class="Symbol">;</a> <a id="722" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="731" class="Symbol">)</a>
<a id="733" class="Keyword">open</a> <a id="738" class="Keyword">import</a> <a id="745" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="761" class="Keyword">using</a> <a id="767" class="Symbol">(</a> <a id="769" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="774" class="Symbol">;</a> <a id="776" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="780" class="Symbol">;</a> <a id="782" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="786" class="Symbol">)</a>

<a id="789" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="871" class="Keyword">open</a> <a id="876" class="Keyword">import</a> <a id="883" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="906" class="Keyword">using</a> <a id="912" class="Symbol">(</a><a id="913" href="Overture.Preliminaries.html#5228" class="Function Operator">_⁻¹</a><a id="916" class="Symbol">;</a> <a id="918" href="Overture.Preliminaries.html#5627" class="Function">𝑖𝑑</a><a id="920" class="Symbol">;</a> <a id="922" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a><a id="925" class="Symbol">;</a> <a id="927" href="Overture.Preliminaries.html#4562" class="Function Operator">∥_∥</a><a id="930" class="Symbol">)</a>
<a id="932" class="Keyword">open</a> <a id="937" class="Keyword">import</a> <a id="944" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="967" class="Keyword">using</a> <a id="973" class="Symbol">(</a> <a id="975" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="983" class="Symbol">;</a> <a id="985" href="Algebras.Basic.html#9410" class="Function Operator">_̂_</a> <a id="989" class="Symbol">;</a> <a id="991" href="Algebras.Basic.html#8345" class="Record">algebra</a> <a id="999" class="Symbol">)</a>

<a id="1002" class="Keyword">private</a> <a id="1010" class="Keyword">variable</a> <a id="1019" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="1021" href="Algebras.Products.html#1021" class="Generalizable">β</a> <a id="1023" href="Algebras.Products.html#1023" class="Generalizable">ρ</a> <a id="1025" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="1027" class="Symbol">:</a> <a id="1029" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [UniversalAlgebra][] library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1785" href="Algebras.Products.html#1785" class="Function">⨅</a> <a id="1787" class="Symbol">:</a> <a id="1789" class="Symbol">{</a><a id="1790" href="Algebras.Products.html#1790" class="Bound">I</a> <a id="1792" class="Symbol">:</a> <a id="1794" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="1799" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="1801" class="Symbol">}(</a><a id="1803" href="Algebras.Products.html#1803" class="Bound">𝒜</a> <a id="1805" class="Symbol">:</a> <a id="1807" href="Algebras.Products.html#1790" class="Bound">I</a> <a id="1809" class="Symbol">→</a> <a id="1811" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="1819" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="1821" href="Algebras.Products.html#486" class="Bound">𝑆</a> <a id="1823" class="Symbol">)</a> <a id="1825" class="Symbol">→</a> <a id="1827" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="1835" class="Symbol">(</a><a id="1836" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="1838" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1840" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="1841" class="Symbol">)</a> <a id="1843" href="Algebras.Products.html#486" class="Bound">𝑆</a>

<a id="1846" href="Algebras.Products.html#1785" class="Function">⨅</a> <a id="1848" class="Symbol">{</a><a id="1849" class="Argument">I</a> <a id="1851" class="Symbol">=</a> <a id="1853" href="Algebras.Products.html#1853" class="Bound">I</a><a id="1854" class="Symbol">}</a> <a id="1856" href="Algebras.Products.html#1856" class="Bound">𝒜</a> <a id="1858" class="Symbol">=</a> <a id="1860" class="Symbol">(</a> <a id="1862" class="Symbol">∀</a> <a id="1864" class="Symbol">(</a><a id="1865" href="Algebras.Products.html#1865" class="Bound">i</a> <a id="1867" class="Symbol">:</a> <a id="1869" href="Algebras.Products.html#1853" class="Bound">I</a><a id="1870" class="Symbol">)</a> <a id="1872" class="Symbol">→</a> <a id="1874" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1876" href="Algebras.Products.html#1856" class="Bound">𝒜</a> <a id="1878" href="Algebras.Products.html#1865" class="Bound">i</a> <a id="1880" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1882" class="Symbol">)</a> <a id="1884" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1896" class="Comment">-- domain of the product algebra</a>
               <a id="1944" class="Symbol">λ</a> <a id="1946" href="Algebras.Products.html#1946" class="Bound">𝑓</a> <a id="1948" href="Algebras.Products.html#1948" class="Bound">𝑎</a> <a id="1950" href="Algebras.Products.html#1950" class="Bound">i</a> <a id="1952" class="Symbol">→</a> <a id="1954" class="Symbol">(</a><a id="1955" href="Algebras.Products.html#1946" class="Bound">𝑓</a> <a id="1957" href="Algebras.Basic.html#9410" class="Function Operator">̂</a> <a id="1959" href="Algebras.Products.html#1856" class="Bound">𝒜</a> <a id="1961" href="Algebras.Products.html#1950" class="Bound">i</a><a id="1962" class="Symbol">)</a> <a id="1964" class="Symbol">λ</a> <a id="1966" href="Algebras.Products.html#1966" class="Bound">x</a> <a id="1968" class="Symbol">→</a> <a id="1970" href="Algebras.Products.html#1948" class="Bound">𝑎</a> <a id="1972" href="Algebras.Products.html#1966" class="Bound">x</a> <a id="1974" href="Algebras.Products.html#1950" class="Bound">i</a>   <a id="1978" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2471" class="Keyword">open</a> <a id="2476" href="Algebras.Basic.html#8345" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2485" href="Algebras.Products.html#2485" class="Function">⨅&#39;</a> <a id="2488" class="Symbol">:</a> <a id="2490" class="Symbol">{</a><a id="2491" href="Algebras.Products.html#2491" class="Bound">I</a> <a id="2493" class="Symbol">:</a> <a id="2495" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="2500" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="2502" class="Symbol">}(</a><a id="2504" href="Algebras.Products.html#2504" class="Bound">𝒜</a> <a id="2506" class="Symbol">:</a> <a id="2508" href="Algebras.Products.html#2491" class="Bound">I</a> <a id="2510" class="Symbol">→</a> <a id="2512" href="Algebras.Basic.html#8345" class="Record">algebra</a> <a id="2520" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="2522" href="Algebras.Products.html#486" class="Bound">𝑆</a><a id="2523" class="Symbol">)</a> <a id="2525" class="Symbol">→</a> <a id="2527" href="Algebras.Basic.html#8345" class="Record">algebra</a> <a id="2535" class="Symbol">(</a><a id="2536" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="2538" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2540" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="2541" class="Symbol">)</a> <a id="2543" href="Algebras.Products.html#486" class="Bound">𝑆</a>

<a id="2546" href="Algebras.Products.html#2485" class="Function">⨅&#39;</a> <a id="2549" class="Symbol">{</a><a id="2550" href="Algebras.Products.html#2550" class="Bound">I</a><a id="2551" class="Symbol">}</a> <a id="2553" href="Algebras.Products.html#2553" class="Bound">𝒜</a> <a id="2555" class="Symbol">=</a> <a id="2557" class="Keyword">record</a> <a id="2564" class="Symbol">{</a> <a id="2566" href="Algebras.Basic.html#8443" class="Field">carrier</a> <a id="2574" class="Symbol">=</a> <a id="2576" class="Symbol">∀</a> <a id="2578" href="Algebras.Products.html#2578" class="Bound">i</a> <a id="2580" class="Symbol">→</a> <a id="2582" href="Algebras.Basic.html#8443" class="Field">carrier</a> <a id="2590" class="Symbol">(</a><a id="2591" href="Algebras.Products.html#2553" class="Bound">𝒜</a> <a id="2593" href="Algebras.Products.html#2578" class="Bound">i</a><a id="2594" class="Symbol">)</a> <a id="2596" class="Symbol">;</a>                 <a id="2614" class="Comment">-- domain</a>
                     <a id="2645" href="Algebras.Basic.html#8462" class="Field">opsymbol</a> <a id="2654" class="Symbol">=</a> <a id="2656" class="Symbol">λ</a> <a id="2658" href="Algebras.Products.html#2658" class="Bound">𝑓</a> <a id="2660" href="Algebras.Products.html#2660" class="Bound">𝑎</a> <a id="2662" href="Algebras.Products.html#2662" class="Bound">i</a> <a id="2664" class="Symbol">→</a> <a id="2666" class="Symbol">(</a><a id="2667" href="Algebras.Basic.html#8462" class="Field">opsymbol</a> <a id="2676" class="Symbol">(</a><a id="2677" href="Algebras.Products.html#2553" class="Bound">𝒜</a> <a id="2679" href="Algebras.Products.html#2662" class="Bound">i</a><a id="2680" class="Symbol">))</a> <a id="2683" href="Algebras.Products.html#2658" class="Bound">𝑓</a> <a id="2685" class="Symbol">λ</a> <a id="2687" href="Algebras.Products.html#2687" class="Bound">x</a> <a id="2689" class="Symbol">→</a> <a id="2691" href="Algebras.Products.html#2660" class="Bound">𝑎</a> <a id="2693" href="Algebras.Products.html#2687" class="Bound">x</a> <a id="2695" href="Algebras.Products.html#2662" class="Bound">i</a> <a id="2697" class="Symbol">}</a> <a id="2699" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2981" href="Algebras.Products.html#2981" class="Function">ov</a> <a id="2984" class="Symbol">:</a> <a id="2986" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="2992" class="Symbol">→</a> <a id="2994" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3000" href="Algebras.Products.html#2981" class="Function">ov</a> <a id="3003" href="Algebras.Products.html#3003" class="Bound">α</a> <a id="3005" class="Symbol">=</a> <a id="3007" href="Algebras.Products.html#500" class="Bound">𝓞</a> <a id="3009" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3011" href="Algebras.Products.html#502" class="Bound">𝓥</a> <a id="3013" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3015" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3020" href="Algebras.Products.html#3003" class="Bound">α</a>

</pre>



## <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra α 𝑆`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred (Algebra α 𝑆) β`, for some type `β`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not what we want.  For recall that `Pred (Algebra α 𝑆) β` is just an alias for the function type `Algebra α 𝑆 → Type β`, and the semantics of the latter takes `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α 𝑆) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α 𝑆` belongs to `𝒦`.  Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra α 𝑆` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.

<pre class="Agda">

<a id="4707" class="Keyword">module</a> <a id="4714" href="Algebras.Products.html#4714" class="Module">_</a> <a id="4716" class="Symbol">{</a><a id="4717" href="Algebras.Products.html#4717" class="Bound">𝒦</a> <a id="4719" class="Symbol">:</a> <a id="4721" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4726" class="Symbol">(</a><a id="4727" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="4735" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="4737" href="Algebras.Products.html#486" class="Bound">𝑆</a><a id="4738" class="Symbol">)(</a><a id="4740" href="Algebras.Products.html#2981" class="Function">ov</a> <a id="4743" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="4744" class="Symbol">)}</a> <a id="4747" class="Keyword">where</a>
 <a id="4754" href="Algebras.Products.html#4754" class="Function">ℑ</a> <a id="4756" class="Symbol">:</a> <a id="4758" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="4763" class="Symbol">(</a><a id="4764" href="Algebras.Products.html#2981" class="Function">ov</a> <a id="4767" href="Algebras.Products.html#4735" class="Bound">α</a><a id="4768" class="Symbol">)</a>
 <a id="4771" href="Algebras.Products.html#4754" class="Function">ℑ</a> <a id="4773" class="Symbol">=</a> <a id="4775" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4778" href="Algebras.Products.html#4778" class="Bound">𝑨</a> <a id="4780" href="Data.Product.html#916" class="Function">∈</a> <a id="4782" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="4790" href="Algebras.Products.html#4735" class="Bound">α</a> <a id="4792" href="Algebras.Products.html#486" class="Bound">𝑆</a> <a id="4794" href="Data.Product.html#916" class="Function">]</a> <a id="4796" href="Algebras.Products.html#4778" class="Bound">𝑨</a> <a id="4798" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4800" href="Algebras.Products.html#4717" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5149" href="Algebras.Products.html#5149" class="Function">𝔄</a> <a id="5151" class="Symbol">:</a> <a id="5153" href="Algebras.Products.html#4754" class="Function">ℑ</a> <a id="5155" class="Symbol">→</a> <a id="5157" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="5165" href="Algebras.Products.html#4735" class="Bound">α</a> <a id="5167" href="Algebras.Products.html#486" class="Bound">𝑆</a>
 <a id="5170" href="Algebras.Products.html#5149" class="Function">𝔄</a> <a id="5172" href="Algebras.Products.html#5172" class="Bound">i</a> <a id="5174" class="Symbol">=</a> <a id="5176" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="5178" href="Algebras.Products.html#5172" class="Bound">i</a> <a id="5180" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5296" href="Algebras.Products.html#5296" class="Function">class-product</a> <a id="5310" class="Symbol">:</a> <a id="5312" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="5320" class="Symbol">(</a><a id="5321" href="Algebras.Products.html#2981" class="Function">ov</a> <a id="5324" href="Algebras.Products.html#4735" class="Bound">α</a><a id="5325" class="Symbol">)</a> <a id="5327" href="Algebras.Products.html#486" class="Bound">𝑆</a>
 <a id="5330" href="Algebras.Products.html#5296" class="Function">class-product</a> <a id="5344" class="Symbol">=</a> <a id="5346" href="Algebras.Products.html#1785" class="Function">⨅</a> <a id="5348" href="Algebras.Products.html#5149" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Algebras.Basic](Algebras.Basic.html)</span>
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
