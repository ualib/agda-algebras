---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---


### Products of Algebras and Product Algebras

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="300" class="Symbol">{-#</a> <a id="304" class="Keyword">OPTIONS</a> <a id="312" class="Pragma">--without-K</a> <a id="324" class="Pragma">--exact-split</a> <a id="338" class="Pragma">--safe</a> <a id="345" class="Symbol">#-}</a>


<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="378" class="Keyword">using</a> <a id="384" class="Symbol">(</a> <a id="386" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="388" class="Symbol">;</a> <a id="390" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a> <a id="392" class="Symbol">;</a> <a id="394" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="404" class="Symbol">)</a>

<a id="407" class="Keyword">module</a> <a id="414" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="432" class="Symbol">{</a><a id="433" href="Algebras.Products.html#433" class="Bound">𝑆</a> <a id="435" class="Symbol">:</a> <a id="437" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="447" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="449" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a><a id="450" class="Symbol">}</a> <a id="452" class="Keyword">where</a>

<a id="459" class="Comment">-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="580" class="Keyword">using</a> <a id="586" class="Symbol">(</a> <a id="588" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="593" class="Symbol">;</a> <a id="595" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="599" class="Symbol">;</a> <a id="601" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="607" class="Symbol">)</a> <a id="609" class="Keyword">renaming</a> <a id="618" class="Symbol">(</a> <a id="620" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="624" class="Symbol">to</a> <a id="627" class="Primitive">Type</a> <a id="632" class="Symbol">)</a>
<a id="634" class="Keyword">open</a> <a id="639" class="Keyword">import</a> <a id="646" href="Data.Product.html" class="Module">Data.Product</a>    <a id="662" class="Keyword">using</a> <a id="668" class="Symbol">(</a> <a id="670" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="674" class="Symbol">;</a> <a id="676" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="678" class="Symbol">;</a> <a id="680" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="689" class="Symbol">)</a>
<a id="691" class="Keyword">open</a> <a id="696" class="Keyword">import</a> <a id="703" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="719" class="Keyword">using</a> <a id="725" class="Symbol">(</a> <a id="727" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="732" class="Symbol">;</a> <a id="734" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="738" class="Symbol">;</a> <a id="740" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="744" class="Symbol">)</a>

<a id="747" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="840" class="Keyword">open</a> <a id="845" class="Keyword">import</a> <a id="852" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="875" class="Keyword">using</a> <a id="881" class="Symbol">(</a><a id="882" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a><a id="885" class="Symbol">;</a> <a id="887" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a><a id="889" class="Symbol">;</a> <a id="891" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a><a id="894" class="Symbol">;</a> <a id="896" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a><a id="899" class="Symbol">)</a>
<a id="901" class="Keyword">open</a> <a id="906" class="Keyword">import</a> <a id="913" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="936" class="Keyword">using</a> <a id="942" class="Symbol">(</a> <a id="944" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="952" class="Symbol">;</a> <a id="954" href="Algebras.Basic.html#9889" class="Function Operator">_̂_</a> <a id="958" class="Symbol">;</a> <a id="960" href="Algebras.Basic.html#8637" class="Record">algebra</a> <a id="968" class="Symbol">)</a>

<a id="971" class="Keyword">private</a> <a id="979" class="Keyword">variable</a> <a id="988" href="Algebras.Products.html#988" class="Generalizable">α</a> <a id="990" href="Algebras.Products.html#990" class="Generalizable">β</a> <a id="992" href="Algebras.Products.html#992" class="Generalizable">ρ</a> <a id="994" href="Algebras.Products.html#994" class="Generalizable">𝓘</a> <a id="996" class="Symbol">:</a> <a id="998" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [UniversalAlgebra][] library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1754" href="Algebras.Products.html#1754" class="Function">⨅</a> <a id="1756" class="Symbol">:</a> <a id="1758" class="Symbol">{</a><a id="1759" href="Algebras.Products.html#1759" class="Bound">I</a> <a id="1761" class="Symbol">:</a> <a id="1763" href="Algebras.Products.html#627" class="Primitive">Type</a> <a id="1768" href="Algebras.Products.html#994" class="Generalizable">𝓘</a> <a id="1770" class="Symbol">}(</a><a id="1772" href="Algebras.Products.html#1772" class="Bound">𝒜</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="Algebras.Products.html#1759" class="Bound">I</a> <a id="1778" class="Symbol">→</a> <a id="1780" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="1788" href="Algebras.Products.html#988" class="Generalizable">α</a> <a id="1790" href="Algebras.Products.html#433" class="Bound">𝑆</a> <a id="1792" class="Symbol">)</a> <a id="1794" class="Symbol">→</a> <a id="1796" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="1804" class="Symbol">(</a><a id="1805" href="Algebras.Products.html#994" class="Generalizable">𝓘</a> <a id="1807" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1809" href="Algebras.Products.html#988" class="Generalizable">α</a><a id="1810" class="Symbol">)</a> <a id="1812" href="Algebras.Products.html#433" class="Bound">𝑆</a>

<a id="1815" href="Algebras.Products.html#1754" class="Function">⨅</a> <a id="1817" class="Symbol">{</a><a id="1818" class="Argument">I</a> <a id="1820" class="Symbol">=</a> <a id="1822" href="Algebras.Products.html#1822" class="Bound">I</a><a id="1823" class="Symbol">}</a> <a id="1825" href="Algebras.Products.html#1825" class="Bound">𝒜</a> <a id="1827" class="Symbol">=</a> <a id="1829" class="Symbol">(</a> <a id="1831" class="Symbol">∀</a> <a id="1833" class="Symbol">(</a><a id="1834" href="Algebras.Products.html#1834" class="Bound">i</a> <a id="1836" class="Symbol">:</a> <a id="1838" href="Algebras.Products.html#1822" class="Bound">I</a><a id="1839" class="Symbol">)</a> <a id="1841" class="Symbol">→</a> <a id="1843" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1845" href="Algebras.Products.html#1825" class="Bound">𝒜</a> <a id="1847" href="Algebras.Products.html#1834" class="Bound">i</a> <a id="1849" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1851" class="Symbol">)</a> <a id="1853" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1865" class="Comment">-- domain of the product algebra</a>
               <a id="1913" class="Symbol">λ</a> <a id="1915" href="Algebras.Products.html#1915" class="Bound">𝑓</a> <a id="1917" href="Algebras.Products.html#1917" class="Bound">𝑎</a> <a id="1919" href="Algebras.Products.html#1919" class="Bound">i</a> <a id="1921" class="Symbol">→</a> <a id="1923" class="Symbol">(</a><a id="1924" href="Algebras.Products.html#1915" class="Bound">𝑓</a> <a id="1926" href="Algebras.Basic.html#9889" class="Function Operator">̂</a> <a id="1928" href="Algebras.Products.html#1825" class="Bound">𝒜</a> <a id="1930" href="Algebras.Products.html#1919" class="Bound">i</a><a id="1931" class="Symbol">)</a> <a id="1933" class="Symbol">λ</a> <a id="1935" href="Algebras.Products.html#1935" class="Bound">x</a> <a id="1937" class="Symbol">→</a> <a id="1939" href="Algebras.Products.html#1917" class="Bound">𝑎</a> <a id="1941" href="Algebras.Products.html#1935" class="Bound">x</a> <a id="1943" href="Algebras.Products.html#1919" class="Bound">i</a>   <a id="1947" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2440" class="Keyword">open</a> <a id="2445" href="Algebras.Basic.html#8637" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2454" href="Algebras.Products.html#2454" class="Function">⨅&#39;</a> <a id="2457" class="Symbol">:</a> <a id="2459" class="Symbol">{</a><a id="2460" href="Algebras.Products.html#2460" class="Bound">I</a> <a id="2462" class="Symbol">:</a> <a id="2464" href="Algebras.Products.html#627" class="Primitive">Type</a> <a id="2469" href="Algebras.Products.html#994" class="Generalizable">𝓘</a> <a id="2471" class="Symbol">}(</a><a id="2473" href="Algebras.Products.html#2473" class="Bound">𝒜</a> <a id="2475" class="Symbol">:</a> <a id="2477" href="Algebras.Products.html#2460" class="Bound">I</a> <a id="2479" class="Symbol">→</a> <a id="2481" href="Algebras.Basic.html#8637" class="Record">algebra</a> <a id="2489" href="Algebras.Products.html#988" class="Generalizable">α</a> <a id="2491" href="Algebras.Products.html#433" class="Bound">𝑆</a><a id="2492" class="Symbol">)</a> <a id="2494" class="Symbol">→</a> <a id="2496" href="Algebras.Basic.html#8637" class="Record">algebra</a> <a id="2504" class="Symbol">(</a><a id="2505" href="Algebras.Products.html#994" class="Generalizable">𝓘</a> <a id="2507" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2509" href="Algebras.Products.html#988" class="Generalizable">α</a><a id="2510" class="Symbol">)</a> <a id="2512" href="Algebras.Products.html#433" class="Bound">𝑆</a>

<a id="2515" href="Algebras.Products.html#2454" class="Function">⨅&#39;</a> <a id="2518" class="Symbol">{</a><a id="2519" href="Algebras.Products.html#2519" class="Bound">I</a><a id="2520" class="Symbol">}</a> <a id="2522" href="Algebras.Products.html#2522" class="Bound">𝒜</a> <a id="2524" class="Symbol">=</a> <a id="2526" class="Keyword">record</a> <a id="2533" class="Symbol">{</a> <a id="2535" href="Algebras.Basic.html#8735" class="Field">carrier</a> <a id="2543" class="Symbol">=</a> <a id="2545" class="Symbol">∀</a> <a id="2547" href="Algebras.Products.html#2547" class="Bound">i</a> <a id="2549" class="Symbol">→</a> <a id="2551" href="Algebras.Basic.html#8735" class="Field">carrier</a> <a id="2559" class="Symbol">(</a><a id="2560" href="Algebras.Products.html#2522" class="Bound">𝒜</a> <a id="2562" href="Algebras.Products.html#2547" class="Bound">i</a><a id="2563" class="Symbol">)</a> <a id="2565" class="Symbol">;</a>                 <a id="2583" class="Comment">-- domain</a>
                     <a id="2614" href="Algebras.Basic.html#8754" class="Field">opsymbol</a> <a id="2623" class="Symbol">=</a> <a id="2625" class="Symbol">λ</a> <a id="2627" href="Algebras.Products.html#2627" class="Bound">𝑓</a> <a id="2629" href="Algebras.Products.html#2629" class="Bound">𝑎</a> <a id="2631" href="Algebras.Products.html#2631" class="Bound">i</a> <a id="2633" class="Symbol">→</a> <a id="2635" class="Symbol">(</a><a id="2636" href="Algebras.Basic.html#8754" class="Field">opsymbol</a> <a id="2645" class="Symbol">(</a><a id="2646" href="Algebras.Products.html#2522" class="Bound">𝒜</a> <a id="2648" href="Algebras.Products.html#2631" class="Bound">i</a><a id="2649" class="Symbol">))</a> <a id="2652" href="Algebras.Products.html#2627" class="Bound">𝑓</a> <a id="2654" class="Symbol">λ</a> <a id="2656" href="Algebras.Products.html#2656" class="Bound">x</a> <a id="2658" class="Symbol">→</a> <a id="2660" href="Algebras.Products.html#2629" class="Bound">𝑎</a> <a id="2662" href="Algebras.Products.html#2656" class="Bound">x</a> <a id="2664" href="Algebras.Products.html#2631" class="Bound">i</a> <a id="2666" class="Symbol">}</a> <a id="2668" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2950" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="2953" class="Symbol">:</a> <a id="2955" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="2961" class="Symbol">→</a> <a id="2963" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="2969" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="2972" href="Algebras.Products.html#2972" class="Bound">α</a> <a id="2974" class="Symbol">=</a> <a id="2976" href="Algebras.Products.html#447" class="Bound">𝓞</a> <a id="2978" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2980" href="Algebras.Products.html#449" class="Bound">𝓥</a> <a id="2982" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2984" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2989" href="Algebras.Products.html#2972" class="Bound">α</a>

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

<a id="4760" class="Keyword">module</a> <a id="4767" href="Algebras.Products.html#4767" class="Module">_</a> <a id="4769" class="Symbol">{</a><a id="4770" href="Algebras.Products.html#4770" class="Bound">𝒦</a> <a id="4772" class="Symbol">:</a> <a id="4774" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4779" class="Symbol">(</a><a id="4780" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="4788" href="Algebras.Products.html#988" class="Generalizable">α</a> <a id="4790" href="Algebras.Products.html#433" class="Bound">𝑆</a><a id="4791" class="Symbol">)(</a><a id="4793" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="4796" href="Algebras.Products.html#988" class="Generalizable">α</a><a id="4797" class="Symbol">)}</a> <a id="4800" class="Keyword">where</a>
 <a id="4807" href="Algebras.Products.html#4807" class="Function">ℑ</a> <a id="4809" class="Symbol">:</a> <a id="4811" href="Algebras.Products.html#627" class="Primitive">Type</a> <a id="4816" class="Symbol">(</a><a id="4817" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="4820" href="Algebras.Products.html#4788" class="Bound">α</a><a id="4821" class="Symbol">)</a>
 <a id="4824" href="Algebras.Products.html#4807" class="Function">ℑ</a> <a id="4826" class="Symbol">=</a> <a id="4828" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4831" href="Algebras.Products.html#4831" class="Bound">𝑨</a> <a id="4833" href="Data.Product.html#916" class="Function">∈</a> <a id="4835" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="4843" href="Algebras.Products.html#4788" class="Bound">α</a> <a id="4845" href="Algebras.Products.html#433" class="Bound">𝑆</a> <a id="4847" href="Data.Product.html#916" class="Function">]</a> <a id="4849" href="Algebras.Products.html#4831" class="Bound">𝑨</a> <a id="4851" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4853" href="Algebras.Products.html#4770" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5202" href="Algebras.Products.html#5202" class="Function">𝔄</a> <a id="5204" class="Symbol">:</a> <a id="5206" href="Algebras.Products.html#4807" class="Function">ℑ</a> <a id="5208" class="Symbol">→</a> <a id="5210" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="5218" href="Algebras.Products.html#4788" class="Bound">α</a> <a id="5220" href="Algebras.Products.html#433" class="Bound">𝑆</a>
 <a id="5223" href="Algebras.Products.html#5202" class="Function">𝔄</a> <a id="5225" href="Algebras.Products.html#5225" class="Bound">i</a> <a id="5227" class="Symbol">=</a> <a id="5229" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="5231" href="Algebras.Products.html#5225" class="Bound">i</a> <a id="5233" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5349" href="Algebras.Products.html#5349" class="Function">class-product</a> <a id="5363" class="Symbol">:</a> <a id="5365" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="5373" class="Symbol">(</a><a id="5374" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="5377" href="Algebras.Products.html#4788" class="Bound">α</a><a id="5378" class="Symbol">)</a> <a id="5380" href="Algebras.Products.html#433" class="Bound">𝑆</a>
 <a id="5383" href="Algebras.Products.html#5349" class="Function">class-product</a> <a id="5397" class="Symbol">=</a> <a id="5399" href="Algebras.Products.html#1754" class="Function">⨅</a> <a id="5401" href="Algebras.Products.html#5202" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

--------------------------------------------

<br>
<br>

[← Algebras.Congruences](Algebras.Congruences.html)
<span style="float:right;">[Algebras.Setoid →](Algebras.Setoid.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
