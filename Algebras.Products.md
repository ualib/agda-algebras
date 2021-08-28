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

From now on, the modules of the [agda-algebras](https://github.com/ualib/agda-algebras) library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1867" href="Algebras.Products.html#1867" class="Function">⨅</a> <a id="1869" class="Symbol">:</a> <a id="1871" class="Symbol">{</a><a id="1872" href="Algebras.Products.html#1872" class="Bound">I</a> <a id="1874" class="Symbol">:</a> <a id="1876" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="1881" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="1883" class="Symbol">}(</a><a id="1885" href="Algebras.Products.html#1885" class="Bound">𝒜</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="Algebras.Products.html#1872" class="Bound">I</a> <a id="1891" class="Symbol">→</a> <a id="1893" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="1901" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="1903" href="Algebras.Products.html#486" class="Bound">𝑆</a> <a id="1905" class="Symbol">)</a> <a id="1907" class="Symbol">→</a> <a id="1909" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="1917" class="Symbol">(</a><a id="1918" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="1920" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1922" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="1923" class="Symbol">)</a> <a id="1925" href="Algebras.Products.html#486" class="Bound">𝑆</a>

<a id="1928" href="Algebras.Products.html#1867" class="Function">⨅</a> <a id="1930" class="Symbol">{</a><a id="1931" class="Argument">I</a> <a id="1933" class="Symbol">=</a> <a id="1935" href="Algebras.Products.html#1935" class="Bound">I</a><a id="1936" class="Symbol">}</a> <a id="1938" href="Algebras.Products.html#1938" class="Bound">𝒜</a> <a id="1940" class="Symbol">=</a> <a id="1942" class="Symbol">(</a> <a id="1944" class="Symbol">∀</a> <a id="1946" class="Symbol">(</a><a id="1947" href="Algebras.Products.html#1947" class="Bound">i</a> <a id="1949" class="Symbol">:</a> <a id="1951" href="Algebras.Products.html#1935" class="Bound">I</a><a id="1952" class="Symbol">)</a> <a id="1954" class="Symbol">→</a> <a id="1956" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1958" href="Algebras.Products.html#1938" class="Bound">𝒜</a> <a id="1960" href="Algebras.Products.html#1947" class="Bound">i</a> <a id="1962" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1964" class="Symbol">)</a> <a id="1966" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1978" class="Comment">-- domain of the product algebra</a>
               <a id="2026" class="Symbol">λ</a> <a id="2028" href="Algebras.Products.html#2028" class="Bound">𝑓</a> <a id="2030" href="Algebras.Products.html#2030" class="Bound">𝑎</a> <a id="2032" href="Algebras.Products.html#2032" class="Bound">i</a> <a id="2034" class="Symbol">→</a> <a id="2036" class="Symbol">(</a><a id="2037" href="Algebras.Products.html#2028" class="Bound">𝑓</a> <a id="2039" href="Algebras.Basic.html#9410" class="Function Operator">̂</a> <a id="2041" href="Algebras.Products.html#1938" class="Bound">𝒜</a> <a id="2043" href="Algebras.Products.html#2032" class="Bound">i</a><a id="2044" class="Symbol">)</a> <a id="2046" class="Symbol">λ</a> <a id="2048" href="Algebras.Products.html#2048" class="Bound">x</a> <a id="2050" class="Symbol">→</a> <a id="2052" href="Algebras.Products.html#2030" class="Bound">𝑎</a> <a id="2054" href="Algebras.Products.html#2048" class="Bound">x</a> <a id="2056" href="Algebras.Products.html#2032" class="Bound">i</a>   <a id="2060" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [agda-algebras](https://github.com/ualib/agda-algebras) library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2588" class="Keyword">open</a> <a id="2593" href="Algebras.Basic.html#8345" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2602" href="Algebras.Products.html#2602" class="Function">⨅&#39;</a> <a id="2605" class="Symbol">:</a> <a id="2607" class="Symbol">{</a><a id="2608" href="Algebras.Products.html#2608" class="Bound">I</a> <a id="2610" class="Symbol">:</a> <a id="2612" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="2617" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="2619" class="Symbol">}(</a><a id="2621" href="Algebras.Products.html#2621" class="Bound">𝒜</a> <a id="2623" class="Symbol">:</a> <a id="2625" href="Algebras.Products.html#2608" class="Bound">I</a> <a id="2627" class="Symbol">→</a> <a id="2629" href="Algebras.Basic.html#8345" class="Record">algebra</a> <a id="2637" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="2639" href="Algebras.Products.html#486" class="Bound">𝑆</a><a id="2640" class="Symbol">)</a> <a id="2642" class="Symbol">→</a> <a id="2644" href="Algebras.Basic.html#8345" class="Record">algebra</a> <a id="2652" class="Symbol">(</a><a id="2653" href="Algebras.Products.html#1025" class="Generalizable">𝓘</a> <a id="2655" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2657" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="2658" class="Symbol">)</a> <a id="2660" href="Algebras.Products.html#486" class="Bound">𝑆</a>

<a id="2663" href="Algebras.Products.html#2602" class="Function">⨅&#39;</a> <a id="2666" class="Symbol">{</a><a id="2667" href="Algebras.Products.html#2667" class="Bound">I</a><a id="2668" class="Symbol">}</a> <a id="2670" href="Algebras.Products.html#2670" class="Bound">𝒜</a> <a id="2672" class="Symbol">=</a> <a id="2674" class="Keyword">record</a> <a id="2681" class="Symbol">{</a> <a id="2683" href="Algebras.Basic.html#8443" class="Field">carrier</a> <a id="2691" class="Symbol">=</a> <a id="2693" class="Symbol">∀</a> <a id="2695" href="Algebras.Products.html#2695" class="Bound">i</a> <a id="2697" class="Symbol">→</a> <a id="2699" href="Algebras.Basic.html#8443" class="Field">carrier</a> <a id="2707" class="Symbol">(</a><a id="2708" href="Algebras.Products.html#2670" class="Bound">𝒜</a> <a id="2710" href="Algebras.Products.html#2695" class="Bound">i</a><a id="2711" class="Symbol">)</a> <a id="2713" class="Symbol">;</a>                 <a id="2731" class="Comment">-- domain</a>
                     <a id="2762" href="Algebras.Basic.html#8462" class="Field">opsymbol</a> <a id="2771" class="Symbol">=</a> <a id="2773" class="Symbol">λ</a> <a id="2775" href="Algebras.Products.html#2775" class="Bound">𝑓</a> <a id="2777" href="Algebras.Products.html#2777" class="Bound">𝑎</a> <a id="2779" href="Algebras.Products.html#2779" class="Bound">i</a> <a id="2781" class="Symbol">→</a> <a id="2783" class="Symbol">(</a><a id="2784" href="Algebras.Basic.html#8462" class="Field">opsymbol</a> <a id="2793" class="Symbol">(</a><a id="2794" href="Algebras.Products.html#2670" class="Bound">𝒜</a> <a id="2796" href="Algebras.Products.html#2779" class="Bound">i</a><a id="2797" class="Symbol">))</a> <a id="2800" href="Algebras.Products.html#2775" class="Bound">𝑓</a> <a id="2802" class="Symbol">λ</a> <a id="2804" href="Algebras.Products.html#2804" class="Bound">x</a> <a id="2806" class="Symbol">→</a> <a id="2808" href="Algebras.Products.html#2777" class="Bound">𝑎</a> <a id="2810" href="Algebras.Products.html#2804" class="Bound">x</a> <a id="2812" href="Algebras.Products.html#2779" class="Bound">i</a> <a id="2814" class="Symbol">}</a> <a id="2816" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [agda-algebras](https://github.com/ualib/agda-algebras) library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3133" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="3136" class="Symbol">:</a> <a id="3138" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3144" class="Symbol">→</a> <a id="3146" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3152" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="3155" href="Algebras.Products.html#3155" class="Bound">α</a> <a id="3157" class="Symbol">=</a> <a id="3159" href="Algebras.Products.html#500" class="Bound">𝓞</a> <a id="3161" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3163" href="Algebras.Products.html#502" class="Bound">𝓥</a> <a id="3165" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3167" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3172" href="Algebras.Products.html#3155" class="Bound">α</a>

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

<a id="4859" class="Keyword">module</a> <a id="4866" href="Algebras.Products.html#4866" class="Module">_</a> <a id="4868" class="Symbol">{</a><a id="4869" href="Algebras.Products.html#4869" class="Bound">𝒦</a> <a id="4871" class="Symbol">:</a> <a id="4873" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4878" class="Symbol">(</a><a id="4879" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="4887" href="Algebras.Products.html#1019" class="Generalizable">α</a> <a id="4889" href="Algebras.Products.html#486" class="Bound">𝑆</a><a id="4890" class="Symbol">)(</a><a id="4892" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="4895" href="Algebras.Products.html#1019" class="Generalizable">α</a><a id="4896" class="Symbol">)}</a> <a id="4899" class="Keyword">where</a>
 <a id="4906" href="Algebras.Products.html#4906" class="Function">ℑ</a> <a id="4908" class="Symbol">:</a> <a id="4910" href="Algebras.Products.html#669" class="Primitive">Type</a> <a id="4915" class="Symbol">(</a><a id="4916" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="4919" href="Algebras.Products.html#4887" class="Bound">α</a><a id="4920" class="Symbol">)</a>
 <a id="4923" href="Algebras.Products.html#4906" class="Function">ℑ</a> <a id="4925" class="Symbol">=</a> <a id="4927" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4930" href="Algebras.Products.html#4930" class="Bound">𝑨</a> <a id="4932" href="Data.Product.html#916" class="Function">∈</a> <a id="4934" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="4942" href="Algebras.Products.html#4887" class="Bound">α</a> <a id="4944" href="Algebras.Products.html#486" class="Bound">𝑆</a> <a id="4946" href="Data.Product.html#916" class="Function">]</a> <a id="4948" href="Algebras.Products.html#4930" class="Bound">𝑨</a> <a id="4950" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4952" href="Algebras.Products.html#4869" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5301" href="Algebras.Products.html#5301" class="Function">𝔄</a> <a id="5303" class="Symbol">:</a> <a id="5305" href="Algebras.Products.html#4906" class="Function">ℑ</a> <a id="5307" class="Symbol">→</a> <a id="5309" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="5317" href="Algebras.Products.html#4887" class="Bound">α</a> <a id="5319" href="Algebras.Products.html#486" class="Bound">𝑆</a>
 <a id="5322" href="Algebras.Products.html#5301" class="Function">𝔄</a> <a id="5324" href="Algebras.Products.html#5324" class="Bound">i</a> <a id="5326" class="Symbol">=</a> <a id="5328" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="5330" href="Algebras.Products.html#5324" class="Bound">i</a> <a id="5332" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5448" href="Algebras.Products.html#5448" class="Function">class-product</a> <a id="5462" class="Symbol">:</a> <a id="5464" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="5472" class="Symbol">(</a><a id="5473" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="5476" href="Algebras.Products.html#4887" class="Bound">α</a><a id="5477" class="Symbol">)</a> <a id="5479" href="Algebras.Products.html#486" class="Bound">𝑆</a>
 <a id="5482" href="Algebras.Products.html#5448" class="Function">class-product</a> <a id="5496" class="Symbol">=</a> <a id="5498" href="Algebras.Products.html#1867" class="Function">⨅</a> <a id="5500" href="Algebras.Products.html#5301" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Algebras.Basic](Algebras.Basic.html)</span>
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
