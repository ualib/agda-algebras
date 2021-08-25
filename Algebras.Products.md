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

<a id="513" class="Comment">-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="634" class="Keyword">using</a> <a id="640" class="Symbol">(</a> <a id="642" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="647" class="Symbol">;</a> <a id="649" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="653" class="Symbol">;</a> <a id="655" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="661" class="Symbol">)</a> <a id="663" class="Keyword">renaming</a> <a id="672" class="Symbol">(</a> <a id="674" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="678" class="Symbol">to</a> <a id="681" class="Primitive">Type</a> <a id="686" class="Symbol">)</a>
<a id="688" class="Keyword">open</a> <a id="693" class="Keyword">import</a> <a id="700" href="Data.Product.html" class="Module">Data.Product</a>    <a id="716" class="Keyword">using</a> <a id="722" class="Symbol">(</a> <a id="724" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="728" class="Symbol">;</a> <a id="730" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="732" class="Symbol">;</a> <a id="734" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="743" class="Symbol">)</a>
<a id="745" class="Keyword">open</a> <a id="750" class="Keyword">import</a> <a id="757" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="773" class="Keyword">using</a> <a id="779" class="Symbol">(</a> <a id="781" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="786" class="Symbol">;</a> <a id="788" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="792" class="Symbol">;</a> <a id="794" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="798" class="Symbol">)</a>

<a id="801" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="894" class="Keyword">open</a> <a id="899" class="Keyword">import</a> <a id="906" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="929" class="Keyword">using</a> <a id="935" class="Symbol">(</a><a id="936" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a><a id="939" class="Symbol">;</a> <a id="941" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a><a id="943" class="Symbol">;</a> <a id="945" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a><a id="948" class="Symbol">;</a> <a id="950" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a><a id="953" class="Symbol">)</a>
<a id="955" class="Keyword">open</a> <a id="960" class="Keyword">import</a> <a id="967" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="990" class="Keyword">using</a> <a id="996" class="Symbol">(</a> <a id="998" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1006" class="Symbol">;</a> <a id="1008" href="Algebras.Basic.html#8352" class="Function Operator">_̂_</a> <a id="1012" class="Symbol">;</a> <a id="1014" href="Algebras.Basic.html#7283" class="Record">algebra</a> <a id="1022" class="Symbol">)</a>

<a id="1025" class="Keyword">private</a> <a id="1033" class="Keyword">variable</a> <a id="1042" href="Algebras.Products.html#1042" class="Generalizable">α</a> <a id="1044" href="Algebras.Products.html#1044" class="Generalizable">β</a> <a id="1046" href="Algebras.Products.html#1046" class="Generalizable">ρ</a> <a id="1048" href="Algebras.Products.html#1048" class="Generalizable">𝓘</a> <a id="1050" class="Symbol">:</a> <a id="1052" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [UniversalAlgebra][] library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1808" href="Algebras.Products.html#1808" class="Function">⨅</a> <a id="1810" class="Symbol">:</a> <a id="1812" class="Symbol">{</a><a id="1813" href="Algebras.Products.html#1813" class="Bound">I</a> <a id="1815" class="Symbol">:</a> <a id="1817" href="Algebras.Products.html#681" class="Primitive">Type</a> <a id="1822" href="Algebras.Products.html#1048" class="Generalizable">𝓘</a> <a id="1824" class="Symbol">}(</a><a id="1826" href="Algebras.Products.html#1826" class="Bound">𝒜</a> <a id="1828" class="Symbol">:</a> <a id="1830" href="Algebras.Products.html#1813" class="Bound">I</a> <a id="1832" class="Symbol">→</a> <a id="1834" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1842" href="Algebras.Products.html#1042" class="Generalizable">α</a> <a id="1844" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="1846" class="Symbol">)</a> <a id="1848" class="Symbol">→</a> <a id="1850" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="1858" class="Symbol">(</a><a id="1859" href="Algebras.Products.html#1048" class="Generalizable">𝓘</a> <a id="1861" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1863" href="Algebras.Products.html#1042" class="Generalizable">α</a><a id="1864" class="Symbol">)</a> <a id="1866" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="1869" href="Algebras.Products.html#1808" class="Function">⨅</a> <a id="1871" class="Symbol">{</a><a id="1872" class="Argument">I</a> <a id="1874" class="Symbol">=</a> <a id="1876" href="Algebras.Products.html#1876" class="Bound">I</a><a id="1877" class="Symbol">}</a> <a id="1879" href="Algebras.Products.html#1879" class="Bound">𝒜</a> <a id="1881" class="Symbol">=</a> <a id="1883" class="Symbol">(</a> <a id="1885" class="Symbol">∀</a> <a id="1887" class="Symbol">(</a><a id="1888" href="Algebras.Products.html#1888" class="Bound">i</a> <a id="1890" class="Symbol">:</a> <a id="1892" href="Algebras.Products.html#1876" class="Bound">I</a><a id="1893" class="Symbol">)</a> <a id="1895" class="Symbol">→</a> <a id="1897" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1899" href="Algebras.Products.html#1879" class="Bound">𝒜</a> <a id="1901" href="Algebras.Products.html#1888" class="Bound">i</a> <a id="1903" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1905" class="Symbol">)</a> <a id="1907" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1919" class="Comment">-- domain of the product algebra</a>
               <a id="1967" class="Symbol">λ</a> <a id="1969" href="Algebras.Products.html#1969" class="Bound">𝑓</a> <a id="1971" href="Algebras.Products.html#1971" class="Bound">𝑎</a> <a id="1973" href="Algebras.Products.html#1973" class="Bound">i</a> <a id="1975" class="Symbol">→</a> <a id="1977" class="Symbol">(</a><a id="1978" href="Algebras.Products.html#1969" class="Bound">𝑓</a> <a id="1980" href="Algebras.Basic.html#8352" class="Function Operator">̂</a> <a id="1982" href="Algebras.Products.html#1879" class="Bound">𝒜</a> <a id="1984" href="Algebras.Products.html#1973" class="Bound">i</a><a id="1985" class="Symbol">)</a> <a id="1987" class="Symbol">λ</a> <a id="1989" href="Algebras.Products.html#1989" class="Bound">x</a> <a id="1991" class="Symbol">→</a> <a id="1993" href="Algebras.Products.html#1971" class="Bound">𝑎</a> <a id="1995" href="Algebras.Products.html#1989" class="Bound">x</a> <a id="1997" href="Algebras.Products.html#1973" class="Bound">i</a>   <a id="2001" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2494" class="Keyword">open</a> <a id="2499" href="Algebras.Basic.html#7283" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2508" href="Algebras.Products.html#2508" class="Function">⨅&#39;</a> <a id="2511" class="Symbol">:</a> <a id="2513" class="Symbol">{</a><a id="2514" href="Algebras.Products.html#2514" class="Bound">I</a> <a id="2516" class="Symbol">:</a> <a id="2518" href="Algebras.Products.html#681" class="Primitive">Type</a> <a id="2523" href="Algebras.Products.html#1048" class="Generalizable">𝓘</a> <a id="2525" class="Symbol">}(</a><a id="2527" href="Algebras.Products.html#2527" class="Bound">𝒜</a> <a id="2529" class="Symbol">:</a> <a id="2531" href="Algebras.Products.html#2514" class="Bound">I</a> <a id="2533" class="Symbol">→</a> <a id="2535" href="Algebras.Basic.html#7283" class="Record">algebra</a> <a id="2543" href="Algebras.Products.html#1042" class="Generalizable">α</a> <a id="2545" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="2546" class="Symbol">)</a> <a id="2548" class="Symbol">→</a> <a id="2550" href="Algebras.Basic.html#7283" class="Record">algebra</a> <a id="2558" class="Symbol">(</a><a id="2559" href="Algebras.Products.html#1048" class="Generalizable">𝓘</a> <a id="2561" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2563" href="Algebras.Products.html#1042" class="Generalizable">α</a><a id="2564" class="Symbol">)</a> <a id="2566" href="Algebras.Products.html#487" class="Bound">𝑆</a>

<a id="2569" href="Algebras.Products.html#2508" class="Function">⨅&#39;</a> <a id="2572" class="Symbol">{</a><a id="2573" href="Algebras.Products.html#2573" class="Bound">I</a><a id="2574" class="Symbol">}</a> <a id="2576" href="Algebras.Products.html#2576" class="Bound">𝒜</a> <a id="2578" class="Symbol">=</a> <a id="2580" class="Keyword">record</a> <a id="2587" class="Symbol">{</a> <a id="2589" href="Algebras.Basic.html#7381" class="Field">carrier</a> <a id="2597" class="Symbol">=</a> <a id="2599" class="Symbol">∀</a> <a id="2601" href="Algebras.Products.html#2601" class="Bound">i</a> <a id="2603" class="Symbol">→</a> <a id="2605" href="Algebras.Basic.html#7381" class="Field">carrier</a> <a id="2613" class="Symbol">(</a><a id="2614" href="Algebras.Products.html#2576" class="Bound">𝒜</a> <a id="2616" href="Algebras.Products.html#2601" class="Bound">i</a><a id="2617" class="Symbol">)</a> <a id="2619" class="Symbol">;</a>                 <a id="2637" class="Comment">-- domain</a>
                     <a id="2668" href="Algebras.Basic.html#7400" class="Field">opsymbol</a> <a id="2677" class="Symbol">=</a> <a id="2679" class="Symbol">λ</a> <a id="2681" href="Algebras.Products.html#2681" class="Bound">𝑓</a> <a id="2683" href="Algebras.Products.html#2683" class="Bound">𝑎</a> <a id="2685" href="Algebras.Products.html#2685" class="Bound">i</a> <a id="2687" class="Symbol">→</a> <a id="2689" class="Symbol">(</a><a id="2690" href="Algebras.Basic.html#7400" class="Field">opsymbol</a> <a id="2699" class="Symbol">(</a><a id="2700" href="Algebras.Products.html#2576" class="Bound">𝒜</a> <a id="2702" href="Algebras.Products.html#2685" class="Bound">i</a><a id="2703" class="Symbol">))</a> <a id="2706" href="Algebras.Products.html#2681" class="Bound">𝑓</a> <a id="2708" class="Symbol">λ</a> <a id="2710" href="Algebras.Products.html#2710" class="Bound">x</a> <a id="2712" class="Symbol">→</a> <a id="2714" href="Algebras.Products.html#2683" class="Bound">𝑎</a> <a id="2716" href="Algebras.Products.html#2710" class="Bound">x</a> <a id="2718" href="Algebras.Products.html#2685" class="Bound">i</a> <a id="2720" class="Symbol">}</a> <a id="2722" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3004" href="Algebras.Products.html#3004" class="Function">ov</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3015" class="Symbol">→</a> <a id="3017" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3023" href="Algebras.Products.html#3004" class="Function">ov</a> <a id="3026" href="Algebras.Products.html#3026" class="Bound">α</a> <a id="3028" class="Symbol">=</a> <a id="3030" href="Algebras.Products.html#501" class="Bound">𝓞</a> <a id="3032" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3034" href="Algebras.Products.html#503" class="Bound">𝓥</a> <a id="3036" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3038" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3043" href="Algebras.Products.html#3026" class="Bound">α</a>

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

<a id="4814" class="Keyword">module</a> <a id="4821" href="Algebras.Products.html#4821" class="Module">_</a> <a id="4823" class="Symbol">{</a><a id="4824" href="Algebras.Products.html#4824" class="Bound">𝒦</a> <a id="4826" class="Symbol">:</a> <a id="4828" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4833" class="Symbol">(</a><a id="4834" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="4842" href="Algebras.Products.html#1042" class="Generalizable">α</a> <a id="4844" href="Algebras.Products.html#487" class="Bound">𝑆</a><a id="4845" class="Symbol">)(</a><a id="4847" href="Algebras.Products.html#3004" class="Function">ov</a> <a id="4850" href="Algebras.Products.html#1042" class="Generalizable">α</a><a id="4851" class="Symbol">)}</a> <a id="4854" class="Keyword">where</a>
 <a id="4861" href="Algebras.Products.html#4861" class="Function">ℑ</a> <a id="4863" class="Symbol">:</a> <a id="4865" href="Algebras.Products.html#681" class="Primitive">Type</a> <a id="4870" class="Symbol">(</a><a id="4871" href="Algebras.Products.html#3004" class="Function">ov</a> <a id="4874" href="Algebras.Products.html#4842" class="Bound">α</a><a id="4875" class="Symbol">)</a>
 <a id="4878" href="Algebras.Products.html#4861" class="Function">ℑ</a> <a id="4880" class="Symbol">=</a> <a id="4882" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4885" href="Algebras.Products.html#4885" class="Bound">𝑨</a> <a id="4887" href="Data.Product.html#916" class="Function">∈</a> <a id="4889" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="4897" href="Algebras.Products.html#4842" class="Bound">α</a> <a id="4899" href="Algebras.Products.html#487" class="Bound">𝑆</a> <a id="4901" href="Data.Product.html#916" class="Function">]</a> <a id="4903" href="Algebras.Products.html#4885" class="Bound">𝑨</a> <a id="4905" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4907" href="Algebras.Products.html#4824" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5256" href="Algebras.Products.html#5256" class="Function">𝔄</a> <a id="5258" class="Symbol">:</a> <a id="5260" href="Algebras.Products.html#4861" class="Function">ℑ</a> <a id="5262" class="Symbol">→</a> <a id="5264" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="5272" href="Algebras.Products.html#4842" class="Bound">α</a> <a id="5274" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5277" href="Algebras.Products.html#5256" class="Function">𝔄</a> <a id="5279" href="Algebras.Products.html#5279" class="Bound">i</a> <a id="5281" class="Symbol">=</a> <a id="5283" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="5285" href="Algebras.Products.html#5279" class="Bound">i</a> <a id="5287" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5403" href="Algebras.Products.html#5403" class="Function">class-product</a> <a id="5417" class="Symbol">:</a> <a id="5419" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="5427" class="Symbol">(</a><a id="5428" href="Algebras.Products.html#3004" class="Function">ov</a> <a id="5431" href="Algebras.Products.html#4842" class="Bound">α</a><a id="5432" class="Symbol">)</a> <a id="5434" href="Algebras.Products.html#487" class="Bound">𝑆</a>
 <a id="5437" href="Algebras.Products.html#5403" class="Function">class-product</a> <a id="5451" class="Symbol">=</a> <a id="5453" href="Algebras.Products.html#1808" class="Function">⨅</a> <a id="5455" href="Algebras.Products.html#5256" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

--------------------------------------------

<br>

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
