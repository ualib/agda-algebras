---
layout: default
title : "Algebras.Products module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

### <a id="products-of-algebras-and-product-algebras">Products of Algebras and Product Algebras</a>

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="355" class="Symbol">{-#</a> <a id="359" class="Keyword">OPTIONS</a> <a id="367" class="Pragma">--without-K</a> <a id="379" class="Pragma">--exact-split</a> <a id="393" class="Pragma">--safe</a> <a id="400" class="Symbol">#-}</a>


<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="433" class="Keyword">using</a> <a id="439" class="Symbol">(</a> <a id="441" href="Algebras.Basic.html#1142" class="Generalizable">𝓞</a> <a id="443" class="Symbol">;</a> <a id="445" href="Algebras.Basic.html#1144" class="Generalizable">𝓥</a> <a id="447" class="Symbol">;</a> <a id="449" href="Algebras.Basic.html#3870" class="Function">Signature</a> <a id="459" class="Symbol">)</a>

<a id="462" class="Keyword">module</a> <a id="469" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="487" class="Symbol">{</a><a id="488" href="Algebras.Products.html#488" class="Bound">𝑆</a> <a id="490" class="Symbol">:</a> <a id="492" href="Algebras.Basic.html#3870" class="Function">Signature</a> <a id="502" href="Algebras.Basic.html#1142" class="Generalizable">𝓞</a> <a id="504" href="Algebras.Basic.html#1144" class="Generalizable">𝓥</a><a id="505" class="Symbol">}</a> <a id="507" class="Keyword">where</a>

<a id="514" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="596" class="Keyword">open</a> <a id="601" class="Keyword">import</a> <a id="608" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="624" class="Keyword">using</a> <a id="630" class="Symbol">(</a> <a id="632" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="637" class="Symbol">;</a> <a id="639" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="643" class="Symbol">;</a> <a id="645" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="651" class="Symbol">)</a> <a id="653" class="Keyword">renaming</a> <a id="662" class="Symbol">(</a> <a id="664" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="668" class="Symbol">to</a> <a id="671" class="Primitive">Type</a> <a id="676" class="Symbol">)</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="Data.Product.html" class="Module">Data.Product</a>    <a id="706" class="Keyword">using</a> <a id="712" class="Symbol">(</a> <a id="714" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="718" class="Symbol">;</a> <a id="720" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="722" class="Symbol">;</a> <a id="724" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="733" class="Symbol">)</a>
<a id="735" class="Keyword">open</a> <a id="740" class="Keyword">import</a> <a id="747" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="763" class="Keyword">using</a> <a id="769" class="Symbol">(</a> <a id="771" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="776" class="Symbol">;</a> <a id="778" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="782" class="Symbol">;</a> <a id="784" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="788" class="Symbol">)</a>

<a id="791" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="873" class="Keyword">open</a> <a id="878" class="Keyword">import</a> <a id="885" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="908" class="Keyword">using</a> <a id="914" class="Symbol">(</a><a id="915" href="Overture.Preliminaries.html#5082" class="Function Operator">_⁻¹</a><a id="918" class="Symbol">;</a> <a id="920" href="Overture.Preliminaries.html#5479" class="Function">𝑖𝑑</a><a id="922" class="Symbol">;</a> <a id="924" href="Overture.Preliminaries.html#4379" class="Function Operator">∣_∣</a><a id="927" class="Symbol">;</a> <a id="929" href="Overture.Preliminaries.html#4417" class="Function Operator">∥_∥</a><a id="932" class="Symbol">)</a>
<a id="934" class="Keyword">open</a> <a id="939" class="Keyword">import</a> <a id="946" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>         <a id="969" class="Keyword">using</a> <a id="975" class="Symbol">(</a> <a id="977" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="985" class="Symbol">;</a> <a id="987" href="Algebras.Basic.html#9409" class="Function Operator">_̂_</a> <a id="991" class="Symbol">;</a> <a id="993" href="Algebras.Basic.html#8343" class="Record">algebra</a> <a id="1001" class="Symbol">)</a>

<a id="1004" class="Keyword">private</a> <a id="1012" class="Keyword">variable</a> <a id="1021" href="Algebras.Products.html#1021" class="Generalizable">α</a> <a id="1023" href="Algebras.Products.html#1023" class="Generalizable">β</a> <a id="1025" href="Algebras.Products.html#1025" class="Generalizable">ρ</a> <a id="1027" href="Algebras.Products.html#1027" class="Generalizable">𝓘</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [agda-algebras](https://github.com/ualib/agda-algebras) library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1869" href="Algebras.Products.html#1869" class="Function">⨅</a> <a id="1871" class="Symbol">:</a> <a id="1873" class="Symbol">{</a><a id="1874" href="Algebras.Products.html#1874" class="Bound">I</a> <a id="1876" class="Symbol">:</a> <a id="1878" href="Algebras.Products.html#671" class="Primitive">Type</a> <a id="1883" href="Algebras.Products.html#1027" class="Generalizable">𝓘</a> <a id="1885" class="Symbol">}(</a><a id="1887" href="Algebras.Products.html#1887" class="Bound">𝒜</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="Algebras.Products.html#1874" class="Bound">I</a> <a id="1893" class="Symbol">→</a> <a id="1895" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="1903" href="Algebras.Products.html#1021" class="Generalizable">α</a> <a id="1905" href="Algebras.Products.html#488" class="Bound">𝑆</a> <a id="1907" class="Symbol">)</a> <a id="1909" class="Symbol">→</a> <a id="1911" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="1919" class="Symbol">(</a><a id="1920" href="Algebras.Products.html#1027" class="Generalizable">𝓘</a> <a id="1922" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1924" href="Algebras.Products.html#1021" class="Generalizable">α</a><a id="1925" class="Symbol">)</a> <a id="1927" href="Algebras.Products.html#488" class="Bound">𝑆</a>

<a id="1930" href="Algebras.Products.html#1869" class="Function">⨅</a> <a id="1932" class="Symbol">{</a><a id="1933" class="Argument">I</a> <a id="1935" class="Symbol">=</a> <a id="1937" href="Algebras.Products.html#1937" class="Bound">I</a><a id="1938" class="Symbol">}</a> <a id="1940" href="Algebras.Products.html#1940" class="Bound">𝒜</a> <a id="1942" class="Symbol">=</a> <a id="1944" class="Symbol">(</a> <a id="1946" class="Symbol">∀</a> <a id="1948" class="Symbol">(</a><a id="1949" href="Algebras.Products.html#1949" class="Bound">i</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="Algebras.Products.html#1937" class="Bound">I</a><a id="1954" class="Symbol">)</a> <a id="1956" class="Symbol">→</a> <a id="1958" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a> <a id="1960" href="Algebras.Products.html#1940" class="Bound">𝒜</a> <a id="1962" href="Algebras.Products.html#1949" class="Bound">i</a> <a id="1964" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a> <a id="1966" class="Symbol">)</a> <a id="1968" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="1980" class="Comment">-- domain of the product algebra</a>
               <a id="2028" class="Symbol">λ</a> <a id="2030" href="Algebras.Products.html#2030" class="Bound">𝑓</a> <a id="2032" href="Algebras.Products.html#2032" class="Bound">𝑎</a> <a id="2034" href="Algebras.Products.html#2034" class="Bound">i</a> <a id="2036" class="Symbol">→</a> <a id="2038" class="Symbol">(</a><a id="2039" href="Algebras.Products.html#2030" class="Bound">𝑓</a> <a id="2041" href="Algebras.Basic.html#9409" class="Function Operator">̂</a> <a id="2043" href="Algebras.Products.html#1940" class="Bound">𝒜</a> <a id="2045" href="Algebras.Products.html#2034" class="Bound">i</a><a id="2046" class="Symbol">)</a> <a id="2048" class="Symbol">λ</a> <a id="2050" href="Algebras.Products.html#2050" class="Bound">x</a> <a id="2052" class="Symbol">→</a> <a id="2054" href="Algebras.Products.html#2032" class="Bound">𝑎</a> <a id="2056" href="Algebras.Products.html#2050" class="Bound">x</a> <a id="2058" href="Algebras.Products.html#2034" class="Bound">i</a>   <a id="2062" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [agda-algebras](https://github.com/ualib/agda-algebras) library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2590" class="Keyword">open</a> <a id="2595" href="Algebras.Basic.html#8343" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2604" href="Algebras.Products.html#2604" class="Function">⨅&#39;</a> <a id="2607" class="Symbol">:</a> <a id="2609" class="Symbol">{</a><a id="2610" href="Algebras.Products.html#2610" class="Bound">I</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="Algebras.Products.html#671" class="Primitive">Type</a> <a id="2619" href="Algebras.Products.html#1027" class="Generalizable">𝓘</a> <a id="2621" class="Symbol">}(</a><a id="2623" href="Algebras.Products.html#2623" class="Bound">𝒜</a> <a id="2625" class="Symbol">:</a> <a id="2627" href="Algebras.Products.html#2610" class="Bound">I</a> <a id="2629" class="Symbol">→</a> <a id="2631" href="Algebras.Basic.html#8343" class="Record">algebra</a> <a id="2639" href="Algebras.Products.html#1021" class="Generalizable">α</a> <a id="2641" href="Algebras.Products.html#488" class="Bound">𝑆</a><a id="2642" class="Symbol">)</a> <a id="2644" class="Symbol">→</a> <a id="2646" href="Algebras.Basic.html#8343" class="Record">algebra</a> <a id="2654" class="Symbol">(</a><a id="2655" href="Algebras.Products.html#1027" class="Generalizable">𝓘</a> <a id="2657" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2659" href="Algebras.Products.html#1021" class="Generalizable">α</a><a id="2660" class="Symbol">)</a> <a id="2662" href="Algebras.Products.html#488" class="Bound">𝑆</a>

<a id="2665" href="Algebras.Products.html#2604" class="Function">⨅&#39;</a> <a id="2668" class="Symbol">{</a><a id="2669" href="Algebras.Products.html#2669" class="Bound">I</a><a id="2670" class="Symbol">}</a> <a id="2672" href="Algebras.Products.html#2672" class="Bound">𝒜</a> <a id="2674" class="Symbol">=</a> <a id="2676" class="Keyword">record</a> <a id="2683" class="Symbol">{</a> <a id="2685" href="Algebras.Basic.html#8441" class="Field">carrier</a> <a id="2693" class="Symbol">=</a> <a id="2695" class="Symbol">∀</a> <a id="2697" href="Algebras.Products.html#2697" class="Bound">i</a> <a id="2699" class="Symbol">→</a> <a id="2701" href="Algebras.Basic.html#8441" class="Field">carrier</a> <a id="2709" class="Symbol">(</a><a id="2710" href="Algebras.Products.html#2672" class="Bound">𝒜</a> <a id="2712" href="Algebras.Products.html#2697" class="Bound">i</a><a id="2713" class="Symbol">)</a> <a id="2715" class="Symbol">;</a>                 <a id="2733" class="Comment">-- domain</a>
                     <a id="2764" href="Algebras.Basic.html#8460" class="Field">opsymbol</a> <a id="2773" class="Symbol">=</a> <a id="2775" class="Symbol">λ</a> <a id="2777" href="Algebras.Products.html#2777" class="Bound">𝑓</a> <a id="2779" href="Algebras.Products.html#2779" class="Bound">𝑎</a> <a id="2781" href="Algebras.Products.html#2781" class="Bound">i</a> <a id="2783" class="Symbol">→</a> <a id="2785" class="Symbol">(</a><a id="2786" href="Algebras.Basic.html#8460" class="Field">opsymbol</a> <a id="2795" class="Symbol">(</a><a id="2796" href="Algebras.Products.html#2672" class="Bound">𝒜</a> <a id="2798" href="Algebras.Products.html#2781" class="Bound">i</a><a id="2799" class="Symbol">))</a> <a id="2802" href="Algebras.Products.html#2777" class="Bound">𝑓</a> <a id="2804" class="Symbol">λ</a> <a id="2806" href="Algebras.Products.html#2806" class="Bound">x</a> <a id="2808" class="Symbol">→</a> <a id="2810" href="Algebras.Products.html#2779" class="Bound">𝑎</a> <a id="2812" href="Algebras.Products.html#2806" class="Bound">x</a> <a id="2814" href="Algebras.Products.html#2781" class="Bound">i</a> <a id="2816" class="Symbol">}</a> <a id="2818" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [agda-algebras](https://github.com/ualib/agda-algebras) library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3135" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="3138" class="Symbol">:</a> <a id="3140" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3146" class="Symbol">→</a> <a id="3148" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3154" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="3157" href="Algebras.Products.html#3157" class="Bound">α</a> <a id="3159" class="Symbol">=</a> <a id="3161" href="Algebras.Products.html#502" class="Bound">𝓞</a> <a id="3163" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3165" href="Algebras.Products.html#504" class="Bound">𝓥</a> <a id="3167" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3169" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3174" href="Algebras.Products.html#3157" class="Bound">α</a>

</pre>



### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra α 𝑆`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred (Algebra α 𝑆) β`, for some type `β`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not what we want.  For recall that `Pred (Algebra α 𝑆) β` is just an alias for the function type `Algebra α 𝑆 → Type β`, and the semantics of the latter takes `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α 𝑆) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α 𝑆` belongs to `𝒦`.  Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra α 𝑆` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.

<pre class="Agda">

<a id="4862" class="Keyword">module</a> <a id="4869" href="Algebras.Products.html#4869" class="Module">_</a> <a id="4871" class="Symbol">{</a><a id="4872" href="Algebras.Products.html#4872" class="Bound">𝒦</a> <a id="4874" class="Symbol">:</a> <a id="4876" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4881" class="Symbol">(</a><a id="4882" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="4890" href="Algebras.Products.html#1021" class="Generalizable">α</a> <a id="4892" href="Algebras.Products.html#488" class="Bound">𝑆</a><a id="4893" class="Symbol">)(</a><a id="4895" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="4898" href="Algebras.Products.html#1021" class="Generalizable">α</a><a id="4899" class="Symbol">)}</a> <a id="4902" class="Keyword">where</a>
 <a id="4909" href="Algebras.Products.html#4909" class="Function">ℑ</a> <a id="4911" class="Symbol">:</a> <a id="4913" href="Algebras.Products.html#671" class="Primitive">Type</a> <a id="4918" class="Symbol">(</a><a id="4919" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="4922" href="Algebras.Products.html#4890" class="Bound">α</a><a id="4923" class="Symbol">)</a>
 <a id="4926" href="Algebras.Products.html#4909" class="Function">ℑ</a> <a id="4928" class="Symbol">=</a> <a id="4930" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4933" href="Algebras.Products.html#4933" class="Bound">𝑨</a> <a id="4935" href="Data.Product.html#916" class="Function">∈</a> <a id="4937" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="4945" href="Algebras.Products.html#4890" class="Bound">α</a> <a id="4947" href="Algebras.Products.html#488" class="Bound">𝑆</a> <a id="4949" href="Data.Product.html#916" class="Function">]</a> <a id="4951" href="Algebras.Products.html#4933" class="Bound">𝑨</a> <a id="4953" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4955" href="Algebras.Products.html#4872" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5304" href="Algebras.Products.html#5304" class="Function">𝔄</a> <a id="5306" class="Symbol">:</a> <a id="5308" href="Algebras.Products.html#4909" class="Function">ℑ</a> <a id="5310" class="Symbol">→</a> <a id="5312" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="5320" href="Algebras.Products.html#4890" class="Bound">α</a> <a id="5322" href="Algebras.Products.html#488" class="Bound">𝑆</a>
 <a id="5325" href="Algebras.Products.html#5304" class="Function">𝔄</a> <a id="5327" href="Algebras.Products.html#5327" class="Bound">i</a> <a id="5329" class="Symbol">=</a> <a id="5331" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a> <a id="5333" href="Algebras.Products.html#5327" class="Bound">i</a> <a id="5335" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5451" href="Algebras.Products.html#5451" class="Function">class-product</a> <a id="5465" class="Symbol">:</a> <a id="5467" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="5475" class="Symbol">(</a><a id="5476" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="5479" href="Algebras.Products.html#4890" class="Bound">α</a><a id="5480" class="Symbol">)</a> <a id="5482" href="Algebras.Products.html#488" class="Bound">𝑆</a>
 <a id="5485" href="Algebras.Products.html#5451" class="Function">class-product</a> <a id="5499" class="Symbol">=</a> <a id="5501" href="Algebras.Products.html#1869" class="Function">⨅</a> <a id="5503" href="Algebras.Products.html#5304" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Algebras.Basic](Algebras.Basic.html)</span>
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
