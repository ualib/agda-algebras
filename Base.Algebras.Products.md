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


<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="448" class="Keyword">using</a> <a id="454" class="Symbol">(</a> <a id="456" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓞</a> <a id="458" class="Symbol">;</a> <a id="460" href="Base.Algebras.Basic.html#1164" class="Generalizable">𝓥</a> <a id="462" class="Symbol">;</a> <a id="464" href="Base.Algebras.Basic.html#3890" class="Function">Signature</a> <a id="474" class="Symbol">)</a>

<a id="477" class="Keyword">module</a> <a id="484" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a> <a id="507" class="Symbol">{</a><a id="508" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a> <a id="510" class="Symbol">:</a> <a id="512" href="Base.Algebras.Basic.html#3890" class="Function">Signature</a> <a id="522" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓞</a> <a id="524" href="Base.Algebras.Basic.html#1164" class="Generalizable">𝓥</a><a id="525" class="Symbol">}</a> <a id="527" class="Keyword">where</a>

<a id="534" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="644" class="Keyword">using</a> <a id="650" class="Symbol">(</a> <a id="652" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="657" class="Symbol">;</a> <a id="659" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="663" class="Symbol">;</a> <a id="665" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="671" class="Symbol">)</a> <a id="673" class="Keyword">renaming</a> <a id="682" class="Symbol">(</a> <a id="684" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="688" class="Symbol">to</a> <a id="691" class="Primitive">Type</a> <a id="696" class="Symbol">)</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="Data.Product.html" class="Module">Data.Product</a>    <a id="726" class="Keyword">using</a> <a id="732" class="Symbol">(</a> <a id="734" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="738" class="Symbol">;</a> <a id="740" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="742" class="Symbol">;</a> <a id="744" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="753" class="Symbol">)</a>
<a id="755" class="Keyword">open</a> <a id="760" class="Keyword">import</a> <a id="767" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="783" class="Keyword">using</a> <a id="789" class="Symbol">(</a> <a id="791" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="796" class="Symbol">;</a> <a id="798" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="802" class="Symbol">;</a> <a id="804" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="808" class="Symbol">)</a>

<a id="811" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="893" class="Keyword">open</a> <a id="898" class="Keyword">import</a> <a id="905" href="Base.Overture.Preliminaries.html" class="Module">Base.Overture.Preliminaries</a> <a id="933" class="Keyword">using</a> <a id="939" class="Symbol">(</a><a id="940" href="Base.Overture.Preliminaries.html#4995" class="Function Operator">_⁻¹</a><a id="943" class="Symbol">;</a> <a id="945" href="Base.Overture.Preliminaries.html#5394" class="Function">𝑖𝑑</a><a id="947" class="Symbol">;</a> <a id="949" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣_∣</a><a id="952" class="Symbol">;</a> <a id="954" href="Base.Overture.Preliminaries.html#4440" class="Function Operator">∥_∥</a><a id="957" class="Symbol">)</a>
<a id="959" class="Keyword">open</a> <a id="964" class="Keyword">import</a> <a id="971" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>         <a id="999" class="Keyword">using</a> <a id="1005" class="Symbol">(</a> <a id="1007" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="1015" class="Symbol">;</a> <a id="1017" href="Base.Algebras.Basic.html#9366" class="Function Operator">_̂_</a> <a id="1021" class="Symbol">;</a> <a id="1023" href="Base.Algebras.Basic.html#8300" class="Record">algebra</a> <a id="1031" class="Symbol">)</a>

<a id="1034" class="Keyword">private</a> <a id="1042" class="Keyword">variable</a> <a id="1051" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a> <a id="1053" href="Base.Algebras.Products.html#1053" class="Generalizable">β</a> <a id="1055" href="Base.Algebras.Products.html#1055" class="Generalizable">ρ</a> <a id="1057" href="Base.Algebras.Products.html#1057" class="Generalizable">𝓘</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the [agda-algebras](https://github.com/ualib/agda-algebras) library will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1899" href="Base.Algebras.Products.html#1899" class="Function">⨅</a> <a id="1901" class="Symbol">:</a> <a id="1903" class="Symbol">{</a><a id="1904" href="Base.Algebras.Products.html#1904" class="Bound">I</a> <a id="1906" class="Symbol">:</a> <a id="1908" href="Base.Algebras.Products.html#691" class="Primitive">Type</a> <a id="1913" href="Base.Algebras.Products.html#1057" class="Generalizable">𝓘</a> <a id="1915" class="Symbol">}(</a><a id="1917" href="Base.Algebras.Products.html#1917" class="Bound">𝒜</a> <a id="1919" class="Symbol">:</a> <a id="1921" href="Base.Algebras.Products.html#1904" class="Bound">I</a> <a id="1923" class="Symbol">→</a> <a id="1925" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="1933" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a> <a id="1935" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a> <a id="1937" class="Symbol">)</a> <a id="1939" class="Symbol">→</a> <a id="1941" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="1949" class="Symbol">(</a><a id="1950" href="Base.Algebras.Products.html#1057" class="Generalizable">𝓘</a> <a id="1952" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1954" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a><a id="1955" class="Symbol">)</a> <a id="1957" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a>

<a id="1960" href="Base.Algebras.Products.html#1899" class="Function">⨅</a> <a id="1962" class="Symbol">{</a><a id="1963" class="Argument">I</a> <a id="1965" class="Symbol">=</a> <a id="1967" href="Base.Algebras.Products.html#1967" class="Bound">I</a><a id="1968" class="Symbol">}</a> <a id="1970" href="Base.Algebras.Products.html#1970" class="Bound">𝒜</a> <a id="1972" class="Symbol">=</a> <a id="1974" class="Symbol">(</a> <a id="1976" class="Symbol">∀</a> <a id="1978" class="Symbol">(</a><a id="1979" href="Base.Algebras.Products.html#1979" class="Bound">i</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="Base.Algebras.Products.html#1967" class="Bound">I</a><a id="1984" class="Symbol">)</a> <a id="1986" class="Symbol">→</a> <a id="1988" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a> <a id="1990" href="Base.Algebras.Products.html#1970" class="Bound">𝒜</a> <a id="1992" href="Base.Algebras.Products.html#1979" class="Bound">i</a> <a id="1994" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a> <a id="1996" class="Symbol">)</a> <a id="1998" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>           <a id="2010" class="Comment">-- domain of the product algebra</a>
               <a id="2058" class="Symbol">λ</a> <a id="2060" href="Base.Algebras.Products.html#2060" class="Bound">𝑓</a> <a id="2062" href="Base.Algebras.Products.html#2062" class="Bound">𝑎</a> <a id="2064" href="Base.Algebras.Products.html#2064" class="Bound">i</a> <a id="2066" class="Symbol">→</a> <a id="2068" class="Symbol">(</a><a id="2069" href="Base.Algebras.Products.html#2060" class="Bound">𝑓</a> <a id="2071" href="Base.Algebras.Basic.html#9366" class="Function Operator">̂</a> <a id="2073" href="Base.Algebras.Products.html#1970" class="Bound">𝒜</a> <a id="2075" href="Base.Algebras.Products.html#2064" class="Bound">i</a><a id="2076" class="Symbol">)</a> <a id="2078" class="Symbol">λ</a> <a id="2080" href="Base.Algebras.Products.html#2080" class="Bound">x</a> <a id="2082" class="Symbol">→</a> <a id="2084" href="Base.Algebras.Products.html#2062" class="Bound">𝑎</a> <a id="2086" href="Base.Algebras.Products.html#2080" class="Bound">x</a> <a id="2088" href="Base.Algebras.Products.html#2064" class="Bound">i</a>   <a id="2092" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [agda-algebras](https://github.com/ualib/agda-algebras) library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

<a id="2620" class="Keyword">open</a> <a id="2625" href="Base.Algebras.Basic.html#8300" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2634" href="Base.Algebras.Products.html#2634" class="Function">⨅&#39;</a> <a id="2637" class="Symbol">:</a> <a id="2639" class="Symbol">{</a><a id="2640" href="Base.Algebras.Products.html#2640" class="Bound">I</a> <a id="2642" class="Symbol">:</a> <a id="2644" href="Base.Algebras.Products.html#691" class="Primitive">Type</a> <a id="2649" href="Base.Algebras.Products.html#1057" class="Generalizable">𝓘</a> <a id="2651" class="Symbol">}(</a><a id="2653" href="Base.Algebras.Products.html#2653" class="Bound">𝒜</a> <a id="2655" class="Symbol">:</a> <a id="2657" href="Base.Algebras.Products.html#2640" class="Bound">I</a> <a id="2659" class="Symbol">→</a> <a id="2661" href="Base.Algebras.Basic.html#8300" class="Record">algebra</a> <a id="2669" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a> <a id="2671" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a><a id="2672" class="Symbol">)</a> <a id="2674" class="Symbol">→</a> <a id="2676" href="Base.Algebras.Basic.html#8300" class="Record">algebra</a> <a id="2684" class="Symbol">(</a><a id="2685" href="Base.Algebras.Products.html#1057" class="Generalizable">𝓘</a> <a id="2687" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2689" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a><a id="2690" class="Symbol">)</a> <a id="2692" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a>

<a id="2695" href="Base.Algebras.Products.html#2634" class="Function">⨅&#39;</a> <a id="2698" class="Symbol">{</a><a id="2699" href="Base.Algebras.Products.html#2699" class="Bound">I</a><a id="2700" class="Symbol">}</a> <a id="2702" href="Base.Algebras.Products.html#2702" class="Bound">𝒜</a> <a id="2704" class="Symbol">=</a> <a id="2706" class="Keyword">record</a> <a id="2713" class="Symbol">{</a> <a id="2715" href="Base.Algebras.Basic.html#8398" class="Field">carrier</a> <a id="2723" class="Symbol">=</a> <a id="2725" class="Symbol">∀</a> <a id="2727" href="Base.Algebras.Products.html#2727" class="Bound">i</a> <a id="2729" class="Symbol">→</a> <a id="2731" href="Base.Algebras.Basic.html#8398" class="Field">carrier</a> <a id="2739" class="Symbol">(</a><a id="2740" href="Base.Algebras.Products.html#2702" class="Bound">𝒜</a> <a id="2742" href="Base.Algebras.Products.html#2727" class="Bound">i</a><a id="2743" class="Symbol">)</a> <a id="2745" class="Symbol">;</a>                 <a id="2763" class="Comment">-- domain</a>
                     <a id="2794" href="Base.Algebras.Basic.html#8417" class="Field">opsymbol</a> <a id="2803" class="Symbol">=</a> <a id="2805" class="Symbol">λ</a> <a id="2807" href="Base.Algebras.Products.html#2807" class="Bound">𝑓</a> <a id="2809" href="Base.Algebras.Products.html#2809" class="Bound">𝑎</a> <a id="2811" href="Base.Algebras.Products.html#2811" class="Bound">i</a> <a id="2813" class="Symbol">→</a> <a id="2815" class="Symbol">(</a><a id="2816" href="Base.Algebras.Basic.html#8417" class="Field">opsymbol</a> <a id="2825" class="Symbol">(</a><a id="2826" href="Base.Algebras.Products.html#2702" class="Bound">𝒜</a> <a id="2828" href="Base.Algebras.Products.html#2811" class="Bound">i</a><a id="2829" class="Symbol">))</a> <a id="2832" href="Base.Algebras.Products.html#2807" class="Bound">𝑓</a> <a id="2834" class="Symbol">λ</a> <a id="2836" href="Base.Algebras.Products.html#2836" class="Bound">x</a> <a id="2838" class="Symbol">→</a> <a id="2840" href="Base.Algebras.Products.html#2809" class="Bound">𝑎</a> <a id="2842" href="Base.Algebras.Products.html#2836" class="Bound">x</a> <a id="2844" href="Base.Algebras.Products.html#2811" class="Bound">i</a> <a id="2846" class="Symbol">}</a> <a id="2848" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [agda-algebras](https://github.com/ualib/agda-algebras) library that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3165" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="3168" class="Symbol">:</a> <a id="3170" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3176" class="Symbol">→</a> <a id="3178" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3184" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="3187" href="Base.Algebras.Products.html#3187" class="Bound">α</a> <a id="3189" class="Symbol">=</a> <a id="3191" href="Base.Algebras.Products.html#522" class="Bound">𝓞</a> <a id="3193" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3195" href="Base.Algebras.Products.html#524" class="Bound">𝓥</a> <a id="3197" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3199" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3204" href="Base.Algebras.Products.html#3187" class="Bound">α</a>

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

<a id="4892" class="Keyword">module</a> <a id="4899" href="Base.Algebras.Products.html#4899" class="Module">_</a> <a id="4901" class="Symbol">{</a><a id="4902" href="Base.Algebras.Products.html#4902" class="Bound">𝒦</a> <a id="4904" class="Symbol">:</a> <a id="4906" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4911" class="Symbol">(</a><a id="4912" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="4920" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a> <a id="4922" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a><a id="4923" class="Symbol">)(</a><a id="4925" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="4928" href="Base.Algebras.Products.html#1051" class="Generalizable">α</a><a id="4929" class="Symbol">)}</a> <a id="4932" class="Keyword">where</a>
 <a id="4939" href="Base.Algebras.Products.html#4939" class="Function">ℑ</a> <a id="4941" class="Symbol">:</a> <a id="4943" href="Base.Algebras.Products.html#691" class="Primitive">Type</a> <a id="4948" class="Symbol">(</a><a id="4949" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="4952" href="Base.Algebras.Products.html#4920" class="Bound">α</a><a id="4953" class="Symbol">)</a>
 <a id="4956" href="Base.Algebras.Products.html#4939" class="Function">ℑ</a> <a id="4958" class="Symbol">=</a> <a id="4960" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4963" href="Base.Algebras.Products.html#4963" class="Bound">𝑨</a> <a id="4965" href="Data.Product.html#916" class="Function">∈</a> <a id="4967" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="4975" href="Base.Algebras.Products.html#4920" class="Bound">α</a> <a id="4977" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a> <a id="4979" href="Data.Product.html#916" class="Function">]</a> <a id="4981" href="Base.Algebras.Products.html#4963" class="Bound">𝑨</a> <a id="4983" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4985" href="Base.Algebras.Products.html#4902" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5334" href="Base.Algebras.Products.html#5334" class="Function">𝔄</a> <a id="5336" class="Symbol">:</a> <a id="5338" href="Base.Algebras.Products.html#4939" class="Function">ℑ</a> <a id="5340" class="Symbol">→</a> <a id="5342" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="5350" href="Base.Algebras.Products.html#4920" class="Bound">α</a> <a id="5352" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a>
 <a id="5355" href="Base.Algebras.Products.html#5334" class="Function">𝔄</a> <a id="5357" href="Base.Algebras.Products.html#5357" class="Bound">i</a> <a id="5359" class="Symbol">=</a> <a id="5361" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a> <a id="5363" href="Base.Algebras.Products.html#5357" class="Bound">i</a> <a id="5365" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5481" href="Base.Algebras.Products.html#5481" class="Function">class-product</a> <a id="5495" class="Symbol">:</a> <a id="5497" href="Base.Algebras.Basic.html#6259" class="Function">Algebra</a> <a id="5505" class="Symbol">(</a><a id="5506" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="5509" href="Base.Algebras.Products.html#4920" class="Bound">α</a><a id="5510" class="Symbol">)</a> <a id="5512" href="Base.Algebras.Products.html#508" class="Bound">𝑆</a>
 <a id="5515" href="Base.Algebras.Products.html#5481" class="Function">class-product</a> <a id="5529" class="Symbol">=</a> <a id="5531" href="Base.Algebras.Products.html#1899" class="Function">⨅</a> <a id="5533" href="Base.Algebras.Products.html#5334" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Base.Algebras.Basic](Base.Algebras.Basic.html)</span>
<span style="float:right;">[Base.Algebras.Congruences →](Base.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
