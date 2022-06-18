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

<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="Overture.html" class="Module">Overture</a> <a id="436" class="Keyword">using</a> <a id="442" class="Symbol">(</a> <a id="444" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="446" class="Symbol">;</a> <a id="448" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a> <a id="450" class="Symbol">;</a> <a id="452" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="462" class="Symbol">)</a>

<a id="465" class="Keyword">module</a> <a id="472" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a> <a id="495" class="Symbol">{</a><a id="496" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a> <a id="498" class="Symbol">:</a> <a id="500" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="510" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="512" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a><a id="513" class="Symbol">}</a> <a id="515" class="Keyword">where</a>

<a id="522" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="604" class="Keyword">open</a> <a id="609" class="Keyword">import</a> <a id="616" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="632" class="Keyword">using</a> <a id="638" class="Symbol">()</a> <a id="641" class="Keyword">renaming</a> <a id="650" class="Symbol">(</a> <a id="652" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="656" class="Symbol">to</a> <a id="659" class="Primitive">Type</a> <a id="664" class="Symbol">)</a>
<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="Data.Product.html" class="Module">Data.Product</a>    <a id="694" class="Keyword">using</a> <a id="700" class="Symbol">(</a> <a id="702" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="706" class="Symbol">;</a> <a id="708" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="710" class="Symbol">;</a> <a id="712" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="721" class="Symbol">)</a>
<a id="723" class="Keyword">open</a> <a id="728" class="Keyword">import</a> <a id="735" href="Level.html" class="Module">Level</a>           <a id="751" class="Keyword">using</a> <a id="757" class="Symbol">(</a> <a id="759" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="765" class="Symbol">;</a> <a id="767" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="771" class="Symbol">;</a> <a id="773" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="777" class="Symbol">)</a>
<a id="779" class="Keyword">open</a> <a id="784" class="Keyword">import</a> <a id="791" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="807" class="Keyword">using</a> <a id="813" class="Symbol">(</a> <a id="815" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="820" class="Symbol">;</a> <a id="822" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="826" class="Symbol">;</a> <a id="828" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="832" class="Symbol">)</a>

<a id="835" class="Comment">-- Imports from agda-algebras ---------------------------------------------------</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="Overture.html" class="Module">Overture</a>                     <a id="958" class="Keyword">using</a> <a id="964" class="Symbol">(</a><a id="965" href="Overture.Basic.html#4897" class="Function Operator">_⁻¹</a><a id="968" class="Symbol">;</a> <a id="970" href="Overture.Basic.html#5296" class="Function">𝑖𝑑</a><a id="972" class="Symbol">;</a> <a id="974" href="Overture.Basic.html#4303" class="Function Operator">∣_∣</a><a id="977" class="Symbol">;</a> <a id="979" href="Overture.Basic.html#4341" class="Function Operator">∥_∥</a><a id="982" class="Symbol">)</a>
<a id="984" class="Keyword">open</a> <a id="989" class="Keyword">import</a> <a id="996" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="1016" class="Symbol">{</a><a id="1017" class="Argument">𝑆</a> <a id="1019" class="Symbol">=</a> <a id="1021" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a><a id="1022" class="Symbol">}</a>  <a id="1025" class="Keyword">using</a> <a id="1031" class="Symbol">(</a> <a id="1033" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="1041" class="Symbol">;</a> <a id="1043" href="Base.Algebras.Basic.html#6152" class="Function Operator">_̂_</a> <a id="1047" class="Symbol">;</a> <a id="1049" href="Base.Algebras.Basic.html#5089" class="Record">algebra</a> <a id="1057" class="Symbol">)</a>

<a id="1060" class="Keyword">private</a> <a id="1068" class="Keyword">variable</a> <a id="1077" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="1079" href="Base.Algebras.Products.html#1079" class="Generalizable">β</a> <a id="1081" href="Base.Algebras.Products.html#1081" class="Generalizable">ρ</a> <a id="1083" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1085" class="Symbol">:</a> <a id="1087" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

From now on, the modules of the
[agda-algebras](https://github.com/ualib/agda-algebras) library will assume a
fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I :
Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the algebra
whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the
algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary
operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such
that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 :=
(i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product
of* `𝑆`-*algebras* is represented by the following type.

<pre class="Agda">

<a id="⨅"></a><a id="1925" href="Base.Algebras.Products.html#1925" class="Function">⨅</a> <a id="1927" class="Symbol">:</a> <a id="1929" class="Symbol">{</a><a id="1930" href="Base.Algebras.Products.html#1930" class="Bound">I</a> <a id="1932" class="Symbol">:</a> <a id="1934" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="1939" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1941" class="Symbol">}(</a><a id="1943" href="Base.Algebras.Products.html#1943" class="Bound">𝒜</a> <a id="1945" class="Symbol">:</a> <a id="1947" href="Base.Algebras.Products.html#1930" class="Bound">I</a> <a id="1949" class="Symbol">→</a> <a id="1951" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="1959" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="1961" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a> <a id="1963" class="Symbol">)</a> <a id="1965" class="Symbol">→</a> <a id="1967" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="1975" class="Symbol">(</a><a id="1976" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="1978" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1980" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="1981" class="Symbol">)</a> <a id="1983" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a>

<a id="1986" href="Base.Algebras.Products.html#1925" class="Function">⨅</a> <a id="1988" class="Symbol">{</a><a id="1989" class="Argument">I</a> <a id="1991" class="Symbol">=</a> <a id="1993" href="Base.Algebras.Products.html#1993" class="Bound">I</a><a id="1994" class="Symbol">}</a> <a id="1996" href="Base.Algebras.Products.html#1996" class="Bound">𝒜</a> <a id="1998" class="Symbol">=</a>  <a id="2001" class="Symbol">(</a> <a id="2003" class="Symbol">∀</a> <a id="2005" class="Symbol">(</a><a id="2006" href="Base.Algebras.Products.html#2006" class="Bound">i</a> <a id="2008" class="Symbol">:</a> <a id="2010" href="Base.Algebras.Products.html#1993" class="Bound">I</a><a id="2011" class="Symbol">)</a> <a id="2013" class="Symbol">→</a> <a id="2015" href="Overture.Basic.html#4303" class="Function Operator">∣</a> <a id="2017" href="Base.Algebras.Products.html#1996" class="Bound">𝒜</a> <a id="2019" href="Base.Algebras.Products.html#2006" class="Bound">i</a> <a id="2021" href="Overture.Basic.html#4303" class="Function Operator">∣</a> <a id="2023" class="Symbol">)</a> <a id="2025" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>        <a id="2034" class="Comment">-- domain of the product algebra</a>
                <a id="2083" class="Symbol">λ</a> <a id="2085" href="Base.Algebras.Products.html#2085" class="Bound">𝑓</a> <a id="2087" href="Base.Algebras.Products.html#2087" class="Bound">𝑎</a> <a id="2089" href="Base.Algebras.Products.html#2089" class="Bound">i</a> <a id="2091" class="Symbol">→</a> <a id="2093" class="Symbol">(</a><a id="2094" href="Base.Algebras.Products.html#2085" class="Bound">𝑓</a> <a id="2096" href="Base.Algebras.Basic.html#6152" class="Function Operator">̂</a> <a id="2098" href="Base.Algebras.Products.html#1996" class="Bound">𝒜</a> <a id="2100" href="Base.Algebras.Products.html#2089" class="Bound">i</a><a id="2101" class="Symbol">)</a> <a id="2103" class="Symbol">λ</a> <a id="2105" href="Base.Algebras.Products.html#2105" class="Bound">x</a> <a id="2107" class="Symbol">→</a> <a id="2109" href="Base.Algebras.Products.html#2087" class="Bound">𝑎</a> <a id="2111" href="Base.Algebras.Products.html#2105" class="Bound">x</a> <a id="2113" href="Base.Algebras.Products.html#2089" class="Bound">i</a>  <a id="2116" class="Comment">-- basic operations of the product algebra</a>

</pre>

The type just defined is the one that will be used throughout the
[agda-algebras](https://github.com/ualib/agda-algebras) library whenever the
product of an indexed collection of algebras (of type `Algebra`) is required.
However, for the sake of completeness, here is how one could define a type
representing the product of algebras inhabiting the record type `algebra`. 

<pre class="Agda">

<a id="2559" class="Keyword">open</a> <a id="2564" href="Base.Algebras.Basic.html#5089" class="Module">algebra</a>

<a id="⨅&#39;"></a><a id="2573" href="Base.Algebras.Products.html#2573" class="Function">⨅&#39;</a> <a id="2576" class="Symbol">:</a> <a id="2578" class="Symbol">{</a><a id="2579" href="Base.Algebras.Products.html#2579" class="Bound">I</a> <a id="2581" class="Symbol">:</a> <a id="2583" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="2588" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="2590" class="Symbol">}(</a><a id="2592" href="Base.Algebras.Products.html#2592" class="Bound">𝒜</a> <a id="2594" class="Symbol">:</a> <a id="2596" href="Base.Algebras.Products.html#2579" class="Bound">I</a> <a id="2598" class="Symbol">→</a> <a id="2600" href="Base.Algebras.Basic.html#5089" class="Record">algebra</a> <a id="2608" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="2610" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a><a id="2611" class="Symbol">)</a> <a id="2613" class="Symbol">→</a> <a id="2615" href="Base.Algebras.Basic.html#5089" class="Record">algebra</a> <a id="2623" class="Symbol">(</a><a id="2624" href="Base.Algebras.Products.html#1083" class="Generalizable">𝓘</a> <a id="2626" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2628" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="2629" class="Symbol">)</a> <a id="2631" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a>
<a id="2633" href="Base.Algebras.Products.html#2573" class="Function">⨅&#39;</a> <a id="2636" class="Symbol">{</a><a id="2637" href="Base.Algebras.Products.html#2637" class="Bound">I</a><a id="2638" class="Symbol">}</a> <a id="2640" href="Base.Algebras.Products.html#2640" class="Bound">𝒜</a> <a id="2642" class="Symbol">=</a> <a id="2644" class="Keyword">record</a>  <a id="2652" class="Symbol">{</a> <a id="2654" href="Base.Algebras.Basic.html#5186" class="Field">carrier</a> <a id="2662" class="Symbol">=</a> <a id="2664" class="Symbol">∀</a> <a id="2666" href="Base.Algebras.Products.html#2666" class="Bound">i</a> <a id="2668" class="Symbol">→</a> <a id="2670" href="Base.Algebras.Basic.html#5186" class="Field">carrier</a> <a id="2678" class="Symbol">(</a><a id="2679" href="Base.Algebras.Products.html#2640" class="Bound">𝒜</a> <a id="2681" href="Base.Algebras.Products.html#2666" class="Bound">i</a><a id="2682" class="Symbol">)</a>                         <a id="2708" class="Comment">-- domain</a>
                    <a id="2738" class="Symbol">;</a> <a id="2740" href="Base.Algebras.Basic.html#5205" class="Field">opsymbol</a> <a id="2749" class="Symbol">=</a> <a id="2751" class="Symbol">λ</a> <a id="2753" href="Base.Algebras.Products.html#2753" class="Bound">𝑓</a> <a id="2755" href="Base.Algebras.Products.html#2755" class="Bound">𝑎</a> <a id="2757" href="Base.Algebras.Products.html#2757" class="Bound">i</a> <a id="2759" class="Symbol">→</a> <a id="2761" class="Symbol">(</a><a id="2762" href="Base.Algebras.Basic.html#5205" class="Field">opsymbol</a> <a id="2771" class="Symbol">(</a><a id="2772" href="Base.Algebras.Products.html#2640" class="Bound">𝒜</a> <a id="2774" href="Base.Algebras.Products.html#2757" class="Bound">i</a><a id="2775" class="Symbol">))</a> <a id="2778" href="Base.Algebras.Products.html#2753" class="Bound">𝑓</a> <a id="2780" class="Symbol">λ</a> <a id="2782" href="Base.Algebras.Products.html#2782" class="Bound">x</a> <a id="2784" class="Symbol">→</a> <a id="2786" href="Base.Algebras.Products.html#2755" class="Bound">𝑎</a> <a id="2788" href="Base.Algebras.Products.html#2782" class="Bound">x</a> <a id="2790" href="Base.Algebras.Products.html#2757" class="Bound">i</a> <a id="2792" class="Symbol">}</a>  <a id="2795" class="Comment">-- basic operations</a>
</pre>

**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has
type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the
[agda-algebras](https://github.com/ualib/agda-algebras) library that we define
the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="3109" href="Base.Algebras.Products.html#3109" class="Function">ov</a> <a id="3112" class="Symbol">:</a> <a id="3114" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3120" class="Symbol">→</a> <a id="3122" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3128" href="Base.Algebras.Products.html#3109" class="Function">ov</a> <a id="3131" href="Base.Algebras.Products.html#3131" class="Bound">α</a> <a id="3133" class="Symbol">=</a> <a id="3135" href="Base.Algebras.Products.html#510" class="Bound">𝓞</a> <a id="3137" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3139" href="Base.Algebras.Products.html#512" class="Bound">𝓥</a> <a id="3141" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3143" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3147" href="Base.Algebras.Products.html#3131" class="Bound">α</a>
</pre>


### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type
`Algebra α 𝑆`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred
(Algebra α 𝑆) β`, for some type `β`. Later we will formally state and prove that
the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of
subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns
out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary
(nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not
what we want.  For recall that `Pred (Algebra α 𝑆) β` is just an alias for the
function type `Algebra α 𝑆 → Type β`, and the semantics of the latter takes `𝒦 𝑨`
(and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α 𝑆) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α 𝑆` belongs to `𝒦`.
Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that
maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of
type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems rather nebulous in
that there is no natural indexing class with which to "enumerate" all inhabitants
of `Algebra α 𝑆` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least
heuristically that is how one can view the type `ℑ` that we now define.

<pre class="Agda">

<a id="4832" class="Keyword">module</a> <a id="4839" href="Base.Algebras.Products.html#4839" class="Module">_</a> <a id="4841" class="Symbol">{</a><a id="4842" href="Base.Algebras.Products.html#4842" class="Bound">𝒦</a> <a id="4844" class="Symbol">:</a> <a id="4846" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="4851" class="Symbol">(</a><a id="4852" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="4860" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a> <a id="4862" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a><a id="4863" class="Symbol">)(</a><a id="4865" href="Base.Algebras.Products.html#3109" class="Function">ov</a> <a id="4868" href="Base.Algebras.Products.html#1077" class="Generalizable">α</a><a id="4869" class="Symbol">)}</a> <a id="4872" class="Keyword">where</a>
 <a id="4879" href="Base.Algebras.Products.html#4879" class="Function">ℑ</a> <a id="4881" class="Symbol">:</a> <a id="4883" href="Base.Algebras.Products.html#659" class="Primitive">Type</a> <a id="4888" class="Symbol">(</a><a id="4889" href="Base.Algebras.Products.html#3109" class="Function">ov</a> <a id="4892" href="Base.Algebras.Products.html#4860" class="Bound">α</a><a id="4893" class="Symbol">)</a>
 <a id="4896" href="Base.Algebras.Products.html#4879" class="Function">ℑ</a> <a id="4898" class="Symbol">=</a> <a id="4900" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4903" href="Base.Algebras.Products.html#4903" class="Bound">𝑨</a> <a id="4905" href="Data.Product.html#916" class="Function">∈</a> <a id="4907" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="4915" href="Base.Algebras.Products.html#4860" class="Bound">α</a> <a id="4917" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a> <a id="4919" href="Data.Product.html#916" class="Function">]</a> <a id="4921" href="Base.Algebras.Products.html#4903" class="Bound">𝑨</a> <a id="4923" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="4925" href="Base.Algebras.Products.html#4842" class="Bound">𝒦</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index
`i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where
`𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function
mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="5274" href="Base.Algebras.Products.html#5274" class="Function">𝔄</a> <a id="5276" class="Symbol">:</a> <a id="5278" href="Base.Algebras.Products.html#4879" class="Function">ℑ</a> <a id="5280" class="Symbol">→</a> <a id="5282" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="5290" href="Base.Algebras.Products.html#4860" class="Bound">α</a> <a id="5292" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a>
 <a id="5295" href="Base.Algebras.Products.html#5274" class="Function">𝔄</a> <a id="5297" href="Base.Algebras.Products.html#5297" class="Bound">i</a> <a id="5299" class="Symbol">=</a> <a id="5301" href="Overture.Basic.html#4303" class="Function Operator">∣</a> <a id="5303" href="Base.Algebras.Products.html#5297" class="Bound">i</a> <a id="5305" href="Overture.Basic.html#4303" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of
𝒦.

<pre class="Agda">

 <a id="5421" href="Base.Algebras.Products.html#5421" class="Function">class-product</a> <a id="5435" class="Symbol">:</a> <a id="5437" href="Base.Algebras.Basic.html#3051" class="Function">Algebra</a> <a id="5445" class="Symbol">(</a><a id="5446" href="Base.Algebras.Products.html#3109" class="Function">ov</a> <a id="5449" href="Base.Algebras.Products.html#4860" class="Bound">α</a><a id="5450" class="Symbol">)</a> <a id="5452" href="Base.Algebras.Products.html#496" class="Bound">𝑆</a>
 <a id="5455" href="Base.Algebras.Products.html#5421" class="Function">class-product</a> <a id="5469" class="Symbol">=</a> <a id="5471" href="Base.Algebras.Products.html#1925" class="Function">⨅</a> <a id="5473" href="Base.Algebras.Products.html#5274" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we
can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅
𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Base.Algebras.Basic](Base.Algebras.Basic.html)</span>
<span style="float:right;">[Base.Algebras.Congruences →](Base.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
