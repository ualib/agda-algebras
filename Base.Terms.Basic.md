---
layout: default
title : "Base.Terms.Basic module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "the agda-algebras development team"
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [Base.Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="313" class="Symbol">{-#</a> <a id="317" class="Keyword">OPTIONS</a> <a id="325" class="Pragma">--without-K</a> <a id="337" class="Pragma">--exact-split</a> <a id="351" class="Pragma">--safe</a> <a id="358" class="Symbol">#-}</a>

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>

<a id="396" class="Keyword">module</a> <a id="403" href="Base.Terms.Basic.html" class="Module">Base.Terms.Basic</a> <a id="420" class="Symbol">{</a><a id="421" href="Base.Terms.Basic.html#421" class="Bound">𝑆</a> <a id="423" class="Symbol">:</a> <a id="425" href="Base.Algebras.Basic.html#3888" class="Function">Signature</a> <a id="435" href="Base.Algebras.Basic.html#1160" class="Generalizable">𝓞</a> <a id="437" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓥</a><a id="438" class="Symbol">}</a> <a id="440" class="Keyword">where</a>

<a id="447" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="542" class="Keyword">using</a> <a id="548" class="Symbol">(</a> <a id="550" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="556" class="Symbol">)</a> <a id="558" class="Keyword">renaming</a> <a id="567" class="Symbol">(</a> <a id="569" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="573" class="Symbol">to</a> <a id="576" class="Primitive">Type</a> <a id="581" class="Symbol">)</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="Data.Product.html" class="Module">Data.Product</a>   <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a> <a id="618" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="622" class="Symbol">)</a>

<a id="625" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="Base.Overture.Preliminaries.html" class="Module">Base.Overture.Preliminaries</a>    <a id="736" class="Keyword">using</a> <a id="742" class="Symbol">(</a> <a id="744" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣_∣</a> <a id="748" class="Symbol">;</a> <a id="750" href="Base.Overture.Preliminaries.html#4440" class="Function Operator">∥_∥</a> <a id="754" class="Symbol">)</a>
<a id="756" class="Keyword">open</a> <a id="761" class="Keyword">import</a> <a id="768" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a> <a id="791" class="Symbol">{</a><a id="792" class="Argument">𝑆</a> <a id="794" class="Symbol">=</a> <a id="796" href="Base.Terms.Basic.html#421" class="Bound">𝑆</a><a id="797" class="Symbol">}</a> <a id="799" class="Keyword">using</a> <a id="805" class="Symbol">(</a> <a id="807" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="810" class="Symbol">)</a>

<a id="813" class="Keyword">private</a> <a id="821" class="Keyword">variable</a> <a id="830" href="Base.Terms.Basic.html#830" class="Generalizable">χ</a> <a id="832" class="Symbol">:</a> <a id="834" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

#### <a id="the-type-of-terms">The type of terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `f t` such that `f : ∣ 𝑆 ∣` and `t : ∥ 𝑆 ∥ f → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ f` is the arity of the operation symbol f.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

<pre class="Agda">

<a id="2016" class="Keyword">data</a> <a id="Term"></a><a id="2021" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="2026" class="Symbol">(</a><a id="2027" href="Base.Terms.Basic.html#2027" class="Bound">X</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="Base.Terms.Basic.html#576" class="Primitive">Type</a> <a id="2036" href="Base.Terms.Basic.html#830" class="Generalizable">χ</a> <a id="2038" class="Symbol">)</a> <a id="2040" class="Symbol">:</a> <a id="2042" href="Base.Terms.Basic.html#576" class="Primitive">Type</a> <a id="2047" class="Symbol">(</a><a id="2048" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="2051" href="Base.Terms.Basic.html#2036" class="Bound">χ</a><a id="2052" class="Symbol">)</a>  <a id="2055" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="2062" href="Base.Terms.Basic.html#2062" class="InductiveConstructor">ℊ</a> <a id="2064" class="Symbol">:</a> <a id="2066" href="Base.Terms.Basic.html#2027" class="Bound">X</a> <a id="2068" class="Symbol">→</a> <a id="2070" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="2075" href="Base.Terms.Basic.html#2027" class="Bound">X</a>    <a id="2080" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="2104" href="Base.Terms.Basic.html#2104" class="InductiveConstructor">node</a> <a id="2109" class="Symbol">:</a> <a id="2111" class="Symbol">(</a><a id="2112" href="Base.Terms.Basic.html#2112" class="Bound">f</a> <a id="2114" class="Symbol">:</a> <a id="2116" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a> <a id="2118" href="Base.Terms.Basic.html#421" class="Bound">𝑆</a> <a id="2120" href="Base.Overture.Preliminaries.html#4402" class="Function Operator">∣</a><a id="2121" class="Symbol">)(</a><a id="2123" href="Base.Terms.Basic.html#2123" class="Bound">t</a> <a id="2125" class="Symbol">:</a> <a id="2127" href="Base.Overture.Preliminaries.html#4440" class="Function Operator">∥</a> <a id="2129" href="Base.Terms.Basic.html#421" class="Bound">𝑆</a> <a id="2131" href="Base.Overture.Preliminaries.html#4440" class="Function Operator">∥</a> <a id="2133" href="Base.Terms.Basic.html#2112" class="Bound">f</a> <a id="2135" class="Symbol">→</a> <a id="2137" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="2142" href="Base.Terms.Basic.html#2027" class="Bound">X</a><a id="2143" class="Symbol">)</a> <a id="2145" class="Symbol">→</a> <a id="2147" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="2152" href="Base.Terms.Basic.html#2027" class="Bound">X</a>

<a id="2155" class="Keyword">open</a> <a id="2160" href="Base.Terms.Basic.html#2021" class="Module">Term</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.


#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3304" href="Base.Terms.Basic.html#3304" class="Function">𝑻</a> <a id="3306" class="Symbol">:</a> <a id="3308" class="Symbol">(</a><a id="3309" href="Base.Terms.Basic.html#3309" class="Bound">X</a> <a id="3311" class="Symbol">:</a> <a id="3313" href="Base.Terms.Basic.html#576" class="Primitive">Type</a> <a id="3318" href="Base.Terms.Basic.html#830" class="Generalizable">χ</a> <a id="3320" class="Symbol">)</a> <a id="3322" class="Symbol">→</a> <a id="3324" href="Base.Algebras.Basic.html#6257" class="Function">Algebra</a> <a id="3332" class="Symbol">(</a><a id="3333" href="Base.Algebras.Products.html#3165" class="Function">ov</a> <a id="3336" href="Base.Terms.Basic.html#830" class="Generalizable">χ</a><a id="3337" class="Symbol">)</a> <a id="3339" href="Base.Terms.Basic.html#421" class="Bound">𝑆</a>
<a id="3341" href="Base.Terms.Basic.html#3304" class="Function">𝑻</a> <a id="3343" href="Base.Terms.Basic.html#3343" class="Bound">X</a> <a id="3345" class="Symbol">=</a> <a id="3347" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="3352" href="Base.Terms.Basic.html#3343" class="Bound">X</a> <a id="3354" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3356" href="Base.Terms.Basic.html#2104" class="InductiveConstructor">node</a>

</pre>

------------------------------

<span style="float:left;">[↑ Base.Terms](Base.Terms.html)</span>
<span style="float:right;">[Base.Terms.Properties →](Base.Terms.Properties.html)</span>

{% include UALib.Links.md %}
