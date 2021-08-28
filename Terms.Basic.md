---
layout: default
title : Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the agda-algebras development team][]
---

## <a id="basic-definitions">Basic Definitions</a>

This is the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="300" class="Symbol">{-#</a> <a id="304" class="Keyword">OPTIONS</a> <a id="312" class="Pragma">--without-K</a> <a id="324" class="Pragma">--exact-split</a> <a id="338" class="Pragma">--safe</a> <a id="345" class="Symbol">#-}</a>

<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>

<a id="378" class="Keyword">module</a> <a id="385" href="Terms.Basic.html" class="Module">Terms.Basic</a> <a id="397" class="Symbol">{</a><a id="398" href="Terms.Basic.html#398" class="Bound">𝑆</a> <a id="400" class="Symbol">:</a> <a id="402" href="Algebras.Basic.html#3865" class="Function">Signature</a> <a id="412" href="Algebras.Basic.html#1139" class="Generalizable">𝓞</a> <a id="414" href="Algebras.Basic.html#1141" class="Generalizable">𝓥</a><a id="415" class="Symbol">}</a> <a id="417" class="Keyword">where</a>

<a id="424" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------</a>
<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="519" class="Keyword">using</a> <a id="525" class="Symbol">(</a> <a id="527" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="533" class="Symbol">)</a> <a id="535" class="Keyword">renaming</a> <a id="544" class="Symbol">(</a> <a id="546" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="550" class="Symbol">to</a> <a id="553" class="Primitive">Type</a> <a id="558" class="Symbol">)</a>
<a id="560" class="Keyword">open</a> <a id="565" class="Keyword">import</a> <a id="572" href="Data.Product.html" class="Module">Data.Product</a>   <a id="587" class="Keyword">using</a> <a id="593" class="Symbol">(</a> <a id="595" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="599" class="Symbol">)</a>

<a id="602" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------</a>
<a id="670" class="Keyword">open</a> <a id="675" class="Keyword">import</a> <a id="682" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>    <a id="708" class="Keyword">using</a> <a id="714" class="Symbol">(</a> <a id="716" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a> <a id="720" class="Symbol">;</a> <a id="722" href="Overture.Preliminaries.html#4562" class="Function Operator">∥_∥</a> <a id="726" class="Symbol">)</a>
<a id="728" class="Keyword">open</a> <a id="733" class="Keyword">import</a> <a id="740" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="758" class="Symbol">{</a><a id="759" class="Argument">𝑆</a> <a id="761" class="Symbol">=</a> <a id="763" href="Terms.Basic.html#398" class="Bound">𝑆</a><a id="764" class="Symbol">}</a> <a id="766" class="Keyword">using</a> <a id="772" class="Symbol">(</a> <a id="774" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="777" class="Symbol">)</a>

<a id="780" class="Keyword">private</a> <a id="788" class="Keyword">variable</a> <a id="797" href="Terms.Basic.html#797" class="Generalizable">χ</a> <a id="799" class="Symbol">:</a> <a id="801" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

### <a id="the-type-of-terms">The type of terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `f t` such that `f : ∣ 𝑆 ∣` and `t : ∥ 𝑆 ∥ f → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ f` is the arity of the operation symbol f.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

<pre class="Agda">

<a id="1982" class="Keyword">data</a> <a id="Term"></a><a id="1987" href="Terms.Basic.html#1987" class="Datatype">Term</a> <a id="1992" class="Symbol">(</a><a id="1993" href="Terms.Basic.html#1993" class="Bound">X</a> <a id="1995" class="Symbol">:</a> <a id="1997" href="Terms.Basic.html#553" class="Primitive">Type</a> <a id="2002" href="Terms.Basic.html#797" class="Generalizable">χ</a> <a id="2004" class="Symbol">)</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="Terms.Basic.html#553" class="Primitive">Type</a> <a id="2013" class="Symbol">(</a><a id="2014" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="2017" href="Terms.Basic.html#2002" class="Bound">χ</a><a id="2018" class="Symbol">)</a>  <a id="2021" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="2028" href="Terms.Basic.html#2028" class="InductiveConstructor">ℊ</a> <a id="2030" class="Symbol">:</a> <a id="2032" href="Terms.Basic.html#1993" class="Bound">X</a> <a id="2034" class="Symbol">→</a> <a id="2036" href="Terms.Basic.html#1987" class="Datatype">Term</a> <a id="2041" href="Terms.Basic.html#1993" class="Bound">X</a>    <a id="2046" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="2070" href="Terms.Basic.html#2070" class="InductiveConstructor">node</a> <a id="2075" class="Symbol">:</a> <a id="2077" class="Symbol">(</a><a id="2078" href="Terms.Basic.html#2078" class="Bound">f</a> <a id="2080" class="Symbol">:</a> <a id="2082" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2084" href="Terms.Basic.html#398" class="Bound">𝑆</a> <a id="2086" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2087" class="Symbol">)(</a><a id="2089" href="Terms.Basic.html#2089" class="Bound">t</a> <a id="2091" class="Symbol">:</a> <a id="2093" href="Overture.Preliminaries.html#4562" class="Function Operator">∥</a> <a id="2095" href="Terms.Basic.html#398" class="Bound">𝑆</a> <a id="2097" href="Overture.Preliminaries.html#4562" class="Function Operator">∥</a> <a id="2099" href="Terms.Basic.html#2078" class="Bound">f</a> <a id="2101" class="Symbol">→</a> <a id="2103" href="Terms.Basic.html#1987" class="Datatype">Term</a> <a id="2108" href="Terms.Basic.html#1993" class="Bound">X</a><a id="2109" class="Symbol">)</a> <a id="2111" class="Symbol">→</a> <a id="2113" href="Terms.Basic.html#1987" class="Datatype">Term</a> <a id="2118" href="Terms.Basic.html#1993" class="Bound">X</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.


### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3258" href="Terms.Basic.html#3258" class="Function">𝑻</a> <a id="3260" class="Symbol">:</a> <a id="3262" class="Symbol">(</a><a id="3263" href="Terms.Basic.html#3263" class="Bound">X</a> <a id="3265" class="Symbol">:</a> <a id="3267" href="Terms.Basic.html#553" class="Primitive">Type</a> <a id="3272" href="Terms.Basic.html#797" class="Generalizable">χ</a> <a id="3274" class="Symbol">)</a> <a id="3276" class="Symbol">→</a> <a id="3278" href="Algebras.Basic.html#6228" class="Function">Algebra</a> <a id="3286" class="Symbol">(</a><a id="3287" href="Algebras.Products.html#3133" class="Function">ov</a> <a id="3290" href="Terms.Basic.html#797" class="Generalizable">χ</a><a id="3291" class="Symbol">)</a> <a id="3293" href="Terms.Basic.html#398" class="Bound">𝑆</a>
<a id="3295" href="Terms.Basic.html#3258" class="Function">𝑻</a> <a id="3297" href="Terms.Basic.html#3297" class="Bound">X</a> <a id="3299" class="Symbol">=</a> <a id="3301" href="Terms.Basic.html#1987" class="Datatype">Term</a> <a id="3306" href="Terms.Basic.html#3297" class="Bound">X</a> <a id="3308" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3310" href="Terms.Basic.html#2070" class="InductiveConstructor">node</a>

</pre>

------------------------------

<span style="float:left;">[↑ Terms](Terms.html)</span>
<span style="float:right;">[Terms.Properties →](Terms.Properties.html)</span>

{% include UALib.Links.md %}

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

