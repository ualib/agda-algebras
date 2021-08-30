---
layout: default
title : "Terms.Basic module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "the agda-algebras development team"
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="303" class="Symbol">{-#</a> <a id="307" class="Keyword">OPTIONS</a> <a id="315" class="Pragma">--without-K</a> <a id="327" class="Pragma">--exact-split</a> <a id="341" class="Pragma">--safe</a> <a id="348" class="Symbol">#-}</a>

<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>

<a id="381" class="Keyword">module</a> <a id="388" href="Terms.Basic.html" class="Module">Terms.Basic</a> <a id="400" class="Symbol">{</a><a id="401" href="Terms.Basic.html#401" class="Bound">𝑆</a> <a id="403" class="Symbol">:</a> <a id="405" href="Algebras.Basic.html#3870" class="Function">Signature</a> <a id="415" href="Algebras.Basic.html#1142" class="Generalizable">𝓞</a> <a id="417" href="Algebras.Basic.html#1144" class="Generalizable">𝓥</a><a id="418" class="Symbol">}</a> <a id="420" class="Keyword">where</a>

<a id="427" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="522" class="Keyword">using</a> <a id="528" class="Symbol">(</a> <a id="530" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="536" class="Symbol">)</a> <a id="538" class="Keyword">renaming</a> <a id="547" class="Symbol">(</a> <a id="549" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="553" class="Symbol">to</a> <a id="556" class="Primitive">Type</a> <a id="561" class="Symbol">)</a>
<a id="563" class="Keyword">open</a> <a id="568" class="Keyword">import</a> <a id="575" href="Data.Product.html" class="Module">Data.Product</a>   <a id="590" class="Keyword">using</a> <a id="596" class="Symbol">(</a> <a id="598" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="602" class="Symbol">)</a>

<a id="605" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------</a>
<a id="673" class="Keyword">open</a> <a id="678" class="Keyword">import</a> <a id="685" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>    <a id="711" class="Keyword">using</a> <a id="717" class="Symbol">(</a> <a id="719" href="Overture.Preliminaries.html#4379" class="Function Operator">∣_∣</a> <a id="723" class="Symbol">;</a> <a id="725" href="Overture.Preliminaries.html#4417" class="Function Operator">∥_∥</a> <a id="729" class="Symbol">)</a>
<a id="731" class="Keyword">open</a> <a id="736" class="Keyword">import</a> <a id="743" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="761" class="Symbol">{</a><a id="762" class="Argument">𝑆</a> <a id="764" class="Symbol">=</a> <a id="766" href="Terms.Basic.html#401" class="Bound">𝑆</a><a id="767" class="Symbol">}</a> <a id="769" class="Keyword">using</a> <a id="775" class="Symbol">(</a> <a id="777" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="780" class="Symbol">)</a>

<a id="783" class="Keyword">private</a> <a id="791" class="Keyword">variable</a> <a id="800" href="Terms.Basic.html#800" class="Generalizable">χ</a> <a id="802" class="Symbol">:</a> <a id="804" href="Agda.Primitive.html#597" class="Postulate">Level</a>

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

<a id="1986" class="Keyword">data</a> <a id="Term"></a><a id="1991" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="1996" class="Symbol">(</a><a id="1997" href="Terms.Basic.html#1997" class="Bound">X</a> <a id="1999" class="Symbol">:</a> <a id="2001" href="Terms.Basic.html#556" class="Primitive">Type</a> <a id="2006" href="Terms.Basic.html#800" class="Generalizable">χ</a> <a id="2008" class="Symbol">)</a> <a id="2010" class="Symbol">:</a> <a id="2012" href="Terms.Basic.html#556" class="Primitive">Type</a> <a id="2017" class="Symbol">(</a><a id="2018" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="2021" href="Terms.Basic.html#2006" class="Bound">χ</a><a id="2022" class="Symbol">)</a>  <a id="2025" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="2032" href="Terms.Basic.html#2032" class="InductiveConstructor">ℊ</a> <a id="2034" class="Symbol">:</a> <a id="2036" href="Terms.Basic.html#1997" class="Bound">X</a> <a id="2038" class="Symbol">→</a> <a id="2040" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="2045" href="Terms.Basic.html#1997" class="Bound">X</a>    <a id="2050" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="2074" href="Terms.Basic.html#2074" class="InductiveConstructor">node</a> <a id="2079" class="Symbol">:</a> <a id="2081" class="Symbol">(</a><a id="2082" href="Terms.Basic.html#2082" class="Bound">f</a> <a id="2084" class="Symbol">:</a> <a id="2086" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a> <a id="2088" href="Terms.Basic.html#401" class="Bound">𝑆</a> <a id="2090" href="Overture.Preliminaries.html#4379" class="Function Operator">∣</a><a id="2091" class="Symbol">)(</a><a id="2093" href="Terms.Basic.html#2093" class="Bound">t</a> <a id="2095" class="Symbol">:</a> <a id="2097" href="Overture.Preliminaries.html#4417" class="Function Operator">∥</a> <a id="2099" href="Terms.Basic.html#401" class="Bound">𝑆</a> <a id="2101" href="Overture.Preliminaries.html#4417" class="Function Operator">∥</a> <a id="2103" href="Terms.Basic.html#2082" class="Bound">f</a> <a id="2105" class="Symbol">→</a> <a id="2107" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="2112" href="Terms.Basic.html#1997" class="Bound">X</a><a id="2113" class="Symbol">)</a> <a id="2115" class="Symbol">→</a> <a id="2117" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="2122" href="Terms.Basic.html#1997" class="Bound">X</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.


#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3263" href="Terms.Basic.html#3263" class="Function">𝑻</a> <a id="3265" class="Symbol">:</a> <a id="3267" class="Symbol">(</a><a id="3268" href="Terms.Basic.html#3268" class="Bound">X</a> <a id="3270" class="Symbol">:</a> <a id="3272" href="Terms.Basic.html#556" class="Primitive">Type</a> <a id="3277" href="Terms.Basic.html#800" class="Generalizable">χ</a> <a id="3279" class="Symbol">)</a> <a id="3281" class="Symbol">→</a> <a id="3283" href="Algebras.Basic.html#6234" class="Function">Algebra</a> <a id="3291" class="Symbol">(</a><a id="3292" href="Algebras.Products.html#3135" class="Function">ov</a> <a id="3295" href="Terms.Basic.html#800" class="Generalizable">χ</a><a id="3296" class="Symbol">)</a> <a id="3298" href="Terms.Basic.html#401" class="Bound">𝑆</a>
<a id="3300" href="Terms.Basic.html#3263" class="Function">𝑻</a> <a id="3302" href="Terms.Basic.html#3302" class="Bound">X</a> <a id="3304" class="Symbol">=</a> <a id="3306" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="3311" href="Terms.Basic.html#3302" class="Bound">X</a> <a id="3313" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3315" href="Terms.Basic.html#2074" class="InductiveConstructor">node</a>

</pre>

------------------------------

<span style="float:left;">[↑ Terms](Terms.html)</span>
<span style="float:right;">[Terms.Properties →](Terms.Properties.html)</span>

{% include UALib.Links.md %}
