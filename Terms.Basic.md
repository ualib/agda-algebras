---
layout: default
title : Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the agda-algebras development team][]
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="301" class="Symbol">{-#</a> <a id="305" class="Keyword">OPTIONS</a> <a id="313" class="Pragma">--without-K</a> <a id="325" class="Pragma">--exact-split</a> <a id="339" class="Pragma">--safe</a> <a id="346" class="Symbol">#-}</a>

<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>

<a id="379" class="Keyword">module</a> <a id="386" href="Terms.Basic.html" class="Module">Terms.Basic</a> <a id="398" class="Symbol">{</a><a id="399" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="401" class="Symbol">:</a> <a id="403" href="Algebras.Basic.html#3566" class="Function">Signature</a> <a id="413" href="Algebras.Basic.html#1140" class="Generalizable">𝓞</a> <a id="415" href="Algebras.Basic.html#1142" class="Generalizable">𝓥</a><a id="416" class="Symbol">}</a> <a id="418" class="Keyword">where</a>

<a id="425" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="520" class="Keyword">using</a> <a id="526" class="Symbol">(</a> <a id="528" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="534" class="Symbol">)</a> <a id="536" class="Keyword">renaming</a> <a id="545" class="Symbol">(</a> <a id="547" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="551" class="Symbol">to</a> <a id="554" class="Primitive">Type</a> <a id="559" class="Symbol">)</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="Data.Product.html" class="Module">Data.Product</a>   <a id="588" class="Keyword">using</a> <a id="594" class="Symbol">(</a> <a id="596" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="600" class="Symbol">)</a>

<a id="603" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------</a>
<a id="671" class="Keyword">open</a> <a id="676" class="Keyword">import</a> <a id="683" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>    <a id="709" class="Keyword">using</a> <a id="715" class="Symbol">(</a> <a id="717" href="Overture.Preliminaries.html#4227" class="Function Operator">∣_∣</a> <a id="721" class="Symbol">;</a> <a id="723" href="Overture.Preliminaries.html#4265" class="Function Operator">∥_∥</a> <a id="727" class="Symbol">)</a>
<a id="729" class="Keyword">open</a> <a id="734" class="Keyword">import</a> <a id="741" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="759" class="Symbol">{</a><a id="760" class="Argument">𝑆</a> <a id="762" class="Symbol">=</a> <a id="764" href="Terms.Basic.html#399" class="Bound">𝑆</a><a id="765" class="Symbol">}</a> <a id="767" class="Keyword">using</a> <a id="773" class="Symbol">(</a> <a id="775" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="778" class="Symbol">)</a>

<a id="781" class="Keyword">private</a> <a id="789" class="Keyword">variable</a> <a id="798" href="Terms.Basic.html#798" class="Generalizable">χ</a> <a id="800" class="Symbol">:</a> <a id="802" href="Agda.Primitive.html#597" class="Postulate">Level</a>

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

<a id="1984" class="Keyword">data</a> <a id="Term"></a><a id="1989" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="1994" class="Symbol">(</a><a id="1995" href="Terms.Basic.html#1995" class="Bound">X</a> <a id="1997" class="Symbol">:</a> <a id="1999" href="Terms.Basic.html#554" class="Primitive">Type</a> <a id="2004" href="Terms.Basic.html#798" class="Generalizable">χ</a> <a id="2006" class="Symbol">)</a> <a id="2008" class="Symbol">:</a> <a id="2010" href="Terms.Basic.html#554" class="Primitive">Type</a> <a id="2015" class="Symbol">(</a><a id="2016" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="2019" href="Terms.Basic.html#2004" class="Bound">χ</a><a id="2020" class="Symbol">)</a>  <a id="2023" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="2030" href="Terms.Basic.html#2030" class="InductiveConstructor">ℊ</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Terms.Basic.html#1995" class="Bound">X</a> <a id="2036" class="Symbol">→</a> <a id="2038" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="2043" href="Terms.Basic.html#1995" class="Bound">X</a>    <a id="2048" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="2072" href="Terms.Basic.html#2072" class="InductiveConstructor">node</a> <a id="2077" class="Symbol">:</a> <a id="2079" class="Symbol">(</a><a id="2080" href="Terms.Basic.html#2080" class="Bound">f</a> <a id="2082" class="Symbol">:</a> <a id="2084" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a> <a id="2086" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="2088" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a><a id="2089" class="Symbol">)(</a><a id="2091" href="Terms.Basic.html#2091" class="Bound">t</a> <a id="2093" class="Symbol">:</a> <a id="2095" href="Overture.Preliminaries.html#4265" class="Function Operator">∥</a> <a id="2097" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="2099" href="Overture.Preliminaries.html#4265" class="Function Operator">∥</a> <a id="2101" href="Terms.Basic.html#2080" class="Bound">f</a> <a id="2103" class="Symbol">→</a> <a id="2105" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="2110" href="Terms.Basic.html#1995" class="Bound">X</a><a id="2111" class="Symbol">)</a> <a id="2113" class="Symbol">→</a> <a id="2115" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="2120" href="Terms.Basic.html#1995" class="Bound">X</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.


#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3261" href="Terms.Basic.html#3261" class="Function">𝑻</a> <a id="3263" class="Symbol">:</a> <a id="3265" class="Symbol">(</a><a id="3266" href="Terms.Basic.html#3266" class="Bound">X</a> <a id="3268" class="Symbol">:</a> <a id="3270" href="Terms.Basic.html#554" class="Primitive">Type</a> <a id="3275" href="Terms.Basic.html#798" class="Generalizable">χ</a> <a id="3277" class="Symbol">)</a> <a id="3279" class="Symbol">→</a> <a id="3281" href="Algebras.Basic.html#6008" class="Function">Algebra</a> <a id="3289" class="Symbol">(</a><a id="3290" href="Algebras.Products.html#2982" class="Function">ov</a> <a id="3293" href="Terms.Basic.html#798" class="Generalizable">χ</a><a id="3294" class="Symbol">)</a> <a id="3296" href="Terms.Basic.html#399" class="Bound">𝑆</a>
<a id="3298" href="Terms.Basic.html#3261" class="Function">𝑻</a> <a id="3300" href="Terms.Basic.html#3300" class="Bound">X</a> <a id="3302" class="Symbol">=</a> <a id="3304" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="3309" href="Terms.Basic.html#3300" class="Bound">X</a> <a id="3311" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3313" href="Terms.Basic.html#2072" class="InductiveConstructor">node</a>

</pre>

------------------------------

[↑ Terms](Terms.html)
<span style="float:right;">[Terms.Properties →](Terms.Properties.html)</span>

{% include UALib.Links.md %}

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

