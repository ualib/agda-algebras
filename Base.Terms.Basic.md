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

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="Overture.html" class="Module">Overture</a> <a id="384" class="Keyword">using</a> <a id="390" class="Symbol">(</a><a id="391" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="401" class="Symbol">;</a> <a id="403" href="Overture.Signatures.html#645" class="Generalizable">𝓞</a> <a id="405" class="Symbol">;</a> <a id="407" href="Overture.Signatures.html#647" class="Generalizable">𝓥</a> <a id="409" class="Symbol">)</a>

<a id="412" class="Keyword">module</a> <a id="419" href="Base.Terms.Basic.html" class="Module">Base.Terms.Basic</a> <a id="436" class="Symbol">{</a><a id="437" href="Base.Terms.Basic.html#437" class="Bound">𝑆</a> <a id="439" class="Symbol">:</a> <a id="441" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="451" href="Overture.Signatures.html#645" class="Generalizable">𝓞</a> <a id="453" href="Overture.Signatures.html#647" class="Generalizable">𝓥</a><a id="454" class="Symbol">}</a> <a id="456" class="Keyword">where</a>

<a id="463" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------</a>
<a id="531" class="Keyword">open</a> <a id="536" class="Keyword">import</a> <a id="543" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>         <a id="566" class="Keyword">using</a> <a id="572" class="Symbol">()</a> <a id="575" class="Keyword">renaming</a> <a id="584" class="Symbol">(</a> <a id="586" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="590" class="Symbol">to</a> <a id="593" class="Primitive">Type</a> <a id="598" class="Symbol">)</a>
<a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="Data.Product.html" class="Module">Data.Product</a>           <a id="635" class="Keyword">using</a> <a id="641" class="Symbol">(</a> <a id="643" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="647" class="Symbol">)</a>
<a id="649" class="Keyword">open</a> <a id="654" class="Keyword">import</a> <a id="661" href="Level.html" class="Module">Level</a>                  <a id="684" class="Keyword">using</a> <a id="690" class="Symbol">(</a> <a id="692" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="698" class="Symbol">)</a>

<a id="701" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------</a>
<a id="769" class="Keyword">open</a> <a id="774" class="Keyword">import</a> <a id="781" href="Overture.html" class="Module">Overture</a>          <a id="799" class="Keyword">using</a> <a id="805" class="Symbol">(</a> <a id="807" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a> <a id="811" class="Symbol">;</a> <a id="813" href="Overture.Basic.html#4364" class="Function Operator">∥_∥</a> <a id="817" class="Symbol">)</a>
<a id="819" class="Keyword">open</a> <a id="824" class="Keyword">import</a> <a id="831" href="Base.Algebras.html" class="Module">Base.Algebras</a> <a id="845" class="Symbol">{</a><a id="846" class="Argument">𝑆</a> <a id="848" class="Symbol">=</a> <a id="850" href="Base.Terms.Basic.html#437" class="Bound">𝑆</a><a id="851" class="Symbol">}</a>  <a id="854" class="Keyword">using</a> <a id="860" class="Symbol">(</a> <a id="862" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="870" class="Symbol">;</a> <a id="872" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="875" class="Symbol">)</a>

<a id="878" class="Keyword">private</a> <a id="886" class="Keyword">variable</a> <a id="895" href="Base.Terms.Basic.html#895" class="Generalizable">χ</a> <a id="897" class="Symbol">:</a> <a id="899" href="Agda.Primitive.html#597" class="Postulate">Level</a>
</pre>

#### <a id="the-type-of-terms">The type of terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable
symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`,
that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members
of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction
on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows
(cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `f t` such that `f : ∣ 𝑆 ∣` and `t : ∥ 𝑆 ∥ f → 𝑇ₙ`.
(Recall, `∥ 𝑆 ∥ f` is the arity of the operation symbol `f`.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`.
By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used
to represent the semantic notion of terms in type theory. Indeed, such a representation
is given by the following inductive type.

<pre class="Agda">

<a id="2082" class="Keyword">data</a> <a id="Term"></a><a id="2087" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="2092" class="Symbol">(</a><a id="2093" href="Base.Terms.Basic.html#2093" class="Bound">X</a> <a id="2095" class="Symbol">:</a> <a id="2097" href="Base.Terms.Basic.html#593" class="Primitive">Type</a> <a id="2102" href="Base.Terms.Basic.html#895" class="Generalizable">χ</a> <a id="2104" class="Symbol">)</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="Base.Terms.Basic.html#593" class="Primitive">Type</a> <a id="2113" class="Symbol">(</a><a id="2114" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="2117" href="Base.Terms.Basic.html#2102" class="Bound">χ</a><a id="2118" class="Symbol">)</a>  <a id="2121" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="2128" href="Base.Terms.Basic.html#2128" class="InductiveConstructor">ℊ</a> <a id="2130" class="Symbol">:</a> <a id="2132" href="Base.Terms.Basic.html#2093" class="Bound">X</a> <a id="2134" class="Symbol">→</a> <a id="2136" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="2141" href="Base.Terms.Basic.html#2093" class="Bound">X</a>    <a id="2146" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="2170" href="Base.Terms.Basic.html#2170" class="InductiveConstructor">node</a> <a id="2175" class="Symbol">:</a> <a id="2177" class="Symbol">(</a><a id="2178" href="Base.Terms.Basic.html#2178" class="Bound">f</a> <a id="2180" class="Symbol">:</a> <a id="2182" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="2184" href="Base.Terms.Basic.html#437" class="Bound">𝑆</a> <a id="2186" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="2187" class="Symbol">)(</a><a id="2189" href="Base.Terms.Basic.html#2189" class="Bound">t</a> <a id="2191" class="Symbol">:</a> <a id="2193" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="2195" href="Base.Terms.Basic.html#437" class="Bound">𝑆</a> <a id="2197" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="2199" href="Base.Terms.Basic.html#2178" class="Bound">f</a> <a id="2201" class="Symbol">→</a> <a id="2203" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="2208" href="Base.Terms.Basic.html#2093" class="Bound">X</a><a id="2209" class="Symbol">)</a> <a id="2211" class="Symbol">→</a> <a id="2213" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="2218" href="Base.Terms.Basic.html#2093" class="Bound">X</a>

<a id="2221" class="Keyword">open</a> <a id="2226" href="Base.Terms.Basic.html#2087" class="Module">Term</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ suc χ`.


#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3369" href="Base.Terms.Basic.html#3369" class="Function">𝑻</a> <a id="3371" class="Symbol">:</a> <a id="3373" class="Symbol">(</a><a id="3374" href="Base.Terms.Basic.html#3374" class="Bound">X</a> <a id="3376" class="Symbol">:</a> <a id="3378" href="Base.Terms.Basic.html#593" class="Primitive">Type</a> <a id="3383" href="Base.Terms.Basic.html#895" class="Generalizable">χ</a> <a id="3385" class="Symbol">)</a> <a id="3387" class="Symbol">→</a> <a id="3389" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="3397" class="Symbol">(</a><a id="3398" href="Base.Algebras.Products.html#3097" class="Function">ov</a> <a id="3401" href="Base.Terms.Basic.html#895" class="Generalizable">χ</a><a id="3402" class="Symbol">)</a>
<a id="3404" href="Base.Terms.Basic.html#3369" class="Function">𝑻</a> <a id="3406" href="Base.Terms.Basic.html#3406" class="Bound">X</a> <a id="3408" class="Symbol">=</a> <a id="3410" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="3415" href="Base.Terms.Basic.html#3406" class="Bound">X</a> <a id="3417" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3419" href="Base.Terms.Basic.html#2170" class="InductiveConstructor">node</a>
</pre>

------------------------------

<span style="float:left;">[↑ Base.Terms](Base.Terms.html)</span>
<span style="float:right;">[Base.Terms.Properties →](Base.Terms.Properties.html)</span>

{% include UALib.Links.md %}
