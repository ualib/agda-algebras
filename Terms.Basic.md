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

<a id="379" class="Keyword">module</a> <a id="386" href="Terms.Basic.html" class="Module">Terms.Basic</a> <a id="398" class="Symbol">{</a><a id="399" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="401" class="Symbol">:</a> <a id="403" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="413" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="415" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a><a id="416" class="Symbol">}</a> <a id="418" class="Keyword">where</a>

<a id="425" class="Keyword">open</a> <a id="430" class="Keyword">import</a> <a id="437" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="452" class="Keyword">using</a> <a id="458" class="Symbol">(</a> <a id="460" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="466" class="Symbol">)</a> <a id="468" class="Keyword">renaming</a> <a id="477" class="Symbol">(</a> <a id="479" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="483" class="Symbol">to</a> <a id="486" class="Primitive">Type</a> <a id="491" class="Symbol">)</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="Data.Product.html" class="Module">Data.Product</a>   <a id="520" class="Keyword">using</a> <a id="526" class="Symbol">(</a> <a id="528" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="532" class="Symbol">)</a>

<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>    <a id="573" class="Keyword">using</a> <a id="579" class="Symbol">(</a> <a id="581" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a> <a id="585" class="Symbol">;</a> <a id="587" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a> <a id="591" class="Symbol">)</a>
<a id="593" class="Keyword">open</a> <a id="598" class="Keyword">import</a> <a id="605" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="623" class="Symbol">{</a><a id="624" class="Argument">𝑆</a> <a id="626" class="Symbol">=</a> <a id="628" href="Terms.Basic.html#399" class="Bound">𝑆</a><a id="629" class="Symbol">}</a> <a id="631" class="Keyword">using</a> <a id="637" class="Symbol">(</a> <a id="639" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="642" class="Symbol">)</a>

<a id="645" class="Keyword">private</a> <a id="653" class="Keyword">variable</a> <a id="662" href="Terms.Basic.html#662" class="Generalizable">χ</a> <a id="664" class="Symbol">:</a> <a id="666" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

#### The type of terms

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `𝑓 𝑡` such that `𝑓 : ∣ 𝑆 ∣` and `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ 𝑓` is the arity of the operation symbol 𝑓.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

<pre class="Agda">

<a id="1818" class="Keyword">data</a> <a id="Term"></a><a id="1823" href="Terms.Basic.html#1823" class="Datatype">Term</a> <a id="1828" class="Symbol">(</a><a id="1829" href="Terms.Basic.html#1829" class="Bound">X</a> <a id="1831" class="Symbol">:</a> <a id="1833" href="Terms.Basic.html#486" class="Primitive">Type</a> <a id="1838" href="Terms.Basic.html#662" class="Generalizable">χ</a> <a id="1840" class="Symbol">)</a> <a id="1842" class="Symbol">:</a> <a id="1844" href="Terms.Basic.html#486" class="Primitive">Type</a> <a id="1849" class="Symbol">(</a><a id="1850" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="1853" href="Terms.Basic.html#1838" class="Bound">χ</a><a id="1854" class="Symbol">)</a>  <a id="1857" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="1864" href="Terms.Basic.html#1864" class="InductiveConstructor">ℊ</a> <a id="1866" class="Symbol">:</a> <a id="1868" href="Terms.Basic.html#1829" class="Bound">X</a> <a id="1870" class="Symbol">→</a> <a id="1872" href="Terms.Basic.html#1823" class="Datatype">Term</a> <a id="1877" href="Terms.Basic.html#1829" class="Bound">X</a>    <a id="1882" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="1906" href="Terms.Basic.html#1906" class="InductiveConstructor">node</a> <a id="1911" class="Symbol">:</a> <a id="1913" class="Symbol">(</a><a id="1914" href="Terms.Basic.html#1914" class="Bound">f</a> <a id="1916" class="Symbol">:</a> <a id="1918" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="1920" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="1922" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a><a id="1923" class="Symbol">)(</a><a id="1925" href="Terms.Basic.html#1925" class="Bound">t</a> <a id="1927" class="Symbol">:</a> <a id="1929" href="Overture.Preliminaries.html#4283" class="Function Operator">∥</a> <a id="1931" href="Terms.Basic.html#399" class="Bound">𝑆</a> <a id="1933" href="Overture.Preliminaries.html#4283" class="Function Operator">∥</a> <a id="1935" href="Terms.Basic.html#1914" class="Bound">f</a> <a id="1937" class="Symbol">→</a> <a id="1939" href="Terms.Basic.html#1823" class="Datatype">Term</a> <a id="1944" href="Terms.Basic.html#1829" class="Bound">X</a><a id="1945" class="Symbol">)</a> <a id="1947" class="Symbol">→</a> <a id="1949" href="Terms.Basic.html#1823" class="Datatype">Term</a> <a id="1954" href="Terms.Basic.html#1829" class="Bound">X</a>

</pre>

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.



#### The term algebra

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `𝑓 : ∣ 𝑆 ∣`, denote by `𝑓 ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `𝑡 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑻 X ∣` to the formal term `𝑓 𝑡`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `𝑓 ̂ (𝑻 X)`, one for each symbol `𝑓` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

<pre class="Agda">

<a id="𝑻"></a><a id="3067" href="Terms.Basic.html#3067" class="Function">𝑻</a> <a id="3069" class="Symbol">:</a> <a id="3071" class="Symbol">(</a><a id="3072" href="Terms.Basic.html#3072" class="Bound">X</a> <a id="3074" class="Symbol">:</a> <a id="3076" href="Terms.Basic.html#486" class="Primitive">Type</a> <a id="3081" href="Terms.Basic.html#662" class="Generalizable">χ</a> <a id="3083" class="Symbol">)</a> <a id="3085" class="Symbol">→</a> <a id="3087" href="Algebras.Basic.html#6389" class="Function">Algebra</a> <a id="3095" class="Symbol">(</a><a id="3096" href="Algebras.Products.html#2950" class="Function">ov</a> <a id="3099" href="Terms.Basic.html#662" class="Generalizable">χ</a><a id="3100" class="Symbol">)</a> <a id="3102" href="Terms.Basic.html#399" class="Bound">𝑆</a>
<a id="3104" href="Terms.Basic.html#3067" class="Function">𝑻</a> <a id="3106" href="Terms.Basic.html#3106" class="Bound">X</a> <a id="3108" class="Symbol">=</a> <a id="3110" href="Terms.Basic.html#1823" class="Datatype">Term</a> <a id="3115" href="Terms.Basic.html#3106" class="Bound">X</a> <a id="3117" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3119" href="Terms.Basic.html#1906" class="InductiveConstructor">node</a>

</pre>


------------------------------

<br>
<br>

[↑ Terms](Terms.html)
<span style="float:right;">[Terms.Properties →](Terms.Properties.html)</span>

{% include UALib.Links.md %}

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

