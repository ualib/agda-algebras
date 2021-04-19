---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][]. Here we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as types in Agda *signatures* ([Algebras.Signatures][]), *algebras* ([Algebras.Algebras][]), *product algebras* ([Algebras.Products][]), *congruence relations* and *quotient algebras* ([Algebras.Congruences][]).


A popular way to represent algebraic structures in type theory is with record types.  The Sigma type (defined in [Overture.Preliminaries][]) provides an equivalent alternative that we happen to prefer and we use it throughout the library, both for consistency and because of its direct connection to the existential quantifier of logic. Recall from the Sigma types section of [Overture.Preliminaries][] that the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X` such that `P x` holds;" in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of `P x`. In other terms, the pair `(x , p)` is a witness and proof of the proposition `∃ x ∈ X , P x`.




<pre class="Agda">

<a id="1322" class="Symbol">{-#</a> <a id="1326" class="Keyword">OPTIONS</a> <a id="1334" class="Pragma">--without-K</a> <a id="1346" class="Pragma">--exact-split</a> <a id="1360" class="Pragma">--safe</a> <a id="1367" class="Symbol">#-}</a>

<a id="1372" class="Keyword">module</a> <a id="1379" href="Algebras.html" class="Module">Algebras</a> <a id="1388" class="Keyword">where</a>

<a id="1395" class="Keyword">open</a> <a id="1400" class="Keyword">import</a> <a id="1407" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="1427" class="Keyword">public</a>
<a id="1434" class="Keyword">open</a> <a id="1439" class="Keyword">import</a> <a id="1446" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="1464" class="Keyword">public</a>
<a id="1471" class="Keyword">open</a> <a id="1476" class="Keyword">import</a> <a id="1483" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="1501" class="Keyword">public</a>
<a id="1508" class="Keyword">open</a> <a id="1513" class="Keyword">import</a> <a id="1520" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>

</pre>

-------------------------------------

[← Relations.Extensionality](Relations.Extensionality.html)
<span style="float:right;">[Algebras.Signatures →](Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
