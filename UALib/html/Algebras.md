---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][]. Here we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as types in Agda *signatures* ([Algebras.Signatures][]), *algebras* ([Algebras.Algebras][]), *product algebras* ([Algebras.Products][]), *congruence relations* and *quotient algebras* ([Algebras.Congruences][]).


A popular way to represent algebraic structures in type theory is with record types.  The Sigma type (defined in [Overture.Preliminaries][]) provides an equivalent alternative that we happen to prefer throughout the library, both for consistency and because of its direct connection to the existential quantifier of logic.

Recall, from the Sigma types section of the [Overture.Preliminaries][] module, the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X` such that `P x` holds"; in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of `P x`. In other terms, the pair `(x , p)` is a witness and proof of the proposition `∃ x ∈ X , P x`.




<pre class="Agda">

<a id="1317" class="Symbol">{-#</a> <a id="1321" class="Keyword">OPTIONS</a> <a id="1329" class="Pragma">--without-K</a> <a id="1341" class="Pragma">--exact-split</a> <a id="1355" class="Pragma">--safe</a> <a id="1362" class="Symbol">#-}</a>

<a id="1367" class="Keyword">module</a> <a id="1374" href="Algebras.html" class="Module">Algebras</a> <a id="1383" class="Keyword">where</a>

<a id="1390" class="Keyword">open</a> <a id="1395" class="Keyword">import</a> <a id="1402" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="1422" class="Keyword">public</a>
<a id="1429" class="Keyword">open</a> <a id="1434" class="Keyword">import</a> <a id="1441" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="1459" class="Keyword">public</a>
<a id="1466" class="Keyword">open</a> <a id="1471" class="Keyword">import</a> <a id="1478" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="1496" class="Keyword">public</a>
<a id="1503" class="Keyword">open</a> <a id="1508" class="Keyword">import</a> <a id="1515" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>

</pre>

-------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras.Signatures →](Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
