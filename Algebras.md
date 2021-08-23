---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## Algebra Types

This is the [Algebras][] module of the [Agda Universal Algebra Library][]. Here we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as types in Agda *signatures* ([Algebras.Signatures][]), *algebras* ([Algebras.Algebras][]), *product algebras* ([Algebras.Products][]), *congruence relations* and *quotient algebras* ([Algebras.Congruences][]).


A popular way to represent algebraic structures in type theory is with record types.  The Sigma type (defined in [Overture.Preliminaries][]) provides an equivalent alternative that we happen to prefer and we use it throughout the library, both for consistency and because of its direct connection to the existential quantifier of logic. Recall from the Sigma types section of [Overture.Preliminaries][] that the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X` such that `P x` holds;" in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of `P x`. In other terms, the pair `(x , p)` is a witness and proof of the proposition `∃ x ∈ X , P x`.


<pre class="Agda">

<a id="1315" class="Symbol">{-#</a> <a id="1319" class="Keyword">OPTIONS</a> <a id="1327" class="Pragma">--without-K</a> <a id="1339" class="Pragma">--exact-split</a> <a id="1353" class="Pragma">--safe</a> <a id="1360" class="Symbol">#-}</a>

<a id="1365" class="Keyword">module</a> <a id="1372" href="Algebras.html" class="Module">Algebras</a> <a id="1381" class="Keyword">where</a>

<a id="1388" class="Keyword">open</a> <a id="1393" class="Keyword">import</a> <a id="1400" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>
<a id="1415" class="Keyword">open</a> <a id="1420" class="Keyword">import</a> <a id="1427" href="Algebras.Products.html" class="Module">Algebras.Products</a>
<a id="1445" class="Keyword">open</a> <a id="1450" class="Keyword">import</a> <a id="1457" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>
<a id="1478" class="Keyword">open</a> <a id="1483" class="Keyword">import</a> <a id="1490" href="Algebras.Setoid.html" class="Module">Algebras.Setoid</a>

</pre>

-------------------------------------

<br>
<br>

[← ClosureSystems.Properties](ClosureSystems.Properties.html)
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>


{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

