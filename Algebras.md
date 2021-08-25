---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.

<pre class="Agda">

<a id="476" class="Symbol">{-#</a> <a id="480" class="Keyword">OPTIONS</a> <a id="488" class="Pragma">--without-K</a> <a id="500" class="Pragma">--exact-split</a> <a id="514" class="Pragma">--safe</a> <a id="521" class="Symbol">#-}</a>

<a id="526" class="Keyword">module</a> <a id="533" href="Algebras.html" class="Module">Algebras</a> <a id="542" class="Keyword">where</a>

<a id="549" class="Keyword">open</a> <a id="554" class="Keyword">import</a> <a id="561" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>
<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="Algebras.Products.html" class="Module">Algebras.Products</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>
<a id="639" class="Keyword">open</a> <a id="644" class="Keyword">import</a> <a id="651" href="Algebras.Setoid.html" class="Module">Algebras.Setoid</a>

</pre>

-------------------------------------

[← ClosureSystems.Properties](ClosureSystems.Properties.html)
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

