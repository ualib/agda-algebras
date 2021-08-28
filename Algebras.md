---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

# <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.

<pre class="Agda">

<a id="475" class="Symbol">{-#</a> <a id="479" class="Keyword">OPTIONS</a> <a id="487" class="Pragma">--without-K</a> <a id="499" class="Pragma">--exact-split</a> <a id="513" class="Pragma">--safe</a> <a id="520" class="Symbol">#-}</a>

<a id="525" class="Keyword">module</a> <a id="532" href="Algebras.html" class="Module">Algebras</a> <a id="541" class="Keyword">where</a>

<a id="548" class="Keyword">open</a> <a id="553" class="Keyword">import</a> <a id="560" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>
<a id="575" class="Keyword">open</a> <a id="580" class="Keyword">import</a> <a id="587" href="Algebras.Products.html" class="Module">Algebras.Products</a>
<a id="605" class="Keyword">open</a> <a id="610" class="Keyword">import</a> <a id="617" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>
<a id="638" class="Keyword">open</a> <a id="643" class="Keyword">import</a> <a id="650" href="Algebras.Setoid.html" class="Module">Algebras.Setoid</a>

</pre>

-------------------------------------

<span style="float:left;">[← ClosureSystems.Properties](ClosureSystems.Properties.html)</span>
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

