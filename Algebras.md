---
layout: default
title : "Algebras module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.

<pre class="Agda">

<a id="478" class="Symbol">{-#</a> <a id="482" class="Keyword">OPTIONS</a> <a id="490" class="Pragma">--without-K</a> <a id="502" class="Pragma">--exact-split</a> <a id="516" class="Pragma">--safe</a> <a id="523" class="Symbol">#-}</a>

<a id="528" class="Keyword">module</a> <a id="535" href="Algebras.html" class="Module">Algebras</a> <a id="544" class="Keyword">where</a>

<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>
<a id="578" class="Keyword">open</a> <a id="583" class="Keyword">import</a> <a id="590" href="Algebras.Products.html" class="Module">Algebras.Products</a>
<a id="608" class="Keyword">open</a> <a id="613" class="Keyword">import</a> <a id="620" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>
<a id="641" class="Keyword">open</a> <a id="646" class="Keyword">import</a> <a id="653" href="Algebras.Func.html" class="Module">Algebras.Func</a>

</pre>

-------------------------------------

<span style="float:left;">[← Adjunction.Residuation](Adjunction.Residuation.html)</span>
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>

{% include UALib.Links.md %}
