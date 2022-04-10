---
layout: default
title : "Base.Algebras module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="algebra-types">Algebra Types</a>

This is the [Base.Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.

<pre class="Agda">

<a id="488" class="Symbol">{-#</a> <a id="492" class="Keyword">OPTIONS</a> <a id="500" class="Pragma">--without-K</a> <a id="512" class="Pragma">--exact-split</a> <a id="526" class="Pragma">--safe</a> <a id="533" class="Symbol">#-}</a>

<a id="538" class="Keyword">module</a> <a id="545" href="Base.Algebras.html" class="Module">Base.Algebras</a> <a id="559" class="Keyword">where</a>

<a id="566" class="Keyword">open</a> <a id="571" class="Keyword">import</a> <a id="578" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>
<a id="598" class="Keyword">open</a> <a id="603" class="Keyword">import</a> <a id="610" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a>
<a id="633" class="Keyword">open</a> <a id="638" class="Keyword">import</a> <a id="645" href="Base.Algebras.Congruences.html" class="Module">Base.Algebras.Congruences</a>

</pre>

-------------------------------------

<span style="float:left;">[← Base.Adjunction.Residuation](Base.Adjunction.Residuation.html)</span>
<span style="float:right;">[Base.Algebras.Basic →](Base.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
