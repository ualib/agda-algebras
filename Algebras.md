---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.


<pre class="Agda">

<a id="477" class="Symbol">{-#</a> <a id="481" class="Keyword">OPTIONS</a> <a id="489" class="Pragma">--without-K</a> <a id="501" class="Pragma">--exact-split</a> <a id="515" class="Pragma">--safe</a> <a id="522" class="Symbol">#-}</a>

<a id="527" class="Keyword">module</a> <a id="534" href="Algebras.html" class="Module">Algebras</a> <a id="543" class="Keyword">where</a>

<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>
<a id="577" class="Keyword">open</a> <a id="582" class="Keyword">import</a> <a id="589" href="Algebras.Products.html" class="Module">Algebras.Products</a>
<a id="607" class="Keyword">open</a> <a id="612" class="Keyword">import</a> <a id="619" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>
<a id="640" class="Keyword">open</a> <a id="645" class="Keyword">import</a> <a id="652" href="Algebras.Setoid.html" class="Module">Algebras.Setoid</a>

</pre>

-------------------------------------

<br>
<br>

[← ClosureSystems.Properties](ClosureSystems.Properties.html)
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>


{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

