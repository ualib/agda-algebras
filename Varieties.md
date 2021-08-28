---
layout: default
title : Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

# <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

<pre class="Agda">

<a id="418" class="Symbol">{-#</a> <a id="422" class="Keyword">OPTIONS</a> <a id="430" class="Pragma">--without-K</a> <a id="442" class="Pragma">--exact-split</a> <a id="456" class="Pragma">--safe</a> <a id="463" class="Symbol">#-}</a>

<a id="468" class="Keyword">module</a> <a id="475" href="Varieties.html" class="Module">Varieties</a> <a id="485" class="Keyword">where</a>

<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="Varieties.EquationalLogic.html" class="Module">Varieties.EquationalLogic</a>
<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="Varieties.Closure.html" class="Module">Varieties.Closure</a>
<a id="560" class="Keyword">open</a> <a id="565" class="Keyword">import</a> <a id="572" href="Varieties.Properties.html" class="Module">Varieties.Properties</a>
<a id="593" class="Keyword">open</a> <a id="598" class="Keyword">import</a> <a id="605" href="Varieties.Preservation.html" class="Module">Varieties.Preservation</a>
<a id="628" class="Keyword">open</a> <a id="633" class="Keyword">import</a> <a id="640" href="Varieties.FreeAlgebras.html" class="Module">Varieties.FreeAlgebras</a>
<a id="663" class="Keyword">open</a> <a id="668" class="Keyword">import</a> <a id="675" href="Varieties.Setoid.html" class="Module">Varieties.Setoid</a>

</pre>


---------------------------------

<span style="float:left;">[← Subalgebras.Setoid.Properties](Subalgebras.Setoid.Properties.html)</span>
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
