---
layout: default
title : "Varieties module (Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

<pre class="Agda">

<a id="421" class="Symbol">{-#</a> <a id="425" class="Keyword">OPTIONS</a> <a id="433" class="Pragma">--without-K</a> <a id="445" class="Pragma">--exact-split</a> <a id="459" class="Pragma">--safe</a> <a id="466" class="Symbol">#-}</a>

<a id="471" class="Keyword">module</a> <a id="478" href="Varieties.html" class="Module">Varieties</a> <a id="488" class="Keyword">where</a>

<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="Varieties.EquationalLogic.html" class="Module">Varieties.EquationalLogic</a>
<a id="533" class="Keyword">open</a> <a id="538" class="Keyword">import</a> <a id="545" href="Varieties.Closure.html" class="Module">Varieties.Closure</a>
<a id="563" class="Keyword">open</a> <a id="568" class="Keyword">import</a> <a id="575" href="Varieties.Properties.html" class="Module">Varieties.Properties</a>
<a id="596" class="Keyword">open</a> <a id="601" class="Keyword">import</a> <a id="608" href="Varieties.Preservation.html" class="Module">Varieties.Preservation</a>
<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Varieties.FreeAlgebras.html" class="Module">Varieties.FreeAlgebras</a>
<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="Varieties.Setoid.html" class="Module">Varieties.Setoid</a>

</pre>

---------------------------------

<span style="float:left;">[← Subalgebras.Setoid.Properties](Subalgebras.Setoid.Properties.html)</span>
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
