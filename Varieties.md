---
layout: default
title : Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

<pre class="Agda">

<a id="419" class="Symbol">{-#</a> <a id="423" class="Keyword">OPTIONS</a> <a id="431" class="Pragma">--without-K</a> <a id="443" class="Pragma">--exact-split</a> <a id="457" class="Pragma">--safe</a> <a id="464" class="Symbol">#-}</a>

<a id="469" class="Keyword">module</a> <a id="476" href="Varieties.html" class="Module">Varieties</a> <a id="486" class="Keyword">where</a>

<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="Varieties.EquationalLogic.html" class="Module">Varieties.EquationalLogic</a>
<a id="531" class="Keyword">open</a> <a id="536" class="Keyword">import</a> <a id="543" href="Varieties.Closure.html" class="Module">Varieties.Closure</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="Varieties.Properties.html" class="Module">Varieties.Properties</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="Varieties.Preservation.html" class="Module">Varieties.Preservation</a>
<a id="629" class="Keyword">open</a> <a id="634" class="Keyword">import</a> <a id="641" href="Varieties.FreeAlgebras.html" class="Module">Varieties.FreeAlgebras</a>
<a id="664" class="Keyword">open</a> <a id="669" class="Keyword">import</a> <a id="676" href="Varieties.Setoid.html" class="Module">Varieties.Setoid</a>

</pre>


---------------------------------

[← Subalgebras.Setoid.Properties](Subalgebras.Setoid.Properties.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
