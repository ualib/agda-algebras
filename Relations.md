---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="794" class="Symbol">{-#</a> <a id="798" class="Keyword">OPTIONS</a> <a id="806" class="Pragma">--without-K</a> <a id="818" class="Pragma">--exact-split</a> <a id="832" class="Pragma">--safe</a> <a id="839" class="Symbol">#-}</a>

<a id="844" class="Keyword">module</a> <a id="851" href="Relations.html" class="Module">Relations</a> <a id="861" class="Keyword">where</a>

<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>
<a id="899" class="Keyword">open</a> <a id="904" class="Keyword">import</a> <a id="911" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>
<a id="932" class="Keyword">open</a> <a id="937" class="Keyword">import</a> <a id="944" href="Relations.Properties.html" class="Module">Relations.Properties</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>
<a id="997" class="Keyword">open</a> <a id="1002" class="Keyword">import</a> <a id="1009" href="Relations.Func.html" class="Module">Relations.Func</a>

</pre>

-------------------------------------

<span style="float:left;">[← Overture.Func.Bijective](Overture.Func.Bijective.html)</span>
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
