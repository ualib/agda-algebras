---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Base.Relations][] module of the [Agda Universal Algebra Library][].

In the [Base.Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*.

We refer to these as "discrete relations" to contrast them with the "continuous," *general* and *dependent relations* that we introduce in [Base.Relations.Continuous][].

We call the latter "continuous relations" because they can have arbitrary arity and they can be defined over arbitrary families of types.

Finally, in [Base.Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="774" class="Symbol">{-#</a> <a id="778" class="Keyword">OPTIONS</a> <a id="786" class="Pragma">--without-K</a> <a id="798" class="Pragma">--exact-split</a> <a id="812" class="Pragma">--safe</a> <a id="819" class="Symbol">#-}</a>

<a id="824" class="Keyword">module</a> <a id="831" href="Base.Relations.html" class="Module">Base.Relations</a> <a id="846" class="Keyword">where</a>

<a id="853" class="Keyword">open</a> <a id="858" class="Keyword">import</a> <a id="865" href="Base.Relations.Discrete.html" class="Module">Base.Relations.Discrete</a>    <a id="892" class="Keyword">public</a>
<a id="899" class="Keyword">open</a> <a id="904" class="Keyword">import</a> <a id="911" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>  <a id="938" class="Keyword">public</a>
<a id="945" class="Keyword">open</a> <a id="950" class="Keyword">import</a> <a id="957" href="Base.Relations.Properties.html" class="Module">Base.Relations.Properties</a>  <a id="984" class="Keyword">public</a>
<a id="991" class="Keyword">open</a> <a id="996" class="Keyword">import</a> <a id="1003" href="Base.Relations.Quotients.html" class="Module">Base.Relations.Quotients</a>   <a id="1030" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[↑ Base](Base.html)</span>
<span style="float:right;">[Base.Relations.Discrete →](Base.Relations.Discrete.html)</span>

{% include UALib.Links.md %}
