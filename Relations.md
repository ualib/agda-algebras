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

<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="899" class="Keyword">public</a>
<a id="906" class="Keyword">open</a> <a id="911" class="Keyword">import</a> <a id="918" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="939" class="Keyword">public</a>
<a id="946" class="Keyword">open</a> <a id="951" class="Keyword">import</a> <a id="958" href="Relations.Properties.html" class="Module">Relations.Properties</a> <a id="979" class="Keyword">public</a>
<a id="986" class="Keyword">open</a> <a id="991" class="Keyword">import</a> <a id="998" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1018" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[← Overture.Transformers](Overture.Transformers.html)</span>
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
