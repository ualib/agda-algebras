---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="relation-and-quotient-types">Relation and Quotient Types</a>

This is the [UALib.Relations][] module of the [Agda Universal Algebra Library][].

In [Relations.Discrete][] we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).


<pre class="Agda">
<a id="739" class="Symbol">{-#</a> <a id="743" class="Keyword">OPTIONS</a> <a id="751" class="Pragma">--without-K</a> <a id="763" class="Pragma">--exact-split</a> <a id="777" class="Pragma">--safe</a> <a id="784" class="Symbol">#-}</a>
</pre>

<pre class="Agda">
<a id="813" class="Keyword">module</a> <a id="820" href="Relations.html" class="Module">Relations</a> <a id="830" class="Keyword">where</a>

<a id="837" class="Keyword">open</a> <a id="842" class="Keyword">import</a> <a id="849" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>
<a id="901" class="Keyword">open</a> <a id="906" class="Keyword">import</a> <a id="913" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>
<a id="933" class="Keyword">open</a> <a id="938" class="Keyword">import</a> <a id="945" href="Relations.Truncation.html" class="Module">Relations.Truncation</a>
<a id="966" class="Keyword">open</a> <a id="971" class="Keyword">import</a> <a id="978" href="Relations.Extensionality.html" class="Module">Relations.Extensionality</a>

</pre>


-------------------------------------

<p></p>

[← Overture.Lifts](Overture.Lifts.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
