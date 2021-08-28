---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

# <a id="relations">Relations</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="787" class="Symbol">{-#</a> <a id="791" class="Keyword">OPTIONS</a> <a id="799" class="Pragma">--without-K</a> <a id="811" class="Pragma">--exact-split</a> <a id="825" class="Pragma">--safe</a> <a id="832" class="Symbol">#-}</a>

<a id="837" class="Keyword">module</a> <a id="844" href="Relations.html" class="Module">Relations</a> <a id="854" class="Keyword">where</a>

<a id="861" class="Keyword">open</a> <a id="866" class="Keyword">import</a> <a id="873" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="892" class="Keyword">public</a>
<a id="899" class="Keyword">open</a> <a id="904" class="Keyword">import</a> <a id="911" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="932" class="Keyword">public</a>
<a id="939" class="Keyword">open</a> <a id="944" class="Keyword">import</a> <a id="951" href="Relations.Properties.html" class="Module">Relations.Properties</a> <a id="972" class="Keyword">public</a>
<a id="979" class="Keyword">open</a> <a id="984" class="Keyword">import</a> <a id="991" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1011" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[← Overture.Transformers](Overture.Transformers.html)</span>
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
