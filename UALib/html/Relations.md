---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="relation-and-quotient-types">Relation and Quotient Types</a>

This is the [UALib.Relations][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">
<a id="302" class="Symbol">{-#</a> <a id="306" class="Keyword">OPTIONS</a> <a id="314" class="Pragma">--without-K</a> <a id="326" class="Pragma">--exact-split</a> <a id="340" class="Pragma">--safe</a> <a id="347" class="Symbol">#-}</a>
</pre>

<pre class="Agda">
<a id="376" class="Keyword">module</a> <a id="383" href="Relations.html" class="Module">Relations</a> <a id="393" class="Keyword">where</a>

<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>
<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>
<a id="464" class="Keyword">open</a> <a id="469" class="Keyword">import</a> <a id="476" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="Relations.Truncation.html" class="Module">Relations.Truncation</a>
<a id="529" class="Keyword">open</a> <a id="534" class="Keyword">import</a> <a id="541" href="Relations.RelExtensionality.html" class="Module">Relations.RelExtensionality</a>

</pre>

-------------------------------------

<p></p>

[← Overture.Lifts](Overture.Lifts.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
