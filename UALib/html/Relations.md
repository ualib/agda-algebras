---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="relation-and-quotient-types">Relation and Quotient Types</a>

This chapter presents the [UALib.Relations][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">
<a id="316" class="Symbol">{-#</a> <a id="320" class="Keyword">OPTIONS</a> <a id="328" class="Pragma">--without-K</a> <a id="340" class="Pragma">--exact-split</a> <a id="354" class="Pragma">--safe</a> <a id="361" class="Symbol">#-}</a>
</pre>

<pre class="Agda">
<a id="390" class="Keyword">module</a> <a id="397" href="Relations.html" class="Module">Relations</a> <a id="407" class="Keyword">where</a>

<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="Relations.Truncation.html" class="Module">Relations.Truncation</a>

</pre>

-------------------------------------

[← Prelude.Lifts](Prelude.Lifts.html)
<span style="float:right;">[Relations.Unary →](Relations.Small.html)</span>

{% include UALib.Links.md %}
