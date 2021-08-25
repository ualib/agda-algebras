---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="types-for-relations-and-quotients">Types for Relations and Quotients</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="836" class="Symbol">{-#</a> <a id="840" class="Keyword">OPTIONS</a> <a id="848" class="Pragma">--without-K</a> <a id="860" class="Pragma">--exact-split</a> <a id="874" class="Pragma">--safe</a> <a id="881" class="Symbol">#-}</a>

<a id="886" class="Keyword">module</a> <a id="893" href="Relations.html" class="Module">Relations</a> <a id="903" class="Keyword">where</a>

<a id="910" class="Keyword">open</a> <a id="915" class="Keyword">import</a> <a id="922" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="941" class="Keyword">public</a>
<a id="948" class="Keyword">open</a> <a id="953" class="Keyword">import</a> <a id="960" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="981" class="Keyword">public</a>
<a id="988" class="Keyword">open</a> <a id="993" class="Keyword">import</a> <a id="1000" href="Relations.Properties.html" class="Module">Relations.Properties</a> <a id="1021" class="Keyword">public</a>
<a id="1028" class="Keyword">open</a> <a id="1033" class="Keyword">import</a> <a id="1040" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1060" class="Keyword">public</a>

</pre>


-------------------------------------

<br>

[← Overture.Transformers](Overture.Transformers.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
