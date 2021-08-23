---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="relation-and-quotient-types>Telation and Quotient Types</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="823" class="Symbol">{-#</a> <a id="827" class="Keyword">OPTIONS</a> <a id="835" class="Pragma">--without-K</a> <a id="847" class="Pragma">--exact-split</a> <a id="861" class="Pragma">--safe</a> <a id="868" class="Symbol">#-}</a>

<a id="873" class="Keyword">module</a> <a id="880" href="Relations.html" class="Module">Relations</a> <a id="890" class="Keyword">where</a>

<a id="897" class="Keyword">open</a> <a id="902" class="Keyword">import</a> <a id="909" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="928" class="Keyword">public</a>
<a id="935" class="Keyword">open</a> <a id="940" class="Keyword">import</a> <a id="947" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="968" class="Keyword">public</a>
<a id="975" class="Keyword">open</a> <a id="980" class="Keyword">import</a> <a id="987" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1007" class="Keyword">public</a>

</pre>


-------------------------------------

<br>
<br>

[← Overture.Transformers](Overture.Transformers.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
