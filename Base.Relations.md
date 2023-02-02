---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Base.Relations][] module of the [Agda Universal Algebra Library][].

In the [Base.Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, and higher-ary *finitary* relations.

We refer to these as "discrete relations" to contrast them with the "continuous," *general* and *dependent relations* that we introduce in [Base.Relations.Continuous][].

We call the latter "continuous relations" because they can have arbitrary arity and they can be defined over arbitrary families of types.

Finally, in [Base.Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="811" class="Symbol">{-#</a> <a id="815" class="Keyword">OPTIONS</a> <a id="823" class="Pragma">--without-K</a> <a id="835" class="Pragma">--exact-split</a> <a id="849" class="Pragma">--safe</a> <a id="856" class="Symbol">#-}</a>

<a id="861" class="Keyword">module</a> <a id="868" href="Base.Relations.html" class="Module">Base.Relations</a> <a id="883" class="Keyword">where</a>

<a id="890" class="Keyword">open</a> <a id="895" class="Keyword">import</a> <a id="902" href="Base.Relations.Discrete.html" class="Module">Base.Relations.Discrete</a>    <a id="929" class="Keyword">public</a>
<a id="936" class="Keyword">open</a> <a id="941" class="Keyword">import</a> <a id="948" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>  <a id="975" class="Keyword">public</a>
<a id="982" class="Keyword">open</a> <a id="987" class="Keyword">import</a> <a id="994" href="Base.Relations.Properties.html" class="Module">Base.Relations.Properties</a>  <a id="1021" class="Keyword">public</a>
<a id="1028" class="Keyword">open</a> <a id="1033" class="Keyword">import</a> <a id="1040" href="Base.Relations.Quotients.html" class="Module">Base.Relations.Quotients</a>   <a id="1067" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[↑ Base](Base.html)</span>
<span style="float:right;">[Base.Relations.Discrete →](Base.Relations.Discrete.html)</span>

{% include UALib.Links.md %}
