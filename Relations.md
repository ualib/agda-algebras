---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## Relation and Quotient Types

This is the [UniversalAlgebra.Relations][] module of the [Agda Universal Algebra Library][].

In [Relations.Discrete][] we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).


<pre class="Agda">

<a id="726" class="Symbol">{-#</a> <a id="730" class="Keyword">OPTIONS</a> <a id="738" class="Pragma">--without-K</a> <a id="750" class="Pragma">--exact-split</a> <a id="764" class="Pragma">--safe</a> <a id="771" class="Symbol">#-}</a>

<a id="776" class="Keyword">module</a> <a id="783" href="Relations.html" class="Module">Relations</a> <a id="793" class="Keyword">where</a>

<a id="800" class="Keyword">open</a> <a id="805" class="Keyword">import</a> <a id="812" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="831" class="Keyword">public</a>
<a id="838" class="Keyword">open</a> <a id="843" class="Keyword">import</a> <a id="850" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="871" class="Keyword">public</a>
<a id="878" class="Keyword">open</a> <a id="883" class="Keyword">import</a> <a id="890" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="910" class="Keyword">public</a>

</pre>


-------------------------------------


{% include UALib.Links.md %}


--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
