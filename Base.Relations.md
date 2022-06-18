---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Base.Relations][] module of the [Agda Universal Algebra Library][].

In the [Base.Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Base.Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Base.Relations.Quotients][] we define quotient types.

<pre class="Agda">

<a id="814" class="Symbol">{-#</a> <a id="818" class="Keyword">OPTIONS</a> <a id="826" class="Pragma">--without-K</a> <a id="838" class="Pragma">--exact-split</a> <a id="852" class="Pragma">--safe</a> <a id="859" class="Symbol">#-}</a>

<a id="864" class="Keyword">module</a> <a id="871" href="Base.Relations.html" class="Module">Base.Relations</a> <a id="886" class="Keyword">where</a>

<a id="893" class="Keyword">open</a> <a id="898" class="Keyword">import</a> <a id="905" href="Base.Relations.Discrete.html" class="Module">Base.Relations.Discrete</a>    <a id="932" class="Keyword">public</a>
<a id="939" class="Keyword">open</a> <a id="944" class="Keyword">import</a> <a id="951" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>  <a id="978" class="Keyword">public</a>
<a id="985" class="Keyword">open</a> <a id="990" class="Keyword">import</a> <a id="997" href="Base.Relations.Properties.html" class="Module">Base.Relations.Properties</a>  <a id="1024" class="Keyword">public</a>
<a id="1031" class="Keyword">open</a> <a id="1036" class="Keyword">import</a> <a id="1043" href="Base.Relations.Quotients.html" class="Module">Base.Relations.Quotients</a>   <a id="1070" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[← Base.Overture.Transformers](Base.Overture.Transformers.html)</span>
<span style="float:right;">[Base.Relations.Discrete →](Base.Relations.Discrete.html)</span>

{% include UALib.Links.md %}
