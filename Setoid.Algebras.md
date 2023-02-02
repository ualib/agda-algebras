---
layout: default
title : "Setoid.Algebras module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### <a id="setoid-representation-of-algebras">Setoid Representation of Algebras</a>

<pre class="Agda">

<a id="252" class="Symbol">{-#</a> <a id="256" class="Keyword">OPTIONS</a> <a id="264" class="Pragma">--without-K</a> <a id="276" class="Pragma">--exact-split</a> <a id="290" class="Pragma">--safe</a> <a id="297" class="Symbol">#-}</a>

<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="Overture.html" class="Module">Overture</a> <a id="323" class="Keyword">using</a> <a id="329" class="Symbol">(</a><a id="330" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="332" class="Symbol">;</a> <a id="334" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="336" class="Symbol">;</a> <a id="338" href="Overture.Signatures.html#3282" class="Function">Signature</a><a id="347" class="Symbol">)</a>

<a id="350" class="Keyword">module</a> <a id="357" href="Setoid.Algebras.html" class="Module">Setoid.Algebras</a> <a id="373" class="Symbol">{</a><a id="374" href="Setoid.Algebras.html#374" class="Bound">𝑆</a> <a id="376" class="Symbol">:</a> <a id="378" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="388" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="390" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="391" class="Symbol">}</a> <a id="393" class="Keyword">where</a>

<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="Setoid.Algebras.Basic.html" class="Module">Setoid.Algebras.Basic</a>        <a id="441" class="Symbol">{</a><a id="442" class="Argument">𝑆</a> <a id="444" class="Symbol">=</a> <a id="446" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="447" class="Symbol">}</a> <a id="449" class="Keyword">public</a>
<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="Setoid.Algebras.Products.html" class="Module">Setoid.Algebras.Products</a>     <a id="497" class="Symbol">{</a><a id="498" class="Argument">𝑆</a> <a id="500" class="Symbol">=</a> <a id="502" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="503" class="Symbol">}</a> <a id="505" class="Keyword">public</a>
<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="Setoid.Algebras.Congruences.html" class="Module">Setoid.Algebras.Congruences</a>  <a id="553" class="Symbol">{</a><a id="554" class="Argument">𝑆</a> <a id="556" class="Symbol">=</a> <a id="558" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="559" class="Symbol">}</a> <a id="561" class="Keyword">public</a>
</pre>

--------------------------------

<span style="float:left;">[← Setoid.Relations.Quotients](Setoid.Relations.Quotients.html)</span>
<span style="float:right;">[Setoid.Algebras.Basic →](Setoid.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
