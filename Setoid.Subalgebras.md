---
layout: default
title : "Setoid.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="subalgebra-setoid-types">Subalgebras over setoids</a>

This is the [Setoid.Subalgebras][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="326" class="Symbol">{-#</a> <a id="330" class="Keyword">OPTIONS</a> <a id="338" class="Pragma">--without-K</a> <a id="350" class="Pragma">--exact-split</a> <a id="364" class="Pragma">--safe</a> <a id="371" class="Symbol">#-}</a>

<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="Overture.html" class="Module">Overture</a> <a id="397" class="Keyword">using</a> <a id="403" class="Symbol">(</a><a id="404" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="406" class="Symbol">;</a> <a id="408" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="410" class="Symbol">;</a> <a id="412" href="Overture.Signatures.html#3291" class="Function">Signature</a><a id="421" class="Symbol">)</a>

<a id="424" class="Keyword">module</a> <a id="431" href="Setoid.Subalgebras.html" class="Module">Setoid.Subalgebras</a> <a id="450" class="Symbol">{</a><a id="451" href="Setoid.Subalgebras.html#451" class="Bound">𝑆</a> <a id="453" class="Symbol">:</a> <a id="455" href="Overture.Signatures.html#3291" class="Function">Signature</a> <a id="465" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="467" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="468" class="Symbol">}</a> <a id="470" class="Keyword">where</a>

<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="Setoid.Subalgebras.Subuniverses.html" class="Module">Setoid.Subalgebras.Subuniverses</a>  <a id="522" class="Symbol">{</a><a id="523" class="Argument">𝑆</a> <a id="525" class="Symbol">=</a> <a id="527" href="Setoid.Subalgebras.html#451" class="Bound">𝑆</a><a id="528" class="Symbol">}</a> <a id="530" class="Keyword">public</a>
<a id="537" class="Keyword">open</a> <a id="542" class="Keyword">import</a> <a id="549" href="Setoid.Subalgebras.Subalgebras.html" class="Module">Setoid.Subalgebras.Subalgebras</a>   <a id="582" class="Symbol">{</a><a id="583" class="Argument">𝑆</a> <a id="585" class="Symbol">=</a> <a id="587" href="Setoid.Subalgebras.html#451" class="Bound">𝑆</a><a id="588" class="Symbol">}</a> <a id="590" class="Keyword">public</a>
<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="Setoid.Subalgebras.Properties.html" class="Module">Setoid.Subalgebras.Properties</a>    <a id="642" class="Symbol">{</a><a id="643" class="Argument">𝑆</a> <a id="645" class="Symbol">=</a> <a id="647" href="Setoid.Subalgebras.html#451" class="Bound">𝑆</a><a id="648" class="Symbol">}</a> <a id="650" class="Keyword">public</a>
</pre>

---------------------------------

<span style="float:left;">[← Setoid.Terms.Properties](Setoid.Terms.Properties.html)</span>
<span style="float:right;">[Setoid.Subalgebras.Subuniverses →](Setoid.Subalgebras.Subuniverses.html)</span>

{% include UALib.Links.md %}
