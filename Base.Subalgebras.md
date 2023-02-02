---
layout: default
title : "Base.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="subalgebra-types">Subalgebra Types</a>

This is the [Base.Subalgebras][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="306" class="Symbol">{-#</a> <a id="310" class="Keyword">OPTIONS</a> <a id="318" class="Pragma">--without-K</a> <a id="330" class="Pragma">--exact-split</a> <a id="344" class="Pragma">--safe</a> <a id="351" class="Symbol">#-}</a>

<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="Overture.html" class="Module">Overture</a> <a id="377" class="Keyword">using</a> <a id="383" class="Symbol">(</a> <a id="385" href="Overture.Signatures.html#3303" class="Function">Signature</a> <a id="395" class="Symbol">;</a> <a id="397" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="399" class="Symbol">;</a> <a id="401" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="403" class="Symbol">)</a>

<a id="406" class="Keyword">module</a> <a id="413" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a> <a id="430" class="Symbol">{</a><a id="431" href="Base.Subalgebras.html#431" class="Bound">𝑆</a> <a id="433" class="Symbol">:</a> <a id="435" href="Overture.Signatures.html#3303" class="Function">Signature</a> <a id="445" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="447" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="448" class="Symbol">}</a> <a id="450" class="Keyword">where</a>

<a id="457" class="Keyword">open</a> <a id="462" class="Keyword">import</a> <a id="469" href="Base.Subalgebras.Subuniverses.html" class="Module">Base.Subalgebras.Subuniverses</a>  <a id="500" class="Symbol">{</a><a id="501" class="Argument">𝑆</a> <a id="503" class="Symbol">=</a> <a id="505" href="Base.Subalgebras.html#431" class="Bound">𝑆</a><a id="506" class="Symbol">}</a> <a id="508" class="Keyword">public</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="Base.Subalgebras.Subalgebras.html" class="Module">Base.Subalgebras.Subalgebras</a>   <a id="558" class="Symbol">{</a><a id="559" class="Argument">𝑆</a> <a id="561" class="Symbol">=</a> <a id="563" href="Base.Subalgebras.html#431" class="Bound">𝑆</a><a id="564" class="Symbol">}</a> <a id="566" class="Keyword">public</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="Base.Subalgebras.Properties.html" class="Module">Base.Subalgebras.Properties</a>    <a id="616" class="Symbol">{</a><a id="617" class="Argument">𝑆</a> <a id="619" class="Symbol">=</a> <a id="621" href="Base.Subalgebras.html#431" class="Bound">𝑆</a><a id="622" class="Symbol">}</a> <a id="624" class="Keyword">public</a>
</pre>

--------------------------------------

<span style="float:left;">[← Base.Terms.Properties](Base.Terms.Properties.html)</span>
<span style="float:right;">[Base.Subalgebras.Subuniverses →](Base.Subalgebras.Subuniverses.html)</span>

{% include UALib.Links.md %}
