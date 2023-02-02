---
layout: default
title : "Base.Algebras module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="algebra-types">Algebra Types</a>

This is the [Base.Algebras][] module of the [Agda Universal Algebra Library][]
in which we use type theory and [Agda][] to codify the most basic objects of
universal algebra, such as *signatures*, *algebras*, *product algebras*,
*congruence relations*, and *quotient algebras*.

<pre class="Agda">

<a id="488" class="Symbol">{-#</a> <a id="492" class="Keyword">OPTIONS</a> <a id="500" class="Pragma">--without-K</a> <a id="512" class="Pragma">--exact-split</a> <a id="526" class="Pragma">--safe</a> <a id="533" class="Symbol">#-}</a>

<a id="538" class="Keyword">open</a> <a id="543" class="Keyword">import</a> <a id="550" href="Overture.html" class="Module">Overture</a>  <a id="560" class="Keyword">using</a> <a id="566" class="Symbol">(</a> <a id="568" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="570" class="Symbol">;</a> <a id="572" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="574" class="Symbol">;</a> <a id="576" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="586" class="Symbol">)</a>

<a id="589" class="Keyword">module</a> <a id="596" href="Base.Algebras.html" class="Module">Base.Algebras</a> <a id="610" class="Symbol">{</a><a id="611" href="Base.Algebras.html#611" class="Bound">𝑆</a> <a id="613" class="Symbol">:</a> <a id="615" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="625" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="627" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="629" class="Symbol">}</a> <a id="631" class="Keyword">where</a>

<a id="638" class="Keyword">open</a> <a id="643" class="Keyword">import</a> <a id="650" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>        <a id="677" class="Symbol">{</a><a id="678" class="Argument">𝑆</a> <a id="680" class="Symbol">=</a> <a id="682" href="Base.Algebras.html#611" class="Bound">𝑆</a><a id="683" class="Symbol">}</a> <a id="685" class="Keyword">public</a>
<a id="692" class="Keyword">open</a> <a id="697" class="Keyword">import</a> <a id="704" href="Base.Algebras.Products.html" class="Module">Base.Algebras.Products</a>     <a id="731" class="Symbol">{</a><a id="732" class="Argument">𝑆</a> <a id="734" class="Symbol">=</a> <a id="736" href="Base.Algebras.html#611" class="Bound">𝑆</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">public</a>
<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Base.Algebras.Congruences.html" class="Module">Base.Algebras.Congruences</a>  <a id="785" class="Symbol">{</a><a id="786" class="Argument">𝑆</a> <a id="788" class="Symbol">=</a> <a id="790" href="Base.Algebras.html#611" class="Bound">𝑆</a><a id="791" class="Symbol">}</a> <a id="793" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[← Base.Adjunction.Residuation](Base.Adjunction.Residuation.html)</span>
<span style="float:right;">[Base.Algebras.Basic →](Base.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
