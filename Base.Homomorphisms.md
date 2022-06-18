---
layout: default
title : "Base.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="homomorphism-types">Homomorphism Types</a>

This chapter presents the [Base.Homomorphisms][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="328" class="Symbol">{-#</a> <a id="332" class="Keyword">OPTIONS</a> <a id="340" class="Pragma">--without-K</a> <a id="352" class="Pragma">--exact-split</a> <a id="366" class="Pragma">--safe</a> <a id="373" class="Symbol">#-}</a>

<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="Overture.html" class="Module">Overture</a> <a id="399" class="Keyword">using</a> <a id="405" class="Symbol">(</a><a id="406" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="416" class="Symbol">;</a> <a id="418" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="420" class="Symbol">;</a> <a id="422" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a> <a id="424" class="Symbol">)</a>

<a id="427" class="Keyword">module</a> <a id="434" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a> <a id="453" class="Symbol">{</a><a id="454" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a> <a id="456" class="Symbol">:</a> <a id="458" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="468" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="470" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a><a id="471" class="Symbol">}</a> <a id="473" class="Keyword">where</a>

<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="Base.Homomorphisms.Basic.html" class="Module">Base.Homomorphisms.Basic</a>              <a id="530" class="Symbol">{</a><a id="531" class="Argument">𝑆</a> <a id="533" class="Symbol">=</a> <a id="535" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="536" class="Symbol">}</a> <a id="538" class="Keyword">public</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="Base.Homomorphisms.Properties.html" class="Module">Base.Homomorphisms.Properties</a>         <a id="595" class="Symbol">{</a><a id="596" class="Argument">𝑆</a> <a id="598" class="Symbol">=</a> <a id="600" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="601" class="Symbol">}</a> <a id="603" class="Keyword">public</a>
<a id="610" class="Keyword">open</a> <a id="615" class="Keyword">import</a> <a id="622" href="Base.Homomorphisms.Kernels.html" class="Module">Base.Homomorphisms.Kernels</a>            <a id="660" class="Symbol">{</a><a id="661" class="Argument">𝑆</a> <a id="663" class="Symbol">=</a> <a id="665" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="666" class="Symbol">}</a> <a id="668" class="Keyword">public</a>
<a id="675" class="Keyword">open</a> <a id="680" class="Keyword">import</a> <a id="687" href="Base.Homomorphisms.Products.html" class="Module">Base.Homomorphisms.Products</a>           <a id="725" class="Symbol">{</a><a id="726" class="Argument">𝑆</a> <a id="728" class="Symbol">=</a> <a id="730" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="731" class="Symbol">}</a> <a id="733" class="Keyword">public</a>
<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="Base.Homomorphisms.Noether.html" class="Module">Base.Homomorphisms.Noether</a>            <a id="790" class="Symbol">{</a><a id="791" class="Argument">𝑆</a> <a id="793" class="Symbol">=</a> <a id="795" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="796" class="Symbol">}</a> <a id="798" class="Keyword">public</a>
<a id="805" class="Keyword">open</a> <a id="810" class="Keyword">import</a> <a id="817" href="Base.Homomorphisms.Factor.html" class="Module">Base.Homomorphisms.Factor</a>             <a id="855" class="Symbol">{</a><a id="856" class="Argument">𝑆</a> <a id="858" class="Symbol">=</a> <a id="860" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="861" class="Symbol">}</a> <a id="863" class="Keyword">public</a>
<a id="870" class="Keyword">open</a> <a id="875" class="Keyword">import</a> <a id="882" href="Base.Homomorphisms.Isomorphisms.html" class="Module">Base.Homomorphisms.Isomorphisms</a>       <a id="920" class="Symbol">{</a><a id="921" class="Argument">𝑆</a> <a id="923" class="Symbol">=</a> <a id="925" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="926" class="Symbol">}</a> <a id="928" class="Keyword">public</a>
<a id="935" class="Keyword">open</a> <a id="940" class="Keyword">import</a> <a id="947" href="Base.Homomorphisms.HomomorphicImages.html" class="Module">Base.Homomorphisms.HomomorphicImages</a>  <a id="985" class="Symbol">{</a><a id="986" class="Argument">𝑆</a> <a id="988" class="Symbol">=</a> <a id="990" href="Base.Homomorphisms.html#454" class="Bound">𝑆</a><a id="991" class="Symbol">}</a> <a id="993" class="Keyword">public</a>
</pre>

--------------------------------------

<span style="float:left;">[← Base.Algebras.Congruences](Base.Algebras.Congruences.html)</span>
<span style="float:right;">[Base.Homomorphisms.Basic →](Base.Homomorphisms.Basic.html)</span>

{% include UALib.Links.md %}
