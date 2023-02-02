---
layout: default
title : "Setoid.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### <a id="types-for-homomorphism-of-setoid-algebras">Types for Homomorphism of Setoid Algebras</a>

This is the [Setoid.Homomorphisms][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="365" class="Symbol">{-#</a> <a id="369" class="Keyword">OPTIONS</a> <a id="377" class="Pragma">--without-K</a> <a id="389" class="Pragma">--exact-split</a> <a id="403" class="Pragma">--safe</a> <a id="410" class="Symbol">#-}</a>

<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="Overture.html" class="Module">Overture</a> <a id="436" class="Keyword">using</a> <a id="442" class="Symbol">(</a><a id="443" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="445" class="Symbol">;</a> <a id="447" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="449" class="Symbol">;</a> <a id="451" href="Overture.Signatures.html#3264" class="Function">Signature</a><a id="460" class="Symbol">)</a>

<a id="463" class="Keyword">module</a> <a id="470" href="Setoid.Homomorphisms.html" class="Module">Setoid.Homomorphisms</a> <a id="491" class="Symbol">{</a><a id="492" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a> <a id="494" class="Symbol">:</a> <a id="496" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="506" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="508" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="509" class="Symbol">}</a> <a id="511" class="Keyword">where</a>

<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="Setoid.Homomorphisms.Basic.html" class="Module">Setoid.Homomorphisms.Basic</a>              <a id="570" class="Symbol">{</a><a id="571" class="Argument">𝑆</a> <a id="573" class="Symbol">=</a> <a id="575" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="576" class="Symbol">}</a> <a id="578" class="Keyword">public</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="Setoid.Homomorphisms.Properties.html" class="Module">Setoid.Homomorphisms.Properties</a>         <a id="637" class="Symbol">{</a><a id="638" class="Argument">𝑆</a> <a id="640" class="Symbol">=</a> <a id="642" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="643" class="Symbol">}</a> <a id="645" class="Keyword">public</a>
<a id="652" class="Keyword">open</a> <a id="657" class="Keyword">import</a> <a id="664" href="Setoid.Homomorphisms.Kernels.html" class="Module">Setoid.Homomorphisms.Kernels</a>            <a id="704" class="Symbol">{</a><a id="705" class="Argument">𝑆</a> <a id="707" class="Symbol">=</a> <a id="709" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="710" class="Symbol">}</a> <a id="712" class="Keyword">public</a>
<a id="719" class="Keyword">open</a> <a id="724" class="Keyword">import</a> <a id="731" href="Setoid.Homomorphisms.Products.html" class="Module">Setoid.Homomorphisms.Products</a>           <a id="771" class="Symbol">{</a><a id="772" class="Argument">𝑆</a> <a id="774" class="Symbol">=</a> <a id="776" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="777" class="Symbol">}</a> <a id="779" class="Keyword">public</a>
<a id="786" class="Keyword">open</a> <a id="791" class="Keyword">import</a> <a id="798" href="Setoid.Homomorphisms.Noether.html" class="Module">Setoid.Homomorphisms.Noether</a>            <a id="838" class="Symbol">{</a><a id="839" class="Argument">𝑆</a> <a id="841" class="Symbol">=</a> <a id="843" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="844" class="Symbol">}</a> <a id="846" class="Keyword">public</a>
<a id="853" class="Keyword">open</a> <a id="858" class="Keyword">import</a> <a id="865" href="Setoid.Homomorphisms.Factor.html" class="Module">Setoid.Homomorphisms.Factor</a>             <a id="905" class="Symbol">{</a><a id="906" class="Argument">𝑆</a> <a id="908" class="Symbol">=</a> <a id="910" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="911" class="Symbol">}</a> <a id="913" class="Keyword">public</a>
<a id="920" class="Keyword">open</a> <a id="925" class="Keyword">import</a> <a id="932" href="Setoid.Homomorphisms.Isomorphisms.html" class="Module">Setoid.Homomorphisms.Isomorphisms</a>       <a id="972" class="Symbol">{</a><a id="973" class="Argument">𝑆</a> <a id="975" class="Symbol">=</a> <a id="977" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="978" class="Symbol">}</a> <a id="980" class="Keyword">public</a>
<a id="987" class="Keyword">open</a> <a id="992" class="Keyword">import</a> <a id="999" href="Setoid.Homomorphisms.HomomorphicImages.html" class="Module">Setoid.Homomorphisms.HomomorphicImages</a>  <a id="1039" class="Symbol">{</a><a id="1040" class="Argument">𝑆</a> <a id="1042" class="Symbol">=</a> <a id="1044" href="Setoid.Homomorphisms.html#492" class="Bound">𝑆</a><a id="1045" class="Symbol">}</a> <a id="1047" class="Keyword">public</a>

</pre>

--------------------------------

<span style="float:left;">[← Setoid.Algebras.Congruences](Setoid.Algebras.Congruences.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Basic →](Setoid.Homomorphisms.Basic.html)</span>

{% include UALib.Links.md %}
