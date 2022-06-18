---
layout: default
title : "Setoid module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## <a id="the-setoid-module-of-the-agda-universal-algebra-library">The Setoid Module of the Agda Universal Algebra Library</a>

This module collects all submodule of that part of the library based on setoids, as opposed to "bare" types (see Base.lagda), or Cubical Agda (used in the forthcoming `cubical-agda-algebras` library).

<pre class="Agda">

<a id="459" class="Symbol">{-#</a> <a id="463" class="Keyword">OPTIONS</a> <a id="471" class="Pragma">--without-K</a> <a id="483" class="Pragma">--exact-split</a> <a id="497" class="Pragma">--safe</a> <a id="504" class="Symbol">#-}</a>

<a id="509" class="Keyword">module</a> <a id="516" href="Setoid.html" class="Module">Setoid</a> <a id="523" class="Keyword">where</a>

<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="Setoid.Relations.html" class="Module">Setoid.Relations</a>       <a id="565" class="Keyword">public</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="Setoid.Functions.html" class="Module">Setoid.Functions</a>       <a id="607" class="Keyword">public</a>
<a id="614" class="Keyword">open</a> <a id="619" class="Keyword">import</a> <a id="626" href="Setoid.Algebras.html" class="Module">Setoid.Algebras</a>        <a id="649" class="Keyword">public</a>
<a id="656" class="Keyword">open</a> <a id="661" class="Keyword">import</a> <a id="668" href="Setoid.Homomorphisms.html" class="Module">Setoid.Homomorphisms</a>   <a id="691" class="Keyword">public</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="Setoid.Terms.html" class="Module">Setoid.Terms</a>           <a id="733" class="Keyword">public</a>
<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="Setoid.Subalgebras.html" class="Module">Setoid.Subalgebras</a>     <a id="775" class="Keyword">public</a>
<a id="782" class="Keyword">open</a> <a id="787" class="Keyword">import</a> <a id="794" href="Setoid.Varieties.html" class="Module">Setoid.Varieties</a>       <a id="817" class="Keyword">public</a>
</pre>

--------------------------------------

<span style="float:left;">[↑ Top](index.html)</span>
<span style="float:right;">[Setoid.Relations →](Setoid.Relations.html)</span>


