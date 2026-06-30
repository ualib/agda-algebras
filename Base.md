---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid][] module).

(We have also started developing in parallel the `cubical-agda-algebras` library, based on Cubical Agda.)

<pre class="Agda">

<a id="527" class="Symbol">{-#</a> <a id="531" class="Keyword">OPTIONS</a> <a id="539" class="Pragma">--without-K</a> <a id="551" class="Pragma">--exact-split</a> <a id="565" class="Pragma">--safe</a> <a id="572" class="Symbol">#-}</a>

<a id="577" class="Keyword">module</a> <a id="584" href="Base.html" class="Module">Base</a> <a id="589" class="Keyword">where</a>

<a id="596" class="Keyword">open</a> <a id="601" class="Keyword">import</a> <a id="608" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="623" class="Keyword">open</a> <a id="628" class="Keyword">import</a> <a id="635" href="Base.Functions.html" class="Module">Base.Functions</a>
<a id="650" class="Keyword">open</a> <a id="655" class="Keyword">import</a> <a id="662" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="704" class="Keyword">open</a> <a id="709" class="Keyword">import</a> <a id="716" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="730" class="Keyword">open</a> <a id="735" class="Keyword">import</a> <a id="742" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="761" class="Keyword">open</a> <a id="766" class="Keyword">import</a> <a id="773" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="784" class="Keyword">open</a> <a id="789" class="Keyword">import</a> <a id="796" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="813" class="Keyword">open</a> <a id="818" class="Keyword">import</a> <a id="825" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="840" class="Keyword">open</a> <a id="845" class="Keyword">import</a> <a id="852" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="896" class="Keyword">open</a> <a id="901" class="Keyword">import</a> <a id="908" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[↑ agda-algebras](index.html)</span>
<span style="float:right;">[Base.Relations →](Base.Relations.html)</span>


{% include UALib.Links.md %}
