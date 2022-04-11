---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid][] module).

(We are also developing a version of the library based on Cubical Agda, which will consist of submodules of the the [Cubical][] module, but this work has only just begun).

<pre class="Agda">

<a id="594" class="Symbol">{-#</a> <a id="598" class="Keyword">OPTIONS</a> <a id="606" class="Pragma">--without-K</a> <a id="618" class="Pragma">--exact-split</a> <a id="632" class="Pragma">--safe</a> <a id="639" class="Symbol">#-}</a>

<a id="644" class="Keyword">module</a> <a id="651" href="Base.html" class="Module">Base</a> <a id="656" class="Keyword">where</a>

<a id="663" class="Keyword">open</a> <a id="668" class="Keyword">import</a> <a id="675" href="Base.Overture.html" class="Module">Base.Overture</a>
<a id="689" class="Keyword">open</a> <a id="694" class="Keyword">import</a> <a id="701" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="716" class="Keyword">open</a> <a id="721" class="Keyword">import</a> <a id="728" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="768" class="Keyword">open</a> <a id="773" class="Keyword">import</a> <a id="780" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="799" class="Keyword">open</a> <a id="804" class="Keyword">import</a> <a id="811" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="822" class="Keyword">open</a> <a id="827" class="Keyword">import</a> <a id="834" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="851" class="Keyword">open</a> <a id="856" class="Keyword">import</a> <a id="863" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="878" class="Keyword">open</a> <a id="883" class="Keyword">import</a> <a id="890" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="906" class="Keyword">open</a> <a id="911" class="Keyword">import</a> <a id="918" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="934" class="Keyword">open</a> <a id="939" class="Keyword">import</a> <a id="946" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="962" class="Keyword">open</a> <a id="967" class="Keyword">import</a> <a id="974" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Base.Overture →](Base.Overture.html)</span>


