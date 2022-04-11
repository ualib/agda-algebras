---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid](Setoid.html) module).

(We are also developing a version of the library based on Cubical Agda, which will consist of submodules of the the [Cubical](Cubical.html) module, but this work has only just begun.)

<pre class="Agda">

<a id="617" class="Symbol">{-#</a> <a id="621" class="Keyword">OPTIONS</a> <a id="629" class="Pragma">--without-K</a> <a id="641" class="Pragma">--exact-split</a> <a id="655" class="Pragma">--safe</a> <a id="662" class="Symbol">#-}</a>

<a id="667" class="Keyword">module</a> <a id="674" href="Base.html" class="Module">Base</a> <a id="679" class="Keyword">where</a>

<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="Base.Overture.html" class="Module">Base.Overture</a>
<a id="712" class="Keyword">open</a> <a id="717" class="Keyword">import</a> <a id="724" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="765" class="Keyword">open</a> <a id="770" class="Keyword">import</a> <a id="777" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="791" class="Keyword">open</a> <a id="796" class="Keyword">import</a> <a id="803" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="822" class="Keyword">open</a> <a id="827" class="Keyword">import</a> <a id="834" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="845" class="Keyword">open</a> <a id="850" class="Keyword">import</a> <a id="857" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="874" class="Keyword">open</a> <a id="879" class="Keyword">import</a> <a id="886" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="901" class="Keyword">open</a> <a id="906" class="Keyword">import</a> <a id="913" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="929" class="Keyword">open</a> <a id="934" class="Keyword">import</a> <a id="941" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="957" class="Keyword">open</a> <a id="962" class="Keyword">import</a> <a id="969" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="985" class="Keyword">open</a> <a id="990" class="Keyword">import</a> <a id="997" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Base.Overture →](Base.Overture.html)</span>


