---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to Setoids (see Setoid.lagda) or Cubical Agda (see Cubical.lagda).

<pre class="Agda">

<a id="402" class="Symbol">{-#</a> <a id="406" class="Keyword">OPTIONS</a> <a id="414" class="Pragma">--without-K</a> <a id="426" class="Pragma">--exact-split</a> <a id="440" class="Pragma">--safe</a> <a id="447" class="Symbol">#-}</a>

<a id="452" class="Keyword">module</a> <a id="459" href="Base.html" class="Module">Base</a> <a id="464" class="Keyword">where</a>

<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="Base.Overture.html" class="Module">Base.Overture</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="524" class="Keyword">open</a> <a id="529" class="Keyword">import</a> <a id="536" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="607" class="Keyword">open</a> <a id="612" class="Keyword">import</a> <a id="619" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="630" class="Keyword">open</a> <a id="635" class="Keyword">import</a> <a id="642" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="659" class="Keyword">open</a> <a id="664" class="Keyword">import</a> <a id="671" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="714" class="Keyword">open</a> <a id="719" class="Keyword">import</a> <a id="726" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="770" class="Keyword">open</a> <a id="775" class="Keyword">import</a> <a id="782" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Base.Overture →](Base.Overture.html)</span>


