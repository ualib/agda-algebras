---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid](Setoid.html) module).

(We have also started developing in parallel the `cubical-agda-algebras` library, based on Cubical Agda.)

<pre class="Agda">

<a id="539" class="Symbol">{-#</a> <a id="543" class="Keyword">OPTIONS</a> <a id="551" class="Pragma">--without-K</a> <a id="563" class="Pragma">--exact-split</a> <a id="577" class="Pragma">--safe</a> <a id="584" class="Symbol">#-}</a>

<a id="589" class="Keyword">module</a> <a id="596" href="Base.html" class="Module">Base</a> <a id="601" class="Keyword">where</a>

<a id="608" class="Keyword">open</a> <a id="613" class="Keyword">import</a> <a id="620" href="Base.Overture.html" class="Module">Base.Overture</a>
<a id="634" class="Keyword">open</a> <a id="639" class="Keyword">import</a> <a id="646" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="661" class="Keyword">open</a> <a id="666" class="Keyword">import</a> <a id="673" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="713" class="Keyword">open</a> <a id="718" class="Keyword">import</a> <a id="725" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="744" class="Keyword">open</a> <a id="749" class="Keyword">import</a> <a id="756" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="767" class="Keyword">open</a> <a id="772" class="Keyword">import</a> <a id="779" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="796" class="Keyword">open</a> <a id="801" class="Keyword">import</a> <a id="808" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="823" class="Keyword">open</a> <a id="828" class="Keyword">import</a> <a id="835" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="851" class="Keyword">open</a> <a id="856" class="Keyword">import</a> <a id="863" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="879" class="Keyword">open</a> <a id="884" class="Keyword">import</a> <a id="891" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="907" class="Keyword">open</a> <a id="912" class="Keyword">import</a> <a id="919" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Base.Overture →](Base.Overture.html)</span>


