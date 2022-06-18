---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid](Setoid.html) module).

(We have also started developing in parallel the `cubical-agda-algebras` library, based on Cubical Agda.)

<pre class="Agda">

<a id="538" class="Symbol">{-#</a> <a id="542" class="Keyword">OPTIONS</a> <a id="550" class="Pragma">--without-K</a> <a id="562" class="Pragma">--exact-split</a> <a id="576" class="Pragma">--safe</a> <a id="583" class="Symbol">#-}</a>

<a id="588" class="Keyword">module</a> <a id="595" href="Base.html" class="Module">Base</a> <a id="600" class="Keyword">where</a>

<a id="607" class="Keyword">open</a> <a id="612" class="Keyword">import</a> <a id="619" href="Base.Relations.html" class="Module">Base.Relations</a>
<a id="634" class="Keyword">open</a> <a id="639" class="Keyword">import</a> <a id="646" href="Base.Functions.html" class="Module">Base.Functions</a>
<a id="661" class="Keyword">open</a> <a id="666" class="Keyword">import</a> <a id="673" href="Base.Equality.html" class="Module">Base.Equality</a>
<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="Base.Adjunction.html" class="Module">Base.Adjunction</a>
<a id="715" class="Keyword">open</a> <a id="720" class="Keyword">import</a> <a id="727" href="Base.Algebras.html" class="Module">Base.Algebras</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>
<a id="772" class="Keyword">open</a> <a id="777" class="Keyword">import</a> <a id="784" href="Base.Terms.html" class="Module">Base.Terms</a>
<a id="795" class="Keyword">open</a> <a id="800" class="Keyword">import</a> <a id="807" href="Base.Subalgebras.html" class="Module">Base.Subalgebras</a>
<a id="824" class="Keyword">open</a> <a id="829" class="Keyword">import</a> <a id="836" href="Base.Varieties.html" class="Module">Base.Varieties</a>
<a id="851" class="Keyword">open</a> <a id="856" class="Keyword">import</a> <a id="863" href="Base.Structures.html" class="Module">Base.Structures</a>
<a id="879" class="Keyword">open</a> <a id="884" class="Keyword">import</a> <a id="891" href="Base.Categories.html" class="Module">Base.Categories</a>
<a id="907" class="Keyword">open</a> <a id="912" class="Keyword">import</a> <a id="919" href="Base.Complexity.html" class="Module">Base.Complexity</a>

</pre>

--------------------------------------

<span style="float:left;">[↑ agda-algebras](index.html)</span>
<span style="float:right;">[Base.Relations →](Base.Relations.html)</span>


