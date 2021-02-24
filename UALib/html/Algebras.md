---
layout: default
title : UALib.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This chapter presents the [UALib.Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic concepts and theorems of universal algebra. In this module we codify such notions as operation, signature, and algebraic structure.

<pre class="Agda">

<a id="468" class="Symbol">{-#</a> <a id="472" class="Keyword">OPTIONS</a> <a id="480" class="Pragma">--without-K</a> <a id="492" class="Pragma">--exact-split</a> <a id="506" class="Pragma">--safe</a> <a id="513" class="Symbol">#-}</a>

<a id="518" class="Keyword">module</a> <a id="525" href="Algebras.html" class="Module">Algebras</a> <a id="534" class="Keyword">where</a>

<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="573" class="Keyword">public</a>
<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="610" class="Keyword">public</a>
<a id="617" class="Keyword">open</a> <a id="622" class="Keyword">import</a> <a id="629" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="647" class="Keyword">public</a>
<a id="654" class="Keyword">open</a> <a id="659" class="Keyword">import</a> <a id="666" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>

</pre>

-------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras.Signatures →](Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
