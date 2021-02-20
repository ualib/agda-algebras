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

<a id="518" class="Keyword">module</a> <a id="525" href="UALib.Algebras.html" class="Module">UALib.Algebras</a> <a id="540" class="Keyword">where</a>

<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="585" class="Keyword">public</a>
<a id="592" class="Keyword">open</a> <a id="597" class="Keyword">import</a> <a id="604" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="628" class="Keyword">public</a>
<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="UALib.Algebras.Products.html" class="Module">UALib.Algebras.Products</a> <a id="671" class="Keyword">public</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="UALib.Algebras.Congruences.html" class="Module">UALib.Algebras.Congruences</a>

</pre>

-------------------------------------

[← UALib.Relations.](UALib.Prelude.Extensionality.html)
<span style="float:right;">[UALib.Algebras.Signatures →](UALib.Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
