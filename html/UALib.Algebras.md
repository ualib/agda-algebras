---
layout: default
title : UALib.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebras">Algebras</a>

This chapter presents the [UALib.Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic concepts and theorems of universal algebra. In this module we codify such notions as operation, signature, and algebraic structure.

<pre class="Agda">
<a id="463" class="Symbol">{-#</a> <a id="467" class="Keyword">OPTIONS</a> <a id="475" class="Pragma">--without-K</a> <a id="487" class="Pragma">--exact-split</a> <a id="501" class="Pragma">--safe</a> <a id="508" class="Symbol">#-}</a>
</pre>

<pre class="Agda">

<a id="538" class="Keyword">module</a> <a id="545" href="UALib.Algebras.html" class="Module">UALib.Algebras</a> <a id="560" class="Keyword">where</a>

<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="605" class="Keyword">public</a>
<a id="612" class="Keyword">open</a> <a id="617" class="Keyword">import</a> <a id="624" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="648" class="Keyword">public</a>
<a id="655" class="Keyword">open</a> <a id="660" class="Keyword">import</a> <a id="667" href="UALib.Algebras.Products.html" class="Module">UALib.Algebras.Products</a> <a id="691" class="Keyword">public</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="UALib.Algebras.Lifts.html" class="Module">UALib.Algebras.Lifts</a> <a id="731" class="Keyword">public</a>

</pre>

-------------------------------------

[← UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Algebras.Signatures →](UALib.Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
