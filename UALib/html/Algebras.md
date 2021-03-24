---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This chapter presents the [Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic definitions and theorems of universal algebra. In this module we define types that codify the notions of operation, signature, algebra, product of algebras, congruence relation, and quotient algebra, and prove many of their basic properties.

<pre class="Agda">

<a id="566" class="Symbol">{-#</a> <a id="570" class="Keyword">OPTIONS</a> <a id="578" class="Pragma">--without-K</a> <a id="590" class="Pragma">--exact-split</a> <a id="604" class="Pragma">--safe</a> <a id="611" class="Symbol">#-}</a>

<a id="616" class="Keyword">module</a> <a id="623" href="Algebras.html" class="Module">Algebras</a> <a id="632" class="Keyword">where</a>

<a id="639" class="Keyword">open</a> <a id="644" class="Keyword">import</a> <a id="651" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="671" class="Keyword">public</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="708" class="Keyword">public</a>
<a id="715" class="Keyword">open</a> <a id="720" class="Keyword">import</a> <a id="727" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="745" class="Keyword">public</a>
<a id="752" class="Keyword">open</a> <a id="757" class="Keyword">import</a> <a id="764" href="Algebras.Congruences.html" class="Module">Algebras.Congruences</a>

</pre>

-------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras.Signatures →](Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
