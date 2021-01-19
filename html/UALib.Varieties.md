---
layout: default
title : UALib.Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [UALib.Varieties][] module of the [Agda Universal Algebra Library][].

Here we define types for theories and their models and for equational logic.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.

<pre class="Agda">

<a id="783" class="Symbol">{-#</a> <a id="787" class="Keyword">OPTIONS</a> <a id="795" class="Pragma">--without-K</a> <a id="807" class="Pragma">--exact-split</a> <a id="821" class="Pragma">--safe</a> <a id="828" class="Symbol">#-}</a>

<a id="833" class="Keyword">module</a> <a id="840" href="UALib.Varieties.html" class="Module">UALib.Varieties</a> <a id="856" class="Keyword">where</a>

<a id="863" class="Keyword">open</a> <a id="868" class="Keyword">import</a> <a id="875" href="UALib.Varieties.ModelTheory.html" class="Module">UALib.Varieties.ModelTheory</a>
<a id="903" class="Keyword">open</a> <a id="908" class="Keyword">import</a> <a id="915" href="UALib.Varieties.EquationalLogic.html" class="Module">UALib.Varieties.EquationalLogic</a>
<a id="947" class="Keyword">open</a> <a id="952" class="Keyword">import</a> <a id="959" href="UALib.Varieties.Varieties.html" class="Module">UALib.Varieties.Varieties</a>
<a id="985" class="Keyword">open</a> <a id="990" class="Keyword">import</a> <a id="997" href="UALib.Varieties.Preservation.html" class="Module">UALib.Varieties.Preservation</a>

</pre>

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Birkhoff →](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}
