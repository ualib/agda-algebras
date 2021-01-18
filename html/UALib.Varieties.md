---
layout: default
title : UALib.Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [UALib.Varieties][] module of the [Agda Universal Algebra Library][].

Here we define type for for theories and their models, and equational logic.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators H, S, P that are composable.  Separately, we define an inductive type `V` to represent closure under `H`, `S`, and `P`.

<!-- consequently, we expect that `V 𝒦 ≡ H (S (P 𝒦))` holds each class 𝒦 of algebras of a fixed signature. -->

<pre class="Agda">

<a id="845" class="Symbol">{-#</a> <a id="849" class="Keyword">OPTIONS</a> <a id="857" class="Pragma">--without-K</a> <a id="869" class="Pragma">--exact-split</a> <a id="883" class="Pragma">--safe</a> <a id="890" class="Symbol">#-}</a>

<a id="895" class="Keyword">module</a> <a id="902" href="UALib.Varieties.html" class="Module">UALib.Varieties</a> <a id="918" class="Keyword">where</a>

<a id="925" class="Keyword">open</a> <a id="930" class="Keyword">import</a> <a id="937" href="UALib.Varieties.ModelTheory.html" class="Module">UALib.Varieties.ModelTheory</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="UALib.Varieties.EquationalLogic.html" class="Module">UALib.Varieties.EquationalLogic</a>
<a id="1009" class="Keyword">open</a> <a id="1014" class="Keyword">import</a> <a id="1021" href="UALib.Varieties.Varieties.html" class="Module">UALib.Varieties.Varieties</a>
<a id="1047" class="Keyword">open</a> <a id="1052" class="Keyword">import</a> <a id="1059" href="UALib.Varieties.Preservation.html" class="Module">UALib.Varieties.Preservation</a>

</pre>

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Birkhoff →](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}
