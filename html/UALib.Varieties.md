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
<a id="850" class="Symbol">{-#</a> <a id="854" class="Keyword">OPTIONS</a> <a id="862" class="Pragma">--without-K</a> <a id="874" class="Pragma">--exact-split</a> <a id="888" class="Pragma">--safe</a> <a id="895" class="Symbol">#-}</a>
</pre>

<pre class="Agda">

<a id="925" class="Keyword">module</a> <a id="932" href="UALib.Varieties.html" class="Module">UALib.Varieties</a> <a id="948" class="Keyword">where</a>

<a id="955" class="Keyword">open</a> <a id="960" class="Keyword">import</a> <a id="967" href="UALib.Varieties.ModelTheory.html" class="Module">UALib.Varieties.ModelTheory</a>
<a id="995" class="Keyword">open</a> <a id="1000" class="Keyword">import</a> <a id="1007" href="UALib.Varieties.EquationalLogic.html" class="Module">UALib.Varieties.EquationalLogic</a>
<a id="1039" class="Keyword">open</a> <a id="1044" class="Keyword">import</a> <a id="1051" href="UALib.Varieties.Varieties.html" class="Module">UALib.Varieties.Varieties</a>
<a id="1077" class="Keyword">open</a> <a id="1082" class="Keyword">import</a> <a id="1089" href="UALib.Varieties.Preservation.html" class="Module">UALib.Varieties.Preservation</a>

</pre>

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Birkhoff →](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}
