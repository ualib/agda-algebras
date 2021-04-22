---
layout: default
title : Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models and for equational logic and prove properties of these types.

Let 𝑆 be a signature. By an **identity** or **equation** in 𝑆 we mean an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻 X. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds. In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 **models** the identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature, we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊧ p ≋ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

<pre class="Agda">

<a id="1225" class="Symbol">{-#</a> <a id="1229" class="Keyword">OPTIONS</a> <a id="1237" class="Pragma">--without-K</a> <a id="1249" class="Pragma">--exact-split</a> <a id="1263" class="Pragma">--safe</a> <a id="1270" class="Symbol">#-}</a>

<a id="1275" class="Keyword">module</a> <a id="1282" href="Varieties.html" class="Module">Varieties</a> <a id="1292" class="Keyword">where</a>

<a id="1299" class="Keyword">open</a> <a id="1304" class="Keyword">import</a> <a id="1311" href="Varieties.EquationalLogic.html" class="Module">Varieties.EquationalLogic</a>
<a id="1337" class="Keyword">open</a> <a id="1342" class="Keyword">import</a> <a id="1349" href="Varieties.Varieties.html" class="Module">Varieties.Varieties</a>
<a id="1369" class="Keyword">open</a> <a id="1374" class="Keyword">import</a> <a id="1381" href="Varieties.Preservation.html" class="Module">Varieties.Preservation</a>
<a id="1404" class="Keyword">open</a> <a id="1409" class="Keyword">import</a> <a id="1416" href="Varieties.FreeAlgebras.html" class="Module">Varieties.FreeAlgebras</a>

</pre>

--------------------------------------

[← Subalgebras](Subalgebras.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
