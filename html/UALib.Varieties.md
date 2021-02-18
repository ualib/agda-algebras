---
layout: default
title : UALib.Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [UALib.Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models and for equational logic and prove properties of these types.

Let 𝑆 be a signature. By an **identity** or **equation** in 𝑆 we mean an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻 X. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds. In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 **models** the identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature, we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊧ p ≋ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

<pre class="Agda">

<a id="1237" class="Symbol">{-#</a> <a id="1241" class="Keyword">OPTIONS</a> <a id="1249" class="Pragma">--without-K</a> <a id="1261" class="Pragma">--exact-split</a> <a id="1275" class="Pragma">--safe</a> <a id="1282" class="Symbol">#-}</a>

<a id="1287" class="Keyword">module</a> <a id="1294" href="UALib.Varieties.html" class="Module">UALib.Varieties</a> <a id="1310" class="Keyword">where</a>

<a id="1317" class="Keyword">open</a> <a id="1322" class="Keyword">import</a> <a id="1329" href="UALib.Varieties.ModelTheory.html" class="Module">UALib.Varieties.ModelTheory</a>
<a id="1357" class="Keyword">open</a> <a id="1362" class="Keyword">import</a> <a id="1369" href="UALib.Varieties.EquationalLogic.html" class="Module">UALib.Varieties.EquationalLogic</a>
<a id="1401" class="Keyword">open</a> <a id="1406" class="Keyword">import</a> <a id="1413" href="UALib.Varieties.Varieties.html" class="Module">UALib.Varieties.Varieties</a>
<a id="1439" class="Keyword">open</a> <a id="1444" class="Keyword">import</a> <a id="1451" href="UALib.Varieties.Preservation.html" class="Module">UALib.Varieties.Preservation</a>

</pre>

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Varieties.ModelTheory →](UALib.Varieties.ModelTheory.html)</span>

{% include UALib.Links.md %}
