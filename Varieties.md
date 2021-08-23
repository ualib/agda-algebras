---
layout: default
title : Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

## Equations and Varieties

This is the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

Let 𝑆 be a signature. By an **identity** or **equation** in 𝑆 we mean an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻 X. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds. In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 **models** the identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature, we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊫ 𝑝 ≈ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

<pre class="Agda">

<a id="1201" class="Symbol">{-#</a> <a id="1205" class="Keyword">OPTIONS</a> <a id="1213" class="Pragma">--without-K</a> <a id="1225" class="Pragma">--exact-split</a> <a id="1239" class="Pragma">--safe</a> <a id="1246" class="Symbol">#-}</a>

<a id="1251" class="Keyword">module</a> <a id="1258" href="Varieties.html" class="Module">Varieties</a> <a id="1268" class="Keyword">where</a>

<a id="1275" class="Keyword">open</a> <a id="1280" class="Keyword">import</a> <a id="1287" href="Varieties.EquationalLogic.html" class="Module">Varieties.EquationalLogic</a>
<a id="1313" class="Keyword">open</a> <a id="1318" class="Keyword">import</a> <a id="1325" href="Varieties.Closure.html" class="Module">Varieties.Closure</a>
<a id="1343" class="Keyword">open</a> <a id="1348" class="Keyword">import</a> <a id="1355" href="Varieties.Properties.html" class="Module">Varieties.Properties</a>
<a id="1376" class="Keyword">open</a> <a id="1381" class="Keyword">import</a> <a id="1388" href="Varieties.Preservation.html" class="Module">Varieties.Preservation</a>
<a id="1411" class="Keyword">open</a> <a id="1416" class="Keyword">import</a> <a id="1423" href="Varieties.FreeAlgebras.html" class="Module">Varieties.FreeAlgebras</a>
<a id="1446" class="Keyword">open</a> <a id="1451" class="Keyword">import</a> <a id="1458" href="Varieties.Setoid.html" class="Module">Varieties.Setoid</a>

</pre>


In the Varieties.Properties submodule we prove some closure and invariance properties of ⊧.

In the Varieties.Entailment submodule, we define the entailment relation and prove soundness and completeness of the entailment rules.




---------------------------------

<br>
<br>

[← Subalgebras.Setoid.Properties](Subalgebras.Setoid.Properties.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
