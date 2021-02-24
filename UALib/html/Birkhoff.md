---
layout: default
title : Birkhoff module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="birkhoffs-theorem">Birkhoff's Theorem</a>

This chapter presents the [Birkhoff][] module of the [Agda Universal Algebra Library][].

Here we give a formal proof in [MLTT][] of Birkhoff's theorem which says that a variety is an equational class. In other terms, a class 𝒦 of algebras is closed under the operators `H`, `S`, and `P` if and only if 𝒦 is the class of algebras that satisfy some set of identities.

<pre class="Agda">

<a id="558" class="Symbol">{-#</a> <a id="562" class="Keyword">OPTIONS</a> <a id="570" class="Pragma">--without-K</a> <a id="582" class="Pragma">--exact-split</a> <a id="596" class="Pragma">--safe</a> <a id="603" class="Symbol">#-}</a>

<a id="608" class="Keyword">module</a> <a id="615" href="Birkhoff.html" class="Module">Birkhoff</a> <a id="624" class="Keyword">where</a>

<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Birkhoff.FreeAlgebra.html" class="Module">Birkhoff.FreeAlgebra</a>
<a id="664" class="Keyword">open</a> <a id="669" class="Keyword">import</a> <a id="676" href="Birkhoff.HSPTheorem.html" class="Module">Birkhoff.HSPTheorem</a>

</pre>

--------------------------------------

[← Varieties.Preservation](Varieties.Preservation.html)
<span style="float:right;">[Birkhoff.FreeAlgebra →](Birkhoff.FreeAlgebra.html)</span>

{% include UALib.Links.md %}
