---
layout: default
title : UALib.Birkhoff module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="birkhoffs-theorem">Birkhoff's Theorem</a>

This chapter presents the [UALib.Birkhoff][] module of the [Agda Universal Algebra Library][].

Here we give a formal proof in [MLTT][] of Birkhoff's theorem which says that a variety is an equational class. In other terms, a class 𝒦 of algebras is closed under the operators `H`, `S`, and `P` if and only if 𝒦 is the class of algebras that satisfy some set of identities.

<pre class="Agda">

<a id="570" class="Symbol">{-#</a> <a id="574" class="Keyword">OPTIONS</a> <a id="582" class="Pragma">--without-K</a> <a id="594" class="Pragma">--exact-split</a> <a id="608" class="Pragma">--safe</a> <a id="615" class="Symbol">#-}</a>

<a id="620" class="Keyword">module</a> <a id="627" href="UALib.Birkhoff.html" class="Module">UALib.Birkhoff</a> <a id="642" class="Keyword">where</a>

<a id="649" class="Keyword">open</a> <a id="654" class="Keyword">import</a> <a id="661" href="UALib.Birkhoff.FreeAlgebra.html" class="Module">UALib.Birkhoff.FreeAlgebra</a>
<a id="688" class="Keyword">open</a> <a id="693" class="Keyword">import</a> <a id="700" href="UALib.Birkhoff.HSPLemmas.html" class="Module">UALib.Birkhoff.HSPLemmas</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="UALib.Birkhoff.HSPTheorem.html" class="Module">UALib.Birkhoff.HSPTheorem</a>

</pre>

--------------------------------------

[← UALib.Varieties.Preservation](UALib.Varieties.Preservation.html)
<span style="float:right;">[UALib.Birkhoff.FreeAlgebra →](UALib.Birkhoff.FreeAlgebra.html)</span>

{% include UALib.Links.md %}
