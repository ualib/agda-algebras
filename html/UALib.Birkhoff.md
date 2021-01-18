---
layout: default
title : UALib.Birkhoff module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="birkhoffs-theorem">Birkhoff's Theorem</a>

This chapter presents the [UALib.Birkhoff][] module of the [Agda Universal Algebra Library][].

Here we give a formal proof in [MLTT][] of Birkhoff's theorem &lt;birkhoffs theorem&gt;
(%s &lt;birkhoffs theorem&gt;), which says that a variety is an
equational class. In other terms, if a class 𝒦 of algebras is closed
under the operators 𝑯, 𝑺, 𝑷, then 𝒦 is an equational class (i.e., 𝒦 is
the class of algebras that model a particular set of identities). The
sections below contain (literate) Agda code that formalizes each step of
the (informal) proof we saw above in birkhoffs theorem.
<pre class="Agda">

<a id="783" class="Symbol">{-#</a> <a id="787" class="Keyword">OPTIONS</a> <a id="795" class="Pragma">--without-K</a> <a id="807" class="Pragma">--exact-split</a> <a id="821" class="Pragma">--safe</a> <a id="828" class="Symbol">#-}</a>

<a id="833" class="Keyword">module</a> <a id="840" href="UALib.Birkhoff.html" class="Module">UALib.Birkhoff</a> <a id="855" class="Keyword">where</a>

<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="UALib.Birkhoff.FreeAlgebra.html" class="Module">UALib.Birkhoff.FreeAlgebra</a>
<a id="901" class="Keyword">open</a> <a id="906" class="Keyword">import</a> <a id="913" href="UALib.Birkhoff.Lemmata.html" class="Module">UALib.Birkhoff.Lemmata</a>
<a id="936" class="Keyword">open</a> <a id="941" class="Keyword">import</a> <a id="948" href="UALib.Birkhoff.Theorem.html" class="Module">UALib.Birkhoff.Theorem</a>

</pre>

--------------------------------------

[← UALib.Varieties](UALib.Varieties.html)
<span style="float:right;">[Agda UALib TOC ↑](UALib.html)</span>


{% include UALib.Links.md %}
