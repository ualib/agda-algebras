---
layout: default
title : "Categories module (The Agda Universal Algebra Library)"
date : "2021-08-31"
author: "agda-algebras development team"
---

## <a id="categories">Categories</a>

This is the [Categories][] module of the [Agda Universal Algebra Library][].

This module is intended, not to replace or override anything in the [agda-categories][] library, but rather to collect some experiments in the use of category theory to re-express some of the basic concepts from universal algebra developed in other modules of the agda-algebra library.

The purpose of this effort twofold. First, we hope it makes the types defined in the agda-algebras library more modular and reusable.  Second, we hope that the more general language of category theory will make metaprogramming easier.  Somewhat ironically, one of our main motivations for metaprogramming is to help automate the task of recognizing when we have multiple alternative definitions (or proofs) of a single concept (or theorem) in the library and to potentially remove or consolidate such redundancy.

<pre class="Agda">

<a id="1083" class="Symbol">{-#</a> <a id="1087" class="Keyword">OPTIONS</a> <a id="1095" class="Pragma">--without-K</a> <a id="1107" class="Pragma">--exact-split</a> <a id="1121" class="Pragma">--safe</a> <a id="1128" class="Symbol">#-}</a>

<a id="1133" class="Keyword">module</a> <a id="1140" href="Categories.html" class="Module">Categories</a> <a id="1151" class="Keyword">where</a>

<a id="1158" class="Keyword">open</a> <a id="1163" class="Keyword">import</a> <a id="1170" href="Categories.Functors.html" class="Module">Categories.Functors</a>

</pre>

--------------------------------------

<span style="float:left;">[← Structures.Sigma.Isos](Structures.Sigma.Isos.html)</span>
<span style="float:right;">[Categories.Functors →](Categories.Functors.html)</span>

{% include UALib.Links.md %}
