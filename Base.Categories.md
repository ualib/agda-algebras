---
layout: default
title : "Base.Categories module (The Agda Universal Algebra Library)"
date : "2021-08-31"
author: "agda-algebras development team"
---

## <a id="categories">Categories</a>

This is the [Base.Categories][] module of the [Agda Universal Algebra Library][].

This module is intended, not to replace or override anything in the [agda-categories][] library, but rather to collect some experiments in the use of category theory to re-express some of the basic concepts from universal algebra developed in other modules of the agda-algebra library.

The purpose of this effort twofold. First, we hope it makes the types defined in the agda-algebras library more modular and reusable.  Second, we hope that the more general language of category theory will make metaprogramming easier.  Somewhat ironically, one of our main motivations for metaprogramming is to help automate the task of recognizing when we have multiple alternative definitions (or proofs) of a single concept (or theorem) in the library and to potentially remove or consolidate such redundancy.

<pre class="Agda">

<a id="1093" class="Symbol">{-#</a> <a id="1097" class="Keyword">OPTIONS</a> <a id="1105" class="Pragma">--without-K</a> <a id="1117" class="Pragma">--exact-split</a> <a id="1131" class="Pragma">--safe</a> <a id="1138" class="Symbol">#-}</a>

<a id="1143" class="Keyword">module</a> <a id="1150" href="Base.Categories.html" class="Module">Base.Categories</a> <a id="1166" class="Keyword">where</a>

<a id="1173" class="Keyword">open</a> <a id="1178" class="Keyword">import</a> <a id="1185" href="Base.Categories.Functors.html" class="Module">Base.Categories.Functors</a>  <a id="1211" class="Keyword">public</a>

</pre>

--------------------------------------

<span style="float:left;">[← Base.Adjunction.Galois](Base.Adjunction.Galois.html)</span>
<span style="float:right;">[Base.Categories.Functors →](Base.Categories.Functors.html)</span>

{% include UALib.Links.md %}
