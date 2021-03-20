---
layout: default
title : Prelude module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: Prelude.lagda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 14 Jan 2021
REF: Parts of this module are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

## <a id="prelude">Prelude</a>

This is the [Prelude][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Prelude.lagda][], which resides in the [git repository of the Agda UALib][].

<pre class="Agda">

<a id="811" class="Symbol">{-#</a> <a id="815" class="Keyword">OPTIONS</a> <a id="823" class="Pragma">--without-K</a> <a id="835" class="Pragma">--exact-split</a> <a id="849" class="Pragma">--safe</a> <a id="856" class="Symbol">#-}</a>

<a id="861" class="Keyword">module</a> <a id="868" href="Prelude.html" class="Module">Prelude</a> <a id="876" class="Keyword">where</a>

<a id="883" class="Keyword">open</a> <a id="888" class="Keyword">import</a> <a id="895" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="Prelude.Equality.html" class="Module">Prelude.Equality</a>
<a id="946" class="Keyword">open</a> <a id="951" class="Keyword">import</a> <a id="958" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a>
<a id="981" class="Keyword">open</a> <a id="986" class="Keyword">import</a> <a id="993" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a>
<a id="1010" class="Keyword">open</a> <a id="1015" class="Keyword">import</a> <a id="1022" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a>

</pre>

--------------------------------------

<p></p>

[← Preface](Preface.html)
<span style="float:right;">[Prelude.Preliminaries →](Prelude.Preliminaries.html)</span>

{% include UALib.Links.md %}
