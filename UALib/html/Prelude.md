---
layout: default
title : UALib.Prelude module (Agda Universal Algebra Library)
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

This chapter presents the [UALib.Prelude][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Prelude.lagda][], which resides in the [git repository of the Agda UALib][].

<pre class="Agda">

<a id="837" class="Symbol">{-#</a> <a id="841" class="Keyword">OPTIONS</a> <a id="849" class="Pragma">--without-K</a> <a id="861" class="Pragma">--exact-split</a> <a id="875" class="Pragma">--safe</a> <a id="882" class="Symbol">#-}</a>

<a id="887" class="Keyword">module</a> <a id="894" href="Prelude.html" class="Module">Prelude</a> <a id="902" class="Keyword">where</a>

<a id="909" class="Keyword">open</a> <a id="914" class="Keyword">import</a> <a id="921" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="943" class="Keyword">public</a>
<a id="950" class="Keyword">open</a> <a id="955" class="Keyword">import</a> <a id="962" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="979" class="Keyword">public</a>
<a id="986" class="Keyword">open</a> <a id="991" class="Keyword">import</a> <a id="998" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a> <a id="1015" class="Keyword">public</a>
<a id="1022" class="Keyword">open</a> <a id="1027" class="Keyword">import</a> <a id="1034" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="1057" class="Keyword">public</a>
<a id="1064" class="Keyword">open</a> <a id="1069" class="Keyword">import</a> <a id="1076" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="1090" class="Keyword">public</a>

</pre>

--------------------------------------

[← UALib.Preface](UALib.Preface.html)
<span style="float:right;">[UALib.Prelude.Preliminaries →](UALib.Prelude.Preliminaries.html)</span>

{% include UALib.Links.md %}
