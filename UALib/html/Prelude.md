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

This section presents the [Prelude][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Prelude.lagda][], which resides in the [git repository of the Agda UALib][].

<pre class="Agda">

<a id="825" class="Symbol">{-#</a> <a id="829" class="Keyword">OPTIONS</a> <a id="837" class="Pragma">--without-K</a> <a id="849" class="Pragma">--exact-split</a> <a id="863" class="Pragma">--safe</a> <a id="870" class="Symbol">#-}</a>

<a id="875" class="Keyword">module</a> <a id="882" href="Prelude.html" class="Module">Prelude</a> <a id="890" class="Keyword">where</a>

<a id="897" class="Keyword">open</a> <a id="902" class="Keyword">import</a> <a id="909" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a>
<a id="931" class="Keyword">open</a> <a id="936" class="Keyword">import</a> <a id="943" href="Prelude.Equality.html" class="Module">Prelude.Equality</a>
<a id="960" class="Keyword">open</a> <a id="965" class="Keyword">import</a> <a id="972" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a>
<a id="995" class="Keyword">open</a> <a id="1000" class="Keyword">import</a> <a id="1007" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a>
<a id="1024" class="Keyword">open</a> <a id="1029" class="Keyword">import</a> <a id="1036" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a>

</pre>

--------------------------------------

<p></p>

[← Preface](Preface.html)
<span style="float:right;">[Prelude.Preliminaries →](Prelude.Preliminaries.html)</span>

{% include UALib.Links.md %}
