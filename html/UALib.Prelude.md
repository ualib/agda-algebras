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

<a id="887" class="Keyword">module</a> <a id="894" href="UALib.Prelude.html" class="Module">UALib.Prelude</a> <a id="908" class="Keyword">where</a>

<a id="915" class="Keyword">open</a> <a id="920" class="Keyword">import</a> <a id="927" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="955" class="Keyword">public</a>
<a id="962" class="Keyword">open</a> <a id="967" class="Keyword">import</a> <a id="974" href="UALib.Prelude.Equality.html" class="Module">UALib.Prelude.Equality</a> <a id="997" class="Keyword">public</a>
<a id="1004" class="Keyword">open</a> <a id="1009" class="Keyword">import</a> <a id="1016" href="UALib.Prelude.Inverses.html" class="Module">UALib.Prelude.Inverses</a> <a id="1039" class="Keyword">public</a>
<a id="1046" class="Keyword">open</a> <a id="1051" class="Keyword">import</a> <a id="1058" href="UALib.Prelude.Extensionality.html" class="Module">UALib.Prelude.Extensionality</a> <a id="1087" class="Keyword">public</a>

</pre>

--------------------------------------

[← UALib.Preface](UALib.Preface.html)
<span style="float:right;">[UALib.Algebras →](UALib.Algebras.html)</span>

{% include UALib.Links.md %}
