---
layout: default
title : "Base.Varieties module (Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Base.Varieties][] module of the [Agda Universal Algebra Library][],
where we define types for theories and their models, and for equational logic,
and we prove properties of these types.

<pre class="Agda">

<a id="431" class="Symbol">{-#</a> <a id="435" class="Keyword">OPTIONS</a> <a id="443" class="Pragma">--without-K</a> <a id="455" class="Pragma">--exact-split</a> <a id="469" class="Pragma">--safe</a> <a id="476" class="Symbol">#-}</a>

<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="Overture.html" class="Module">Overture</a> <a id="502" class="Keyword">using</a> <a id="508" class="Symbol">(</a> <a id="510" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="520" class="Symbol">;</a> <a id="522" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="524" class="Symbol">;</a> <a id="526" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="528" class="Symbol">)</a>

<a id="531" class="Keyword">module</a> <a id="538" href="Base.Varieties.html" class="Module">Base.Varieties</a> <a id="553" class="Symbol">{</a><a id="554" href="Base.Varieties.html#554" class="Bound">𝑆</a> <a id="556" class="Symbol">:</a> <a id="558" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="568" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="570" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="571" class="Symbol">}</a> <a id="573" class="Keyword">where</a>

<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="Base.Varieties.EquationalLogic.html" class="Module">Base.Varieties.EquationalLogic</a>  <a id="624" class="Symbol">{</a><a id="625" class="Argument">𝑆</a> <a id="627" class="Symbol">=</a> <a id="629" href="Base.Varieties.html#554" class="Bound">𝑆</a><a id="630" class="Symbol">}</a> <a id="632" class="Keyword">public</a>
<a id="639" class="Keyword">open</a> <a id="644" class="Keyword">import</a> <a id="651" href="Base.Varieties.Closure.html" class="Module">Base.Varieties.Closure</a>          <a id="683" class="Symbol">{</a><a id="684" class="Argument">𝑆</a> <a id="686" class="Symbol">=</a> <a id="688" href="Base.Varieties.html#554" class="Bound">𝑆</a><a id="689" class="Symbol">}</a> <a id="691" class="Keyword">public</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="Base.Varieties.Properties.html" class="Module">Base.Varieties.Properties</a>       <a id="742" class="Symbol">{</a><a id="743" class="Argument">𝑆</a> <a id="745" class="Symbol">=</a> <a id="747" href="Base.Varieties.html#554" class="Bound">𝑆</a><a id="748" class="Symbol">}</a> <a id="750" class="Keyword">public</a>
<a id="757" class="Keyword">open</a> <a id="762" class="Keyword">import</a> <a id="769" href="Base.Varieties.Preservation.html" class="Module">Base.Varieties.Preservation</a>     <a id="801" class="Symbol">{</a><a id="802" class="Argument">𝑆</a> <a id="804" class="Symbol">=</a> <a id="806" href="Base.Varieties.html#554" class="Bound">𝑆</a><a id="807" class="Symbol">}</a> <a id="809" class="Keyword">public</a>

<a id="817" class="Keyword">open</a> <a id="822" class="Keyword">import</a> <a id="829" href="Level.html" class="Module">Level</a> <a id="835" class="Keyword">using</a> <a id="841" class="Symbol">(</a> <a id="843" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="849" class="Symbol">)</a>

<a id="852" class="Keyword">module</a> <a id="859" href="Base.Varieties.html#859" class="Module">_</a> <a id="861" class="Symbol">{</a><a id="862" href="Base.Varieties.html#862" class="Bound">α</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="871" class="Symbol">}</a> <a id="873" class="Keyword">where</a>

 <a id="881" class="Keyword">open</a> <a id="886" class="Keyword">import</a> <a id="893" href="Base.Varieties.FreeAlgebras.html" class="Module">Base.Varieties.FreeAlgebras</a>  <a id="922" class="Symbol">{</a><a id="923" class="Argument">α</a> <a id="925" class="Symbol">=</a> <a id="927" href="Base.Varieties.html#862" class="Bound">α</a><a id="928" class="Symbol">}</a> <a id="930" class="Symbol">{</a><a id="931" class="Argument">𝑆</a> <a id="933" class="Symbol">=</a> <a id="935" href="Base.Varieties.html#554" class="Bound">𝑆</a><a id="936" class="Symbol">}</a> <a id="938" class="Keyword">public</a>
</pre>

---------------------------------

<span style="float:left;">[← Base.Subalgebras.Properties](Base.Subalgebras.Properties.html)</span>
<span style="float:right;">[Base.Varieties.EquationalLogic →](Base.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
