---
layout: default
title : "Setoid.Varieties module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="equations-and-varieties-for-setoids">Equations and Varieties for Setoids</a>

This is the [Setoid.Varieties][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="341" class="Symbol">{-#</a> <a id="345" class="Keyword">OPTIONS</a> <a id="353" class="Pragma">--without-K</a> <a id="365" class="Pragma">--exact-split</a> <a id="379" class="Pragma">--safe</a> <a id="386" class="Symbol">#-}</a>

<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="Overture.html" class="Module">Overture</a> <a id="412" class="Keyword">using</a> <a id="418" class="Symbol">(</a><a id="419" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="421" class="Symbol">;</a> <a id="423" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="425" class="Symbol">;</a> <a id="427" href="Overture.Signatures.html#3282" class="Function">Signature</a><a id="436" class="Symbol">)</a>

<a id="439" class="Keyword">module</a> <a id="446" href="Setoid.Varieties.html" class="Module">Setoid.Varieties</a> <a id="463" class="Symbol">{</a><a id="464" href="Setoid.Varieties.html#464" class="Bound">𝑆</a> <a id="466" class="Symbol">:</a> <a id="468" href="Overture.Signatures.html#3282" class="Function">Signature</a> <a id="478" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="480" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="481" class="Symbol">}</a> <a id="483" class="Keyword">where</a>

<a id="490" class="Keyword">open</a> <a id="495" class="Keyword">import</a> <a id="502" href="Setoid.Varieties.EquationalLogic.html" class="Module">Setoid.Varieties.EquationalLogic</a>   <a id="537" class="Symbol">{</a><a id="538" class="Argument">𝑆</a> <a id="540" class="Symbol">=</a> <a id="542" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="543" class="Symbol">}</a> <a id="545" class="Keyword">public</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="Setoid.Varieties.SoundAndComplete.html" class="Module">Setoid.Varieties.SoundAndComplete</a>  <a id="599" class="Symbol">{</a><a id="600" class="Argument">𝑆</a> <a id="602" class="Symbol">=</a> <a id="604" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="605" class="Symbol">}</a> <a id="607" class="Keyword">public</a>
<a id="614" class="Keyword">open</a> <a id="619" class="Keyword">import</a> <a id="626" href="Setoid.Varieties.Closure.html" class="Module">Setoid.Varieties.Closure</a>           <a id="661" class="Symbol">{</a><a id="662" class="Argument">𝑆</a> <a id="664" class="Symbol">=</a> <a id="666" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="667" class="Symbol">}</a> <a id="669" class="Keyword">public</a>
<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="Setoid.Varieties.Properties.html" class="Module">Setoid.Varieties.Properties</a>        <a id="723" class="Symbol">{</a><a id="724" class="Argument">𝑆</a> <a id="726" class="Symbol">=</a> <a id="728" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="729" class="Symbol">}</a> <a id="731" class="Keyword">public</a>
<a id="738" class="Keyword">open</a> <a id="743" class="Keyword">import</a> <a id="750" href="Setoid.Varieties.Preservation.html" class="Module">Setoid.Varieties.Preservation</a>      <a id="785" class="Symbol">{</a><a id="786" class="Argument">𝑆</a> <a id="788" class="Symbol">=</a> <a id="790" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="791" class="Symbol">}</a> <a id="793" class="Keyword">public</a>
<a id="800" class="Keyword">open</a> <a id="805" class="Keyword">import</a> <a id="812" href="Setoid.Varieties.FreeAlgebras.html" class="Module">Setoid.Varieties.FreeAlgebras</a>      <a id="847" class="Symbol">{</a><a id="848" class="Argument">𝑆</a> <a id="850" class="Symbol">=</a> <a id="852" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="853" class="Symbol">}</a> <a id="855" class="Keyword">public</a>
<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="Setoid.Varieties.HSP.html" class="Module">Setoid.Varieties.HSP</a>               <a id="909" class="Symbol">{</a><a id="910" class="Argument">𝑆</a> <a id="912" class="Symbol">=</a> <a id="914" href="Setoid.Varieties.html#464" class="Bound">𝑆</a><a id="915" class="Symbol">}</a> <a id="917" class="Keyword">public</a>

</pre>

--------------------------------

<span style="float:left;">[← Setoid.Subalgebras.Properties](Setoid.Subalgebras.Properties.html)</span>
<span style="float:right;">[Setoid.Varieties.EquationalLogic →](Setoid.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
