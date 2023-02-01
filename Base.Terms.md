---
layout: default
title : "Base.Terms module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="types-for-terms">Types for Terms</a>

This is the [Base.Terms][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="292" class="Symbol">{-#</a> <a id="296" class="Keyword">OPTIONS</a> <a id="304" class="Pragma">--without-K</a> <a id="316" class="Pragma">--exact-split</a> <a id="330" class="Pragma">--safe</a> <a id="337" class="Symbol">#-}</a>

<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="Overture.html" class="Module">Overture</a> <a id="363" class="Keyword">using</a> <a id="369" class="Symbol">(</a><a id="370" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="380" class="Symbol">;</a> <a id="382" href="Overture.Signatures.html#645" class="Generalizable">𝓞</a> <a id="384" class="Symbol">;</a> <a id="386" href="Overture.Signatures.html#647" class="Generalizable">𝓥</a> <a id="388" class="Symbol">)</a>

<a id="391" class="Keyword">module</a> <a id="398" href="Base.Terms.html" class="Module">Base.Terms</a> <a id="409" class="Symbol">{</a><a id="410" href="Base.Terms.html#410" class="Bound">𝑆</a> <a id="412" class="Symbol">:</a> <a id="414" href="Overture.Signatures.html#3300" class="Function">Signature</a> <a id="424" href="Overture.Signatures.html#645" class="Generalizable">𝓞</a> <a id="426" href="Overture.Signatures.html#647" class="Generalizable">𝓥</a><a id="427" class="Symbol">}</a> <a id="429" class="Keyword">where</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Base.Terms.Basic.html" class="Module">Base.Terms.Basic</a>       <a id="471" class="Symbol">{</a><a id="472" class="Argument">𝑆</a> <a id="474" class="Symbol">=</a> <a id="476" href="Base.Terms.html#410" class="Bound">𝑆</a><a id="477" class="Symbol">}</a> <a id="479" class="Keyword">public</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="Base.Terms.Properties.html" class="Module">Base.Terms.Properties</a>  <a id="521" class="Symbol">{</a><a id="522" class="Argument">𝑆</a> <a id="524" class="Symbol">=</a> <a id="526" href="Base.Terms.html#410" class="Bound">𝑆</a><a id="527" class="Symbol">}</a> <a id="529" class="Keyword">public</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="Base.Terms.Operations.html" class="Module">Base.Terms.Operations</a>  <a id="571" class="Symbol">{</a><a id="572" class="Argument">𝑆</a> <a id="574" class="Symbol">=</a> <a id="576" href="Base.Terms.html#410" class="Bound">𝑆</a><a id="577" class="Symbol">}</a> <a id="579" class="Keyword">public</a>

</pre>

-------------------------------------

<span style="float:left;">[← Base.Homomorphisms.HomomorphicImages](Base.Homomorphisms.HomomorphicImages.html)</span>
<span style="float:right;">[Base.Terms.Basic →](Base.Terms.Basic.html)</span>

{% include UALib.Links.md %}
