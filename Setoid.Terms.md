---
layout: default
title : "Setoid.Terms module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

### <a id="terms-on-setoids">Terms on setoids</a>

This is the [Setoid.Terms][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="299" class="Symbol">{-#</a> <a id="303" class="Keyword">OPTIONS</a> <a id="311" class="Pragma">--without-K</a> <a id="323" class="Pragma">--exact-split</a> <a id="337" class="Pragma">--safe</a> <a id="344" class="Symbol">#-}</a>

<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="Overture.html" class="Module">Overture</a> <a id="370" class="Keyword">using</a> <a id="376" class="Symbol">(</a><a id="377" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="379" class="Symbol">;</a> <a id="381" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a> <a id="383" class="Symbol">;</a> <a id="385" href="Overture.Signatures.html#3171" class="Function">Signature</a><a id="394" class="Symbol">)</a>

<a id="397" class="Keyword">module</a> <a id="404" href="Setoid.Terms.html" class="Module">Setoid.Terms</a> <a id="417" class="Symbol">{</a><a id="418" href="Setoid.Terms.html#418" class="Bound">𝑆</a> <a id="420" class="Symbol">:</a> <a id="422" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="432" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="434" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a><a id="435" class="Symbol">}</a> <a id="437" class="Keyword">where</a>

<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="Setoid.Terms.Basic.html" class="Module">Setoid.Terms.Basic</a>       <a id="481" class="Symbol">{</a><a id="482" class="Argument">𝑆</a> <a id="484" class="Symbol">=</a> <a id="486" href="Setoid.Terms.html#418" class="Bound">𝑆</a><a id="487" class="Symbol">}</a> <a id="489" class="Keyword">public</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="Setoid.Terms.Properties.html" class="Module">Setoid.Terms.Properties</a>  <a id="533" class="Symbol">{</a><a id="534" class="Argument">𝑆</a> <a id="536" class="Symbol">=</a> <a id="538" href="Setoid.Terms.html#418" class="Bound">𝑆</a><a id="539" class="Symbol">}</a> <a id="541" class="Keyword">public</a>
<a id="548" class="Keyword">open</a> <a id="553" class="Keyword">import</a> <a id="560" href="Setoid.Terms.Operations.html" class="Module">Setoid.Terms.Operations</a>  <a id="585" class="Symbol">{</a><a id="586" class="Argument">𝑆</a> <a id="588" class="Symbol">=</a> <a id="590" href="Setoid.Terms.html#418" class="Bound">𝑆</a><a id="591" class="Symbol">}</a> <a id="593" class="Keyword">public</a>
</pre>

--------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.HomomorphicImages](Setoid.Homomorphisms.HomomorphicImages.html)</span>
<span style="float:right;">[Setoid.Terms.Basic →](Setoid.Terms.Basic.html)</span>

{% include UALib.Links.md %}
