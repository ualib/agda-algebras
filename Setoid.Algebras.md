---
layout: default
title : "Setoid.Algebras module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### <a id="setoid-representation-of-algebras">Setoid Representation of Algebras</a>

<pre class="Agda">

<a id="252" class="Symbol">{-#</a> <a id="256" class="Keyword">OPTIONS</a> <a id="264" class="Pragma">--without-K</a> <a id="276" class="Pragma">--exact-split</a> <a id="290" class="Pragma">--safe</a> <a id="297" class="Symbol">#-}</a>

<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="Overture.html" class="Module">Overture</a> <a id="323" class="Keyword">using</a> <a id="329" class="Symbol">(</a><a id="330" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="332" class="Symbol">;</a> <a id="334" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a> <a id="336" class="Symbol">;</a> <a id="338" href="Overture.Signatures.html#3171" class="Function">Signature</a><a id="347" class="Symbol">)</a>

<a id="350" class="Keyword">module</a> <a id="357" href="Setoid.Algebras.html" class="Module">Setoid.Algebras</a> <a id="373" class="Symbol">{</a><a id="374" href="Setoid.Algebras.html#374" class="Bound">𝑆</a> <a id="376" class="Symbol">:</a> <a id="378" href="Overture.Signatures.html#3171" class="Function">Signature</a> <a id="388" href="Overture.Signatures.html#520" class="Generalizable">𝓞</a> <a id="390" href="Overture.Signatures.html#522" class="Generalizable">𝓥</a><a id="391" class="Symbol">}</a> <a id="393" class="Keyword">where</a>

 <a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="Setoid.Algebras.Basic.html" class="Module">Setoid.Algebras.Basic</a>        <a id="442" class="Symbol">{</a><a id="443" class="Argument">𝑆</a>  <a id="446" class="Symbol">=</a> <a id="448" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="449" class="Symbol">}</a> <a id="451" class="Keyword">public</a>
 <a id="459" class="Keyword">open</a> <a id="464" class="Keyword">import</a> <a id="471" href="Setoid.Algebras.Products.html" class="Module">Setoid.Algebras.Products</a>     <a id="500" class="Symbol">{</a><a id="501" class="Argument">𝑆</a>  <a id="504" class="Symbol">=</a> <a id="506" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="507" class="Symbol">}</a> <a id="509" class="Keyword">public</a>
 <a id="517" class="Keyword">open</a> <a id="522" class="Keyword">import</a> <a id="529" href="Setoid.Algebras.Congruences.html" class="Module">Setoid.Algebras.Congruences</a>  <a id="558" class="Symbol">{</a><a id="559" class="Argument">𝑆</a>  <a id="562" class="Symbol">=</a> <a id="564" href="Setoid.Algebras.html#374" class="Bound">𝑆</a><a id="565" class="Symbol">}</a> <a id="567" class="Keyword">public</a>

</pre>

--------------------------------

<span style="float:left;">[← Setoid.Relations.Quotients](Setoid.Relations.Quotients.html)</span>
<span style="float:right;">[Setoid.Algebras.Basic →](Setoid.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
