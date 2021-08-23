---
layout: default
title : Structures.Terms.Basic
date : 2021-07-02
author: [agda-algebras development team][]
---

<pre class="Agda">

<a id="132" class="Symbol">{-#</a> <a id="136" class="Keyword">OPTIONS</a> <a id="144" class="Pragma">--without-K</a> <a id="156" class="Pragma">--exact-split</a> <a id="170" class="Pragma">--safe</a> <a id="177" class="Symbol">#-}</a>

<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="Level.html" class="Module">Level</a>            <a id="211" class="Keyword">using</a> <a id="217" class="Symbol">(</a> <a id="219" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="225" class="Symbol">)</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="Structures.Basic.html" class="Module">Structures.Basic</a> <a id="256" class="Keyword">using</a> <a id="262" class="Symbol">(</a> <a id="264" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="274" class="Symbol">)</a>


<a id="278" class="Keyword">module</a> <a id="285" href="Structures.Terms.Basic.html" class="Module">Structures.Terms.Basic</a> <a id="308" class="Symbol">{</a><a id="309" href="Structures.Terms.Basic.html#309" class="Bound">𝓞</a> <a id="311" href="Structures.Terms.Basic.html#311" class="Bound">𝓥</a> <a id="313" class="Symbol">:</a> <a id="315" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="320" class="Symbol">}{</a><a id="322" href="Structures.Terms.Basic.html#322" class="Bound">𝐹</a> <a id="324" class="Symbol">:</a> <a id="326" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="336" href="Structures.Terms.Basic.html#309" class="Bound">𝓞</a> <a id="338" href="Structures.Terms.Basic.html#311" class="Bound">𝓥</a><a id="339" class="Symbol">}</a> <a id="341" class="Keyword">where</a>

<a id="348" class="Keyword">open</a> <a id="353" class="Keyword">import</a> <a id="360" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="375" class="Keyword">using</a> <a id="381" class="Symbol">(</a> <a id="383" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="388" class="Symbol">;</a> <a id="390" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="394" class="Symbol">)</a> <a id="396" class="Keyword">renaming</a> <a id="405" class="Symbol">(</a> <a id="407" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="411" class="Symbol">to</a> <a id="414" class="Primitive">Type</a> <a id="419" class="Symbol">)</a>

<a id="422" class="Keyword">open</a> <a id="427" href="Structures.Basic.html#1124" class="Module">signature</a>

<a id="438" class="Keyword">data</a> <a id="Term"></a><a id="443" href="Structures.Terms.Basic.html#443" class="Datatype">Term</a>  <a id="449" class="Symbol">{</a><a id="450" href="Structures.Terms.Basic.html#450" class="Bound">χ</a> <a id="452" class="Symbol">:</a> <a id="454" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="459" class="Symbol">}</a> <a id="461" class="Symbol">(</a><a id="462" href="Structures.Terms.Basic.html#462" class="Bound">X</a> <a id="464" class="Symbol">:</a> <a id="466" href="Structures.Terms.Basic.html#414" class="Primitive">Type</a> <a id="471" href="Structures.Terms.Basic.html#450" class="Bound">χ</a> <a id="473" class="Symbol">)</a> <a id="475" class="Symbol">:</a> <a id="477" href="Structures.Terms.Basic.html#414" class="Primitive">Type</a> <a id="482" class="Symbol">(</a><a id="483" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="488" class="Symbol">(</a><a id="489" href="Structures.Terms.Basic.html#309" class="Bound">𝓞</a> <a id="491" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="493" href="Structures.Terms.Basic.html#311" class="Bound">𝓥</a> <a id="495" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="497" href="Structures.Terms.Basic.html#450" class="Bound">χ</a><a id="498" class="Symbol">))</a>  <a id="502" class="Keyword">where</a>
 <a id="Term.ℊ"></a><a id="509" href="Structures.Terms.Basic.html#509" class="InductiveConstructor">ℊ</a> <a id="511" class="Symbol">:</a> <a id="513" href="Structures.Terms.Basic.html#462" class="Bound">X</a> <a id="515" class="Symbol">→</a> <a id="517" href="Structures.Terms.Basic.html#443" class="Datatype">Term</a> <a id="522" href="Structures.Terms.Basic.html#462" class="Bound">X</a>    <a id="527" class="Comment">-- (ℊ for &quot;generator&quot;)</a>
 <a id="Term.node"></a><a id="551" href="Structures.Terms.Basic.html#551" class="InductiveConstructor">node</a> <a id="556" class="Symbol">:</a> <a id="558" class="Symbol">(</a><a id="559" href="Structures.Terms.Basic.html#559" class="Bound">f</a> <a id="561" class="Symbol">:</a> <a id="563" href="Structures.Basic.html#1185" class="Field">symbol</a> <a id="570" href="Structures.Terms.Basic.html#322" class="Bound">𝐹</a><a id="571" class="Symbol">)(</a><a id="573" href="Structures.Terms.Basic.html#573" class="Bound">𝑡</a> <a id="575" class="Symbol">:</a> <a id="577" class="Symbol">(</a><a id="578" href="Structures.Basic.html#1203" class="Field">arity</a> <a id="584" href="Structures.Terms.Basic.html#322" class="Bound">𝐹</a><a id="585" class="Symbol">)</a> <a id="587" href="Structures.Terms.Basic.html#559" class="Bound">f</a> <a id="589" class="Symbol">→</a> <a id="591" href="Structures.Terms.Basic.html#443" class="Datatype">Term</a> <a id="596" href="Structures.Terms.Basic.html#462" class="Bound">X</a><a id="597" class="Symbol">)</a> <a id="599" class="Symbol">→</a> <a id="601" href="Structures.Terms.Basic.html#443" class="Datatype">Term</a> <a id="606" href="Structures.Terms.Basic.html#462" class="Bound">X</a>

</pre>

--------------------------------

<br>
<br>

[↑ Structures.Terms](Structures.Terms.html)
<span style="float:right;">[Structures.Terms.Operations →](Structures.Terms.Operations.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
