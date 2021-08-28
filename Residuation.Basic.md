---
layout: default
title : Residuation.Basic module (The Agda Universal Algebra Library)
date : 2021-07-12
author: [agda-algebras development team][]
---

## <a id="basic-definitions">Basic definitions</a>

<pre class="Agda">

<a id="223" class="Symbol">{-#</a> <a id="227" class="Keyword">OPTIONS</a> <a id="235" class="Pragma">--without-K</a> <a id="247" class="Pragma">--exact-split</a> <a id="261" class="Pragma">--safe</a> <a id="268" class="Symbol">#-}</a>

<a id="273" class="Keyword">module</a> <a id="280" href="Residuation.Basic.html" class="Module">Residuation.Basic</a> <a id="298" class="Keyword">where</a>

<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>          <a id="341" class="Keyword">using</a> <a id="347" class="Symbol">(</a> <a id="349" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="353" class="Symbol">;</a>  <a id="356" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="362" class="Symbol">;</a> <a id="364" href="Agda.Primitive.html#780" class="Primitive">lsuc</a><a id="368" class="Symbol">)</a> <a id="370" class="Keyword">renaming</a> <a id="379" class="Symbol">(</a> <a id="381" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="385" class="Symbol">to</a> <a id="388" class="Primitive">Type</a> <a id="393" class="Symbol">)</a>
<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="Function.Base.html" class="Module">Function.Base</a>           <a id="431" class="Keyword">using</a> <a id="437" class="Symbol">(</a> <a id="439" href="Function.Base.html#6285" class="Function Operator">_on_</a> <a id="444" class="Symbol">)</a>
<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a> <a id="482" class="Keyword">using</a> <a id="488" class="Symbol">(</a> <a id="490" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="496" class="Symbol">)</a>
<a id="498" class="Keyword">open</a> <a id="503" class="Keyword">import</a> <a id="510" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>    <a id="534" class="Keyword">using</a> <a id="540" class="Symbol">(</a> <a id="542" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="556" class="Symbol">)</a>


<a id="560" class="Keyword">module</a> <a id="567" href="Residuation.Basic.html#567" class="Module">_</a> <a id="569" class="Symbol">{</a><a id="570" href="Residuation.Basic.html#570" class="Bound">α</a> <a id="572" href="Residuation.Basic.html#572" class="Bound">ιᵃ</a> <a id="575" href="Residuation.Basic.html#575" class="Bound">ρᵃ</a> <a id="578" class="Symbol">:</a> <a id="580" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="585" class="Symbol">}</a> <a id="587" class="Symbol">(</a><a id="588" href="Residuation.Basic.html#588" class="Bound">A</a> <a id="590" class="Symbol">:</a> <a id="592" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="598" href="Residuation.Basic.html#570" class="Bound">α</a> <a id="600" href="Residuation.Basic.html#572" class="Bound">ιᵃ</a> <a id="603" href="Residuation.Basic.html#575" class="Bound">ρᵃ</a><a id="605" class="Symbol">)</a>
         <a id="616" class="Symbol">{</a><a id="617" href="Residuation.Basic.html#617" class="Bound">β</a> <a id="619" href="Residuation.Basic.html#619" class="Bound">ιᵇ</a> <a id="622" href="Residuation.Basic.html#622" class="Bound">ρᵇ</a> <a id="625" class="Symbol">:</a> <a id="627" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="632" class="Symbol">}</a> <a id="634" class="Symbol">(</a><a id="635" href="Residuation.Basic.html#635" class="Bound">B</a> <a id="637" class="Symbol">:</a> <a id="639" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="645" href="Residuation.Basic.html#617" class="Bound">β</a> <a id="647" href="Residuation.Basic.html#619" class="Bound">ιᵇ</a> <a id="650" href="Residuation.Basic.html#622" class="Bound">ρᵇ</a><a id="652" class="Symbol">)</a>
         <a id="663" class="Keyword">where</a>

 <a id="671" class="Keyword">open</a> <a id="676" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a>

 <a id="684" class="Keyword">private</a>
  <a id="694" href="Residuation.Basic.html#694" class="Function Operator">_≤A_</a> <a id="699" class="Symbol">=</a> <a id="701" href="Relation.Binary.Bundles.html#3167" class="Field Operator">_≤_</a> <a id="705" href="Residuation.Basic.html#588" class="Bound">A</a>
  <a id="709" href="Residuation.Basic.html#709" class="Function Operator">_≤B_</a> <a id="714" class="Symbol">=</a> <a id="716" href="Relation.Binary.Bundles.html#3167" class="Field Operator">_≤_</a> <a id="720" href="Residuation.Basic.html#635" class="Bound">B</a>

 <a id="724" class="Keyword">record</a> <a id="731" href="Residuation.Basic.html#731" class="Record">Residuation</a> <a id="743" class="Symbol">:</a> <a id="745" href="Residuation.Basic.html#388" class="Primitive">Type</a> <a id="750" class="Symbol">(</a><a id="751" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="756" class="Symbol">(</a><a id="757" href="Residuation.Basic.html#570" class="Bound">α</a> <a id="759" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="761" href="Residuation.Basic.html#575" class="Bound">ρᵃ</a> <a id="764" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="766" href="Residuation.Basic.html#617" class="Bound">β</a> <a id="768" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="770" href="Residuation.Basic.html#622" class="Bound">ρᵇ</a><a id="772" class="Symbol">))</a>  <a id="776" class="Keyword">where</a>
  <a id="784" class="Keyword">field</a>
   <a id="793" href="Residuation.Basic.html#793" class="Field">f</a>     <a id="799" class="Symbol">:</a> <a id="801" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="809" href="Residuation.Basic.html#588" class="Bound">A</a> <a id="811" class="Symbol">→</a> <a id="813" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="821" href="Residuation.Basic.html#635" class="Bound">B</a>
   <a id="826" href="Residuation.Basic.html#826" class="Field">g</a>     <a id="832" class="Symbol">:</a> <a id="834" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="842" href="Residuation.Basic.html#635" class="Bound">B</a> <a id="844" class="Symbol">→</a> <a id="846" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="854" href="Residuation.Basic.html#588" class="Bound">A</a>
   <a id="859" href="Residuation.Basic.html#859" class="Field">fhom</a>  <a id="865" class="Symbol">:</a> <a id="867" href="Residuation.Basic.html#793" class="Field">f</a> <a id="869" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="879" href="Residuation.Basic.html#694" class="Function Operator">_≤A_</a> <a id="884" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="886" href="Residuation.Basic.html#709" class="Function Operator">_≤B_</a>
   <a id="894" href="Residuation.Basic.html#894" class="Field">ghom</a>  <a id="900" class="Symbol">:</a> <a id="902" href="Residuation.Basic.html#826" class="Field">g</a> <a id="904" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="914" href="Residuation.Basic.html#709" class="Function Operator">_≤B_</a> <a id="919" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="921" href="Residuation.Basic.html#694" class="Function Operator">_≤A_</a>
   <a id="929" href="Residuation.Basic.html#929" class="Field">gf≥id</a> <a id="935" class="Symbol">:</a> <a id="937" class="Symbol">∀</a> <a id="939" href="Residuation.Basic.html#939" class="Bound">a</a> <a id="941" class="Symbol">→</a> <a id="943" href="Residuation.Basic.html#939" class="Bound">a</a> <a id="945" href="Residuation.Basic.html#694" class="Function Operator">≤A</a> <a id="948" href="Residuation.Basic.html#826" class="Field">g</a> <a id="950" class="Symbol">(</a><a id="951" href="Residuation.Basic.html#793" class="Field">f</a> <a id="953" href="Residuation.Basic.html#939" class="Bound">a</a><a id="954" class="Symbol">)</a>
   <a id="959" href="Residuation.Basic.html#959" class="Field">fg≤id</a> <a id="965" class="Symbol">:</a> <a id="967" class="Symbol">∀</a> <a id="969" href="Residuation.Basic.html#969" class="Bound">b</a> <a id="971" class="Symbol">→</a> <a id="973" href="Residuation.Basic.html#793" class="Field">f</a> <a id="975" class="Symbol">(</a><a id="976" href="Residuation.Basic.html#826" class="Field">g</a> <a id="978" href="Residuation.Basic.html#969" class="Bound">b</a><a id="979" class="Symbol">)</a> <a id="981" href="Residuation.Basic.html#709" class="Function Operator">≤B</a> <a id="984" href="Residuation.Basic.html#969" class="Bound">b</a>


</pre>

------------------------------------------

<span style="float:left;">[↑ Residuation ](Residuation.html)</span>
<span style="float:right;">[Residuation.Properties →](Residuation.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
