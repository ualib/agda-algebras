---
layout: default
title : "Residuation.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-12"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

<pre class="Agda">

<a id="226" class="Symbol">{-#</a> <a id="230" class="Keyword">OPTIONS</a> <a id="238" class="Pragma">--without-K</a> <a id="250" class="Pragma">--exact-split</a> <a id="264" class="Pragma">--safe</a> <a id="271" class="Symbol">#-}</a>

<a id="276" class="Keyword">module</a> <a id="283" href="Residuation.Basic.html" class="Module">Residuation.Basic</a> <a id="301" class="Keyword">where</a>

<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>          <a id="344" class="Keyword">using</a> <a id="350" class="Symbol">(</a> <a id="352" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="356" class="Symbol">;</a>  <a id="359" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="365" class="Symbol">;</a> <a id="367" href="Agda.Primitive.html#780" class="Primitive">lsuc</a><a id="371" class="Symbol">)</a> <a id="373" class="Keyword">renaming</a> <a id="382" class="Symbol">(</a> <a id="384" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="388" class="Symbol">to</a> <a id="391" class="Primitive">Type</a> <a id="396" class="Symbol">)</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="Function.Base.html" class="Module">Function.Base</a>           <a id="434" class="Keyword">using</a> <a id="440" class="Symbol">(</a> <a id="442" href="Function.Base.html#6285" class="Function Operator">_on_</a> <a id="447" class="Symbol">)</a>
<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a> <a id="485" class="Keyword">using</a> <a id="491" class="Symbol">(</a> <a id="493" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="499" class="Symbol">)</a>
<a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>    <a id="537" class="Keyword">using</a> <a id="543" class="Symbol">(</a> <a id="545" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="559" class="Symbol">)</a>


<a id="563" class="Keyword">module</a> <a id="570" href="Residuation.Basic.html#570" class="Module">_</a> <a id="572" class="Symbol">{</a><a id="573" href="Residuation.Basic.html#573" class="Bound">α</a> <a id="575" href="Residuation.Basic.html#575" class="Bound">ιᵃ</a> <a id="578" href="Residuation.Basic.html#578" class="Bound">ρᵃ</a> <a id="581" class="Symbol">:</a> <a id="583" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="588" class="Symbol">}</a> <a id="590" class="Symbol">(</a><a id="591" href="Residuation.Basic.html#591" class="Bound">A</a> <a id="593" class="Symbol">:</a> <a id="595" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="601" href="Residuation.Basic.html#573" class="Bound">α</a> <a id="603" href="Residuation.Basic.html#575" class="Bound">ιᵃ</a> <a id="606" href="Residuation.Basic.html#578" class="Bound">ρᵃ</a><a id="608" class="Symbol">)</a>
         <a id="619" class="Symbol">{</a><a id="620" href="Residuation.Basic.html#620" class="Bound">β</a> <a id="622" href="Residuation.Basic.html#622" class="Bound">ιᵇ</a> <a id="625" href="Residuation.Basic.html#625" class="Bound">ρᵇ</a> <a id="628" class="Symbol">:</a> <a id="630" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="635" class="Symbol">}</a> <a id="637" class="Symbol">(</a><a id="638" href="Residuation.Basic.html#638" class="Bound">B</a> <a id="640" class="Symbol">:</a> <a id="642" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="648" href="Residuation.Basic.html#620" class="Bound">β</a> <a id="650" href="Residuation.Basic.html#622" class="Bound">ιᵇ</a> <a id="653" href="Residuation.Basic.html#625" class="Bound">ρᵇ</a><a id="655" class="Symbol">)</a>
         <a id="666" class="Keyword">where</a>

 <a id="674" class="Keyword">open</a> <a id="679" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a>

 <a id="687" class="Keyword">private</a>
  <a id="697" href="Residuation.Basic.html#697" class="Function Operator">_≤A_</a> <a id="702" class="Symbol">=</a> <a id="704" href="Relation.Binary.Bundles.html#3167" class="Field Operator">_≤_</a> <a id="708" href="Residuation.Basic.html#591" class="Bound">A</a>
  <a id="712" href="Residuation.Basic.html#712" class="Function Operator">_≤B_</a> <a id="717" class="Symbol">=</a> <a id="719" href="Relation.Binary.Bundles.html#3167" class="Field Operator">_≤_</a> <a id="723" href="Residuation.Basic.html#638" class="Bound">B</a>

 <a id="727" class="Keyword">record</a> <a id="734" href="Residuation.Basic.html#734" class="Record">Residuation</a> <a id="746" class="Symbol">:</a> <a id="748" href="Residuation.Basic.html#391" class="Primitive">Type</a> <a id="753" class="Symbol">(</a><a id="754" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="759" class="Symbol">(</a><a id="760" href="Residuation.Basic.html#573" class="Bound">α</a> <a id="762" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="764" href="Residuation.Basic.html#578" class="Bound">ρᵃ</a> <a id="767" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="769" href="Residuation.Basic.html#620" class="Bound">β</a> <a id="771" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="773" href="Residuation.Basic.html#625" class="Bound">ρᵇ</a><a id="775" class="Symbol">))</a>  <a id="779" class="Keyword">where</a>
  <a id="787" class="Keyword">field</a>
   <a id="796" href="Residuation.Basic.html#796" class="Field">f</a>     <a id="802" class="Symbol">:</a> <a id="804" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="812" href="Residuation.Basic.html#591" class="Bound">A</a> <a id="814" class="Symbol">→</a> <a id="816" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="824" href="Residuation.Basic.html#638" class="Bound">B</a>
   <a id="829" href="Residuation.Basic.html#829" class="Field">g</a>     <a id="835" class="Symbol">:</a> <a id="837" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="845" href="Residuation.Basic.html#638" class="Bound">B</a> <a id="847" class="Symbol">→</a> <a id="849" href="Relation.Binary.Bundles.html#3104" class="Field">Carrier</a> <a id="857" href="Residuation.Basic.html#591" class="Bound">A</a>
   <a id="862" href="Residuation.Basic.html#862" class="Field">fhom</a>  <a id="868" class="Symbol">:</a> <a id="870" href="Residuation.Basic.html#796" class="Field">f</a> <a id="872" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="882" href="Residuation.Basic.html#697" class="Function Operator">_≤A_</a> <a id="887" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="889" href="Residuation.Basic.html#712" class="Function Operator">_≤B_</a>
   <a id="897" href="Residuation.Basic.html#897" class="Field">ghom</a>  <a id="903" class="Symbol">:</a> <a id="905" href="Residuation.Basic.html#829" class="Field">g</a> <a id="907" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="917" href="Residuation.Basic.html#712" class="Function Operator">_≤B_</a> <a id="922" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="924" href="Residuation.Basic.html#697" class="Function Operator">_≤A_</a>
   <a id="932" href="Residuation.Basic.html#932" class="Field">gf≥id</a> <a id="938" class="Symbol">:</a> <a id="940" class="Symbol">∀</a> <a id="942" href="Residuation.Basic.html#942" class="Bound">a</a> <a id="944" class="Symbol">→</a> <a id="946" href="Residuation.Basic.html#942" class="Bound">a</a> <a id="948" href="Residuation.Basic.html#697" class="Function Operator">≤A</a> <a id="951" href="Residuation.Basic.html#829" class="Field">g</a> <a id="953" class="Symbol">(</a><a id="954" href="Residuation.Basic.html#796" class="Field">f</a> <a id="956" href="Residuation.Basic.html#942" class="Bound">a</a><a id="957" class="Symbol">)</a>
   <a id="962" href="Residuation.Basic.html#962" class="Field">fg≤id</a> <a id="968" class="Symbol">:</a> <a id="970" class="Symbol">∀</a> <a id="972" href="Residuation.Basic.html#972" class="Bound">b</a> <a id="974" class="Symbol">→</a> <a id="976" href="Residuation.Basic.html#796" class="Field">f</a> <a id="978" class="Symbol">(</a><a id="979" href="Residuation.Basic.html#829" class="Field">g</a> <a id="981" href="Residuation.Basic.html#972" class="Bound">b</a><a id="982" class="Symbol">)</a> <a id="984" href="Residuation.Basic.html#712" class="Function Operator">≤B</a> <a id="987" href="Residuation.Basic.html#972" class="Bound">b</a>


</pre>

------------------------------------------

<span style="float:left;">[↑ Residuation ](Residuation.html)</span>
<span style="float:right;">[Residuation.Properties →](Residuation.Properties.html)</span>

{% include UALib.Links.md %}
