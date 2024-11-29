---
layout: default
title : "Base.Functions.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions">Injective functions</a>

This is the [Base.Functions.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` is *injective* (or *monic*) if it
does not map two distinct elements of the domain to the same point in
the codomain. The following type manifests this property.

<pre class="Agda">

<a id="485" class="Symbol">{-#</a> <a id="489" class="Keyword">OPTIONS</a> <a id="497" class="Pragma">--without-K</a> <a id="509" class="Pragma">--exact-split</a> <a id="523" class="Pragma">--safe</a> <a id="530" class="Symbol">#-}</a>

<a id="535" class="Keyword">module</a> <a id="542" href="Base.Functions.Injective.html" class="Module">Base.Functions.Injective</a> <a id="567" class="Keyword">where</a>

<a id="574" class="Comment">-- Imports from Agda and the Agda Standard Library -------------------------------</a>
<a id="657" class="Keyword">open</a> <a id="662" class="Keyword">import</a> <a id="669" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>                         <a id="708" class="Keyword">using</a> <a id="714" class="Symbol">()</a> <a id="717" class="Keyword">renaming</a> <a id="726" class="Symbol">(</a> <a id="728" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="732" class="Symbol">to</a> <a id="735" class="Primitive">Type</a> <a id="740" class="Symbol">)</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="Function.html" class="Module">Function</a>                               <a id="793" class="Keyword">using</a> <a id="799" class="Symbol">(</a> <a id="801" href="Function.Bundles.html#12180" class="Function Operator">_↣_</a> <a id="805" class="Symbol">;</a>  <a id="808" href="Function.Base.html#1115" class="Function Operator">_∘_</a> <a id="812" class="Symbol">;</a> <a id="814" href="Function.Definitions.html#842" class="Function">Injective</a> <a id="824" class="Symbol">)</a>
<a id="826" class="Keyword">open</a> <a id="831" class="Keyword">import</a> <a id="838" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a>            <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a> <a id="885" href="Function.Construct.Identity.html#4131" class="Function">↣-id</a> <a id="890" class="Symbol">)</a>
<a id="892" class="Keyword">open</a> <a id="897" class="Keyword">import</a> <a id="904" href="Level.html" class="Module">Level</a>                                  <a id="943" class="Keyword">using</a> <a id="949" class="Symbol">(</a> <a id="951" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="955" class="Symbol">;</a> <a id="957" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="963" class="Symbol">)</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="Relation.Binary.html" class="Module">Relation.Binary</a>                        <a id="1016" class="Keyword">using</a> <a id="1022" class="Symbol">(</a> <a id="1024" href="Relation.Binary.Core.html#896" class="Function">Rel</a> <a id="1028" class="Symbol">)</a>
<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>  <a id="1081" class="Keyword">using</a> <a id="1087" class="Symbol">(</a> <a id="1089" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="1093" class="Symbol">;</a> <a id="1095" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="1100" class="Symbol">)</a>

<a id="1103" class="Keyword">private</a> <a id="1111" class="Keyword">variable</a> <a id="1120" href="Base.Functions.Injective.html#1120" class="Generalizable">a</a> <a id="1122" href="Base.Functions.Injective.html#1122" class="Generalizable">b</a> <a id="1124" href="Base.Functions.Injective.html#1124" class="Generalizable">c</a> <a id="1126" class="Symbol">:</a> <a id="1128" href="Agda.Primitive.html#742" class="Postulate">Level</a>

<a id="id-is-injective"></a><a id="1135" href="Base.Functions.Injective.html#1135" class="Function">id-is-injective</a> <a id="1151" class="Symbol">:</a> <a id="1153" class="Symbol">{</a><a id="1154" href="Base.Functions.Injective.html#1154" class="Bound">A</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1163" href="Base.Functions.Injective.html#1120" class="Generalizable">a</a><a id="1164" class="Symbol">}</a> <a id="1166" class="Symbol">→</a> <a id="1168" href="Base.Functions.Injective.html#1154" class="Bound">A</a> <a id="1170" href="Function.Bundles.html#12180" class="Function Operator">↣</a> <a id="1172" href="Base.Functions.Injective.html#1154" class="Bound">A</a>
<a id="1174" href="Base.Functions.Injective.html#1135" class="Function">id-is-injective</a> <a id="1190" class="Symbol">{</a><a id="1191" class="Argument">A</a> <a id="1193" class="Symbol">=</a> <a id="1195" href="Base.Functions.Injective.html#1195" class="Bound">A</a><a id="1196" class="Symbol">}</a> <a id="1198" class="Symbol">=</a> <a id="1200" href="Function.Construct.Identity.html#4131" class="Function">↣-id</a> <a id="1205" href="Base.Functions.Injective.html#1195" class="Bound">A</a>

<a id="1208" class="Keyword">module</a> <a id="1215" href="Base.Functions.Injective.html#1215" class="Module">_</a> <a id="1217" class="Symbol">{</a><a id="1218" href="Base.Functions.Injective.html#1218" class="Bound">A</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1227" href="Base.Functions.Injective.html#1120" class="Generalizable">a</a><a id="1228" class="Symbol">}{</a><a id="1230" href="Base.Functions.Injective.html#1230" class="Bound">B</a> <a id="1232" class="Symbol">:</a> <a id="1234" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1239" href="Base.Functions.Injective.html#1122" class="Generalizable">b</a><a id="1240" class="Symbol">}</a> <a id="1242" class="Keyword">where</a>

 <a id="1250" href="Base.Functions.Injective.html#1250" class="Function">IsInjective</a> <a id="1262" class="Symbol">:</a> <a id="1264" class="Symbol">(</a><a id="1265" href="Base.Functions.Injective.html#1218" class="Bound">A</a> <a id="1267" class="Symbol">→</a> <a id="1269" href="Base.Functions.Injective.html#1230" class="Bound">B</a><a id="1270" class="Symbol">)</a> <a id="1272" class="Symbol">→</a> <a id="1274" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1279" class="Symbol">(</a><a id="1280" href="Base.Functions.Injective.html#1227" class="Bound">a</a> <a id="1282" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1284" href="Base.Functions.Injective.html#1239" class="Bound">b</a><a id="1285" class="Symbol">)</a>
 <a id="1288" href="Base.Functions.Injective.html#1250" class="Function">IsInjective</a> <a id="1300" href="Base.Functions.Injective.html#1300" class="Bound">f</a> <a id="1302" class="Symbol">=</a> <a id="1304" href="Function.Definitions.html#842" class="Function">Injective</a> <a id="1314" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="1318" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="1322" href="Base.Functions.Injective.html#1300" class="Bound">f</a>

</pre>

The composition of injective functions is injective.

<pre class="Agda">

<a id="∘-injective"></a><a id="1405" href="Base.Functions.Injective.html#1405" class="Function">∘-injective</a> <a id="1417" class="Symbol">:</a>  <a id="1420" class="Symbol">{</a><a id="1421" href="Base.Functions.Injective.html#1421" class="Bound">A</a> <a id="1423" class="Symbol">:</a> <a id="1425" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1430" href="Base.Functions.Injective.html#1120" class="Generalizable">a</a><a id="1431" class="Symbol">}{</a><a id="1433" href="Base.Functions.Injective.html#1433" class="Bound">B</a> <a id="1435" class="Symbol">:</a> <a id="1437" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1442" href="Base.Functions.Injective.html#1122" class="Generalizable">b</a><a id="1443" class="Symbol">}{</a><a id="1445" href="Base.Functions.Injective.html#1445" class="Bound">C</a> <a id="1447" class="Symbol">:</a> <a id="1449" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1454" href="Base.Functions.Injective.html#1124" class="Generalizable">c</a><a id="1455" class="Symbol">}{</a><a id="1457" href="Base.Functions.Injective.html#1457" class="Bound">f</a> <a id="1459" class="Symbol">:</a> <a id="1461" href="Base.Functions.Injective.html#1421" class="Bound">A</a> <a id="1463" class="Symbol">→</a> <a id="1465" href="Base.Functions.Injective.html#1433" class="Bound">B</a><a id="1466" class="Symbol">}{</a><a id="1468" href="Base.Functions.Injective.html#1468" class="Bound">g</a> <a id="1470" class="Symbol">:</a> <a id="1472" href="Base.Functions.Injective.html#1433" class="Bound">B</a> <a id="1474" class="Symbol">→</a> <a id="1476" href="Base.Functions.Injective.html#1445" class="Bound">C</a><a id="1477" class="Symbol">}</a>
  <a id="1481" class="Symbol">→</a>            <a id="1494" href="Base.Functions.Injective.html#1250" class="Function">IsInjective</a> <a id="1506" href="Base.Functions.Injective.html#1457" class="Bound">f</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="Base.Functions.Injective.html#1250" class="Function">IsInjective</a> <a id="1522" href="Base.Functions.Injective.html#1468" class="Bound">g</a> <a id="1524" class="Symbol">→</a> <a id="1526" href="Base.Functions.Injective.html#1250" class="Function">IsInjective</a> <a id="1538" class="Symbol">(</a><a id="1539" href="Base.Functions.Injective.html#1468" class="Bound">g</a> <a id="1541" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="1543" href="Base.Functions.Injective.html#1457" class="Bound">f</a><a id="1544" class="Symbol">)</a>

<a id="1547" href="Base.Functions.Injective.html#1405" class="Function">∘-injective</a> <a id="1559" href="Base.Functions.Injective.html#1559" class="Bound">fi</a> <a id="1562" href="Base.Functions.Injective.html#1562" class="Bound">gi</a> <a id="1565" class="Symbol">=</a> <a id="1567" class="Symbol">λ</a> <a id="1569" href="Base.Functions.Injective.html#1569" class="Bound">x</a> <a id="1571" class="Symbol">→</a> <a id="1573" href="Base.Functions.Injective.html#1559" class="Bound">fi</a> <a id="1576" class="Symbol">(</a><a id="1577" href="Base.Functions.Injective.html#1562" class="Bound">gi</a> <a id="1580" href="Base.Functions.Injective.html#1569" class="Bound">x</a><a id="1581" class="Symbol">)</a>
</pre>

--------------------------------------

<span style="float:left;">[← Base.Functions.FuncInverses](Base.Functions.FuncInverses.html)</span>
<span style="float:right;">[Base.Functions.Surjective →](Base.Functions.Surjective.html)</span>

{% include UALib.Links.md %}


