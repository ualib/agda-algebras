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
<a id="657" class="Keyword">open</a> <a id="662" class="Keyword">import</a> <a id="669" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>                         <a id="708" class="Keyword">using</a> <a id="714" class="Symbol">()</a> <a id="717" class="Keyword">renaming</a> <a id="726" class="Symbol">(</a> <a id="728" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="732" class="Symbol">to</a> <a id="735" class="Primitive">Type</a> <a id="740" class="Symbol">)</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="Function.html" class="Module">Function</a>                               <a id="793" class="Keyword">using</a> <a id="799" class="Symbol">(</a> <a id="801" href="Function.Bundles.html#8289" class="Function Operator">_↣_</a> <a id="805" class="Symbol">;</a>  <a id="808" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="812" class="Symbol">;</a> <a id="814" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="824" class="Symbol">)</a>
<a id="826" class="Keyword">open</a> <a id="831" class="Keyword">import</a> <a id="838" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a>            <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a> <a id="885" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="890" class="Symbol">)</a>
<a id="892" class="Keyword">open</a> <a id="897" class="Keyword">import</a> <a id="904" href="Level.html" class="Module">Level</a>                                  <a id="943" class="Keyword">using</a> <a id="949" class="Symbol">(</a> <a id="951" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="955" class="Symbol">;</a> <a id="957" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="963" class="Symbol">)</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="Relation.Binary.html" class="Module">Relation.Binary</a>                        <a id="1016" class="Keyword">using</a> <a id="1022" class="Symbol">(</a> <a id="1024" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1028" class="Symbol">)</a>
<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>  <a id="1081" class="Keyword">using</a> <a id="1087" class="Symbol">(</a> <a id="1089" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1093" class="Symbol">;</a> <a id="1095" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1100" class="Symbol">)</a>

<a id="1103" class="Keyword">private</a> <a id="1111" class="Keyword">variable</a> <a id="1120" href="Base.Functions.Injective.html#1120" class="Generalizable">α</a> <a id="1122" href="Base.Functions.Injective.html#1122" class="Generalizable">β</a> <a id="1124" href="Base.Functions.Injective.html#1124" class="Generalizable">γ</a> <a id="1126" href="Base.Functions.Injective.html#1126" class="Generalizable">ℓ₁</a> <a id="1129" href="Base.Functions.Injective.html#1129" class="Generalizable">ℓ₂</a> <a id="1132" href="Base.Functions.Injective.html#1132" class="Generalizable">ℓ₃</a> <a id="1135" class="Symbol">:</a> <a id="1137" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="id-is-injective"></a><a id="1144" href="Base.Functions.Injective.html#1144" class="Function">id-is-injective</a> <a id="1160" class="Symbol">:</a> <a id="1162" class="Symbol">{</a><a id="1163" href="Base.Functions.Injective.html#1163" class="Bound">A</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1172" href="Base.Functions.Injective.html#1120" class="Generalizable">α</a><a id="1173" class="Symbol">}</a> <a id="1175" class="Symbol">→</a> <a id="1177" href="Base.Functions.Injective.html#1163" class="Bound">A</a> <a id="1179" href="Function.Bundles.html#8289" class="Function Operator">↣</a> <a id="1181" href="Base.Functions.Injective.html#1163" class="Bound">A</a>
<a id="1183" href="Base.Functions.Injective.html#1144" class="Function">id-is-injective</a> <a id="1199" class="Symbol">{</a><a id="1200" class="Argument">A</a> <a id="1202" class="Symbol">=</a> <a id="1204" href="Base.Functions.Injective.html#1204" class="Bound">A</a><a id="1205" class="Symbol">}</a> <a id="1207" class="Symbol">=</a> <a id="1209" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="1214" href="Base.Functions.Injective.html#1204" class="Bound">A</a>

<a id="1217" class="Keyword">module</a> <a id="1224" href="Base.Functions.Injective.html#1224" class="Module">_</a> <a id="1226" class="Symbol">{</a><a id="1227" href="Base.Functions.Injective.html#1227" class="Bound">A</a> <a id="1229" class="Symbol">:</a> <a id="1231" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1236" href="Base.Functions.Injective.html#1120" class="Generalizable">α</a><a id="1237" class="Symbol">}{</a><a id="1239" href="Base.Functions.Injective.html#1239" class="Bound">B</a> <a id="1241" class="Symbol">:</a> <a id="1243" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1248" href="Base.Functions.Injective.html#1122" class="Generalizable">β</a><a id="1249" class="Symbol">}</a> <a id="1251" class="Keyword">where</a>

 <a id="1259" href="Base.Functions.Injective.html#1259" class="Function">IsInjective</a> <a id="1271" class="Symbol">:</a> <a id="1273" class="Symbol">(</a><a id="1274" href="Base.Functions.Injective.html#1227" class="Bound">A</a> <a id="1276" class="Symbol">→</a> <a id="1278" href="Base.Functions.Injective.html#1239" class="Bound">B</a><a id="1279" class="Symbol">)</a> <a id="1281" class="Symbol">→</a> <a id="1283" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1288" class="Symbol">(</a><a id="1289" href="Base.Functions.Injective.html#1236" class="Bound">α</a> <a id="1291" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1293" href="Base.Functions.Injective.html#1248" class="Bound">β</a><a id="1294" class="Symbol">)</a>
 <a id="1297" href="Base.Functions.Injective.html#1259" class="Function">IsInjective</a> <a id="1309" href="Base.Functions.Injective.html#1309" class="Bound">f</a> <a id="1311" class="Symbol">=</a> <a id="1313" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="1323" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1327" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1331" href="Base.Functions.Injective.html#1309" class="Bound">f</a>

</pre>

The composition of injective functions is injective.

<pre class="Agda">

<a id="∘-injective"></a><a id="1414" href="Base.Functions.Injective.html#1414" class="Function">∘-injective</a> <a id="1426" class="Symbol">:</a>  <a id="1429" class="Symbol">{</a><a id="1430" href="Base.Functions.Injective.html#1430" class="Bound">A</a> <a id="1432" class="Symbol">:</a> <a id="1434" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1439" href="Base.Functions.Injective.html#1120" class="Generalizable">α</a><a id="1440" class="Symbol">}{</a><a id="1442" href="Base.Functions.Injective.html#1442" class="Bound">B</a> <a id="1444" class="Symbol">:</a> <a id="1446" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1451" href="Base.Functions.Injective.html#1122" class="Generalizable">β</a><a id="1452" class="Symbol">}{</a><a id="1454" href="Base.Functions.Injective.html#1454" class="Bound">C</a> <a id="1456" class="Symbol">:</a> <a id="1458" href="Base.Functions.Injective.html#735" class="Primitive">Type</a> <a id="1463" href="Base.Functions.Injective.html#1124" class="Generalizable">γ</a><a id="1464" class="Symbol">}{</a><a id="1466" href="Base.Functions.Injective.html#1466" class="Bound">f</a> <a id="1468" class="Symbol">:</a> <a id="1470" href="Base.Functions.Injective.html#1430" class="Bound">A</a> <a id="1472" class="Symbol">→</a> <a id="1474" href="Base.Functions.Injective.html#1442" class="Bound">B</a><a id="1475" class="Symbol">}{</a><a id="1477" href="Base.Functions.Injective.html#1477" class="Bound">g</a> <a id="1479" class="Symbol">:</a> <a id="1481" href="Base.Functions.Injective.html#1442" class="Bound">B</a> <a id="1483" class="Symbol">→</a> <a id="1485" href="Base.Functions.Injective.html#1454" class="Bound">C</a><a id="1486" class="Symbol">}</a>
  <a id="1490" class="Symbol">→</a>            <a id="1503" href="Base.Functions.Injective.html#1259" class="Function">IsInjective</a> <a id="1515" href="Base.Functions.Injective.html#1466" class="Bound">f</a> <a id="1517" class="Symbol">→</a> <a id="1519" href="Base.Functions.Injective.html#1259" class="Function">IsInjective</a> <a id="1531" href="Base.Functions.Injective.html#1477" class="Bound">g</a> <a id="1533" class="Symbol">→</a> <a id="1535" href="Base.Functions.Injective.html#1259" class="Function">IsInjective</a> <a id="1547" class="Symbol">(</a><a id="1548" href="Base.Functions.Injective.html#1477" class="Bound">g</a> <a id="1550" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1552" href="Base.Functions.Injective.html#1466" class="Bound">f</a><a id="1553" class="Symbol">)</a>

<a id="1556" href="Base.Functions.Injective.html#1414" class="Function">∘-injective</a> <a id="1568" href="Base.Functions.Injective.html#1568" class="Bound">fi</a> <a id="1571" href="Base.Functions.Injective.html#1571" class="Bound">gi</a> <a id="1574" class="Symbol">=</a> <a id="1576" class="Symbol">λ</a> <a id="1578" href="Base.Functions.Injective.html#1578" class="Bound">x</a> <a id="1580" class="Symbol">→</a> <a id="1582" href="Base.Functions.Injective.html#1568" class="Bound">fi</a> <a id="1585" class="Symbol">(</a><a id="1586" href="Base.Functions.Injective.html#1571" class="Bound">gi</a> <a id="1589" href="Base.Functions.Injective.html#1578" class="Bound">x</a><a id="1590" class="Symbol">)</a>
</pre>

--------------------------------------

<span style="float:left;">[← Base.Functions.FuncInverses](Base.Functions.FuncInverses.html)</span>
<span style="float:right;">[Base.Functions.Surjective →](Base.Functions.Surjective.html)</span>

{% include UALib.Links.md %}


