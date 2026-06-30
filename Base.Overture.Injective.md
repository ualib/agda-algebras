---
layout: default
title : "Base.Overture.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions">Injective functions</a>

This is the [Base.Overture.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

<pre class="Agda">

<a id="483" class="Symbol">{-#</a> <a id="487" class="Keyword">OPTIONS</a> <a id="495" class="Pragma">--without-K</a> <a id="507" class="Pragma">--exact-split</a> <a id="521" class="Pragma">--safe</a> <a id="528" class="Symbol">#-}</a>

<a id="533" class="Keyword">module</a> <a id="540" href="Base.Overture.Injective.html" class="Module">Base.Overture.Injective</a> <a id="564" class="Keyword">where</a>

<a id="571" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------------------------------</a>
<a id="668" class="Keyword">open</a> <a id="673" class="Keyword">import</a> <a id="680" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="697" class="Keyword">using</a> <a id="703" class="Symbol">(</a> <a id="705" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="709" class="Symbol">;</a> <a id="711" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="717" class="Symbol">)</a> <a id="719" class="Keyword">renaming</a> <a id="728" class="Symbol">(</a> <a id="730" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="734" class="Symbol">to</a> <a id="737" class="Primitive">Type</a> <a id="742" class="Symbol">)</a>
<a id="744" class="Keyword">open</a> <a id="749" class="Keyword">import</a> <a id="756" href="Function.Bundles.html" class="Module">Function.Bundles</a>                      <a id="794" class="Keyword">using</a> <a id="800" class="Symbol">(</a> <a id="802" href="Function.Bundles.html#8289" class="Function Operator">_↣_</a> <a id="806" class="Symbol">)</a>
<a id="808" class="Keyword">open</a> <a id="813" class="Keyword">import</a> <a id="820" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a>           <a id="858" class="Keyword">using</a> <a id="864" class="Symbol">(</a> <a id="866" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="871" class="Symbol">)</a>
<a id="873" class="Keyword">open</a> <a id="878" class="Keyword">import</a> <a id="885" href="Function.Base.html" class="Module">Function.Base</a>                         <a id="923" class="Keyword">using</a> <a id="929" class="Symbol">(</a> <a id="931" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="935" class="Symbol">)</a>
<a id="937" class="Keyword">open</a> <a id="942" class="Keyword">import</a> <a id="949" href="Function.Definitions.html" class="Module">Function.Definitions</a> <a id="970" class="Symbol">as</a> <a id="973" class="Module">FD</a>            <a id="987" class="Keyword">using</a> <a id="993" class="Symbol">(</a> <a id="995" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="1005" class="Symbol">)</a>
<a id="1007" class="Keyword">open</a> <a id="1012" class="Keyword">import</a> <a id="1019" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1057" class="Keyword">using</a> <a id="1063" class="Symbol">(</a> <a id="1065" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1069" class="Symbol">;</a> <a id="1071" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1076" class="Symbol">)</a>
<a id="1078" class="Keyword">open</a> <a id="1083" class="Keyword">import</a> <a id="1090" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="1107" class="Keyword">using</a> <a id="1113" class="Symbol">(</a> <a id="1115" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1119" class="Symbol">)</a>


<a id="1123" class="Keyword">private</a> <a id="1131" class="Keyword">variable</a> <a id="1140" href="Base.Overture.Injective.html#1140" class="Generalizable">α</a> <a id="1142" href="Base.Overture.Injective.html#1142" class="Generalizable">β</a> <a id="1144" href="Base.Overture.Injective.html#1144" class="Generalizable">γ</a> <a id="1146" href="Base.Overture.Injective.html#1146" class="Generalizable">ℓ₁</a> <a id="1149" href="Base.Overture.Injective.html#1149" class="Generalizable">ℓ₂</a> <a id="1152" href="Base.Overture.Injective.html#1152" class="Generalizable">ℓ₃</a> <a id="1155" class="Symbol">:</a> <a id="1157" href="Agda.Primitive.html#597" class="Postulate">Level</a>


<a id="id-is-injective"></a><a id="1165" href="Base.Overture.Injective.html#1165" class="Function">id-is-injective</a> <a id="1181" class="Symbol">:</a> <a id="1183" class="Symbol">{</a><a id="1184" href="Base.Overture.Injective.html#1184" class="Bound">A</a> <a id="1186" class="Symbol">:</a> <a id="1188" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1193" href="Base.Overture.Injective.html#1140" class="Generalizable">α</a><a id="1194" class="Symbol">}</a> <a id="1196" class="Symbol">→</a> <a id="1198" href="Base.Overture.Injective.html#1184" class="Bound">A</a> <a id="1200" href="Function.Bundles.html#8289" class="Function Operator">↣</a> <a id="1202" href="Base.Overture.Injective.html#1184" class="Bound">A</a>
<a id="1204" href="Base.Overture.Injective.html#1165" class="Function">id-is-injective</a> <a id="1220" class="Symbol">{</a><a id="1221" class="Argument">A</a> <a id="1223" class="Symbol">=</a> <a id="1225" href="Base.Overture.Injective.html#1225" class="Bound">A</a><a id="1226" class="Symbol">}</a> <a id="1228" class="Symbol">=</a> <a id="1230" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="1235" href="Base.Overture.Injective.html#1225" class="Bound">A</a>

<a id="1238" class="Keyword">module</a> <a id="1245" href="Base.Overture.Injective.html#1245" class="Module">_</a> <a id="1247" class="Symbol">{</a><a id="1248" href="Base.Overture.Injective.html#1248" class="Bound">A</a> <a id="1250" class="Symbol">:</a> <a id="1252" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1257" href="Base.Overture.Injective.html#1140" class="Generalizable">α</a><a id="1258" class="Symbol">}{</a><a id="1260" href="Base.Overture.Injective.html#1260" class="Bound">B</a> <a id="1262" class="Symbol">:</a> <a id="1264" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1269" href="Base.Overture.Injective.html#1142" class="Generalizable">β</a><a id="1270" class="Symbol">}</a> <a id="1272" class="Keyword">where</a>

 <a id="1280" href="Base.Overture.Injective.html#1280" class="Function">IsInjective</a> <a id="1292" class="Symbol">:</a> <a id="1294" class="Symbol">(</a><a id="1295" href="Base.Overture.Injective.html#1248" class="Bound">A</a> <a id="1297" class="Symbol">→</a> <a id="1299" href="Base.Overture.Injective.html#1260" class="Bound">B</a><a id="1300" class="Symbol">)</a> <a id="1302" class="Symbol">→</a> <a id="1304" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1309" class="Symbol">(</a><a id="1310" href="Base.Overture.Injective.html#1257" class="Bound">α</a> <a id="1312" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1314" href="Base.Overture.Injective.html#1269" class="Bound">β</a><a id="1315" class="Symbol">)</a>
 <a id="1318" href="Base.Overture.Injective.html#1280" class="Function">IsInjective</a> <a id="1330" href="Base.Overture.Injective.html#1330" class="Bound">f</a> <a id="1332" class="Symbol">=</a> <a id="1334" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="1344" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1348" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1352" href="Base.Overture.Injective.html#1330" class="Bound">f</a>

</pre>

Next, we prove that the composition of injective functions is injective.

<pre class="Agda">

<a id="∘-injective"></a><a id="1455" href="Base.Overture.Injective.html#1455" class="Function">∘-injective</a> <a id="1467" class="Symbol">:</a> <a id="1469" class="Symbol">{</a><a id="1470" href="Base.Overture.Injective.html#1470" class="Bound">A</a> <a id="1472" class="Symbol">:</a> <a id="1474" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1479" href="Base.Overture.Injective.html#1140" class="Generalizable">α</a><a id="1480" class="Symbol">}{</a><a id="1482" href="Base.Overture.Injective.html#1482" class="Bound">B</a> <a id="1484" class="Symbol">:</a> <a id="1486" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1491" href="Base.Overture.Injective.html#1142" class="Generalizable">β</a><a id="1492" class="Symbol">}{</a><a id="1494" href="Base.Overture.Injective.html#1494" class="Bound">C</a> <a id="1496" class="Symbol">:</a> <a id="1498" href="Base.Overture.Injective.html#737" class="Primitive">Type</a> <a id="1503" href="Base.Overture.Injective.html#1144" class="Generalizable">γ</a><a id="1504" class="Symbol">}{</a><a id="1506" href="Base.Overture.Injective.html#1506" class="Bound">f</a> <a id="1508" class="Symbol">:</a> <a id="1510" href="Base.Overture.Injective.html#1470" class="Bound">A</a> <a id="1512" class="Symbol">→</a> <a id="1514" href="Base.Overture.Injective.html#1482" class="Bound">B</a><a id="1515" class="Symbol">}{</a><a id="1517" href="Base.Overture.Injective.html#1517" class="Bound">g</a> <a id="1519" class="Symbol">:</a> <a id="1521" href="Base.Overture.Injective.html#1482" class="Bound">B</a> <a id="1523" class="Symbol">→</a> <a id="1525" href="Base.Overture.Injective.html#1494" class="Bound">C</a><a id="1526" class="Symbol">}</a>
  <a id="1530" class="Symbol">→</a>           <a id="1542" href="Base.Overture.Injective.html#1280" class="Function">IsInjective</a> <a id="1554" href="Base.Overture.Injective.html#1506" class="Bound">f</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="Base.Overture.Injective.html#1280" class="Function">IsInjective</a> <a id="1570" href="Base.Overture.Injective.html#1517" class="Bound">g</a> <a id="1572" class="Symbol">→</a> <a id="1574" href="Base.Overture.Injective.html#1280" class="Function">IsInjective</a> <a id="1586" class="Symbol">(</a><a id="1587" href="Base.Overture.Injective.html#1517" class="Bound">g</a> <a id="1589" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1591" href="Base.Overture.Injective.html#1506" class="Bound">f</a><a id="1592" class="Symbol">)</a>
<a id="1594" href="Base.Overture.Injective.html#1455" class="Function">∘-injective</a> <a id="1606" href="Base.Overture.Injective.html#1606" class="Bound">fi</a> <a id="1609" href="Base.Overture.Injective.html#1609" class="Bound">gi</a> <a id="1612" class="Symbol">=</a> <a id="1614" class="Symbol">λ</a> <a id="1616" href="Base.Overture.Injective.html#1616" class="Bound">x</a> <a id="1618" class="Symbol">→</a> <a id="1620" href="Base.Overture.Injective.html#1606" class="Bound">fi</a> <a id="1623" class="Symbol">(</a><a id="1624" href="Base.Overture.Injective.html#1609" class="Bound">gi</a> <a id="1627" href="Base.Overture.Injective.html#1616" class="Bound">x</a><a id="1628" class="Symbol">)</a>

</pre>

--------------------------------------

<span style="float:left;">[← Base.Overture.FuncInverses](Base.Overture.FuncInverses.html)</span>
<span style="float:right;">[Base.Overture.Surjective →](Base.Overture.Surjective.html)</span>

{% include UALib.Links.md %}


