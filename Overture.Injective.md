---
layout: default
title : "Overture.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions">Injective functions</a>

This is the [Overture.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

<pre class="Agda">

<a id="473" class="Symbol">{-#</a> <a id="477" class="Keyword">OPTIONS</a> <a id="485" class="Pragma">--without-K</a> <a id="497" class="Pragma">--exact-split</a> <a id="511" class="Pragma">--safe</a> <a id="518" class="Symbol">#-}</a>

<a id="523" class="Keyword">module</a> <a id="530" href="Overture.Injective.html" class="Module">Overture.Injective</a> <a id="549" class="Keyword">where</a>

<a id="556" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------------------------------</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="682" class="Keyword">using</a> <a id="688" class="Symbol">(</a> <a id="690" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="694" class="Symbol">;</a> <a id="696" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="702" class="Symbol">)</a> <a id="704" class="Keyword">renaming</a> <a id="713" class="Symbol">(</a> <a id="715" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="719" class="Symbol">to</a> <a id="722" class="Primitive">Type</a> <a id="727" class="Symbol">)</a>
<a id="729" class="Keyword">open</a> <a id="734" class="Keyword">import</a> <a id="741" href="Function.Bundles.html" class="Module">Function.Bundles</a>                      <a id="779" class="Keyword">using</a> <a id="785" class="Symbol">(</a> <a id="787" href="Function.Bundles.html#8289" class="Function Operator">_↣_</a> <a id="791" class="Symbol">)</a>
<a id="793" class="Keyword">open</a> <a id="798" class="Keyword">import</a> <a id="805" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a>           <a id="843" class="Keyword">using</a> <a id="849" class="Symbol">(</a> <a id="851" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="856" class="Symbol">)</a>
<a id="858" class="Keyword">open</a> <a id="863" class="Keyword">import</a> <a id="870" href="Function.Base.html" class="Module">Function.Base</a>                         <a id="908" class="Keyword">using</a> <a id="914" class="Symbol">(</a> <a id="916" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="920" class="Symbol">)</a>
<a id="922" class="Keyword">open</a> <a id="927" class="Keyword">import</a> <a id="934" href="Function.Definitions.html" class="Module">Function.Definitions</a> <a id="955" class="Symbol">as</a> <a id="958" class="Module">FD</a>            <a id="972" class="Keyword">using</a> <a id="978" class="Symbol">(</a> <a id="980" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="990" class="Symbol">)</a>
<a id="992" class="Keyword">open</a> <a id="997" class="Keyword">import</a> <a id="1004" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1042" class="Keyword">using</a> <a id="1048" class="Symbol">(</a> <a id="1050" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1054" class="Symbol">;</a> <a id="1056" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1061" class="Symbol">)</a>
<a id="1063" class="Keyword">open</a> <a id="1068" class="Keyword">import</a> <a id="1075" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="1092" class="Keyword">using</a> <a id="1098" class="Symbol">(</a> <a id="1100" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1104" class="Symbol">)</a>


<a id="1108" class="Keyword">private</a> <a id="1116" class="Keyword">variable</a> <a id="1125" href="Overture.Injective.html#1125" class="Generalizable">α</a> <a id="1127" href="Overture.Injective.html#1127" class="Generalizable">β</a> <a id="1129" href="Overture.Injective.html#1129" class="Generalizable">γ</a> <a id="1131" href="Overture.Injective.html#1131" class="Generalizable">ℓ₁</a> <a id="1134" href="Overture.Injective.html#1134" class="Generalizable">ℓ₂</a> <a id="1137" href="Overture.Injective.html#1137" class="Generalizable">ℓ₃</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="Agda.Primitive.html#597" class="Postulate">Level</a>


<a id="id-is-injective"></a><a id="1150" href="Overture.Injective.html#1150" class="Function">id-is-injective</a> <a id="1166" class="Symbol">:</a> <a id="1168" class="Symbol">{</a><a id="1169" href="Overture.Injective.html#1169" class="Bound">A</a> <a id="1171" class="Symbol">:</a> <a id="1173" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1178" href="Overture.Injective.html#1125" class="Generalizable">α</a><a id="1179" class="Symbol">}</a> <a id="1181" class="Symbol">→</a> <a id="1183" href="Overture.Injective.html#1169" class="Bound">A</a> <a id="1185" href="Function.Bundles.html#8289" class="Function Operator">↣</a> <a id="1187" href="Overture.Injective.html#1169" class="Bound">A</a>
<a id="1189" href="Overture.Injective.html#1150" class="Function">id-is-injective</a> <a id="1205" class="Symbol">{</a><a id="1206" class="Argument">A</a> <a id="1208" class="Symbol">=</a> <a id="1210" href="Overture.Injective.html#1210" class="Bound">A</a><a id="1211" class="Symbol">}</a> <a id="1213" class="Symbol">=</a> <a id="1215" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="1220" href="Overture.Injective.html#1210" class="Bound">A</a>

<a id="1223" class="Keyword">module</a> <a id="1230" href="Overture.Injective.html#1230" class="Module">_</a> <a id="1232" class="Symbol">{</a><a id="1233" href="Overture.Injective.html#1233" class="Bound">A</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1242" href="Overture.Injective.html#1125" class="Generalizable">α</a><a id="1243" class="Symbol">}{</a><a id="1245" href="Overture.Injective.html#1245" class="Bound">B</a> <a id="1247" class="Symbol">:</a> <a id="1249" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1254" href="Overture.Injective.html#1127" class="Generalizable">β</a><a id="1255" class="Symbol">}</a> <a id="1257" class="Keyword">where</a>

 <a id="1265" href="Overture.Injective.html#1265" class="Function">IsInjective</a> <a id="1277" class="Symbol">:</a> <a id="1279" class="Symbol">(</a><a id="1280" href="Overture.Injective.html#1233" class="Bound">A</a> <a id="1282" class="Symbol">→</a> <a id="1284" href="Overture.Injective.html#1245" class="Bound">B</a><a id="1285" class="Symbol">)</a> <a id="1287" class="Symbol">→</a> <a id="1289" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1294" class="Symbol">(</a><a id="1295" href="Overture.Injective.html#1242" class="Bound">α</a> <a id="1297" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1299" href="Overture.Injective.html#1254" class="Bound">β</a><a id="1300" class="Symbol">)</a>
 <a id="1303" href="Overture.Injective.html#1265" class="Function">IsInjective</a> <a id="1315" href="Overture.Injective.html#1315" class="Bound">f</a> <a id="1317" class="Symbol">=</a> <a id="1319" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="1329" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1333" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1337" href="Overture.Injective.html#1315" class="Bound">f</a>

</pre>

Next, we prove that the composition of injective functions is injective.

<pre class="Agda">

<a id="∘-injective"></a><a id="1440" href="Overture.Injective.html#1440" class="Function">∘-injective</a> <a id="1452" class="Symbol">:</a> <a id="1454" class="Symbol">{</a><a id="1455" href="Overture.Injective.html#1455" class="Bound">A</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1464" href="Overture.Injective.html#1125" class="Generalizable">α</a><a id="1465" class="Symbol">}{</a><a id="1467" href="Overture.Injective.html#1467" class="Bound">B</a> <a id="1469" class="Symbol">:</a> <a id="1471" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1476" href="Overture.Injective.html#1127" class="Generalizable">β</a><a id="1477" class="Symbol">}{</a><a id="1479" href="Overture.Injective.html#1479" class="Bound">C</a> <a id="1481" class="Symbol">:</a> <a id="1483" href="Overture.Injective.html#722" class="Primitive">Type</a> <a id="1488" href="Overture.Injective.html#1129" class="Generalizable">γ</a><a id="1489" class="Symbol">}{</a><a id="1491" href="Overture.Injective.html#1491" class="Bound">f</a> <a id="1493" class="Symbol">:</a> <a id="1495" href="Overture.Injective.html#1455" class="Bound">A</a> <a id="1497" class="Symbol">→</a> <a id="1499" href="Overture.Injective.html#1467" class="Bound">B</a><a id="1500" class="Symbol">}{</a><a id="1502" href="Overture.Injective.html#1502" class="Bound">g</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="Overture.Injective.html#1467" class="Bound">B</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="Overture.Injective.html#1479" class="Bound">C</a><a id="1511" class="Symbol">}</a>
  <a id="1515" class="Symbol">→</a>           <a id="1527" href="Overture.Injective.html#1265" class="Function">IsInjective</a> <a id="1539" href="Overture.Injective.html#1491" class="Bound">f</a> <a id="1541" class="Symbol">→</a> <a id="1543" href="Overture.Injective.html#1265" class="Function">IsInjective</a> <a id="1555" href="Overture.Injective.html#1502" class="Bound">g</a> <a id="1557" class="Symbol">→</a> <a id="1559" href="Overture.Injective.html#1265" class="Function">IsInjective</a> <a id="1571" class="Symbol">(</a><a id="1572" href="Overture.Injective.html#1502" class="Bound">g</a> <a id="1574" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1576" href="Overture.Injective.html#1491" class="Bound">f</a><a id="1577" class="Symbol">)</a>
<a id="1579" href="Overture.Injective.html#1440" class="Function">∘-injective</a> <a id="1591" href="Overture.Injective.html#1591" class="Bound">fi</a> <a id="1594" href="Overture.Injective.html#1594" class="Bound">gi</a> <a id="1597" class="Symbol">=</a> <a id="1599" class="Symbol">λ</a> <a id="1601" href="Overture.Injective.html#1601" class="Bound">x</a> <a id="1603" class="Symbol">→</a> <a id="1605" href="Overture.Injective.html#1591" class="Bound">fi</a> <a id="1608" class="Symbol">(</a><a id="1609" href="Overture.Injective.html#1594" class="Bound">gi</a> <a id="1612" href="Overture.Injective.html#1601" class="Bound">x</a><a id="1613" class="Symbol">)</a>

</pre>

--------------------------------------

<span style="float:left;">[← Overture.FuncInverses](Overture.FuncInverses.html)</span>
<span style="float:right;">[Overture.Surjective →](Overture.Surjective.html)</span>

{% include UALib.Links.md %}


