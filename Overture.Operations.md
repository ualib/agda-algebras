---
layout: default
title : "Overture.Operations module (The Agda Universal Algebra Library)"
date : "2022-06-17"
author: "the agda-algebras development team"
---

### <a id="Operations">Operations</a>

This is the [Overture.Operations][] module of the [Agda Universal Algebra Library][].

For consistency and readability, we reserve two universe variables for special
purposes. The first of these is `𝓞` which we used in the [Overture.Signatures][]
as the universe of the type of *operation symbols* of a signature. The second is
`𝓥` which we reserve for types representing *arities* of relations or operations.

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`,
which gives us a very general way to represent an operation as a function type with
domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary
projection operations* on `A` are represented as inhabitants of the type `Op I A` as
follows.

<pre class="Agda">

<a id="973" class="Symbol">{-#</a> <a id="977" class="Keyword">OPTIONS</a> <a id="985" class="Pragma">--without-K</a> <a id="997" class="Pragma">--exact-split</a> <a id="1011" class="Pragma">--safe</a> <a id="1018" class="Symbol">#-}</a>

<a id="1023" class="Keyword">module</a> <a id="1030" href="Overture.Operations.html" class="Module">Overture.Operations</a> <a id="1050" class="Keyword">where</a>

<a id="1057" class="Comment">-- Imports from Agda and the Agda Standard Library ----------------------------------------------</a>
<a id="1155" class="Keyword">open</a> <a id="1160" class="Keyword">import</a> <a id="1167" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>               <a id="1196" class="Keyword">using</a> <a id="1202" class="Symbol">()</a> <a id="1205" class="Keyword">renaming</a> <a id="1214" class="Symbol">(</a> <a id="1216" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1220" class="Symbol">to</a> <a id="1223" class="Primitive">Type</a> <a id="1228" class="Symbol">)</a>
<a id="1230" class="Keyword">open</a> <a id="1235" class="Keyword">import</a> <a id="1242" href="Level.html" class="Module">Level</a>                        <a id="1271" class="Keyword">using</a> <a id="1277" class="Symbol">(</a> <a id="1279" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1285" class="Symbol">;</a> <a id="1287" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1291" class="Symbol">)</a>

<a id="1294" class="Keyword">private</a> <a id="1302" class="Keyword">variable</a> <a id="1311" href="Overture.Operations.html#1311" class="Generalizable">α</a> <a id="1313" href="Overture.Operations.html#1313" class="Generalizable">β</a> <a id="1315" href="Overture.Operations.html#1315" class="Generalizable">ρ</a> <a id="1317" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="Agda.Primitive.html#597" class="Postulate">Level</a>
</pre>

<pre class="Agda">

<a id="1353" class="Comment">-- The type of operations on A of arity I</a>
<a id="Op"></a><a id="1395" href="Overture.Operations.html#1395" class="Function">Op</a> <a id="1398" class="Symbol">:</a> <a id="1400" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1405" href="Overture.Operations.html#1311" class="Generalizable">α</a> <a id="1407" class="Symbol">→</a> <a id="1409" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1414" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a> <a id="1416" class="Symbol">→</a> <a id="1418" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1423" class="Symbol">(</a><a id="1424" href="Overture.Operations.html#1311" class="Generalizable">α</a> <a id="1426" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1428" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a><a id="1429" class="Symbol">)</a>
<a id="1431" href="Overture.Operations.html#1395" class="Function">Op</a> <a id="1434" href="Overture.Operations.html#1434" class="Bound">A</a> <a id="1436" href="Overture.Operations.html#1436" class="Bound">I</a> <a id="1438" class="Symbol">=</a> <a id="1440" class="Symbol">(</a><a id="1441" href="Overture.Operations.html#1436" class="Bound">I</a> <a id="1443" class="Symbol">→</a> <a id="1445" href="Overture.Operations.html#1434" class="Bound">A</a><a id="1446" class="Symbol">)</a> <a id="1448" class="Symbol">→</a> <a id="1450" href="Overture.Operations.html#1434" class="Bound">A</a>

<a id="1453" class="Comment">-- Example (projections)</a>
<a id="π"></a><a id="1478" href="Overture.Operations.html#1478" class="Function">π</a> <a id="1480" class="Symbol">:</a> <a id="1482" class="Symbol">{</a><a id="1483" href="Overture.Operations.html#1483" class="Bound">I</a> <a id="1485" class="Symbol">:</a> <a id="1487" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1492" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a><a id="1493" class="Symbol">}</a> <a id="1495" class="Symbol">{</a><a id="1496" href="Overture.Operations.html#1496" class="Bound">A</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1505" href="Overture.Operations.html#1311" class="Generalizable">α</a> <a id="1507" class="Symbol">}</a> <a id="1509" class="Symbol">→</a> <a id="1511" href="Overture.Operations.html#1483" class="Bound">I</a> <a id="1513" class="Symbol">→</a> <a id="1515" href="Overture.Operations.html#1395" class="Function">Op</a> <a id="1518" href="Overture.Operations.html#1496" class="Bound">A</a> <a id="1520" href="Overture.Operations.html#1483" class="Bound">I</a>
<a id="1522" href="Overture.Operations.html#1478" class="Function">π</a> <a id="1524" href="Overture.Operations.html#1524" class="Bound">i</a> <a id="1526" href="Overture.Operations.html#1526" class="Bound">x</a> <a id="1528" class="Symbol">=</a> <a id="1530" href="Overture.Operations.html#1526" class="Bound">x</a> <a id="1532" href="Overture.Operations.html#1524" class="Bound">i</a>

<a id="1535" class="Comment">-- return the arity of a given operation symbol</a>

<a id="arity[_]"></a><a id="1584" href="Overture.Operations.html#1584" class="Function Operator">arity[_]</a> <a id="1593" class="Symbol">:</a> <a id="1595" class="Symbol">{</a><a id="1596" href="Overture.Operations.html#1596" class="Bound">I</a> <a id="1598" class="Symbol">:</a> <a id="1600" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1605" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a><a id="1606" class="Symbol">}</a> <a id="1608" class="Symbol">{</a><a id="1609" href="Overture.Operations.html#1609" class="Bound">A</a> <a id="1611" class="Symbol">:</a> <a id="1613" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1618" href="Overture.Operations.html#1311" class="Generalizable">α</a> <a id="1620" class="Symbol">}</a> <a id="1622" class="Symbol">→</a> <a id="1624" href="Overture.Operations.html#1395" class="Function">Op</a> <a id="1627" href="Overture.Operations.html#1609" class="Bound">A</a> <a id="1629" href="Overture.Operations.html#1596" class="Bound">I</a> <a id="1631" class="Symbol">→</a> <a id="1633" href="Overture.Operations.html#1223" class="Primitive">Type</a> <a id="1638" href="Overture.Operations.html#1317" class="Generalizable">𝓥</a>
<a id="1640" href="Overture.Operations.html#1584" class="Function Operator">arity[_]</a> <a id="1649" class="Symbol">{</a><a id="1650" class="Argument">I</a> <a id="1652" class="Symbol">=</a> <a id="1654" href="Overture.Operations.html#1654" class="Bound">I</a><a id="1655" class="Symbol">}</a> <a id="1657" href="Overture.Operations.html#1657" class="Bound">f</a> <a id="1659" class="Symbol">=</a> <a id="1661" href="Overture.Operations.html#1654" class="Bound">I</a>

</pre>

-----------

<span style="float:left;">[← Overture.Signatures](Overture.Signatures.html)</span>
<span style="float:right;">[Base →](Base.html)</span>


{% include UALib.Links.md %}

