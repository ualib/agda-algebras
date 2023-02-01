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

<a id="1057" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------</a>
<a id="1138" class="Keyword">open</a> <a id="1143" class="Keyword">import</a> <a id="1150" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>               <a id="1179" class="Keyword">using</a> <a id="1185" class="Symbol">()</a> <a id="1188" class="Keyword">renaming</a> <a id="1197" class="Symbol">(</a> <a id="1199" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1203" class="Symbol">to</a> <a id="1206" class="Primitive">Type</a> <a id="1211" class="Symbol">)</a>
<a id="1213" class="Keyword">open</a> <a id="1218" class="Keyword">import</a> <a id="1225" href="Level.html" class="Module">Level</a>                        <a id="1254" class="Keyword">using</a> <a id="1260" class="Symbol">(</a> <a id="1262" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1268" class="Symbol">;</a> <a id="1270" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1274" class="Symbol">)</a>

<a id="1277" class="Keyword">private</a> <a id="1285" class="Keyword">variable</a> <a id="1294" href="Overture.Operations.html#1294" class="Generalizable">α</a> <a id="1296" href="Overture.Operations.html#1296" class="Generalizable">β</a> <a id="1298" href="Overture.Operations.html#1298" class="Generalizable">ρ</a> <a id="1300" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a> <a id="1302" class="Symbol">:</a> <a id="1304" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="1311" class="Comment">-- The type of operations on A of arity I</a>
<a id="Op"></a><a id="1353" href="Overture.Operations.html#1353" class="Function">Op</a> <a id="1356" class="Symbol">:</a> <a id="1358" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1363" href="Overture.Operations.html#1294" class="Generalizable">α</a> <a id="1365" class="Symbol">→</a> <a id="1367" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1372" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a> <a id="1374" class="Symbol">→</a> <a id="1376" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1381" class="Symbol">(</a><a id="1382" href="Overture.Operations.html#1294" class="Generalizable">α</a> <a id="1384" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1386" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a><a id="1387" class="Symbol">)</a>
<a id="1389" href="Overture.Operations.html#1353" class="Function">Op</a> <a id="1392" href="Overture.Operations.html#1392" class="Bound">A</a> <a id="1394" href="Overture.Operations.html#1394" class="Bound">I</a> <a id="1396" class="Symbol">=</a> <a id="1398" class="Symbol">(</a><a id="1399" href="Overture.Operations.html#1394" class="Bound">I</a> <a id="1401" class="Symbol">→</a> <a id="1403" href="Overture.Operations.html#1392" class="Bound">A</a><a id="1404" class="Symbol">)</a> <a id="1406" class="Symbol">→</a> <a id="1408" href="Overture.Operations.html#1392" class="Bound">A</a>

<a id="1411" class="Comment">-- Example (projections)</a>
<a id="π"></a><a id="1436" href="Overture.Operations.html#1436" class="Function">π</a> <a id="1438" class="Symbol">:</a> <a id="1440" class="Symbol">{</a><a id="1441" href="Overture.Operations.html#1441" class="Bound">I</a> <a id="1443" class="Symbol">:</a> <a id="1445" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1450" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a><a id="1451" class="Symbol">}</a> <a id="1453" class="Symbol">{</a><a id="1454" href="Overture.Operations.html#1454" class="Bound">A</a> <a id="1456" class="Symbol">:</a> <a id="1458" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1463" href="Overture.Operations.html#1294" class="Generalizable">α</a> <a id="1465" class="Symbol">}</a> <a id="1467" class="Symbol">→</a> <a id="1469" href="Overture.Operations.html#1441" class="Bound">I</a> <a id="1471" class="Symbol">→</a> <a id="1473" href="Overture.Operations.html#1353" class="Function">Op</a> <a id="1476" href="Overture.Operations.html#1454" class="Bound">A</a> <a id="1478" href="Overture.Operations.html#1441" class="Bound">I</a>
<a id="1480" href="Overture.Operations.html#1436" class="Function">π</a> <a id="1482" href="Overture.Operations.html#1482" class="Bound">i</a> <a id="1484" href="Overture.Operations.html#1484" class="Bound">x</a> <a id="1486" class="Symbol">=</a> <a id="1488" href="Overture.Operations.html#1484" class="Bound">x</a> <a id="1490" href="Overture.Operations.html#1482" class="Bound">i</a>

<a id="1493" class="Comment">-- return the arity of a given operation symbol</a>
<a id="arity[_]"></a><a id="1541" href="Overture.Operations.html#1541" class="Function Operator">arity[_]</a> <a id="1550" class="Symbol">:</a> <a id="1552" class="Symbol">{</a><a id="1553" href="Overture.Operations.html#1553" class="Bound">I</a> <a id="1555" class="Symbol">:</a> <a id="1557" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1562" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a><a id="1563" class="Symbol">}</a> <a id="1565" class="Symbol">{</a><a id="1566" href="Overture.Operations.html#1566" class="Bound">A</a> <a id="1568" class="Symbol">:</a> <a id="1570" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1575" href="Overture.Operations.html#1294" class="Generalizable">α</a> <a id="1577" class="Symbol">}</a> <a id="1579" class="Symbol">→</a> <a id="1581" href="Overture.Operations.html#1353" class="Function">Op</a> <a id="1584" href="Overture.Operations.html#1566" class="Bound">A</a> <a id="1586" href="Overture.Operations.html#1553" class="Bound">I</a> <a id="1588" class="Symbol">→</a> <a id="1590" href="Overture.Operations.html#1206" class="Primitive">Type</a> <a id="1595" href="Overture.Operations.html#1300" class="Generalizable">𝓥</a>
<a id="1597" href="Overture.Operations.html#1541" class="Function Operator">arity[_]</a> <a id="1606" class="Symbol">{</a><a id="1607" class="Argument">I</a> <a id="1609" class="Symbol">=</a> <a id="1611" href="Overture.Operations.html#1611" class="Bound">I</a><a id="1612" class="Symbol">}</a> <a id="1614" href="Overture.Operations.html#1614" class="Bound">f</a> <a id="1616" class="Symbol">=</a> <a id="1618" href="Overture.Operations.html#1611" class="Bound">I</a>
</pre>

-----------

<span style="float:left;">[← Overture.Signatures](Overture.Signatures.html)</span>
<span style="float:right;">[Base →](Base.html)</span>


{% include UALib.Links.md %}

