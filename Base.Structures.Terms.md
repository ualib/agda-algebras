---
layout: default
title : "Base.Structures.Terms (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="interpretation-of-terms-in-general-structures">Interpretation of Terms in General Structures</a>

This is the [Base.Structures.Terms][] module of the [Agda Universal Algebra Library][].

When we interpret a term in a structure we call the resulting
function a *term operation*. Given a term `p` and a structure `𝑨`,
we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.
This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and
   if `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then
   define `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = f t`, where `f : ∣ 𝑆 ∣` is an operation symbol,
   if `t : (arity 𝐹) f → 𝑻 X` is a tuple of terms, and
   if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then
   define `𝑨 ⟦ p ⟧ a := (f ᵒ 𝑨) (λ i → 𝑨 ⟦ t i ⟧ a)`.

Thus interpretation of a term is defined by structural induction.

<pre class="Agda">

<a id="1017" class="Symbol">{-#</a> <a id="1021" class="Keyword">OPTIONS</a> <a id="1029" class="Pragma">--without-K</a> <a id="1041" class="Pragma">--exact-split</a> <a id="1055" class="Pragma">--safe</a> <a id="1062" class="Symbol">#-}</a>

<a id="1067" class="Keyword">module</a> <a id="1074" href="Base.Structures.Terms.html" class="Module">Base.Structures.Terms</a> <a id="1096" class="Keyword">where</a>

<a id="1103" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="1176" class="Keyword">open</a> <a id="1181" class="Keyword">import</a> <a id="1188" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="1204" class="Keyword">using</a> <a id="1210" class="Symbol">()</a> <a id="1213" class="Keyword">renaming</a> <a id="1222" class="Symbol">(</a> <a id="1224" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1228" class="Symbol">to</a> <a id="1231" class="Primitive">Type</a> <a id="1236" class="Symbol">)</a>
<a id="1238" class="Keyword">open</a> <a id="1243" class="Keyword">import</a> <a id="1250" href="Level.html" class="Module">Level</a>           <a id="1266" class="Keyword">using</a> <a id="1272" class="Symbol">(</a> <a id="1274" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1280" class="Symbol">)</a>

<a id="1283" class="Keyword">open</a> <a id="1288" class="Keyword">import</a> <a id="1295" href="Base.Structures.Basic.html" class="Module">Base.Structures.Basic</a>  <a id="1318" class="Keyword">using</a> <a id="1324" class="Symbol">(</a> <a id="1326" href="Base.Structures.Basic.html#1233" class="Record">signature</a> <a id="1336" class="Symbol">;</a> <a id="1338" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="1348" class="Symbol">;</a> <a id="1350" href="Base.Structures.Basic.html#2214" class="Function Operator">_ᵒ_</a> <a id="1354" class="Symbol">)</a>
<a id="1356" class="Keyword">open</a> <a id="1361" class="Keyword">import</a> <a id="1368" href="Base.Terms.Basic.html" class="Module">Base.Terms.Basic</a>

<a id="1386" class="Keyword">private</a> <a id="1394" class="Keyword">variable</a>
 <a id="1404" href="Base.Structures.Terms.html#1404" class="Generalizable">𝓞₀</a> <a id="1407" href="Base.Structures.Terms.html#1407" class="Generalizable">𝓥₀</a> <a id="1410" href="Base.Structures.Terms.html#1410" class="Generalizable">𝓞₁</a> <a id="1413" href="Base.Structures.Terms.html#1413" class="Generalizable">𝓥₁</a> <a id="1416" href="Base.Structures.Terms.html#1416" class="Generalizable">χ</a> <a id="1418" href="Base.Structures.Terms.html#1418" class="Generalizable">α</a> <a id="1420" href="Base.Structures.Terms.html#1420" class="Generalizable">ρ</a> <a id="1422" class="Symbol">:</a> <a id="1424" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1431" href="Base.Structures.Terms.html#1431" class="Generalizable">𝐹</a> <a id="1433" class="Symbol">:</a> <a id="1435" href="Base.Structures.Basic.html#1233" class="Record">signature</a> <a id="1445" href="Base.Structures.Terms.html#1404" class="Generalizable">𝓞₀</a> <a id="1448" href="Base.Structures.Terms.html#1407" class="Generalizable">𝓥₀</a>
 <a id="1452" href="Base.Structures.Terms.html#1452" class="Generalizable">𝑅</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="Base.Structures.Basic.html#1233" class="Record">signature</a> <a id="1466" href="Base.Structures.Terms.html#1410" class="Generalizable">𝓞₁</a> <a id="1469" href="Base.Structures.Terms.html#1413" class="Generalizable">𝓥₁</a>
 <a id="1473" href="Base.Structures.Terms.html#1473" class="Generalizable">X</a> <a id="1475" class="Symbol">:</a> <a id="1477" href="Base.Structures.Terms.html#1231" class="Primitive">Type</a> <a id="1482" href="Base.Structures.Terms.html#1416" class="Generalizable">χ</a>

<a id="1485" class="Keyword">open</a> <a id="1490" href="Base.Structures.Basic.html#1233" class="Module">signature</a>
<a id="1500" class="Keyword">open</a> <a id="1505" href="Base.Structures.Basic.html#1566" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1516" href="Base.Structures.Terms.html#1516" class="Function Operator">_⟦_⟧</a> <a id="1521" class="Symbol">:</a> <a id="1523" class="Symbol">(</a><a id="1524" href="Base.Structures.Terms.html#1524" class="Bound">𝑨</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="1538" href="Base.Structures.Terms.html#1431" class="Generalizable">𝐹</a> <a id="1540" href="Base.Structures.Terms.html#1452" class="Generalizable">𝑅</a> <a id="1542" class="Symbol">{</a><a id="1543" href="Base.Structures.Terms.html#1418" class="Generalizable">α</a><a id="1544" class="Symbol">}</a> <a id="1546" class="Symbol">{</a><a id="1547" href="Base.Structures.Terms.html#1420" class="Generalizable">ρ</a><a id="1548" class="Symbol">})</a> <a id="1551" class="Symbol">→</a> <a id="1553" href="Base.Terms.Basic.html#2087" class="Datatype">Term</a> <a id="1558" href="Base.Structures.Terms.html#1473" class="Generalizable">X</a> <a id="1560" class="Symbol">→</a> <a id="1562" class="Symbol">(</a><a id="1563" href="Base.Structures.Terms.html#1473" class="Generalizable">X</a> <a id="1565" class="Symbol">→</a> <a id="1567" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="1575" href="Base.Structures.Terms.html#1524" class="Bound">𝑨</a><a id="1576" class="Symbol">)</a> <a id="1578" class="Symbol">→</a> <a id="1580" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="1588" href="Base.Structures.Terms.html#1524" class="Bound">𝑨</a>
<a id="1590" href="Base.Structures.Terms.html#1590" class="Bound">𝑨</a> <a id="1592" href="Base.Structures.Terms.html#1516" class="Function Operator">⟦</a> <a id="1594" href="Base.Terms.Basic.html#2128" class="InductiveConstructor">ℊ</a> <a id="1596" href="Base.Structures.Terms.html#1596" class="Bound">x</a> <a id="1598" href="Base.Structures.Terms.html#1516" class="Function Operator">⟧</a> <a id="1600" class="Symbol">=</a> <a id="1602" class="Symbol">λ</a> <a id="1604" href="Base.Structures.Terms.html#1604" class="Bound">a</a> <a id="1606" class="Symbol">→</a> <a id="1608" href="Base.Structures.Terms.html#1604" class="Bound">a</a> <a id="1610" href="Base.Structures.Terms.html#1596" class="Bound">x</a>
<a id="1612" href="Base.Structures.Terms.html#1612" class="Bound">𝑨</a> <a id="1614" href="Base.Structures.Terms.html#1516" class="Function Operator">⟦</a> <a id="1616" href="Base.Terms.Basic.html#2170" class="InductiveConstructor">node</a> <a id="1621" href="Base.Structures.Terms.html#1621" class="Bound">f</a> <a id="1623" href="Base.Structures.Terms.html#1623" class="Bound">t</a> <a id="1625" href="Base.Structures.Terms.html#1516" class="Function Operator">⟧</a> <a id="1627" class="Symbol">=</a> <a id="1629" class="Symbol">λ</a> <a id="1631" href="Base.Structures.Terms.html#1631" class="Bound">a</a> <a id="1633" class="Symbol">→</a> <a id="1635" class="Symbol">(</a><a id="1636" href="Base.Structures.Terms.html#1621" class="Bound">f</a> <a id="1638" href="Base.Structures.Basic.html#2214" class="Function Operator">ᵒ</a> <a id="1640" href="Base.Structures.Terms.html#1612" class="Bound">𝑨</a><a id="1641" class="Symbol">)</a> <a id="1643" class="Symbol">(λ</a> <a id="1646" href="Base.Structures.Terms.html#1646" class="Bound">i</a> <a id="1648" class="Symbol">→</a> <a id="1650" class="Symbol">(</a><a id="1651" href="Base.Structures.Terms.html#1612" class="Bound">𝑨</a> <a id="1653" href="Base.Structures.Terms.html#1516" class="Function Operator">⟦</a> <a id="1655" href="Base.Structures.Terms.html#1623" class="Bound">t</a> <a id="1657" href="Base.Structures.Terms.html#1646" class="Bound">i</a> <a id="1659" href="Base.Structures.Terms.html#1516" class="Function Operator">⟧</a> <a id="1661" class="Symbol">)</a> <a id="1663" href="Base.Structures.Terms.html#1631" class="Bound">a</a><a id="1664" class="Symbol">)</a>
</pre>

--------------------------------

<span style="float:left;">[← Base.Structures.Isos](Base.Structures.Isos.html)</span>
<span style="float:right;">[Base.Structures.Substructures →](Base.Structures.Substructures.html)</span>

{% include UALib.Links.md %}
