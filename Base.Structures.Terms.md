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
<a id="1176" class="Keyword">open</a> <a id="1181" class="Keyword">import</a> <a id="1188" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>         <a id="1211" class="Keyword">using</a> <a id="1217" class="Symbol">(</a> <a id="1219" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1224" class="Symbol">;</a> <a id="1226" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1230" class="Symbol">;</a> <a id="1232" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1238" class="Symbol">)</a> <a id="1240" class="Keyword">renaming</a> <a id="1249" class="Symbol">(</a> <a id="1251" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1255" class="Symbol">to</a> <a id="1258" class="Primitive">Type</a> <a id="1263" class="Symbol">)</a>
<a id="1265" class="Keyword">open</a> <a id="1270" class="Keyword">import</a> <a id="1277" href="Base.Structures.Basic.html" class="Module">Base.Structures.Basic</a>  <a id="1300" class="Keyword">using</a> <a id="1306" class="Symbol">(</a> <a id="1308" href="Base.Structures.Basic.html#1264" class="Record">signature</a> <a id="1318" class="Symbol">;</a> <a id="1320" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="1330" class="Symbol">;</a> <a id="1332" href="Base.Structures.Basic.html#2230" class="Function Operator">_ᵒ_</a> <a id="1336" class="Symbol">)</a>
<a id="1338" class="Keyword">open</a> <a id="1343" class="Keyword">import</a> <a id="1350" href="Base.Terms.Basic.html" class="Module">Base.Terms.Basic</a>

<a id="1368" class="Keyword">private</a> <a id="1376" class="Keyword">variable</a>
 <a id="1386" href="Base.Structures.Terms.html#1386" class="Generalizable">𝓞₀</a> <a id="1389" href="Base.Structures.Terms.html#1389" class="Generalizable">𝓥₀</a> <a id="1392" href="Base.Structures.Terms.html#1392" class="Generalizable">𝓞₁</a> <a id="1395" href="Base.Structures.Terms.html#1395" class="Generalizable">𝓥₁</a> <a id="1398" href="Base.Structures.Terms.html#1398" class="Generalizable">χ</a> <a id="1400" href="Base.Structures.Terms.html#1400" class="Generalizable">α</a> <a id="1402" href="Base.Structures.Terms.html#1402" class="Generalizable">ρ</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1413" href="Base.Structures.Terms.html#1413" class="Generalizable">𝐹</a> <a id="1415" class="Symbol">:</a> <a id="1417" href="Base.Structures.Basic.html#1264" class="Record">signature</a> <a id="1427" href="Base.Structures.Terms.html#1386" class="Generalizable">𝓞₀</a> <a id="1430" href="Base.Structures.Terms.html#1389" class="Generalizable">𝓥₀</a>
 <a id="1434" href="Base.Structures.Terms.html#1434" class="Generalizable">𝑅</a> <a id="1436" class="Symbol">:</a> <a id="1438" href="Base.Structures.Basic.html#1264" class="Record">signature</a> <a id="1448" href="Base.Structures.Terms.html#1392" class="Generalizable">𝓞₁</a> <a id="1451" href="Base.Structures.Terms.html#1395" class="Generalizable">𝓥₁</a>
 <a id="1455" href="Base.Structures.Terms.html#1455" class="Generalizable">X</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="Base.Structures.Terms.html#1258" class="Primitive">Type</a> <a id="1464" href="Base.Structures.Terms.html#1398" class="Generalizable">χ</a>

<a id="1467" class="Keyword">open</a> <a id="1472" href="Base.Structures.Basic.html#1264" class="Module">signature</a>
<a id="1482" class="Keyword">open</a> <a id="1487" href="Base.Structures.Basic.html#1598" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1498" href="Base.Structures.Terms.html#1498" class="Function Operator">_⟦_⟧</a> <a id="1503" class="Symbol">:</a> <a id="1505" class="Symbol">(</a><a id="1506" href="Base.Structures.Terms.html#1506" class="Bound">𝑨</a> <a id="1508" class="Symbol">:</a> <a id="1510" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="1520" href="Base.Structures.Terms.html#1413" class="Generalizable">𝐹</a> <a id="1522" href="Base.Structures.Terms.html#1434" class="Generalizable">𝑅</a> <a id="1524" class="Symbol">{</a><a id="1525" href="Base.Structures.Terms.html#1400" class="Generalizable">α</a><a id="1526" class="Symbol">}</a> <a id="1528" class="Symbol">{</a><a id="1529" href="Base.Structures.Terms.html#1402" class="Generalizable">ρ</a><a id="1530" class="Symbol">})</a> <a id="1533" class="Symbol">→</a> <a id="1535" href="Base.Terms.Basic.html#2021" class="Datatype">Term</a> <a id="1540" href="Base.Structures.Terms.html#1455" class="Generalizable">X</a> <a id="1542" class="Symbol">→</a> <a id="1544" class="Symbol">(</a><a id="1545" href="Base.Structures.Terms.html#1455" class="Generalizable">X</a> <a id="1547" class="Symbol">→</a> <a id="1549" href="Base.Structures.Basic.html#1750" class="Field">carrier</a> <a id="1557" href="Base.Structures.Terms.html#1506" class="Bound">𝑨</a><a id="1558" class="Symbol">)</a> <a id="1560" class="Symbol">→</a> <a id="1562" href="Base.Structures.Basic.html#1750" class="Field">carrier</a> <a id="1570" href="Base.Structures.Terms.html#1506" class="Bound">𝑨</a>
<a id="1572" href="Base.Structures.Terms.html#1572" class="Bound">𝑨</a> <a id="1574" href="Base.Structures.Terms.html#1498" class="Function Operator">⟦</a> <a id="1576" href="Base.Terms.Basic.html#2062" class="InductiveConstructor">ℊ</a> <a id="1578" href="Base.Structures.Terms.html#1578" class="Bound">x</a> <a id="1580" href="Base.Structures.Terms.html#1498" class="Function Operator">⟧</a> <a id="1582" class="Symbol">=</a> <a id="1584" class="Symbol">λ</a> <a id="1586" href="Base.Structures.Terms.html#1586" class="Bound">a</a> <a id="1588" class="Symbol">→</a> <a id="1590" href="Base.Structures.Terms.html#1586" class="Bound">a</a> <a id="1592" href="Base.Structures.Terms.html#1578" class="Bound">x</a>
<a id="1594" href="Base.Structures.Terms.html#1594" class="Bound">𝑨</a> <a id="1596" href="Base.Structures.Terms.html#1498" class="Function Operator">⟦</a> <a id="1598" href="Base.Terms.Basic.html#2104" class="InductiveConstructor">node</a> <a id="1603" href="Base.Structures.Terms.html#1603" class="Bound">f</a> <a id="1605" href="Base.Structures.Terms.html#1605" class="Bound">t</a> <a id="1607" href="Base.Structures.Terms.html#1498" class="Function Operator">⟧</a> <a id="1609" class="Symbol">=</a> <a id="1611" class="Symbol">λ</a> <a id="1613" href="Base.Structures.Terms.html#1613" class="Bound">a</a> <a id="1615" class="Symbol">→</a> <a id="1617" class="Symbol">(</a><a id="1618" href="Base.Structures.Terms.html#1603" class="Bound">f</a> <a id="1620" href="Base.Structures.Basic.html#2230" class="Function Operator">ᵒ</a> <a id="1622" href="Base.Structures.Terms.html#1594" class="Bound">𝑨</a><a id="1623" class="Symbol">)</a> <a id="1625" class="Symbol">(λ</a> <a id="1628" href="Base.Structures.Terms.html#1628" class="Bound">i</a> <a id="1630" class="Symbol">→</a> <a id="1632" class="Symbol">(</a><a id="1633" href="Base.Structures.Terms.html#1594" class="Bound">𝑨</a> <a id="1635" href="Base.Structures.Terms.html#1498" class="Function Operator">⟦</a> <a id="1637" href="Base.Structures.Terms.html#1605" class="Bound">t</a> <a id="1639" href="Base.Structures.Terms.html#1628" class="Bound">i</a> <a id="1641" href="Base.Structures.Terms.html#1498" class="Function Operator">⟧</a> <a id="1643" class="Symbol">)</a> <a id="1645" href="Base.Structures.Terms.html#1613" class="Bound">a</a><a id="1646" class="Symbol">)</a>

</pre>

--------------------------------

<span style="float:left;">[← Base.Structures.Isos](Base.Structures.Isos.html)</span>
<span style="float:right;">[Base.Structures.Substructures →](Base.Structures.Substructures.html)</span>

{% include UALib.Links.md %}
