---
layout: default
title : "Structures.Terms (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="interpretation-of-terms-in-general-structures">Interpretation of Terms in General Structures</a>

This is the [Structures.Terms][] module of the [Agda Universal Algebra Library][].

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

<a id="1007" class="Symbol">{-#</a> <a id="1011" class="Keyword">OPTIONS</a> <a id="1019" class="Pragma">--without-K</a> <a id="1031" class="Pragma">--exact-split</a> <a id="1045" class="Pragma">--safe</a> <a id="1052" class="Symbol">#-}</a>

<a id="1057" class="Keyword">module</a> <a id="1064" href="Structures.Terms.html" class="Module">Structures.Terms</a> <a id="1081" class="Keyword">where</a>

<a id="1088" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="1161" class="Keyword">open</a> <a id="1166" class="Keyword">import</a> <a id="1173" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="1190" class="Keyword">using</a> <a id="1196" class="Symbol">(</a> <a id="1198" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1203" class="Symbol">;</a> <a id="1205" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1209" class="Symbol">;</a> <a id="1211" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1217" class="Symbol">)</a> <a id="1219" class="Keyword">renaming</a> <a id="1228" class="Symbol">(</a> <a id="1230" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1234" class="Symbol">to</a> <a id="1237" class="Primitive">Type</a> <a id="1242" class="Symbol">)</a>
<a id="1244" class="Keyword">open</a> <a id="1249" class="Keyword">import</a> <a id="1256" href="Structures.Basic.html" class="Module">Structures.Basic</a> <a id="1273" class="Keyword">using</a> <a id="1279" class="Symbol">(</a> <a id="1281" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="1291" class="Symbol">;</a> <a id="1293" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="1303" class="Symbol">;</a> <a id="1305" href="Structures.Basic.html#2200" class="Function Operator">_ᵒ_</a> <a id="1309" class="Symbol">)</a>
<a id="1311" class="Keyword">open</a> <a id="1316" class="Keyword">import</a> <a id="1323" href="Terms.Basic.html" class="Module">Terms.Basic</a>

<a id="1336" class="Keyword">private</a> <a id="1344" class="Keyword">variable</a>
 <a id="1354" href="Structures.Terms.html#1354" class="Generalizable">𝓞₀</a> <a id="1357" href="Structures.Terms.html#1357" class="Generalizable">𝓥₀</a> <a id="1360" href="Structures.Terms.html#1360" class="Generalizable">𝓞₁</a> <a id="1363" href="Structures.Terms.html#1363" class="Generalizable">𝓥₁</a> <a id="1366" href="Structures.Terms.html#1366" class="Generalizable">χ</a> <a id="1368" href="Structures.Terms.html#1368" class="Generalizable">α</a> <a id="1370" href="Structures.Terms.html#1370" class="Generalizable">ρ</a> <a id="1372" class="Symbol">:</a> <a id="1374" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1381" href="Structures.Terms.html#1381" class="Generalizable">𝐹</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="1395" href="Structures.Terms.html#1354" class="Generalizable">𝓞₀</a> <a id="1398" href="Structures.Terms.html#1357" class="Generalizable">𝓥₀</a>
 <a id="1402" href="Structures.Terms.html#1402" class="Generalizable">𝑅</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="1416" href="Structures.Terms.html#1360" class="Generalizable">𝓞₁</a> <a id="1419" href="Structures.Terms.html#1363" class="Generalizable">𝓥₁</a>
 <a id="1423" href="Structures.Terms.html#1423" class="Generalizable">X</a> <a id="1425" class="Symbol">:</a> <a id="1427" href="Structures.Terms.html#1237" class="Primitive">Type</a> <a id="1432" href="Structures.Terms.html#1366" class="Generalizable">χ</a>

<a id="1435" class="Keyword">open</a> <a id="1440" href="Structures.Basic.html#1234" class="Module">signature</a>
<a id="1450" class="Keyword">open</a> <a id="1455" href="Structures.Basic.html#1568" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1466" href="Structures.Terms.html#1466" class="Function Operator">_⟦_⟧</a> <a id="1471" class="Symbol">:</a> <a id="1473" class="Symbol">(</a><a id="1474" href="Structures.Terms.html#1474" class="Bound">𝑨</a> <a id="1476" class="Symbol">:</a> <a id="1478" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="1488" href="Structures.Terms.html#1381" class="Generalizable">𝐹</a> <a id="1490" href="Structures.Terms.html#1402" class="Generalizable">𝑅</a> <a id="1492" class="Symbol">{</a><a id="1493" href="Structures.Terms.html#1368" class="Generalizable">α</a><a id="1494" class="Symbol">}</a> <a id="1496" class="Symbol">{</a><a id="1497" href="Structures.Terms.html#1370" class="Generalizable">ρ</a><a id="1498" class="Symbol">})</a> <a id="1501" class="Symbol">→</a> <a id="1503" href="Terms.Basic.html#1991" class="Datatype">Term</a> <a id="1508" href="Structures.Terms.html#1423" class="Generalizable">X</a> <a id="1510" class="Symbol">→</a> <a id="1512" class="Symbol">(</a><a id="1513" href="Structures.Terms.html#1423" class="Generalizable">X</a> <a id="1515" class="Symbol">→</a> <a id="1517" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="1525" href="Structures.Terms.html#1474" class="Bound">𝑨</a><a id="1526" class="Symbol">)</a> <a id="1528" class="Symbol">→</a> <a id="1530" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="1538" href="Structures.Terms.html#1474" class="Bound">𝑨</a>
<a id="1540" href="Structures.Terms.html#1540" class="Bound">𝑨</a> <a id="1542" href="Structures.Terms.html#1466" class="Function Operator">⟦</a> <a id="1544" href="Terms.Basic.html#2032" class="InductiveConstructor">ℊ</a> <a id="1546" href="Structures.Terms.html#1546" class="Bound">x</a> <a id="1548" href="Structures.Terms.html#1466" class="Function Operator">⟧</a> <a id="1550" class="Symbol">=</a> <a id="1552" class="Symbol">λ</a> <a id="1554" href="Structures.Terms.html#1554" class="Bound">a</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="Structures.Terms.html#1554" class="Bound">a</a> <a id="1560" href="Structures.Terms.html#1546" class="Bound">x</a>
<a id="1562" href="Structures.Terms.html#1562" class="Bound">𝑨</a> <a id="1564" href="Structures.Terms.html#1466" class="Function Operator">⟦</a> <a id="1566" href="Terms.Basic.html#2074" class="InductiveConstructor">node</a> <a id="1571" href="Structures.Terms.html#1571" class="Bound">f</a> <a id="1573" href="Structures.Terms.html#1573" class="Bound">t</a> <a id="1575" href="Structures.Terms.html#1466" class="Function Operator">⟧</a> <a id="1577" class="Symbol">=</a> <a id="1579" class="Symbol">λ</a> <a id="1581" href="Structures.Terms.html#1581" class="Bound">a</a> <a id="1583" class="Symbol">→</a> <a id="1585" class="Symbol">(</a><a id="1586" href="Structures.Terms.html#1571" class="Bound">f</a> <a id="1588" href="Structures.Basic.html#2200" class="Function Operator">ᵒ</a> <a id="1590" href="Structures.Terms.html#1562" class="Bound">𝑨</a><a id="1591" class="Symbol">)</a> <a id="1593" class="Symbol">(λ</a> <a id="1596" href="Structures.Terms.html#1596" class="Bound">i</a> <a id="1598" class="Symbol">→</a> <a id="1600" class="Symbol">(</a><a id="1601" href="Structures.Terms.html#1562" class="Bound">𝑨</a> <a id="1603" href="Structures.Terms.html#1466" class="Function Operator">⟦</a> <a id="1605" href="Structures.Terms.html#1573" class="Bound">t</a> <a id="1607" href="Structures.Terms.html#1596" class="Bound">i</a> <a id="1609" href="Structures.Terms.html#1466" class="Function Operator">⟧</a> <a id="1611" class="Symbol">)</a> <a id="1613" href="Structures.Terms.html#1581" class="Bound">a</a><a id="1614" class="Symbol">)</a>

</pre>

--------------------------------

<span style="float:left;">[← Structures.Isos](Structures.Isos.html)</span>
<span style="float:right;">[Structures.Substructures →](Structures.Substructures.html)</span>

{% include UALib.Links.md %}
