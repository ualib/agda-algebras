---
layout: default
title : Structures.Terms (The Agda Universal Algebra Library)
date : 2021-07-26
author: [agda-algebras development team][]
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

<a id="1005" class="Symbol">{-#</a> <a id="1009" class="Keyword">OPTIONS</a> <a id="1017" class="Pragma">--without-K</a> <a id="1029" class="Pragma">--exact-split</a> <a id="1043" class="Pragma">--safe</a> <a id="1050" class="Symbol">#-}</a>

<a id="1055" class="Keyword">module</a> <a id="1062" href="Structures.Terms.html" class="Module">Structures.Terms</a> <a id="1079" class="Keyword">where</a>

<a id="1086" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="1159" class="Keyword">open</a> <a id="1164" class="Keyword">import</a> <a id="1171" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="1189" class="Keyword">using</a> <a id="1195" class="Symbol">(</a> <a id="1197" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1202" class="Symbol">;</a> <a id="1204" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1208" class="Symbol">;</a> <a id="1210" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1216" class="Symbol">)</a> <a id="1218" class="Keyword">renaming</a> <a id="1227" class="Symbol">(</a> <a id="1229" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1233" class="Symbol">to</a> <a id="1236" class="Primitive">Type</a> <a id="1241" class="Symbol">)</a>
<a id="1243" class="Keyword">open</a> <a id="1248" class="Keyword">import</a> <a id="1255" href="Structures.Basic.html" class="Module">Structures.Basic</a>  <a id="1273" class="Keyword">using</a> <a id="1279" class="Symbol">(</a> <a id="1281" href="Structures.Basic.html#1232" class="Record">signature</a> <a id="1291" class="Symbol">;</a> <a id="1293" href="Structures.Basic.html#1566" class="Record">structure</a> <a id="1303" class="Symbol">;</a> <a id="1305" href="Structures.Basic.html#2198" class="Function Operator">_ᵒ_</a> <a id="1309" class="Symbol">)</a>
<a id="1311" class="Keyword">open</a> <a id="1316" class="Keyword">import</a> <a id="1323" href="Terms.Basic.html" class="Module">Terms.Basic</a>


<a id="1337" class="Keyword">private</a> <a id="1345" class="Keyword">variable</a>
 <a id="1355" href="Structures.Terms.html#1355" class="Generalizable">𝓞₀</a> <a id="1358" href="Structures.Terms.html#1358" class="Generalizable">𝓥₀</a> <a id="1361" href="Structures.Terms.html#1361" class="Generalizable">𝓞₁</a> <a id="1364" href="Structures.Terms.html#1364" class="Generalizable">𝓥₁</a> <a id="1367" href="Structures.Terms.html#1367" class="Generalizable">χ</a> <a id="1369" href="Structures.Terms.html#1369" class="Generalizable">α</a> <a id="1371" href="Structures.Terms.html#1371" class="Generalizable">ρ</a> <a id="1373" class="Symbol">:</a> <a id="1375" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1382" href="Structures.Terms.html#1382" class="Generalizable">𝐹</a> <a id="1384" class="Symbol">:</a> <a id="1386" href="Structures.Basic.html#1232" class="Record">signature</a> <a id="1396" href="Structures.Terms.html#1355" class="Generalizable">𝓞₀</a> <a id="1399" href="Structures.Terms.html#1358" class="Generalizable">𝓥₀</a>
 <a id="1403" href="Structures.Terms.html#1403" class="Generalizable">𝑅</a> <a id="1405" class="Symbol">:</a> <a id="1407" href="Structures.Basic.html#1232" class="Record">signature</a> <a id="1417" href="Structures.Terms.html#1361" class="Generalizable">𝓞₁</a> <a id="1420" href="Structures.Terms.html#1364" class="Generalizable">𝓥₁</a>
 <a id="1424" href="Structures.Terms.html#1424" class="Generalizable">X</a> <a id="1426" class="Symbol">:</a> <a id="1428" href="Structures.Terms.html#1236" class="Primitive">Type</a> <a id="1433" href="Structures.Terms.html#1367" class="Generalizable">χ</a>

<a id="1436" class="Keyword">open</a> <a id="1441" href="Structures.Basic.html#1232" class="Module">signature</a>
<a id="1451" class="Keyword">open</a> <a id="1456" href="Structures.Basic.html#1566" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1467" href="Structures.Terms.html#1467" class="Function Operator">_⟦_⟧</a> <a id="1472" class="Symbol">:</a> <a id="1474" class="Symbol">(</a><a id="1475" href="Structures.Terms.html#1475" class="Bound">𝑨</a> <a id="1477" class="Symbol">:</a> <a id="1479" href="Structures.Basic.html#1566" class="Record">structure</a> <a id="1489" href="Structures.Terms.html#1382" class="Generalizable">𝐹</a> <a id="1491" href="Structures.Terms.html#1403" class="Generalizable">𝑅</a> <a id="1493" class="Symbol">{</a><a id="1494" href="Structures.Terms.html#1369" class="Generalizable">α</a><a id="1495" class="Symbol">}</a> <a id="1497" class="Symbol">{</a><a id="1498" href="Structures.Terms.html#1371" class="Generalizable">ρ</a><a id="1499" class="Symbol">})</a> <a id="1502" class="Symbol">→</a> <a id="1504" href="Terms.Basic.html#1989" class="Datatype">Term</a> <a id="1509" href="Structures.Terms.html#1424" class="Generalizable">X</a> <a id="1511" class="Symbol">→</a> <a id="1513" class="Symbol">(</a><a id="1514" href="Structures.Terms.html#1424" class="Generalizable">X</a> <a id="1516" class="Symbol">→</a> <a id="1518" href="Structures.Basic.html#1718" class="Field">carrier</a> <a id="1526" href="Structures.Terms.html#1475" class="Bound">𝑨</a><a id="1527" class="Symbol">)</a> <a id="1529" class="Symbol">→</a> <a id="1531" href="Structures.Basic.html#1718" class="Field">carrier</a> <a id="1539" href="Structures.Terms.html#1475" class="Bound">𝑨</a>
<a id="1541" href="Structures.Terms.html#1541" class="Bound">𝑨</a> <a id="1543" href="Structures.Terms.html#1467" class="Function Operator">⟦</a> <a id="1545" href="Terms.Basic.html#2030" class="InductiveConstructor">ℊ</a> <a id="1547" href="Structures.Terms.html#1547" class="Bound">x</a> <a id="1549" href="Structures.Terms.html#1467" class="Function Operator">⟧</a> <a id="1551" class="Symbol">=</a> <a id="1553" class="Symbol">λ</a> <a id="1555" href="Structures.Terms.html#1555" class="Bound">a</a> <a id="1557" class="Symbol">→</a> <a id="1559" href="Structures.Terms.html#1555" class="Bound">a</a> <a id="1561" href="Structures.Terms.html#1547" class="Bound">x</a>
<a id="1563" href="Structures.Terms.html#1563" class="Bound">𝑨</a> <a id="1565" href="Structures.Terms.html#1467" class="Function Operator">⟦</a> <a id="1567" href="Terms.Basic.html#2072" class="InductiveConstructor">node</a> <a id="1572" href="Structures.Terms.html#1572" class="Bound">f</a> <a id="1574" href="Structures.Terms.html#1574" class="Bound">t</a> <a id="1576" href="Structures.Terms.html#1467" class="Function Operator">⟧</a> <a id="1578" class="Symbol">=</a> <a id="1580" class="Symbol">λ</a> <a id="1582" href="Structures.Terms.html#1582" class="Bound">a</a> <a id="1584" class="Symbol">→</a> <a id="1586" class="Symbol">(</a><a id="1587" href="Structures.Terms.html#1572" class="Bound">f</a> <a id="1589" href="Structures.Basic.html#2198" class="Function Operator">ᵒ</a> <a id="1591" href="Structures.Terms.html#1563" class="Bound">𝑨</a><a id="1592" class="Symbol">)</a> <a id="1594" class="Symbol">(λ</a> <a id="1597" href="Structures.Terms.html#1597" class="Bound">i</a> <a id="1599" class="Symbol">→</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Structures.Terms.html#1563" class="Bound">𝑨</a> <a id="1604" href="Structures.Terms.html#1467" class="Function Operator">⟦</a> <a id="1606" href="Structures.Terms.html#1574" class="Bound">t</a> <a id="1608" href="Structures.Terms.html#1597" class="Bound">i</a> <a id="1610" href="Structures.Terms.html#1467" class="Function Operator">⟧</a> <a id="1612" class="Symbol">)</a> <a id="1614" href="Structures.Terms.html#1582" class="Bound">a</a><a id="1615" class="Symbol">)</a>

</pre>

--------------------------------

[← Structures.Isos](Structures.Isos.html)
<span style="float:right;">[Structures.Substructures →](Structures.Substructures.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


