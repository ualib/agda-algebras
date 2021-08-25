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

<a id="1086" class="Keyword">open</a> <a id="1091" class="Keyword">import</a> <a id="1098" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="1116" class="Keyword">using</a> <a id="1122" class="Symbol">(</a> <a id="1124" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1129" class="Symbol">;</a> <a id="1131" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1135" class="Symbol">;</a> <a id="1137" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1143" class="Symbol">)</a> <a id="1145" class="Keyword">renaming</a> <a id="1154" class="Symbol">(</a> <a id="1156" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1160" class="Symbol">to</a> <a id="1163" class="Primitive">Type</a> <a id="1168" class="Symbol">)</a>
<a id="1170" class="Keyword">open</a> <a id="1175" class="Keyword">import</a> <a id="1182" href="Structures.Basic.html" class="Module">Structures.Basic</a>  <a id="1200" class="Keyword">using</a> <a id="1206" class="Symbol">(</a> <a id="1208" href="Structures.Basic.html#1258" class="Record">signature</a> <a id="1218" class="Symbol">;</a> <a id="1220" href="Structures.Basic.html#1592" class="Record">structure</a> <a id="1230" class="Symbol">;</a> <a id="1232" href="Structures.Basic.html#2224" class="Function Operator">_ᵒ_</a> <a id="1236" class="Symbol">)</a>
<a id="1238" class="Keyword">open</a> <a id="1243" class="Keyword">import</a> <a id="1250" href="Terms.Basic.html" class="Module">Terms.Basic</a>


<a id="1264" class="Keyword">private</a> <a id="1272" class="Keyword">variable</a>
 <a id="1282" href="Structures.Terms.html#1282" class="Generalizable">𝓞₀</a> <a id="1285" href="Structures.Terms.html#1285" class="Generalizable">𝓥₀</a> <a id="1288" href="Structures.Terms.html#1288" class="Generalizable">𝓞₁</a> <a id="1291" href="Structures.Terms.html#1291" class="Generalizable">𝓥₁</a> <a id="1294" href="Structures.Terms.html#1294" class="Generalizable">χ</a> <a id="1296" href="Structures.Terms.html#1296" class="Generalizable">α</a> <a id="1298" href="Structures.Terms.html#1298" class="Generalizable">ρ</a> <a id="1300" class="Symbol">:</a> <a id="1302" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1309" href="Structures.Terms.html#1309" class="Generalizable">𝐹</a> <a id="1311" class="Symbol">:</a> <a id="1313" href="Structures.Basic.html#1258" class="Record">signature</a> <a id="1323" href="Structures.Terms.html#1282" class="Generalizable">𝓞₀</a> <a id="1326" href="Structures.Terms.html#1285" class="Generalizable">𝓥₀</a>
 <a id="1330" href="Structures.Terms.html#1330" class="Generalizable">𝑅</a> <a id="1332" class="Symbol">:</a> <a id="1334" href="Structures.Basic.html#1258" class="Record">signature</a> <a id="1344" href="Structures.Terms.html#1288" class="Generalizable">𝓞₁</a> <a id="1347" href="Structures.Terms.html#1291" class="Generalizable">𝓥₁</a>
 <a id="1351" href="Structures.Terms.html#1351" class="Generalizable">X</a> <a id="1353" class="Symbol">:</a> <a id="1355" href="Structures.Terms.html#1163" class="Primitive">Type</a> <a id="1360" href="Structures.Terms.html#1294" class="Generalizable">χ</a>

<a id="1363" class="Keyword">open</a> <a id="1368" href="Structures.Basic.html#1258" class="Module">signature</a>
<a id="1378" class="Keyword">open</a> <a id="1383" href="Structures.Basic.html#1592" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1394" href="Structures.Terms.html#1394" class="Function Operator">_⟦_⟧</a> <a id="1399" class="Symbol">:</a> <a id="1401" class="Symbol">(</a><a id="1402" href="Structures.Terms.html#1402" class="Bound">𝑨</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Structures.Basic.html#1592" class="Record">structure</a> <a id="1416" href="Structures.Terms.html#1309" class="Generalizable">𝐹</a> <a id="1418" href="Structures.Terms.html#1330" class="Generalizable">𝑅</a> <a id="1420" class="Symbol">{</a><a id="1421" href="Structures.Terms.html#1296" class="Generalizable">α</a><a id="1422" class="Symbol">}</a> <a id="1424" class="Symbol">{</a><a id="1425" href="Structures.Terms.html#1298" class="Generalizable">ρ</a><a id="1426" class="Symbol">})</a> <a id="1429" class="Symbol">→</a> <a id="1431" href="Terms.Basic.html#1853" class="Datatype">Term</a> <a id="1436" href="Structures.Terms.html#1351" class="Generalizable">X</a> <a id="1438" class="Symbol">→</a> <a id="1440" class="Symbol">(</a><a id="1441" href="Structures.Terms.html#1351" class="Generalizable">X</a> <a id="1443" class="Symbol">→</a> <a id="1445" href="Structures.Basic.html#1744" class="Field">carrier</a> <a id="1453" href="Structures.Terms.html#1402" class="Bound">𝑨</a><a id="1454" class="Symbol">)</a> <a id="1456" class="Symbol">→</a> <a id="1458" href="Structures.Basic.html#1744" class="Field">carrier</a> <a id="1466" href="Structures.Terms.html#1402" class="Bound">𝑨</a>
<a id="1468" href="Structures.Terms.html#1468" class="Bound">𝑨</a> <a id="1470" href="Structures.Terms.html#1394" class="Function Operator">⟦</a> <a id="1472" href="Terms.Basic.html#1894" class="InductiveConstructor">ℊ</a> <a id="1474" href="Structures.Terms.html#1474" class="Bound">x</a> <a id="1476" href="Structures.Terms.html#1394" class="Function Operator">⟧</a> <a id="1478" class="Symbol">=</a> <a id="1480" class="Symbol">λ</a> <a id="1482" href="Structures.Terms.html#1482" class="Bound">a</a> <a id="1484" class="Symbol">→</a> <a id="1486" href="Structures.Terms.html#1482" class="Bound">a</a> <a id="1488" href="Structures.Terms.html#1474" class="Bound">x</a>
<a id="1490" href="Structures.Terms.html#1490" class="Bound">𝑨</a> <a id="1492" href="Structures.Terms.html#1394" class="Function Operator">⟦</a> <a id="1494" href="Terms.Basic.html#1936" class="InductiveConstructor">node</a> <a id="1499" href="Structures.Terms.html#1499" class="Bound">f</a> <a id="1501" href="Structures.Terms.html#1501" class="Bound">t</a> <a id="1503" href="Structures.Terms.html#1394" class="Function Operator">⟧</a> <a id="1505" class="Symbol">=</a> <a id="1507" class="Symbol">λ</a> <a id="1509" href="Structures.Terms.html#1509" class="Bound">a</a> <a id="1511" class="Symbol">→</a> <a id="1513" class="Symbol">(</a><a id="1514" href="Structures.Terms.html#1499" class="Bound">f</a> <a id="1516" href="Structures.Basic.html#2224" class="Function Operator">ᵒ</a> <a id="1518" href="Structures.Terms.html#1490" class="Bound">𝑨</a><a id="1519" class="Symbol">)</a> <a id="1521" class="Symbol">(λ</a> <a id="1524" href="Structures.Terms.html#1524" class="Bound">i</a> <a id="1526" class="Symbol">→</a> <a id="1528" class="Symbol">(</a><a id="1529" href="Structures.Terms.html#1490" class="Bound">𝑨</a> <a id="1531" href="Structures.Terms.html#1394" class="Function Operator">⟦</a> <a id="1533" href="Structures.Terms.html#1501" class="Bound">t</a> <a id="1535" href="Structures.Terms.html#1524" class="Bound">i</a> <a id="1537" href="Structures.Terms.html#1394" class="Function Operator">⟧</a> <a id="1539" class="Symbol">)</a> <a id="1541" href="Structures.Terms.html#1509" class="Bound">a</a><a id="1542" class="Symbol">)</a>

</pre>

--------------------------------

<br>

[← Structures.Isos](Structures.Isos.html)
<span style="float:right;">[Structures.Substructures →](Structures.Substructures.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


