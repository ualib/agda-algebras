---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### <a id="closure-systems-and-operators">Closure Systems and Operators</a>

#### <a id="closure-systems">Closure Systems</a>

A *closure system* on a set `X` is a collection `𝒞` of subsets of `X` that is closed
under arbitrary intersection (including the empty intersection, so `⋂ ∅ = X ∈ 𝒞`.

Thus a closure system is a complete meet semilattice with respect to the subset
inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the closed
sets of a closure system form a complete lattice.
(See J.B. Nation's [Lattice Theory Notes](http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf), Theorem 2.5.)

Some examples of closure systems are the following:

* order ideals of an ordered set
* subalgebras of an algebra
* equivalence relations on a set
* congruence relations of an algebra


<pre class="Agda">

<a id="1011" class="Symbol">{-#</a> <a id="1015" class="Keyword">OPTIONS</a> <a id="1023" class="Pragma">--without-K</a> <a id="1035" class="Pragma">--exact-split</a> <a id="1049" class="Pragma">--safe</a> <a id="1056" class="Symbol">#-}</a>

<a id="1061" class="Keyword">module</a> <a id="1068" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1089" class="Keyword">where</a>

<a id="1096" class="Keyword">open</a> <a id="1101" class="Keyword">import</a> <a id="1108" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1133" class="Keyword">using</a> <a id="1139" class="Symbol">(</a> <a id="1141" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1145" class="Symbol">;</a> <a id="1147" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1152" class="Symbol">)</a>     <a id="1158" class="Keyword">renaming</a> <a id="1167" class="Symbol">(</a> <a id="1169" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1173" class="Symbol">to</a> <a id="1176" class="Primitive">Type</a> <a id="1181" class="Symbol">)</a>
<a id="1183" class="Keyword">import</a> <a id="1190" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1210" class="Keyword">open</a> <a id="1215" class="Keyword">import</a> <a id="1222" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1247" class="Keyword">using</a> <a id="1253" class="Symbol">(</a> <a id="1255" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1264" class="Symbol">)</a>
<a id="1266" class="Keyword">open</a> <a id="1271" class="Keyword">import</a> <a id="1278" href="Level.html" class="Module">Level</a>                    <a id="1303" class="Keyword">using</a> <a id="1309" class="Symbol">(</a> <a id="1311" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1317" class="Symbol">;</a> <a id="1319" href="Level.html#400" class="Record">Lift</a> <a id="1324" class="Symbol">)</a>   <a id="1328" class="Keyword">renaming</a> <a id="1337" class="Symbol">(</a> <a id="1339" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1344" class="Symbol">to</a> <a id="1347" class="Primitive">ℓ₀</a> <a id="1350" class="Symbol">)</a>
<a id="1352" class="Keyword">open</a> <a id="1357" class="Keyword">import</a> <a id="1364" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1389" class="Keyword">using</a> <a id="1395" class="Symbol">(</a> <a id="1397" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1403" class="Symbol">)</a>
<a id="1405" class="Keyword">open</a> <a id="1410" class="Keyword">import</a> <a id="1417" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1442" class="Keyword">using</a> <a id="1448" class="Symbol">(</a> <a id="1450" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1464" class="Symbol">)</a>
<a id="1466" class="Keyword">open</a> <a id="1471" class="Keyword">import</a> <a id="1478" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1503" class="Keyword">using</a> <a id="1509" class="Symbol">(</a> <a id="1511" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1516" class="Symbol">;</a> <a id="1518" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1522" class="Symbol">;</a> <a id="1524" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1526" class="Symbol">)</a>

<a id="1529" class="Keyword">open</a> <a id="1534" class="Keyword">import</a> <a id="1541" href="ClosureSystems.Definitions.html" class="Module">ClosureSystems.Definitions</a> <a id="1568" class="Keyword">using</a> <a id="1574" class="Symbol">(</a> <a id="1576" href="ClosureSystems.Definitions.html#581" class="Function">Extensive</a> <a id="1586" class="Symbol">)</a>


<a id="1590" class="Keyword">module</a> <a id="1597" href="ClosureSystems.Basic.html#1597" class="Module">_</a> <a id="1599" class="Symbol">{</a><a id="1600" href="ClosureSystems.Basic.html#1600" class="Bound">χ</a> <a id="1602" href="ClosureSystems.Basic.html#1602" class="Bound">ℓ</a> <a id="1604" href="ClosureSystems.Basic.html#1604" class="Bound">ρ</a> <a id="1606" class="Symbol">:</a> <a id="1608" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1613" class="Symbol">}{</a><a id="1615" href="ClosureSystems.Basic.html#1615" class="Bound">X</a> <a id="1617" class="Symbol">:</a> <a id="1619" href="ClosureSystems.Basic.html#1176" class="Primitive">Type</a> <a id="1624" href="ClosureSystems.Basic.html#1600" class="Bound">χ</a><a id="1625" class="Symbol">}</a> <a id="1627" class="Keyword">where</a>

 <a id="1635" href="ClosureSystems.Basic.html#1635" class="Function">IntersectClosed</a> <a id="1651" class="Symbol">:</a> <a id="1653" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1658" class="Symbol">(</a><a id="1659" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1664" href="ClosureSystems.Basic.html#1615" class="Bound">X</a> <a id="1666" href="ClosureSystems.Basic.html#1602" class="Bound">ℓ</a><a id="1667" class="Symbol">)</a> <a id="1669" href="ClosureSystems.Basic.html#1604" class="Bound">ρ</a> <a id="1671" class="Symbol">→</a> <a id="1673" href="ClosureSystems.Basic.html#1176" class="Primitive">Type</a> <a id="1678" class="Symbol">_</a>
 <a id="1681" href="ClosureSystems.Basic.html#1635" class="Function">IntersectClosed</a> <a id="1697" href="ClosureSystems.Basic.html#1697" class="Bound">C</a> <a id="1699" class="Symbol">=</a> <a id="1701" class="Symbol">∀</a> <a id="1703" class="Symbol">{</a><a id="1704" href="ClosureSystems.Basic.html#1704" class="Bound">I</a> <a id="1706" class="Symbol">:</a> <a id="1708" href="ClosureSystems.Basic.html#1176" class="Primitive">Type</a> <a id="1713" href="ClosureSystems.Basic.html#1602" class="Bound">ℓ</a><a id="1714" class="Symbol">}{</a><a id="1716" href="ClosureSystems.Basic.html#1716" class="Bound">c</a> <a id="1718" class="Symbol">:</a> <a id="1720" href="ClosureSystems.Basic.html#1704" class="Bound">I</a> <a id="1722" class="Symbol">→</a> <a id="1724" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1729" href="ClosureSystems.Basic.html#1615" class="Bound">X</a> <a id="1731" href="ClosureSystems.Basic.html#1602" class="Bound">ℓ</a><a id="1732" class="Symbol">}</a> <a id="1734" class="Symbol">→</a> <a id="1736" class="Symbol">(∀</a> <a id="1739" href="ClosureSystems.Basic.html#1739" class="Bound">i</a> <a id="1741" class="Symbol">→</a> <a id="1743" class="Symbol">(</a><a id="1744" href="ClosureSystems.Basic.html#1716" class="Bound">c</a> <a id="1746" href="ClosureSystems.Basic.html#1739" class="Bound">i</a><a id="1747" class="Symbol">)</a> <a id="1749" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1751" href="ClosureSystems.Basic.html#1697" class="Bound">C</a><a id="1752" class="Symbol">)</a> <a id="1754" class="Symbol">→</a> <a id="1756" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1758" href="ClosureSystems.Basic.html#1704" class="Bound">I</a> <a id="1760" href="ClosureSystems.Basic.html#1716" class="Bound">c</a> <a id="1762" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1764" href="ClosureSystems.Basic.html#1697" class="Bound">C</a>

 <a id="1768" href="ClosureSystems.Basic.html#1768" class="Function">ClosureSystem</a> <a id="1782" class="Symbol">:</a> <a id="1784" href="ClosureSystems.Basic.html#1176" class="Primitive">Type</a> <a id="1789" class="Symbol">_</a>
 <a id="1792" href="ClosureSystems.Basic.html#1768" class="Function">ClosureSystem</a> <a id="1806" class="Symbol">=</a> <a id="1808" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1811" href="ClosureSystems.Basic.html#1811" class="Bound">C</a> <a id="1813" href="Data.Product.html#916" class="Function">∈</a> <a id="1815" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1820" class="Symbol">(</a><a id="1821" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1826" href="ClosureSystems.Basic.html#1615" class="Bound">X</a> <a id="1828" href="ClosureSystems.Basic.html#1602" class="Bound">ℓ</a><a id="1829" class="Symbol">)</a> <a id="1831" href="ClosureSystems.Basic.html#1604" class="Bound">ρ</a> <a id="1833" href="Data.Product.html#916" class="Function">]</a> <a id="1835" href="ClosureSystems.Basic.html#1635" class="Function">IntersectClosed</a> <a id="1851" href="ClosureSystems.Basic.html#1811" class="Bound">C</a>

</pre>


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2230" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2290" class="Keyword">record</a> <a id="ClOp"></a><a id="2297" href="ClosureSystems.Basic.html#2297" class="Record">ClOp</a> <a id="2302" class="Symbol">{</a><a id="2303" href="ClosureSystems.Basic.html#2303" class="Bound">ℓ</a> <a id="2305" href="ClosureSystems.Basic.html#2305" class="Bound">ℓ₁</a> <a id="2308" href="ClosureSystems.Basic.html#2308" class="Bound">ℓ₂</a> <a id="2311" class="Symbol">:</a> <a id="2313" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2318" class="Symbol">}(</a><a id="2320" href="ClosureSystems.Basic.html#2320" class="Bound">𝑨</a> <a id="2322" class="Symbol">:</a> <a id="2324" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2330" href="ClosureSystems.Basic.html#2303" class="Bound">ℓ</a> <a id="2332" href="ClosureSystems.Basic.html#2305" class="Bound">ℓ₁</a> <a id="2335" href="ClosureSystems.Basic.html#2308" class="Bound">ℓ₂</a><a id="2337" class="Symbol">)</a> <a id="2339" class="Symbol">:</a> <a id="2341" href="ClosureSystems.Basic.html#1176" class="Primitive">Type</a>  <a id="2347" class="Symbol">(</a><a id="2348" href="ClosureSystems.Basic.html#2303" class="Bound">ℓ</a> <a id="2350" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2352" href="ClosureSystems.Basic.html#2308" class="Bound">ℓ₂</a> <a id="2355" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2357" href="ClosureSystems.Basic.html#2305" class="Bound">ℓ₁</a><a id="2359" class="Symbol">)</a> <a id="2361" class="Keyword">where</a>

 <a id="2369" class="Keyword">open</a> <a id="2374" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2380" href="ClosureSystems.Basic.html#2320" class="Bound">𝑨</a>
 <a id="2383" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2394" href="ClosureSystems.Basic.html#2394" class="Function">A</a> <a id="2396" class="Symbol">=</a> <a id="2398" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2408" class="Keyword">open</a> <a id="2413" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2433" class="Symbol">(</a><a id="2434" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2437" class="Symbol">)</a>

 <a id="2441" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2449" href="ClosureSystems.Basic.html#2449" class="Field">C</a> <a id="2451" class="Symbol">:</a> <a id="2453" href="ClosureSystems.Basic.html#2394" class="Function">A</a> <a id="2455" class="Symbol">→</a> <a id="2457" href="ClosureSystems.Basic.html#2394" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2461" href="ClosureSystems.Basic.html#2461" class="Field">isExtensive</a>       <a id="2479" class="Symbol">:</a> <a id="2481" href="ClosureSystems.Definitions.html#581" class="Function">Extensive</a> <a id="2491" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2495" href="ClosureSystems.Basic.html#2449" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2499" href="ClosureSystems.Basic.html#2499" class="Field">isOrderPreserving</a> <a id="2517" class="Symbol">:</a> <a id="2519" href="ClosureSystems.Basic.html#2449" class="Field">C</a> <a id="2521" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2531" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2535" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2537" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2543" href="ClosureSystems.Basic.html#2543" class="Field">isIdempotent</a>      <a id="2561" class="Symbol">:</a> <a id="2563" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2577" href="ClosureSystems.Basic.html#2449" class="Field">C</a>

</pre>


--------------------------------------

<br>
<br>

[← ClosureSystems.Definitions](ClosureSystems.Definitions.html)
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
