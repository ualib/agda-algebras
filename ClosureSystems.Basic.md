---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### Closure Systems and Operators

#### Closure Systems

A *closure system* on a set `X` is a collection `𝒞` of subsets of `X` that is closed
under arbitrary intersection (including the empty intersection, so `⋂ ∅ = X ∈ 𝒞`.

Thus a closure system is a complete meet semilattice with respect to the subset
inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the closed
sets of a closure system form a complete lattice.
(See J.B. Nation's [Lattice Theory Notes](http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf).)
\cite[Theorem 2.5]{Nation-notes}

Some examples of closure systems are the following:

* order ideals of an ordered set
* subalgebras of an algebra
* equivalence relations on a set
* congruence relations of an algebra


<pre class="Agda">

<a id="961" class="Symbol">{-#</a> <a id="965" class="Keyword">OPTIONS</a> <a id="973" class="Pragma">--without-K</a> <a id="985" class="Pragma">--exact-split</a> <a id="999" class="Pragma">--safe</a> <a id="1006" class="Symbol">#-}</a>

<a id="1011" class="Keyword">module</a> <a id="1018" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1039" class="Keyword">where</a>

<a id="1046" class="Keyword">open</a> <a id="1051" class="Keyword">import</a> <a id="1058" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1083" class="Keyword">using</a> <a id="1089" class="Symbol">(</a> <a id="1091" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1095" class="Symbol">;</a> <a id="1097" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1102" class="Symbol">)</a>     <a id="1108" class="Keyword">renaming</a> <a id="1117" class="Symbol">(</a> <a id="1119" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1123" class="Symbol">to</a> <a id="1126" class="Primitive">Type</a> <a id="1131" class="Symbol">)</a>
<a id="1133" class="Keyword">import</a> <a id="1140" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1160" class="Keyword">open</a> <a id="1165" class="Keyword">import</a> <a id="1172" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1197" class="Keyword">using</a> <a id="1203" class="Symbol">(</a> <a id="1205" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1214" class="Symbol">)</a>
<a id="1216" class="Keyword">open</a> <a id="1221" class="Keyword">import</a> <a id="1228" href="Level.html" class="Module">Level</a>                    <a id="1253" class="Keyword">using</a> <a id="1259" class="Symbol">(</a> <a id="1261" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1267" class="Symbol">;</a> <a id="1269" href="Level.html#400" class="Record">Lift</a> <a id="1274" class="Symbol">)</a>   <a id="1278" class="Keyword">renaming</a> <a id="1287" class="Symbol">(</a> <a id="1289" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1294" class="Symbol">to</a> <a id="1297" class="Primitive">ℓ₀</a> <a id="1300" class="Symbol">)</a>
<a id="1302" class="Keyword">open</a> <a id="1307" class="Keyword">import</a> <a id="1314" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1339" class="Keyword">using</a> <a id="1345" class="Symbol">(</a> <a id="1347" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1353" class="Symbol">)</a>
<a id="1355" class="Keyword">open</a> <a id="1360" class="Keyword">import</a> <a id="1367" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1392" class="Keyword">using</a> <a id="1398" class="Symbol">(</a> <a id="1400" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1414" class="Symbol">)</a>
<a id="1416" class="Keyword">open</a> <a id="1421" class="Keyword">import</a> <a id="1428" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1453" class="Keyword">using</a> <a id="1459" class="Symbol">(</a> <a id="1461" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1466" class="Symbol">;</a> <a id="1468" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1472" class="Symbol">;</a> <a id="1474" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1476" class="Symbol">)</a>

<a id="1479" class="Keyword">open</a> <a id="1484" class="Keyword">import</a> <a id="1491" href="ClosureSystems.Definitions.html" class="Module">ClosureSystems.Definitions</a> <a id="1518" class="Keyword">using</a> <a id="1524" class="Symbol">(</a> <a id="1526" href="ClosureSystems.Definitions.html#523" class="Function">Extensive</a> <a id="1536" class="Symbol">)</a>


<a id="1540" class="Keyword">module</a> <a id="1547" href="ClosureSystems.Basic.html#1547" class="Module">_</a> <a id="1549" class="Symbol">{</a><a id="1550" href="ClosureSystems.Basic.html#1550" class="Bound">χ</a> <a id="1552" href="ClosureSystems.Basic.html#1552" class="Bound">ℓ</a> <a id="1554" href="ClosureSystems.Basic.html#1554" class="Bound">ρ</a> <a id="1556" class="Symbol">:</a> <a id="1558" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1563" class="Symbol">}{</a><a id="1565" href="ClosureSystems.Basic.html#1565" class="Bound">X</a> <a id="1567" class="Symbol">:</a> <a id="1569" href="ClosureSystems.Basic.html#1126" class="Primitive">Type</a> <a id="1574" href="ClosureSystems.Basic.html#1550" class="Bound">χ</a><a id="1575" class="Symbol">}</a> <a id="1577" class="Keyword">where</a>

 <a id="1585" href="ClosureSystems.Basic.html#1585" class="Function">IntersectClosed</a> <a id="1601" class="Symbol">:</a> <a id="1603" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1608" class="Symbol">(</a><a id="1609" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1614" href="ClosureSystems.Basic.html#1565" class="Bound">X</a> <a id="1616" href="ClosureSystems.Basic.html#1552" class="Bound">ℓ</a><a id="1617" class="Symbol">)</a> <a id="1619" href="ClosureSystems.Basic.html#1554" class="Bound">ρ</a> <a id="1621" class="Symbol">→</a> <a id="1623" href="ClosureSystems.Basic.html#1126" class="Primitive">Type</a> <a id="1628" class="Symbol">_</a>
 <a id="1631" href="ClosureSystems.Basic.html#1585" class="Function">IntersectClosed</a> <a id="1647" href="ClosureSystems.Basic.html#1647" class="Bound">C</a> <a id="1649" class="Symbol">=</a> <a id="1651" class="Symbol">∀</a> <a id="1653" class="Symbol">{</a><a id="1654" href="ClosureSystems.Basic.html#1654" class="Bound">I</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="ClosureSystems.Basic.html#1126" class="Primitive">Type</a> <a id="1663" href="ClosureSystems.Basic.html#1552" class="Bound">ℓ</a><a id="1664" class="Symbol">}{</a><a id="1666" href="ClosureSystems.Basic.html#1666" class="Bound">c</a> <a id="1668" class="Symbol">:</a> <a id="1670" href="ClosureSystems.Basic.html#1654" class="Bound">I</a> <a id="1672" class="Symbol">→</a> <a id="1674" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1679" href="ClosureSystems.Basic.html#1565" class="Bound">X</a> <a id="1681" href="ClosureSystems.Basic.html#1552" class="Bound">ℓ</a><a id="1682" class="Symbol">}</a> <a id="1684" class="Symbol">→</a> <a id="1686" class="Symbol">(∀</a> <a id="1689" href="ClosureSystems.Basic.html#1689" class="Bound">i</a> <a id="1691" class="Symbol">→</a> <a id="1693" class="Symbol">(</a><a id="1694" href="ClosureSystems.Basic.html#1666" class="Bound">c</a> <a id="1696" href="ClosureSystems.Basic.html#1689" class="Bound">i</a><a id="1697" class="Symbol">)</a> <a id="1699" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1701" href="ClosureSystems.Basic.html#1647" class="Bound">C</a><a id="1702" class="Symbol">)</a> <a id="1704" class="Symbol">→</a> <a id="1706" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1708" href="ClosureSystems.Basic.html#1654" class="Bound">I</a> <a id="1710" href="ClosureSystems.Basic.html#1666" class="Bound">c</a> <a id="1712" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1714" href="ClosureSystems.Basic.html#1647" class="Bound">C</a>

 <a id="1718" href="ClosureSystems.Basic.html#1718" class="Function">ClosureSystem</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="ClosureSystems.Basic.html#1126" class="Primitive">Type</a> <a id="1739" class="Symbol">_</a>
 <a id="1742" href="ClosureSystems.Basic.html#1718" class="Function">ClosureSystem</a> <a id="1756" class="Symbol">=</a> <a id="1758" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1761" href="ClosureSystems.Basic.html#1761" class="Bound">C</a> <a id="1763" href="Data.Product.html#916" class="Function">∈</a> <a id="1765" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1770" class="Symbol">(</a><a id="1771" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1776" href="ClosureSystems.Basic.html#1565" class="Bound">X</a> <a id="1778" href="ClosureSystems.Basic.html#1552" class="Bound">ℓ</a><a id="1779" class="Symbol">)</a> <a id="1781" href="ClosureSystems.Basic.html#1554" class="Bound">ρ</a> <a id="1783" href="Data.Product.html#916" class="Function">]</a> <a id="1785" href="ClosureSystems.Basic.html#1585" class="Function">IntersectClosed</a> <a id="1801" href="ClosureSystems.Basic.html#1761" class="Bound">C</a>

</pre>


#### Closure Operators

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2150" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2210" class="Keyword">record</a> <a id="ClOp"></a><a id="2217" href="ClosureSystems.Basic.html#2217" class="Record">ClOp</a> <a id="2222" class="Symbol">{</a><a id="2223" href="ClosureSystems.Basic.html#2223" class="Bound">ℓ</a> <a id="2225" href="ClosureSystems.Basic.html#2225" class="Bound">ℓ₁</a> <a id="2228" href="ClosureSystems.Basic.html#2228" class="Bound">ℓ₂</a> <a id="2231" class="Symbol">:</a> <a id="2233" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2238" class="Symbol">}(</a><a id="2240" href="ClosureSystems.Basic.html#2240" class="Bound">𝑨</a> <a id="2242" class="Symbol">:</a> <a id="2244" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2250" href="ClosureSystems.Basic.html#2223" class="Bound">ℓ</a> <a id="2252" href="ClosureSystems.Basic.html#2225" class="Bound">ℓ₁</a> <a id="2255" href="ClosureSystems.Basic.html#2228" class="Bound">ℓ₂</a><a id="2257" class="Symbol">)</a> <a id="2259" class="Symbol">:</a> <a id="2261" href="ClosureSystems.Basic.html#1126" class="Primitive">Type</a>  <a id="2267" class="Symbol">(</a><a id="2268" href="ClosureSystems.Basic.html#2223" class="Bound">ℓ</a> <a id="2270" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2272" href="ClosureSystems.Basic.html#2228" class="Bound">ℓ₂</a> <a id="2275" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2277" href="ClosureSystems.Basic.html#2225" class="Bound">ℓ₁</a><a id="2279" class="Symbol">)</a> <a id="2281" class="Keyword">where</a>

 <a id="2289" class="Keyword">open</a> <a id="2294" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2300" href="ClosureSystems.Basic.html#2240" class="Bound">𝑨</a>
 <a id="2303" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2314" href="ClosureSystems.Basic.html#2314" class="Function">A</a> <a id="2316" class="Symbol">=</a> <a id="2318" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2328" class="Keyword">open</a> <a id="2333" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2353" class="Symbol">(</a><a id="2354" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2357" class="Symbol">)</a>

 <a id="2361" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2369" href="ClosureSystems.Basic.html#2369" class="Field">C</a> <a id="2371" class="Symbol">:</a> <a id="2373" href="ClosureSystems.Basic.html#2314" class="Function">A</a> <a id="2375" class="Symbol">→</a> <a id="2377" href="ClosureSystems.Basic.html#2314" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2381" href="ClosureSystems.Basic.html#2381" class="Field">isExtensive</a>       <a id="2399" class="Symbol">:</a> <a id="2401" href="ClosureSystems.Definitions.html#523" class="Function">Extensive</a> <a id="2411" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2415" href="ClosureSystems.Basic.html#2369" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2419" href="ClosureSystems.Basic.html#2419" class="Field">isOrderPreserving</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="ClosureSystems.Basic.html#2369" class="Field">C</a> <a id="2441" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2451" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2455" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2457" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2463" href="ClosureSystems.Basic.html#2463" class="Field">isIdempotent</a>      <a id="2481" class="Symbol">:</a> <a id="2483" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2497" href="ClosureSystems.Basic.html#2369" class="Field">C</a>

</pre>




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
