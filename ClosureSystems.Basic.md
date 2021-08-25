---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [ClosureSystems.Basic][] module of the [Agda Universal Algebra Library][].

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

<a id="1075" class="Symbol">{-#</a> <a id="1079" class="Keyword">OPTIONS</a> <a id="1087" class="Pragma">--without-K</a> <a id="1099" class="Pragma">--exact-split</a> <a id="1113" class="Pragma">--safe</a> <a id="1120" class="Symbol">#-}</a>

<a id="1125" class="Keyword">module</a> <a id="1132" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1153" class="Keyword">where</a>

<a id="1160" class="Keyword">open</a> <a id="1165" class="Keyword">import</a> <a id="1172" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1197" class="Keyword">using</a> <a id="1203" class="Symbol">(</a> <a id="1205" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1209" class="Symbol">;</a> <a id="1211" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1216" class="Symbol">)</a> <a id="1218" class="Keyword">renaming</a> <a id="1227" class="Symbol">(</a> <a id="1229" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1233" class="Symbol">to</a> <a id="1236" class="Primitive">Type</a> <a id="1241" class="Symbol">)</a>
<a id="1243" class="Keyword">import</a> <a id="1250" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1270" class="Keyword">open</a> <a id="1275" class="Keyword">import</a> <a id="1282" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1307" class="Keyword">using</a> <a id="1313" class="Symbol">(</a> <a id="1315" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1324" class="Symbol">)</a>
<a id="1326" class="Keyword">open</a> <a id="1331" class="Keyword">import</a> <a id="1338" href="Level.html" class="Module">Level</a>                    <a id="1363" class="Keyword">using</a> <a id="1369" class="Symbol">(</a> <a id="1371" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1377" class="Symbol">;</a> <a id="1379" href="Level.html#400" class="Record">Lift</a> <a id="1384" class="Symbol">)</a> <a id="1386" class="Keyword">renaming</a> <a id="1395" class="Symbol">(</a> <a id="1397" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1402" class="Symbol">to</a> <a id="1405" class="Primitive">ℓ₀</a> <a id="1408" class="Symbol">)</a>
<a id="1410" class="Keyword">open</a> <a id="1415" class="Keyword">import</a> <a id="1422" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1447" class="Keyword">using</a> <a id="1453" class="Symbol">(</a> <a id="1455" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1461" class="Symbol">)</a>
<a id="1463" class="Keyword">open</a> <a id="1468" class="Keyword">import</a> <a id="1475" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1500" class="Keyword">using</a> <a id="1506" class="Symbol">(</a> <a id="1508" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1512" class="Symbol">;</a> <a id="1514" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1528" class="Symbol">)</a>
<a id="1530" class="Keyword">open</a> <a id="1535" class="Keyword">import</a> <a id="1542" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1567" class="Keyword">using</a> <a id="1573" class="Symbol">(</a> <a id="1575" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1580" class="Symbol">;</a> <a id="1582" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1586" class="Symbol">;</a> <a id="1588" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1590" class="Symbol">)</a>


<a id="1594" class="Keyword">private</a> <a id="1602" class="Keyword">variable</a>
 <a id="1612" href="ClosureSystems.Basic.html#1612" class="Generalizable">α</a> <a id="1614" href="ClosureSystems.Basic.html#1614" class="Generalizable">ρ</a> <a id="1616" class="Symbol">:</a> <a id="1618" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1625" href="ClosureSystems.Basic.html#1625" class="Generalizable">a</a> <a id="1627" class="Symbol">:</a> <a id="1629" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="1634" href="ClosureSystems.Basic.html#1612" class="Generalizable">α</a>

<a id="Extensive"></a><a id="1637" href="ClosureSystems.Basic.html#1637" class="Function">Extensive</a> <a id="1647" class="Symbol">:</a> <a id="1649" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1653" href="ClosureSystems.Basic.html#1625" class="Generalizable">a</a> <a id="1655" href="ClosureSystems.Basic.html#1614" class="Generalizable">ρ</a> <a id="1657" class="Symbol">→</a> <a id="1659" class="Symbol">(</a><a id="1660" href="ClosureSystems.Basic.html#1625" class="Generalizable">a</a> <a id="1662" class="Symbol">→</a> <a id="1664" href="ClosureSystems.Basic.html#1625" class="Generalizable">a</a><a id="1665" class="Symbol">)</a> <a id="1667" class="Symbol">→</a> <a id="1669" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="1674" class="Symbol">_</a>
<a id="1676" href="ClosureSystems.Basic.html#1637" class="Function">Extensive</a> <a id="1686" href="ClosureSystems.Basic.html#1686" class="Bound Operator">_≤_</a> <a id="1690" href="ClosureSystems.Basic.html#1690" class="Bound">C</a> <a id="1692" class="Symbol">=</a> <a id="1694" class="Symbol">∀{</a><a id="1696" href="ClosureSystems.Basic.html#1696" class="Bound">x</a><a id="1697" class="Symbol">}</a> <a id="1699" class="Symbol">→</a> <a id="1701" href="ClosureSystems.Basic.html#1696" class="Bound">x</a> <a id="1703" href="ClosureSystems.Basic.html#1686" class="Bound Operator">≤</a> <a id="1705" href="ClosureSystems.Basic.html#1690" class="Bound">C</a> <a id="1707" href="ClosureSystems.Basic.html#1696" class="Bound">x</a>

<a id="1710" class="Comment">-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)</a>

<a id="1804" class="Keyword">module</a> <a id="1811" href="ClosureSystems.Basic.html#1811" class="Module">_</a> <a id="1813" class="Symbol">{</a><a id="1814" href="ClosureSystems.Basic.html#1814" class="Bound">χ</a> <a id="1816" href="ClosureSystems.Basic.html#1816" class="Bound">ρ</a> <a id="1818" href="ClosureSystems.Basic.html#1818" class="Bound">ℓ</a> <a id="1820" class="Symbol">:</a> <a id="1822" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1827" class="Symbol">}{</a><a id="1829" href="ClosureSystems.Basic.html#1829" class="Bound">X</a> <a id="1831" class="Symbol">:</a> <a id="1833" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="1838" href="ClosureSystems.Basic.html#1814" class="Bound">χ</a><a id="1839" class="Symbol">}</a> <a id="1841" class="Keyword">where</a>

 <a id="1849" href="ClosureSystems.Basic.html#1849" class="Function">IntersectClosed</a> <a id="1865" class="Symbol">:</a> <a id="1867" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1872" class="Symbol">(</a><a id="1873" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1878" href="ClosureSystems.Basic.html#1829" class="Bound">X</a> <a id="1880" href="ClosureSystems.Basic.html#1818" class="Bound">ℓ</a><a id="1881" class="Symbol">)</a> <a id="1883" href="ClosureSystems.Basic.html#1816" class="Bound">ρ</a> <a id="1885" class="Symbol">→</a> <a id="1887" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="1892" class="Symbol">_</a>
 <a id="1895" href="ClosureSystems.Basic.html#1849" class="Function">IntersectClosed</a> <a id="1911" href="ClosureSystems.Basic.html#1911" class="Bound">C</a> <a id="1913" class="Symbol">=</a> <a id="1915" class="Symbol">∀</a> <a id="1917" class="Symbol">{</a><a id="1918" href="ClosureSystems.Basic.html#1918" class="Bound">I</a> <a id="1920" class="Symbol">:</a> <a id="1922" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="1927" href="ClosureSystems.Basic.html#1818" class="Bound">ℓ</a><a id="1928" class="Symbol">}{</a><a id="1930" href="ClosureSystems.Basic.html#1930" class="Bound">c</a> <a id="1932" class="Symbol">:</a> <a id="1934" href="ClosureSystems.Basic.html#1918" class="Bound">I</a> <a id="1936" class="Symbol">→</a> <a id="1938" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1943" href="ClosureSystems.Basic.html#1829" class="Bound">X</a> <a id="1945" href="ClosureSystems.Basic.html#1818" class="Bound">ℓ</a><a id="1946" class="Symbol">}</a> <a id="1948" class="Symbol">→</a> <a id="1950" class="Symbol">(∀</a> <a id="1953" href="ClosureSystems.Basic.html#1953" class="Bound">i</a> <a id="1955" class="Symbol">→</a> <a id="1957" class="Symbol">(</a><a id="1958" href="ClosureSystems.Basic.html#1930" class="Bound">c</a> <a id="1960" href="ClosureSystems.Basic.html#1953" class="Bound">i</a><a id="1961" class="Symbol">)</a> <a id="1963" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1965" href="ClosureSystems.Basic.html#1911" class="Bound">C</a><a id="1966" class="Symbol">)</a> <a id="1968" class="Symbol">→</a> <a id="1970" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1972" href="ClosureSystems.Basic.html#1918" class="Bound">I</a> <a id="1974" href="ClosureSystems.Basic.html#1930" class="Bound">c</a> <a id="1976" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1978" href="ClosureSystems.Basic.html#1911" class="Bound">C</a>

 <a id="1982" href="ClosureSystems.Basic.html#1982" class="Function">ClosureSystem</a> <a id="1996" class="Symbol">:</a> <a id="1998" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a> <a id="2003" class="Symbol">_</a>
 <a id="2006" href="ClosureSystems.Basic.html#1982" class="Function">ClosureSystem</a> <a id="2020" class="Symbol">=</a> <a id="2022" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2025" href="ClosureSystems.Basic.html#2025" class="Bound">C</a> <a id="2027" href="Data.Product.html#916" class="Function">∈</a> <a id="2029" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2034" class="Symbol">(</a><a id="2035" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2040" href="ClosureSystems.Basic.html#1829" class="Bound">X</a> <a id="2042" href="ClosureSystems.Basic.html#1818" class="Bound">ℓ</a><a id="2043" class="Symbol">)</a> <a id="2045" href="ClosureSystems.Basic.html#1816" class="Bound">ρ</a> <a id="2047" href="Data.Product.html#916" class="Function">]</a> <a id="2049" href="ClosureSystems.Basic.html#1849" class="Function">IntersectClosed</a> <a id="2065" href="ClosureSystems.Basic.html#2025" class="Bound">C</a>

</pre>


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2444" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2504" class="Keyword">record</a> <a id="ClOp"></a><a id="2511" href="ClosureSystems.Basic.html#2511" class="Record">ClOp</a> <a id="2516" class="Symbol">{</a><a id="2517" href="ClosureSystems.Basic.html#2517" class="Bound">ℓ</a> <a id="2519" href="ClosureSystems.Basic.html#2519" class="Bound">ℓ₁</a> <a id="2522" href="ClosureSystems.Basic.html#2522" class="Bound">ℓ₂</a> <a id="2525" class="Symbol">:</a> <a id="2527" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2532" class="Symbol">}(</a><a id="2534" href="ClosureSystems.Basic.html#2534" class="Bound">𝑨</a> <a id="2536" class="Symbol">:</a> <a id="2538" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2544" href="ClosureSystems.Basic.html#2517" class="Bound">ℓ</a> <a id="2546" href="ClosureSystems.Basic.html#2519" class="Bound">ℓ₁</a> <a id="2549" href="ClosureSystems.Basic.html#2522" class="Bound">ℓ₂</a><a id="2551" class="Symbol">)</a> <a id="2553" class="Symbol">:</a> <a id="2555" href="ClosureSystems.Basic.html#1236" class="Primitive">Type</a>  <a id="2561" class="Symbol">(</a><a id="2562" href="ClosureSystems.Basic.html#2517" class="Bound">ℓ</a> <a id="2564" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2566" href="ClosureSystems.Basic.html#2522" class="Bound">ℓ₂</a> <a id="2569" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2571" href="ClosureSystems.Basic.html#2519" class="Bound">ℓ₁</a><a id="2573" class="Symbol">)</a> <a id="2575" class="Keyword">where</a>

 <a id="2583" class="Keyword">open</a> <a id="2588" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2594" href="ClosureSystems.Basic.html#2534" class="Bound">𝑨</a>
 <a id="2597" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2608" href="ClosureSystems.Basic.html#2608" class="Function">A</a> <a id="2610" class="Symbol">=</a> <a id="2612" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2622" class="Keyword">open</a> <a id="2627" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2647" class="Symbol">(</a><a id="2648" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2651" class="Symbol">)</a>

 <a id="2655" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2663" href="ClosureSystems.Basic.html#2663" class="Field">C</a> <a id="2665" class="Symbol">:</a> <a id="2667" href="ClosureSystems.Basic.html#2608" class="Function">A</a> <a id="2669" class="Symbol">→</a> <a id="2671" href="ClosureSystems.Basic.html#2608" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2675" href="ClosureSystems.Basic.html#2675" class="Field">isExtensive</a>       <a id="2693" class="Symbol">:</a> <a id="2695" href="ClosureSystems.Basic.html#1637" class="Function">Extensive</a> <a id="2705" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2709" href="ClosureSystems.Basic.html#2663" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2713" href="ClosureSystems.Basic.html#2713" class="Field">isOrderPreserving</a> <a id="2731" class="Symbol">:</a> <a id="2733" href="ClosureSystems.Basic.html#2663" class="Field">C</a> <a id="2735" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2745" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2749" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2751" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2757" href="ClosureSystems.Basic.html#2757" class="Field">isIdempotent</a>      <a id="2775" class="Symbol">:</a> <a id="2777" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2791" href="ClosureSystems.Basic.html#2663" class="Field">C</a>

</pre>


--------------------------------------

<br>

[↑ ClosureSystems.Definitions](ClosureSystems.html)
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
