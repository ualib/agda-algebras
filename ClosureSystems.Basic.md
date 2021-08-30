---
layout: default
title : "ClosureSystems.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-08"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

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

<a id="1076" class="Symbol">{-#</a> <a id="1080" class="Keyword">OPTIONS</a> <a id="1088" class="Pragma">--without-K</a> <a id="1100" class="Pragma">--exact-split</a> <a id="1114" class="Pragma">--safe</a> <a id="1121" class="Symbol">#-}</a>

<a id="1126" class="Keyword">module</a> <a id="1133" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1154" class="Keyword">where</a>

<a id="1161" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1253" class="Keyword">open</a> <a id="1258" class="Keyword">import</a> <a id="1265" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1290" class="Keyword">using</a> <a id="1296" class="Symbol">(</a> <a id="1298" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1302" class="Symbol">;</a> <a id="1304" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1309" class="Symbol">)</a> <a id="1311" class="Keyword">renaming</a> <a id="1320" class="Symbol">(</a> <a id="1322" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1326" class="Symbol">to</a> <a id="1329" class="Primitive">Type</a> <a id="1334" class="Symbol">)</a>
<a id="1336" class="Keyword">import</a> <a id="1343" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1363" class="Keyword">open</a> <a id="1368" class="Keyword">import</a> <a id="1375" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1400" class="Keyword">using</a> <a id="1406" class="Symbol">(</a> <a id="1408" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1417" class="Symbol">)</a>
<a id="1419" class="Keyword">open</a> <a id="1424" class="Keyword">import</a> <a id="1431" href="Level.html" class="Module">Level</a>                    <a id="1456" class="Keyword">using</a> <a id="1462" class="Symbol">(</a> <a id="1464" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1470" class="Symbol">;</a> <a id="1472" href="Level.html#400" class="Record">Lift</a> <a id="1477" class="Symbol">)</a> <a id="1479" class="Keyword">renaming</a> <a id="1488" class="Symbol">(</a> <a id="1490" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1495" class="Symbol">to</a> <a id="1498" class="Primitive">ℓ₀</a> <a id="1501" class="Symbol">)</a>
<a id="1503" class="Keyword">open</a> <a id="1508" class="Keyword">import</a> <a id="1515" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1540" class="Keyword">using</a> <a id="1546" class="Symbol">(</a> <a id="1548" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1554" class="Symbol">)</a>
<a id="1556" class="Keyword">open</a> <a id="1561" class="Keyword">import</a> <a id="1568" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1593" class="Keyword">using</a> <a id="1599" class="Symbol">(</a> <a id="1601" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1605" class="Symbol">;</a> <a id="1607" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1621" class="Symbol">)</a>
<a id="1623" class="Keyword">open</a> <a id="1628" class="Keyword">import</a> <a id="1635" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1660" class="Keyword">using</a> <a id="1666" class="Symbol">(</a> <a id="1668" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1673" class="Symbol">;</a> <a id="1675" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1679" class="Symbol">;</a> <a id="1681" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1683" class="Symbol">)</a>

<a id="1686" class="Keyword">private</a> <a id="1694" class="Keyword">variable</a>
 <a id="1704" href="ClosureSystems.Basic.html#1704" class="Generalizable">α</a> <a id="1706" href="ClosureSystems.Basic.html#1706" class="Generalizable">ρ</a> <a id="1708" class="Symbol">:</a> <a id="1710" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1717" href="ClosureSystems.Basic.html#1717" class="Generalizable">a</a> <a id="1719" class="Symbol">:</a> <a id="1721" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="1726" href="ClosureSystems.Basic.html#1704" class="Generalizable">α</a>

<a id="Extensive"></a><a id="1729" href="ClosureSystems.Basic.html#1729" class="Function">Extensive</a> <a id="1739" class="Symbol">:</a> <a id="1741" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1745" href="ClosureSystems.Basic.html#1717" class="Generalizable">a</a> <a id="1747" href="ClosureSystems.Basic.html#1706" class="Generalizable">ρ</a> <a id="1749" class="Symbol">→</a> <a id="1751" class="Symbol">(</a><a id="1752" href="ClosureSystems.Basic.html#1717" class="Generalizable">a</a> <a id="1754" class="Symbol">→</a> <a id="1756" href="ClosureSystems.Basic.html#1717" class="Generalizable">a</a><a id="1757" class="Symbol">)</a> <a id="1759" class="Symbol">→</a> <a id="1761" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="1766" class="Symbol">_</a>
<a id="1768" href="ClosureSystems.Basic.html#1729" class="Function">Extensive</a> <a id="1778" href="ClosureSystems.Basic.html#1778" class="Bound Operator">_≤_</a> <a id="1782" href="ClosureSystems.Basic.html#1782" class="Bound">C</a> <a id="1784" class="Symbol">=</a> <a id="1786" class="Symbol">∀{</a><a id="1788" href="ClosureSystems.Basic.html#1788" class="Bound">x</a><a id="1789" class="Symbol">}</a> <a id="1791" class="Symbol">→</a> <a id="1793" href="ClosureSystems.Basic.html#1788" class="Bound">x</a> <a id="1795" href="ClosureSystems.Basic.html#1778" class="Bound Operator">≤</a> <a id="1797" href="ClosureSystems.Basic.html#1782" class="Bound">C</a> <a id="1799" href="ClosureSystems.Basic.html#1788" class="Bound">x</a>

<a id="1802" class="Comment">-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)</a>

<a id="1896" class="Keyword">module</a> <a id="1903" href="ClosureSystems.Basic.html#1903" class="Module">_</a> <a id="1905" class="Symbol">{</a><a id="1906" href="ClosureSystems.Basic.html#1906" class="Bound">χ</a> <a id="1908" href="ClosureSystems.Basic.html#1908" class="Bound">ρ</a> <a id="1910" href="ClosureSystems.Basic.html#1910" class="Bound">ℓ</a> <a id="1912" class="Symbol">:</a> <a id="1914" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1919" class="Symbol">}{</a><a id="1921" href="ClosureSystems.Basic.html#1921" class="Bound">X</a> <a id="1923" class="Symbol">:</a> <a id="1925" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="1930" href="ClosureSystems.Basic.html#1906" class="Bound">χ</a><a id="1931" class="Symbol">}</a> <a id="1933" class="Keyword">where</a>

 <a id="1941" href="ClosureSystems.Basic.html#1941" class="Function">IntersectClosed</a> <a id="1957" class="Symbol">:</a> <a id="1959" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1964" class="Symbol">(</a><a id="1965" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1970" href="ClosureSystems.Basic.html#1921" class="Bound">X</a> <a id="1972" href="ClosureSystems.Basic.html#1910" class="Bound">ℓ</a><a id="1973" class="Symbol">)</a> <a id="1975" href="ClosureSystems.Basic.html#1908" class="Bound">ρ</a> <a id="1977" class="Symbol">→</a> <a id="1979" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="1984" class="Symbol">_</a>
 <a id="1987" href="ClosureSystems.Basic.html#1941" class="Function">IntersectClosed</a> <a id="2003" href="ClosureSystems.Basic.html#2003" class="Bound">C</a> <a id="2005" class="Symbol">=</a> <a id="2007" class="Symbol">∀</a> <a id="2009" class="Symbol">{</a><a id="2010" href="ClosureSystems.Basic.html#2010" class="Bound">I</a> <a id="2012" class="Symbol">:</a> <a id="2014" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="2019" href="ClosureSystems.Basic.html#1910" class="Bound">ℓ</a><a id="2020" class="Symbol">}{</a><a id="2022" href="ClosureSystems.Basic.html#2022" class="Bound">c</a> <a id="2024" class="Symbol">:</a> <a id="2026" href="ClosureSystems.Basic.html#2010" class="Bound">I</a> <a id="2028" class="Symbol">→</a> <a id="2030" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2035" href="ClosureSystems.Basic.html#1921" class="Bound">X</a> <a id="2037" href="ClosureSystems.Basic.html#1910" class="Bound">ℓ</a><a id="2038" class="Symbol">}</a> <a id="2040" class="Symbol">→</a> <a id="2042" class="Symbol">(∀</a> <a id="2045" href="ClosureSystems.Basic.html#2045" class="Bound">i</a> <a id="2047" class="Symbol">→</a> <a id="2049" class="Symbol">(</a><a id="2050" href="ClosureSystems.Basic.html#2022" class="Bound">c</a> <a id="2052" href="ClosureSystems.Basic.html#2045" class="Bound">i</a><a id="2053" class="Symbol">)</a> <a id="2055" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2057" href="ClosureSystems.Basic.html#2003" class="Bound">C</a><a id="2058" class="Symbol">)</a> <a id="2060" class="Symbol">→</a> <a id="2062" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="2064" href="ClosureSystems.Basic.html#2010" class="Bound">I</a> <a id="2066" href="ClosureSystems.Basic.html#2022" class="Bound">c</a> <a id="2068" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2070" href="ClosureSystems.Basic.html#2003" class="Bound">C</a>

 <a id="2074" href="ClosureSystems.Basic.html#2074" class="Function">ClosureSystem</a> <a id="2088" class="Symbol">:</a> <a id="2090" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a> <a id="2095" class="Symbol">_</a>
 <a id="2098" href="ClosureSystems.Basic.html#2074" class="Function">ClosureSystem</a> <a id="2112" class="Symbol">=</a> <a id="2114" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2117" href="ClosureSystems.Basic.html#2117" class="Bound">C</a> <a id="2119" href="Data.Product.html#916" class="Function">∈</a> <a id="2121" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2126" class="Symbol">(</a><a id="2127" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2132" href="ClosureSystems.Basic.html#1921" class="Bound">X</a> <a id="2134" href="ClosureSystems.Basic.html#1910" class="Bound">ℓ</a><a id="2135" class="Symbol">)</a> <a id="2137" href="ClosureSystems.Basic.html#1908" class="Bound">ρ</a> <a id="2139" href="Data.Product.html#916" class="Function">]</a> <a id="2141" href="ClosureSystems.Basic.html#1941" class="Function">IntersectClosed</a> <a id="2157" href="ClosureSystems.Basic.html#2117" class="Bound">C</a>

</pre>


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2536" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2596" class="Keyword">record</a> <a id="ClOp"></a><a id="2603" href="ClosureSystems.Basic.html#2603" class="Record">ClOp</a> <a id="2608" class="Symbol">{</a><a id="2609" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ</a> <a id="2611" href="ClosureSystems.Basic.html#2611" class="Bound">ℓ₁</a> <a id="2614" href="ClosureSystems.Basic.html#2614" class="Bound">ℓ₂</a> <a id="2617" class="Symbol">:</a> <a id="2619" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2624" class="Symbol">}(</a><a id="2626" href="ClosureSystems.Basic.html#2626" class="Bound">𝑨</a> <a id="2628" class="Symbol">:</a> <a id="2630" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2636" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ</a> <a id="2638" href="ClosureSystems.Basic.html#2611" class="Bound">ℓ₁</a> <a id="2641" href="ClosureSystems.Basic.html#2614" class="Bound">ℓ₂</a><a id="2643" class="Symbol">)</a> <a id="2645" class="Symbol">:</a> <a id="2647" href="ClosureSystems.Basic.html#1329" class="Primitive">Type</a>  <a id="2653" class="Symbol">(</a><a id="2654" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ</a> <a id="2656" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2658" href="ClosureSystems.Basic.html#2614" class="Bound">ℓ₂</a> <a id="2661" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2663" href="ClosureSystems.Basic.html#2611" class="Bound">ℓ₁</a><a id="2665" class="Symbol">)</a> <a id="2667" class="Keyword">where</a>

 <a id="2675" class="Keyword">open</a> <a id="2680" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2686" href="ClosureSystems.Basic.html#2626" class="Bound">𝑨</a>
 <a id="2689" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2700" href="ClosureSystems.Basic.html#2700" class="Function">A</a> <a id="2702" class="Symbol">=</a> <a id="2704" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2714" class="Keyword">open</a> <a id="2719" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2739" class="Symbol">(</a><a id="2740" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2743" class="Symbol">)</a>

 <a id="2747" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2755" href="ClosureSystems.Basic.html#2755" class="Field">C</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="ClosureSystems.Basic.html#2700" class="Function">A</a> <a id="2761" class="Symbol">→</a> <a id="2763" href="ClosureSystems.Basic.html#2700" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2767" href="ClosureSystems.Basic.html#2767" class="Field">isExtensive</a>       <a id="2785" class="Symbol">:</a> <a id="2787" href="ClosureSystems.Basic.html#1729" class="Function">Extensive</a> <a id="2797" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2801" href="ClosureSystems.Basic.html#2755" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2805" href="ClosureSystems.Basic.html#2805" class="Field">isOrderPreserving</a> <a id="2823" class="Symbol">:</a> <a id="2825" href="ClosureSystems.Basic.html#2755" class="Field">C</a> <a id="2827" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2837" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2841" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2843" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2849" href="ClosureSystems.Basic.html#2849" class="Field">isIdempotent</a>      <a id="2867" class="Symbol">:</a> <a id="2869" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2883" href="ClosureSystems.Basic.html#2755" class="Field">C</a>

</pre>

--------------------------------------

<span style="float:left;">[↑ ClosureSystems.Definitions](ClosureSystems.html)</span>
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}
