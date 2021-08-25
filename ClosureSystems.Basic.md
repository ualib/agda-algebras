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

<a id="1074" class="Symbol">{-#</a> <a id="1078" class="Keyword">OPTIONS</a> <a id="1086" class="Pragma">--without-K</a> <a id="1098" class="Pragma">--exact-split</a> <a id="1112" class="Pragma">--safe</a> <a id="1119" class="Symbol">#-}</a>

<a id="1124" class="Keyword">module</a> <a id="1131" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1152" class="Keyword">where</a>

<a id="1159" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1251" class="Keyword">open</a> <a id="1256" class="Keyword">import</a> <a id="1263" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1288" class="Keyword">using</a> <a id="1294" class="Symbol">(</a> <a id="1296" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1300" class="Symbol">;</a> <a id="1302" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1307" class="Symbol">)</a> <a id="1309" class="Keyword">renaming</a> <a id="1318" class="Symbol">(</a> <a id="1320" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1324" class="Symbol">to</a> <a id="1327" class="Primitive">Type</a> <a id="1332" class="Symbol">)</a>
<a id="1334" class="Keyword">import</a> <a id="1341" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1361" class="Keyword">open</a> <a id="1366" class="Keyword">import</a> <a id="1373" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1398" class="Keyword">using</a> <a id="1404" class="Symbol">(</a> <a id="1406" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1415" class="Symbol">)</a>
<a id="1417" class="Keyword">open</a> <a id="1422" class="Keyword">import</a> <a id="1429" href="Level.html" class="Module">Level</a>                    <a id="1454" class="Keyword">using</a> <a id="1460" class="Symbol">(</a> <a id="1462" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1468" class="Symbol">;</a> <a id="1470" href="Level.html#400" class="Record">Lift</a> <a id="1475" class="Symbol">)</a> <a id="1477" class="Keyword">renaming</a> <a id="1486" class="Symbol">(</a> <a id="1488" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1493" class="Symbol">to</a> <a id="1496" class="Primitive">ℓ₀</a> <a id="1499" class="Symbol">)</a>
<a id="1501" class="Keyword">open</a> <a id="1506" class="Keyword">import</a> <a id="1513" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1538" class="Keyword">using</a> <a id="1544" class="Symbol">(</a> <a id="1546" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1552" class="Symbol">)</a>
<a id="1554" class="Keyword">open</a> <a id="1559" class="Keyword">import</a> <a id="1566" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1591" class="Keyword">using</a> <a id="1597" class="Symbol">(</a> <a id="1599" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1603" class="Symbol">;</a> <a id="1605" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1619" class="Symbol">)</a>
<a id="1621" class="Keyword">open</a> <a id="1626" class="Keyword">import</a> <a id="1633" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1658" class="Keyword">using</a> <a id="1664" class="Symbol">(</a> <a id="1666" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1671" class="Symbol">;</a> <a id="1673" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1677" class="Symbol">;</a> <a id="1679" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1681" class="Symbol">)</a>

<a id="1684" class="Keyword">private</a> <a id="1692" class="Keyword">variable</a>
 <a id="1702" href="ClosureSystems.Basic.html#1702" class="Generalizable">α</a> <a id="1704" href="ClosureSystems.Basic.html#1704" class="Generalizable">ρ</a> <a id="1706" class="Symbol">:</a> <a id="1708" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1715" href="ClosureSystems.Basic.html#1715" class="Generalizable">a</a> <a id="1717" class="Symbol">:</a> <a id="1719" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="1724" href="ClosureSystems.Basic.html#1702" class="Generalizable">α</a>

<a id="Extensive"></a><a id="1727" href="ClosureSystems.Basic.html#1727" class="Function">Extensive</a> <a id="1737" class="Symbol">:</a> <a id="1739" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1743" href="ClosureSystems.Basic.html#1715" class="Generalizable">a</a> <a id="1745" href="ClosureSystems.Basic.html#1704" class="Generalizable">ρ</a> <a id="1747" class="Symbol">→</a> <a id="1749" class="Symbol">(</a><a id="1750" href="ClosureSystems.Basic.html#1715" class="Generalizable">a</a> <a id="1752" class="Symbol">→</a> <a id="1754" href="ClosureSystems.Basic.html#1715" class="Generalizable">a</a><a id="1755" class="Symbol">)</a> <a id="1757" class="Symbol">→</a> <a id="1759" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="1764" class="Symbol">_</a>
<a id="1766" href="ClosureSystems.Basic.html#1727" class="Function">Extensive</a> <a id="1776" href="ClosureSystems.Basic.html#1776" class="Bound Operator">_≤_</a> <a id="1780" href="ClosureSystems.Basic.html#1780" class="Bound">C</a> <a id="1782" class="Symbol">=</a> <a id="1784" class="Symbol">∀{</a><a id="1786" href="ClosureSystems.Basic.html#1786" class="Bound">x</a><a id="1787" class="Symbol">}</a> <a id="1789" class="Symbol">→</a> <a id="1791" href="ClosureSystems.Basic.html#1786" class="Bound">x</a> <a id="1793" href="ClosureSystems.Basic.html#1776" class="Bound Operator">≤</a> <a id="1795" href="ClosureSystems.Basic.html#1780" class="Bound">C</a> <a id="1797" href="ClosureSystems.Basic.html#1786" class="Bound">x</a>

<a id="1800" class="Comment">-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)</a>

<a id="1894" class="Keyword">module</a> <a id="1901" href="ClosureSystems.Basic.html#1901" class="Module">_</a> <a id="1903" class="Symbol">{</a><a id="1904" href="ClosureSystems.Basic.html#1904" class="Bound">χ</a> <a id="1906" href="ClosureSystems.Basic.html#1906" class="Bound">ρ</a> <a id="1908" href="ClosureSystems.Basic.html#1908" class="Bound">ℓ</a> <a id="1910" class="Symbol">:</a> <a id="1912" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1917" class="Symbol">}{</a><a id="1919" href="ClosureSystems.Basic.html#1919" class="Bound">X</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="1928" href="ClosureSystems.Basic.html#1904" class="Bound">χ</a><a id="1929" class="Symbol">}</a> <a id="1931" class="Keyword">where</a>

 <a id="1939" href="ClosureSystems.Basic.html#1939" class="Function">IntersectClosed</a> <a id="1955" class="Symbol">:</a> <a id="1957" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1962" class="Symbol">(</a><a id="1963" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1968" href="ClosureSystems.Basic.html#1919" class="Bound">X</a> <a id="1970" href="ClosureSystems.Basic.html#1908" class="Bound">ℓ</a><a id="1971" class="Symbol">)</a> <a id="1973" href="ClosureSystems.Basic.html#1906" class="Bound">ρ</a> <a id="1975" class="Symbol">→</a> <a id="1977" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="1982" class="Symbol">_</a>
 <a id="1985" href="ClosureSystems.Basic.html#1939" class="Function">IntersectClosed</a> <a id="2001" href="ClosureSystems.Basic.html#2001" class="Bound">C</a> <a id="2003" class="Symbol">=</a> <a id="2005" class="Symbol">∀</a> <a id="2007" class="Symbol">{</a><a id="2008" href="ClosureSystems.Basic.html#2008" class="Bound">I</a> <a id="2010" class="Symbol">:</a> <a id="2012" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="2017" href="ClosureSystems.Basic.html#1908" class="Bound">ℓ</a><a id="2018" class="Symbol">}{</a><a id="2020" href="ClosureSystems.Basic.html#2020" class="Bound">c</a> <a id="2022" class="Symbol">:</a> <a id="2024" href="ClosureSystems.Basic.html#2008" class="Bound">I</a> <a id="2026" class="Symbol">→</a> <a id="2028" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2033" href="ClosureSystems.Basic.html#1919" class="Bound">X</a> <a id="2035" href="ClosureSystems.Basic.html#1908" class="Bound">ℓ</a><a id="2036" class="Symbol">}</a> <a id="2038" class="Symbol">→</a> <a id="2040" class="Symbol">(∀</a> <a id="2043" href="ClosureSystems.Basic.html#2043" class="Bound">i</a> <a id="2045" class="Symbol">→</a> <a id="2047" class="Symbol">(</a><a id="2048" href="ClosureSystems.Basic.html#2020" class="Bound">c</a> <a id="2050" href="ClosureSystems.Basic.html#2043" class="Bound">i</a><a id="2051" class="Symbol">)</a> <a id="2053" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2055" href="ClosureSystems.Basic.html#2001" class="Bound">C</a><a id="2056" class="Symbol">)</a> <a id="2058" class="Symbol">→</a> <a id="2060" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="2062" href="ClosureSystems.Basic.html#2008" class="Bound">I</a> <a id="2064" href="ClosureSystems.Basic.html#2020" class="Bound">c</a> <a id="2066" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2068" href="ClosureSystems.Basic.html#2001" class="Bound">C</a>

 <a id="2072" href="ClosureSystems.Basic.html#2072" class="Function">ClosureSystem</a> <a id="2086" class="Symbol">:</a> <a id="2088" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a> <a id="2093" class="Symbol">_</a>
 <a id="2096" href="ClosureSystems.Basic.html#2072" class="Function">ClosureSystem</a> <a id="2110" class="Symbol">=</a> <a id="2112" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2115" href="ClosureSystems.Basic.html#2115" class="Bound">C</a> <a id="2117" href="Data.Product.html#916" class="Function">∈</a> <a id="2119" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2124" class="Symbol">(</a><a id="2125" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2130" href="ClosureSystems.Basic.html#1919" class="Bound">X</a> <a id="2132" href="ClosureSystems.Basic.html#1908" class="Bound">ℓ</a><a id="2133" class="Symbol">)</a> <a id="2135" href="ClosureSystems.Basic.html#1906" class="Bound">ρ</a> <a id="2137" href="Data.Product.html#916" class="Function">]</a> <a id="2139" href="ClosureSystems.Basic.html#1939" class="Function">IntersectClosed</a> <a id="2155" href="ClosureSystems.Basic.html#2115" class="Bound">C</a>

</pre>


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2534" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2594" class="Keyword">record</a> <a id="ClOp"></a><a id="2601" href="ClosureSystems.Basic.html#2601" class="Record">ClOp</a> <a id="2606" class="Symbol">{</a><a id="2607" href="ClosureSystems.Basic.html#2607" class="Bound">ℓ</a> <a id="2609" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₁</a> <a id="2612" href="ClosureSystems.Basic.html#2612" class="Bound">ℓ₂</a> <a id="2615" class="Symbol">:</a> <a id="2617" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2622" class="Symbol">}(</a><a id="2624" href="ClosureSystems.Basic.html#2624" class="Bound">𝑨</a> <a id="2626" class="Symbol">:</a> <a id="2628" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2634" href="ClosureSystems.Basic.html#2607" class="Bound">ℓ</a> <a id="2636" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₁</a> <a id="2639" href="ClosureSystems.Basic.html#2612" class="Bound">ℓ₂</a><a id="2641" class="Symbol">)</a> <a id="2643" class="Symbol">:</a> <a id="2645" href="ClosureSystems.Basic.html#1327" class="Primitive">Type</a>  <a id="2651" class="Symbol">(</a><a id="2652" href="ClosureSystems.Basic.html#2607" class="Bound">ℓ</a> <a id="2654" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2656" href="ClosureSystems.Basic.html#2612" class="Bound">ℓ₂</a> <a id="2659" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2661" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₁</a><a id="2663" class="Symbol">)</a> <a id="2665" class="Keyword">where</a>

 <a id="2673" class="Keyword">open</a> <a id="2678" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2684" href="ClosureSystems.Basic.html#2624" class="Bound">𝑨</a>
 <a id="2687" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2698" href="ClosureSystems.Basic.html#2698" class="Function">A</a> <a id="2700" class="Symbol">=</a> <a id="2702" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2712" class="Keyword">open</a> <a id="2717" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2737" class="Symbol">(</a><a id="2738" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2741" class="Symbol">)</a>

 <a id="2745" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2753" href="ClosureSystems.Basic.html#2753" class="Field">C</a> <a id="2755" class="Symbol">:</a> <a id="2757" href="ClosureSystems.Basic.html#2698" class="Function">A</a> <a id="2759" class="Symbol">→</a> <a id="2761" href="ClosureSystems.Basic.html#2698" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2765" href="ClosureSystems.Basic.html#2765" class="Field">isExtensive</a>       <a id="2783" class="Symbol">:</a> <a id="2785" href="ClosureSystems.Basic.html#1727" class="Function">Extensive</a> <a id="2795" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2799" href="ClosureSystems.Basic.html#2753" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2803" href="ClosureSystems.Basic.html#2803" class="Field">isOrderPreserving</a> <a id="2821" class="Symbol">:</a> <a id="2823" href="ClosureSystems.Basic.html#2753" class="Field">C</a> <a id="2825" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2835" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2839" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2841" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2847" href="ClosureSystems.Basic.html#2847" class="Field">isIdempotent</a>      <a id="2865" class="Symbol">:</a> <a id="2867" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2881" href="ClosureSystems.Basic.html#2753" class="Field">C</a>

</pre>

--------------------------------------

[↑ ClosureSystems.Definitions](ClosureSystems.html)
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
