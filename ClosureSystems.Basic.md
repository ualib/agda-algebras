---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

## <a id="basic-definitions">Basic definitions</a>

This is the [ClosureSystems.Basic][] module of the [Agda Universal Algebra Library][].

### <a id="closure-systems">Closure Systems</a>

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

<a id="1072" class="Symbol">{-#</a> <a id="1076" class="Keyword">OPTIONS</a> <a id="1084" class="Pragma">--without-K</a> <a id="1096" class="Pragma">--exact-split</a> <a id="1110" class="Pragma">--safe</a> <a id="1117" class="Symbol">#-}</a>

<a id="1122" class="Keyword">module</a> <a id="1129" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1150" class="Keyword">where</a>

<a id="1157" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1249" class="Keyword">open</a> <a id="1254" class="Keyword">import</a> <a id="1261" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1286" class="Keyword">using</a> <a id="1292" class="Symbol">(</a> <a id="1294" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1298" class="Symbol">;</a> <a id="1300" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1305" class="Symbol">)</a> <a id="1307" class="Keyword">renaming</a> <a id="1316" class="Symbol">(</a> <a id="1318" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1322" class="Symbol">to</a> <a id="1325" class="Primitive">Type</a> <a id="1330" class="Symbol">)</a>
<a id="1332" class="Keyword">import</a> <a id="1339" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1359" class="Keyword">open</a> <a id="1364" class="Keyword">import</a> <a id="1371" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1396" class="Keyword">using</a> <a id="1402" class="Symbol">(</a> <a id="1404" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1413" class="Symbol">)</a>
<a id="1415" class="Keyword">open</a> <a id="1420" class="Keyword">import</a> <a id="1427" href="Level.html" class="Module">Level</a>                    <a id="1452" class="Keyword">using</a> <a id="1458" class="Symbol">(</a> <a id="1460" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1466" class="Symbol">;</a> <a id="1468" href="Level.html#400" class="Record">Lift</a> <a id="1473" class="Symbol">)</a> <a id="1475" class="Keyword">renaming</a> <a id="1484" class="Symbol">(</a> <a id="1486" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1491" class="Symbol">to</a> <a id="1494" class="Primitive">ℓ₀</a> <a id="1497" class="Symbol">)</a>
<a id="1499" class="Keyword">open</a> <a id="1504" class="Keyword">import</a> <a id="1511" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1536" class="Keyword">using</a> <a id="1542" class="Symbol">(</a> <a id="1544" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1550" class="Symbol">)</a>
<a id="1552" class="Keyword">open</a> <a id="1557" class="Keyword">import</a> <a id="1564" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1589" class="Keyword">using</a> <a id="1595" class="Symbol">(</a> <a id="1597" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1601" class="Symbol">;</a> <a id="1603" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1617" class="Symbol">)</a>
<a id="1619" class="Keyword">open</a> <a id="1624" class="Keyword">import</a> <a id="1631" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1656" class="Keyword">using</a> <a id="1662" class="Symbol">(</a> <a id="1664" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1669" class="Symbol">;</a> <a id="1671" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1675" class="Symbol">;</a> <a id="1677" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1679" class="Symbol">)</a>

<a id="1682" class="Keyword">private</a> <a id="1690" class="Keyword">variable</a>
 <a id="1700" href="ClosureSystems.Basic.html#1700" class="Generalizable">α</a> <a id="1702" href="ClosureSystems.Basic.html#1702" class="Generalizable">ρ</a> <a id="1704" class="Symbol">:</a> <a id="1706" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1713" href="ClosureSystems.Basic.html#1713" class="Generalizable">a</a> <a id="1715" class="Symbol">:</a> <a id="1717" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="1722" href="ClosureSystems.Basic.html#1700" class="Generalizable">α</a>

<a id="Extensive"></a><a id="1725" href="ClosureSystems.Basic.html#1725" class="Function">Extensive</a> <a id="1735" class="Symbol">:</a> <a id="1737" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1741" href="ClosureSystems.Basic.html#1713" class="Generalizable">a</a> <a id="1743" href="ClosureSystems.Basic.html#1702" class="Generalizable">ρ</a> <a id="1745" class="Symbol">→</a> <a id="1747" class="Symbol">(</a><a id="1748" href="ClosureSystems.Basic.html#1713" class="Generalizable">a</a> <a id="1750" class="Symbol">→</a> <a id="1752" href="ClosureSystems.Basic.html#1713" class="Generalizable">a</a><a id="1753" class="Symbol">)</a> <a id="1755" class="Symbol">→</a> <a id="1757" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="1762" class="Symbol">_</a>
<a id="1764" href="ClosureSystems.Basic.html#1725" class="Function">Extensive</a> <a id="1774" href="ClosureSystems.Basic.html#1774" class="Bound Operator">_≤_</a> <a id="1778" href="ClosureSystems.Basic.html#1778" class="Bound">C</a> <a id="1780" class="Symbol">=</a> <a id="1782" class="Symbol">∀{</a><a id="1784" href="ClosureSystems.Basic.html#1784" class="Bound">x</a><a id="1785" class="Symbol">}</a> <a id="1787" class="Symbol">→</a> <a id="1789" href="ClosureSystems.Basic.html#1784" class="Bound">x</a> <a id="1791" href="ClosureSystems.Basic.html#1774" class="Bound Operator">≤</a> <a id="1793" href="ClosureSystems.Basic.html#1778" class="Bound">C</a> <a id="1795" href="ClosureSystems.Basic.html#1784" class="Bound">x</a>

<a id="1798" class="Comment">-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)</a>

<a id="1892" class="Keyword">module</a> <a id="1899" href="ClosureSystems.Basic.html#1899" class="Module">_</a> <a id="1901" class="Symbol">{</a><a id="1902" href="ClosureSystems.Basic.html#1902" class="Bound">χ</a> <a id="1904" href="ClosureSystems.Basic.html#1904" class="Bound">ρ</a> <a id="1906" href="ClosureSystems.Basic.html#1906" class="Bound">ℓ</a> <a id="1908" class="Symbol">:</a> <a id="1910" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1915" class="Symbol">}{</a><a id="1917" href="ClosureSystems.Basic.html#1917" class="Bound">X</a> <a id="1919" class="Symbol">:</a> <a id="1921" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="1926" href="ClosureSystems.Basic.html#1902" class="Bound">χ</a><a id="1927" class="Symbol">}</a> <a id="1929" class="Keyword">where</a>

 <a id="1937" href="ClosureSystems.Basic.html#1937" class="Function">IntersectClosed</a> <a id="1953" class="Symbol">:</a> <a id="1955" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1960" class="Symbol">(</a><a id="1961" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1966" href="ClosureSystems.Basic.html#1917" class="Bound">X</a> <a id="1968" href="ClosureSystems.Basic.html#1906" class="Bound">ℓ</a><a id="1969" class="Symbol">)</a> <a id="1971" href="ClosureSystems.Basic.html#1904" class="Bound">ρ</a> <a id="1973" class="Symbol">→</a> <a id="1975" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="1980" class="Symbol">_</a>
 <a id="1983" href="ClosureSystems.Basic.html#1937" class="Function">IntersectClosed</a> <a id="1999" href="ClosureSystems.Basic.html#1999" class="Bound">C</a> <a id="2001" class="Symbol">=</a> <a id="2003" class="Symbol">∀</a> <a id="2005" class="Symbol">{</a><a id="2006" href="ClosureSystems.Basic.html#2006" class="Bound">I</a> <a id="2008" class="Symbol">:</a> <a id="2010" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="2015" href="ClosureSystems.Basic.html#1906" class="Bound">ℓ</a><a id="2016" class="Symbol">}{</a><a id="2018" href="ClosureSystems.Basic.html#2018" class="Bound">c</a> <a id="2020" class="Symbol">:</a> <a id="2022" href="ClosureSystems.Basic.html#2006" class="Bound">I</a> <a id="2024" class="Symbol">→</a> <a id="2026" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2031" href="ClosureSystems.Basic.html#1917" class="Bound">X</a> <a id="2033" href="ClosureSystems.Basic.html#1906" class="Bound">ℓ</a><a id="2034" class="Symbol">}</a> <a id="2036" class="Symbol">→</a> <a id="2038" class="Symbol">(∀</a> <a id="2041" href="ClosureSystems.Basic.html#2041" class="Bound">i</a> <a id="2043" class="Symbol">→</a> <a id="2045" class="Symbol">(</a><a id="2046" href="ClosureSystems.Basic.html#2018" class="Bound">c</a> <a id="2048" href="ClosureSystems.Basic.html#2041" class="Bound">i</a><a id="2049" class="Symbol">)</a> <a id="2051" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2053" href="ClosureSystems.Basic.html#1999" class="Bound">C</a><a id="2054" class="Symbol">)</a> <a id="2056" class="Symbol">→</a> <a id="2058" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="2060" href="ClosureSystems.Basic.html#2006" class="Bound">I</a> <a id="2062" href="ClosureSystems.Basic.html#2018" class="Bound">c</a> <a id="2064" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2066" href="ClosureSystems.Basic.html#1999" class="Bound">C</a>

 <a id="2070" href="ClosureSystems.Basic.html#2070" class="Function">ClosureSystem</a> <a id="2084" class="Symbol">:</a> <a id="2086" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a> <a id="2091" class="Symbol">_</a>
 <a id="2094" href="ClosureSystems.Basic.html#2070" class="Function">ClosureSystem</a> <a id="2108" class="Symbol">=</a> <a id="2110" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2113" href="ClosureSystems.Basic.html#2113" class="Bound">C</a> <a id="2115" href="Data.Product.html#916" class="Function">∈</a> <a id="2117" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2122" class="Symbol">(</a><a id="2123" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="2128" href="ClosureSystems.Basic.html#1917" class="Bound">X</a> <a id="2130" href="ClosureSystems.Basic.html#1906" class="Bound">ℓ</a><a id="2131" class="Symbol">)</a> <a id="2133" href="ClosureSystems.Basic.html#1904" class="Bound">ρ</a> <a id="2135" href="Data.Product.html#916" class="Function">]</a> <a id="2137" href="ClosureSystems.Basic.html#1937" class="Function">IntersectClosed</a> <a id="2153" href="ClosureSystems.Basic.html#2113" class="Bound">C</a>

</pre>


### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2531" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2591" class="Keyword">record</a> <a id="ClOp"></a><a id="2598" href="ClosureSystems.Basic.html#2598" class="Record">ClOp</a> <a id="2603" class="Symbol">{</a><a id="2604" href="ClosureSystems.Basic.html#2604" class="Bound">ℓ</a> <a id="2606" href="ClosureSystems.Basic.html#2606" class="Bound">ℓ₁</a> <a id="2609" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₂</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2619" class="Symbol">}(</a><a id="2621" href="ClosureSystems.Basic.html#2621" class="Bound">𝑨</a> <a id="2623" class="Symbol">:</a> <a id="2625" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2631" href="ClosureSystems.Basic.html#2604" class="Bound">ℓ</a> <a id="2633" href="ClosureSystems.Basic.html#2606" class="Bound">ℓ₁</a> <a id="2636" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₂</a><a id="2638" class="Symbol">)</a> <a id="2640" class="Symbol">:</a> <a id="2642" href="ClosureSystems.Basic.html#1325" class="Primitive">Type</a>  <a id="2648" class="Symbol">(</a><a id="2649" href="ClosureSystems.Basic.html#2604" class="Bound">ℓ</a> <a id="2651" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2653" href="ClosureSystems.Basic.html#2609" class="Bound">ℓ₂</a> <a id="2656" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2658" href="ClosureSystems.Basic.html#2606" class="Bound">ℓ₁</a><a id="2660" class="Symbol">)</a> <a id="2662" class="Keyword">where</a>

 <a id="2670" class="Keyword">open</a> <a id="2675" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2681" href="ClosureSystems.Basic.html#2621" class="Bound">𝑨</a>
 <a id="2684" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2695" href="ClosureSystems.Basic.html#2695" class="Function">A</a> <a id="2697" class="Symbol">=</a> <a id="2699" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2709" class="Keyword">open</a> <a id="2714" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2734" class="Symbol">(</a><a id="2735" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2738" class="Symbol">)</a>

 <a id="2742" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2750" href="ClosureSystems.Basic.html#2750" class="Field">C</a> <a id="2752" class="Symbol">:</a> <a id="2754" href="ClosureSystems.Basic.html#2695" class="Function">A</a> <a id="2756" class="Symbol">→</a> <a id="2758" href="ClosureSystems.Basic.html#2695" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2762" href="ClosureSystems.Basic.html#2762" class="Field">isExtensive</a>       <a id="2780" class="Symbol">:</a> <a id="2782" href="ClosureSystems.Basic.html#1725" class="Function">Extensive</a> <a id="2792" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2796" href="ClosureSystems.Basic.html#2750" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2800" href="ClosureSystems.Basic.html#2800" class="Field">isOrderPreserving</a> <a id="2818" class="Symbol">:</a> <a id="2820" href="ClosureSystems.Basic.html#2750" class="Field">C</a> <a id="2822" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2832" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2836" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2838" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2844" href="ClosureSystems.Basic.html#2844" class="Field">isIdempotent</a>      <a id="2862" class="Symbol">:</a> <a id="2864" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2878" href="ClosureSystems.Basic.html#2750" class="Field">C</a>

</pre>

--------------------------------------

<span style="float:left;">[↑ ClosureSystems.Definitions](ClosureSystems.html)</span>
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
