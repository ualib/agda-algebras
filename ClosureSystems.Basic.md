---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### <a id="basic-definitions">Basic Definitions</a>

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

<a id="987" class="Symbol">{-#</a> <a id="991" class="Keyword">OPTIONS</a> <a id="999" class="Pragma">--without-K</a> <a id="1011" class="Pragma">--exact-split</a> <a id="1025" class="Pragma">--safe</a> <a id="1032" class="Symbol">#-}</a>

<a id="1037" class="Keyword">module</a> <a id="1044" href="ClosureSystems.Basic.html" class="Module">ClosureSystems.Basic</a> <a id="1065" class="Keyword">where</a>

<a id="1072" class="Keyword">open</a> <a id="1077" class="Keyword">import</a> <a id="1084" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>           <a id="1109" class="Keyword">using</a> <a id="1115" class="Symbol">(</a> <a id="1117" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1121" class="Symbol">;</a> <a id="1123" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1128" class="Symbol">)</a> <a id="1130" class="Keyword">renaming</a> <a id="1139" class="Symbol">(</a> <a id="1141" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1145" class="Symbol">to</a> <a id="1148" class="Primitive">Type</a> <a id="1153" class="Symbol">)</a>
<a id="1155" class="Keyword">import</a> <a id="1162" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a>
<a id="1182" class="Keyword">open</a> <a id="1187" class="Keyword">import</a> <a id="1194" href="Data.Product.html" class="Module">Data.Product</a>             <a id="1219" class="Keyword">using</a> <a id="1225" class="Symbol">(</a> <a id="1227" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1236" class="Symbol">)</a>
<a id="1238" class="Keyword">open</a> <a id="1243" class="Keyword">import</a> <a id="1250" href="Level.html" class="Module">Level</a>                    <a id="1275" class="Keyword">using</a> <a id="1281" class="Symbol">(</a> <a id="1283" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1289" class="Symbol">;</a> <a id="1291" href="Level.html#400" class="Record">Lift</a> <a id="1296" class="Symbol">)</a> <a id="1298" class="Keyword">renaming</a> <a id="1307" class="Symbol">(</a> <a id="1309" href="Agda.Primitive.html#764" class="Primitive">zero</a> <a id="1314" class="Symbol">to</a> <a id="1317" class="Primitive">ℓ₀</a> <a id="1320" class="Symbol">)</a>
<a id="1322" class="Keyword">open</a> <a id="1327" class="Keyword">import</a> <a id="1334" href="Relation.Binary.Bundles.html" class="Module">Relation.Binary.Bundles</a>  <a id="1359" class="Keyword">using</a> <a id="1365" class="Symbol">(</a> <a id="1367" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="1373" class="Symbol">)</a>
<a id="1375" class="Keyword">open</a> <a id="1380" class="Keyword">import</a> <a id="1387" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>     <a id="1412" class="Keyword">using</a> <a id="1418" class="Symbol">(</a> <a id="1420" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1424" class="Symbol">;</a> <a id="1426" href="Relation.Binary.Core.html#1563" class="Function Operator">_Preserves_⟶_</a> <a id="1440" class="Symbol">)</a>
<a id="1442" class="Keyword">open</a> <a id="1447" class="Keyword">import</a> <a id="1454" href="Relation.Unary.html" class="Module">Relation.Unary</a>           <a id="1479" class="Keyword">using</a> <a id="1485" class="Symbol">(</a> <a id="1487" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1492" class="Symbol">;</a> <a id="1494" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="1498" class="Symbol">;</a> <a id="1500" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1502" class="Symbol">)</a>


<a id="1506" class="Keyword">private</a> <a id="1514" class="Keyword">variable</a>
 <a id="1524" href="ClosureSystems.Basic.html#1524" class="Generalizable">α</a> <a id="1526" href="ClosureSystems.Basic.html#1526" class="Generalizable">ρ</a> <a id="1528" class="Symbol">:</a> <a id="1530" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1537" href="ClosureSystems.Basic.html#1537" class="Generalizable">a</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1546" href="ClosureSystems.Basic.html#1524" class="Generalizable">α</a>

<a id="Extensive"></a><a id="1549" href="ClosureSystems.Basic.html#1549" class="Function">Extensive</a> <a id="1559" class="Symbol">:</a> <a id="1561" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="1565" href="ClosureSystems.Basic.html#1537" class="Generalizable">a</a> <a id="1567" href="ClosureSystems.Basic.html#1526" class="Generalizable">ρ</a> <a id="1569" class="Symbol">→</a> <a id="1571" class="Symbol">(</a><a id="1572" href="ClosureSystems.Basic.html#1537" class="Generalizable">a</a> <a id="1574" class="Symbol">→</a> <a id="1576" href="ClosureSystems.Basic.html#1537" class="Generalizable">a</a><a id="1577" class="Symbol">)</a> <a id="1579" class="Symbol">→</a> <a id="1581" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1586" class="Symbol">_</a>
<a id="1588" href="ClosureSystems.Basic.html#1549" class="Function">Extensive</a> <a id="1598" href="ClosureSystems.Basic.html#1598" class="Bound Operator">_≤_</a> <a id="1602" href="ClosureSystems.Basic.html#1602" class="Bound">C</a> <a id="1604" class="Symbol">=</a> <a id="1606" class="Symbol">∀{</a><a id="1608" href="ClosureSystems.Basic.html#1608" class="Bound">x</a><a id="1609" class="Symbol">}</a> <a id="1611" class="Symbol">→</a> <a id="1613" href="ClosureSystems.Basic.html#1608" class="Bound">x</a> <a id="1615" href="ClosureSystems.Basic.html#1598" class="Bound Operator">≤</a> <a id="1617" href="ClosureSystems.Basic.html#1602" class="Bound">C</a> <a id="1619" href="ClosureSystems.Basic.html#1608" class="Bound">x</a>

<a id="1622" class="Comment">-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)</a>

<a id="1716" class="Keyword">module</a> <a id="1723" href="ClosureSystems.Basic.html#1723" class="Module">_</a> <a id="1725" class="Symbol">{</a><a id="1726" href="ClosureSystems.Basic.html#1726" class="Bound">χ</a> <a id="1728" href="ClosureSystems.Basic.html#1728" class="Bound">ρ</a> <a id="1730" href="ClosureSystems.Basic.html#1730" class="Bound">ℓ</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1739" class="Symbol">}{</a><a id="1741" href="ClosureSystems.Basic.html#1741" class="Bound">X</a> <a id="1743" class="Symbol">:</a> <a id="1745" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1750" href="ClosureSystems.Basic.html#1726" class="Bound">χ</a><a id="1751" class="Symbol">}</a> <a id="1753" class="Keyword">where</a>

 <a id="1761" href="ClosureSystems.Basic.html#1761" class="Function">IntersectClosed</a> <a id="1777" class="Symbol">:</a> <a id="1779" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1784" class="Symbol">(</a><a id="1785" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1790" href="ClosureSystems.Basic.html#1741" class="Bound">X</a> <a id="1792" href="ClosureSystems.Basic.html#1730" class="Bound">ℓ</a><a id="1793" class="Symbol">)</a> <a id="1795" href="ClosureSystems.Basic.html#1728" class="Bound">ρ</a> <a id="1797" class="Symbol">→</a> <a id="1799" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1804" class="Symbol">_</a>
 <a id="1807" href="ClosureSystems.Basic.html#1761" class="Function">IntersectClosed</a> <a id="1823" href="ClosureSystems.Basic.html#1823" class="Bound">C</a> <a id="1825" class="Symbol">=</a> <a id="1827" class="Symbol">∀</a> <a id="1829" class="Symbol">{</a><a id="1830" href="ClosureSystems.Basic.html#1830" class="Bound">I</a> <a id="1832" class="Symbol">:</a> <a id="1834" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1839" href="ClosureSystems.Basic.html#1730" class="Bound">ℓ</a><a id="1840" class="Symbol">}{</a><a id="1842" href="ClosureSystems.Basic.html#1842" class="Bound">c</a> <a id="1844" class="Symbol">:</a> <a id="1846" href="ClosureSystems.Basic.html#1830" class="Bound">I</a> <a id="1848" class="Symbol">→</a> <a id="1850" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1855" href="ClosureSystems.Basic.html#1741" class="Bound">X</a> <a id="1857" href="ClosureSystems.Basic.html#1730" class="Bound">ℓ</a><a id="1858" class="Symbol">}</a> <a id="1860" class="Symbol">→</a> <a id="1862" class="Symbol">(∀</a> <a id="1865" href="ClosureSystems.Basic.html#1865" class="Bound">i</a> <a id="1867" class="Symbol">→</a> <a id="1869" class="Symbol">(</a><a id="1870" href="ClosureSystems.Basic.html#1842" class="Bound">c</a> <a id="1872" href="ClosureSystems.Basic.html#1865" class="Bound">i</a><a id="1873" class="Symbol">)</a> <a id="1875" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1877" href="ClosureSystems.Basic.html#1823" class="Bound">C</a><a id="1878" class="Symbol">)</a> <a id="1880" class="Symbol">→</a> <a id="1882" href="Relation.Unary.html#4741" class="Function">⋂</a> <a id="1884" href="ClosureSystems.Basic.html#1830" class="Bound">I</a> <a id="1886" href="ClosureSystems.Basic.html#1842" class="Bound">c</a> <a id="1888" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1890" href="ClosureSystems.Basic.html#1823" class="Bound">C</a>

 <a id="1894" href="ClosureSystems.Basic.html#1894" class="Function">ClosureSystem</a> <a id="1908" class="Symbol">:</a> <a id="1910" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a> <a id="1915" class="Symbol">_</a>
 <a id="1918" href="ClosureSystems.Basic.html#1894" class="Function">ClosureSystem</a> <a id="1932" class="Symbol">=</a> <a id="1934" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1937" href="ClosureSystems.Basic.html#1937" class="Bound">C</a> <a id="1939" href="Data.Product.html#916" class="Function">∈</a> <a id="1941" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1946" class="Symbol">(</a><a id="1947" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1952" href="ClosureSystems.Basic.html#1741" class="Bound">X</a> <a id="1954" href="ClosureSystems.Basic.html#1730" class="Bound">ℓ</a><a id="1955" class="Symbol">)</a> <a id="1957" href="ClosureSystems.Basic.html#1728" class="Bound">ρ</a> <a id="1959" href="Data.Product.html#916" class="Function">]</a> <a id="1961" href="ClosureSystems.Basic.html#1761" class="Function">IntersectClosed</a> <a id="1977" href="ClosureSystems.Basic.html#1937" class="Bound">C</a>

</pre>


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

<pre class="Agda">

<a id="2356" class="Comment">-- ClOp, the inhabitants of which denote closure operators.</a>
<a id="2416" class="Keyword">record</a> <a id="ClOp"></a><a id="2423" href="ClosureSystems.Basic.html#2423" class="Record">ClOp</a> <a id="2428" class="Symbol">{</a><a id="2429" href="ClosureSystems.Basic.html#2429" class="Bound">ℓ</a> <a id="2431" href="ClosureSystems.Basic.html#2431" class="Bound">ℓ₁</a> <a id="2434" href="ClosureSystems.Basic.html#2434" class="Bound">ℓ₂</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2444" class="Symbol">}(</a><a id="2446" href="ClosureSystems.Basic.html#2446" class="Bound">𝑨</a> <a id="2448" class="Symbol">:</a> <a id="2450" href="Relation.Binary.Bundles.html#3028" class="Record">Poset</a> <a id="2456" href="ClosureSystems.Basic.html#2429" class="Bound">ℓ</a> <a id="2458" href="ClosureSystems.Basic.html#2431" class="Bound">ℓ₁</a> <a id="2461" href="ClosureSystems.Basic.html#2434" class="Bound">ℓ₂</a><a id="2463" class="Symbol">)</a> <a id="2465" class="Symbol">:</a> <a id="2467" href="ClosureSystems.Basic.html#1148" class="Primitive">Type</a>  <a id="2473" class="Symbol">(</a><a id="2474" href="ClosureSystems.Basic.html#2429" class="Bound">ℓ</a> <a id="2476" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2478" href="ClosureSystems.Basic.html#2434" class="Bound">ℓ₂</a> <a id="2481" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2483" href="ClosureSystems.Basic.html#2431" class="Bound">ℓ₁</a><a id="2485" class="Symbol">)</a> <a id="2487" class="Keyword">where</a>

 <a id="2495" class="Keyword">open</a> <a id="2500" href="Relation.Binary.Bundles.html#3028" class="Module">Poset</a> <a id="2506" href="ClosureSystems.Basic.html#2446" class="Bound">𝑨</a>
 <a id="2509" class="Keyword">private</a>
   <a id="ClOp.A"></a><a id="2520" href="ClosureSystems.Basic.html#2520" class="Function">A</a> <a id="2522" class="Symbol">=</a> <a id="2524" href="Relation.Binary.Bundles.html#3104" class="Function">Carrier</a>

 <a id="2534" class="Keyword">open</a> <a id="2539" href="Algebra.Definitions.html" class="Module">Algebra.Definitions</a> <a id="2559" class="Symbol">(</a><a id="2560" href="Relation.Binary.Bundles.html#3131" class="Function Operator">_≈_</a><a id="2563" class="Symbol">)</a>

 <a id="2567" class="Keyword">field</a>
  <a id="ClOp.C"></a><a id="2575" href="ClosureSystems.Basic.html#2575" class="Field">C</a> <a id="2577" class="Symbol">:</a> <a id="2579" href="ClosureSystems.Basic.html#2520" class="Function">A</a> <a id="2581" class="Symbol">→</a> <a id="2583" href="ClosureSystems.Basic.html#2520" class="Function">A</a>
  <a id="ClOp.isExtensive"></a><a id="2587" href="ClosureSystems.Basic.html#2587" class="Field">isExtensive</a>       <a id="2605" class="Symbol">:</a> <a id="2607" href="ClosureSystems.Basic.html#1549" class="Function">Extensive</a> <a id="2617" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2621" href="ClosureSystems.Basic.html#2575" class="Field">C</a>
  <a id="ClOp.isOrderPreserving"></a><a id="2625" href="ClosureSystems.Basic.html#2625" class="Field">isOrderPreserving</a> <a id="2643" class="Symbol">:</a> <a id="2645" href="ClosureSystems.Basic.html#2575" class="Field">C</a> <a id="2647" href="Relation.Binary.Core.html#1563" class="Function Operator">Preserves</a> <a id="2657" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a> <a id="2661" href="Relation.Binary.Core.html#1563" class="Function Operator">⟶</a> <a id="2663" href="Relation.Binary.Bundles.html#3167" class="Function Operator">_≤_</a>
  <a id="ClOp.isIdempotent"></a><a id="2669" href="ClosureSystems.Basic.html#2669" class="Field">isIdempotent</a>      <a id="2687" class="Symbol">:</a> <a id="2689" href="Algebra.Definitions.html#2713" class="Function">IdempotentFun</a> <a id="2703" href="ClosureSystems.Basic.html#2575" class="Field">C</a>

</pre>


--------------------------------------

<br>
<br>

[↑ ClosureSystems.Definitions](ClosureSystems.html)
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
