---
layout: default
title : "Categories.Functors module (The Agda Universal Algebra Library)"
date : "2021-08-30"
author: "agda-algebras development team"
---

### <a id="functors">Functors</a>

This is the [Categories.Functors][] module of the [Agda Universal Algebra Library][].

Recall, a *functor* `F` is a function that maps the objects and morphisms of one category 𝒞 to the objects and morphisms of a category 𝒟 in such a way that the following *functor laws* are satisfied:

* ∀ f g, F(f ∘ g) = F(f) ∘ F(g)
* ∀ A, F(id A) = id (F A)  (where id X denotes the identity map on X)


#### <a id="polynomial-functors">Polynomial functors</a>

The main reference for this section is [Modular Type-Safety Proofs in Agda](https://doi.org/10.1145/2428116.2428120) by Schwaab and Siek (PLPV '07).

An important class of functors for our domain is the class of so called *polynomial functors*. These are functors that are built up using the constant, identity, sum, and product functors.  To be precise, the actions of the latter on objects are as follows: `∀ A B` (objects), `∀ F G` (functors),

* `const B A = B`
* `Id A = A`
* `(F + G) A = F A + G A`
* `(F × G) A = F A × G A`

<pre class="Agda">

<a id="1192" class="Symbol">{-#</a> <a id="1196" class="Keyword">OPTIONS</a> <a id="1204" class="Pragma">--without-K</a> <a id="1216" class="Pragma">--exact-split</a> <a id="1230" class="Pragma">--safe</a> <a id="1237" class="Symbol">#-}</a>

<a id="1242" class="Keyword">module</a> <a id="1249" href="Categories.Functors.html" class="Module">Categories.Functors</a> <a id="1269" class="Keyword">where</a>

<a id="1276" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1368" class="Keyword">open</a> <a id="1373" class="Keyword">import</a> <a id="1380" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="1395" class="Keyword">using</a> <a id="1401" class="Symbol">(</a> <a id="1403" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1407" class="Symbol">;</a> <a id="1409" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1414" class="Symbol">;</a> <a id="1416" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1422" class="Symbol">)</a> <a id="1424" class="Keyword">renaming</a> <a id="1433" class="Symbol">(</a> <a id="1435" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1439" class="Symbol">to</a> <a id="1442" class="Primitive">Type</a> <a id="1447" class="Symbol">;</a> <a id="1449" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="1455" class="Symbol">to</a> <a id="1458" class="Primitive">ℓ₀</a> <a id="1461" class="Symbol">)</a>
<a id="1463" class="Keyword">open</a> <a id="1468" class="Keyword">import</a> <a id="1475" href="Data.Nat.html" class="Module">Data.Nat</a>       <a id="1490" class="Keyword">using</a> <a id="1496" class="Symbol">(</a> <a id="1498" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="1500" class="Symbol">;</a> <a id="1502" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="1507" class="Symbol">;</a> <a id="1509" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="1513" class="Symbol">;</a> <a id="1515" href="Data.Nat.Base.html#1709" class="Function Operator">_&gt;_</a> <a id="1519" class="Symbol">)</a>
<a id="1521" class="Keyword">open</a> <a id="1526" class="Keyword">import</a> <a id="1533" href="Data.Sum.Base.html" class="Module">Data.Sum.Base</a>  <a id="1548" class="Keyword">using</a> <a id="1554" class="Symbol">(</a> <a id="1556" href="Data.Sum.Base.html#734" class="Datatype Operator">_⊎_</a> <a id="1560" class="Symbol">)</a> <a id="1562" class="Keyword">renaming</a> <a id="1571" class="Symbol">(</a> <a id="1573" href="Data.Sum.Base.html#784" class="InductiveConstructor">inj₁</a> <a id="1578" class="Symbol">to</a> <a id="1581" class="InductiveConstructor">inl</a> <a id="1585" class="Symbol">;</a>  <a id="1588" href="Data.Sum.Base.html#809" class="InductiveConstructor">inj₂</a> <a id="1593" class="Symbol">to</a> <a id="1596" class="InductiveConstructor">inr</a> <a id="1600" class="Symbol">)</a>
<a id="1602" class="Keyword">open</a> <a id="1607" class="Keyword">import</a> <a id="1614" href="Data.Product.html" class="Module">Data.Product</a>   <a id="1629" class="Keyword">using</a> <a id="1635" class="Symbol">(</a> <a id="1637" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1646" class="Symbol">;</a> <a id="1648" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="1652" class="Symbol">;</a> <a id="1654" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="1658" class="Symbol">)</a>
<a id="1660" class="Keyword">open</a> <a id="1665" class="Keyword">import</a> <a id="1672" href="Data.Unit.html" class="Module">Data.Unit</a>      <a id="1687" class="Keyword">using</a> <a id="1693" class="Symbol">(</a> <a id="1695" href="Agda.Builtin.Unit.html#201" class="InductiveConstructor">tt</a> <a id="1698" class="Symbol">)</a> <a id="1700" class="Keyword">renaming</a> <a id="1709" class="Symbol">(</a> <a id="1711" href="Agda.Builtin.Unit.html#164" class="Record">⊤</a> <a id="1713" class="Symbol">to</a> <a id="1716" class="Record">⊤₀</a> <a id="1719" class="Symbol">)</a>
<a id="1721" class="Keyword">open</a> <a id="1726" class="Keyword">import</a> <a id="1733" href="Data.Unit.Polymorphic.html" class="Module">Data.Unit.Polymorphic</a>  <a id="1756" class="Keyword">using</a> <a id="1762" class="Symbol">(</a> <a id="1764" href="Data.Unit.Polymorphic.Base.html#480" class="Function">⊤</a> <a id="1766" class="Symbol">)</a>
<a id="1768" class="Keyword">open</a> <a id="1773" class="Keyword">import</a> <a id="1780" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>  <a id="1819" class="Keyword">using</a> <a id="1825" class="Symbol">(</a> <a id="1827" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1831" class="Symbol">;</a> <a id="1833" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1838" class="Symbol">;</a> <a id="1840" href="Relation.Binary.PropositionalEquality.Core.html#830" class="Function Operator">_≢_</a> <a id="1844" class="Symbol">)</a>
<a id="1846" class="Keyword">open</a> <a id="1851" class="Keyword">import</a> <a id="1858" href="Level.html" class="Module">Level</a>

<a id="1865" class="Keyword">private</a> <a id="1873" class="Keyword">variable</a>
 <a id="1883" href="Categories.Functors.html#1883" class="Generalizable">α</a> <a id="1885" href="Categories.Functors.html#1885" class="Generalizable">β</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="1896" class="Keyword">infixl</a> <a id="1903" class="Number">6</a> <a id="1905" href="Categories.Functors.html#2298" class="InductiveConstructor Operator">_⊕_</a>
<a id="1909" class="Keyword">infixr</a> <a id="1916" class="Number">7</a> <a id="1918" href="Categories.Functors.html#2339" class="InductiveConstructor Operator">_⊗_</a>
<a id="1922" class="Keyword">data</a> <a id="Functor₀"></a><a id="1927" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="1936" class="Symbol">:</a> <a id="1938" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="1943" class="Symbol">(</a><a id="1944" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1949" href="Categories.Functors.html#1458" class="Primitive">ℓ₀</a><a id="1951" class="Symbol">)</a> <a id="1953" class="Keyword">where</a>
 <a id="Functor₀.Id"></a><a id="1960" href="Categories.Functors.html#1960" class="InductiveConstructor">Id</a> <a id="1963" class="Symbol">:</a> <a id="1965" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a>
 <a id="Functor₀.Const"></a><a id="1975" href="Categories.Functors.html#1975" class="InductiveConstructor">Const</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="1988" class="Symbol">→</a> <a id="1990" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊕_"></a><a id="2000" href="Categories.Functors.html#2000" class="InductiveConstructor Operator">_⊕_</a> <a id="2004" class="Symbol">:</a> <a id="2006" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="2015" class="Symbol">→</a> <a id="2017" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="2026" class="Symbol">→</a> <a id="2028" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊗_"></a><a id="2038" href="Categories.Functors.html#2038" class="InductiveConstructor Operator">_⊗_</a> <a id="2042" class="Symbol">:</a> <a id="2044" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="2053" class="Symbol">→</a> <a id="2055" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="2064" class="Symbol">→</a> <a id="2066" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a>

<a id="[_]₀"></a><a id="2076" href="Categories.Functors.html#2076" class="Function Operator">[_]₀</a> <a id="2081" class="Symbol">:</a> <a id="2083" href="Categories.Functors.html#1927" class="Datatype">Functor₀</a> <a id="2092" class="Symbol">→</a> <a id="2094" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2099" class="Symbol">→</a> <a id="2101" href="Categories.Functors.html#1442" class="Primitive">Type</a>
<a id="2106" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2108" href="Categories.Functors.html#1960" class="InductiveConstructor">Id</a> <a id="2111" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2114" href="Categories.Functors.html#2114" class="Bound">B</a> <a id="2116" class="Symbol">=</a> <a id="2118" href="Categories.Functors.html#2114" class="Bound">B</a>
<a id="2120" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2122" href="Categories.Functors.html#1975" class="InductiveConstructor">Const</a> <a id="2128" href="Categories.Functors.html#2128" class="Bound">C</a> <a id="2130" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2133" href="Categories.Functors.html#2133" class="Bound">B</a> <a id="2135" class="Symbol">=</a> <a id="2137" href="Categories.Functors.html#2128" class="Bound">C</a>
<a id="2139" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2141" href="Categories.Functors.html#2141" class="Bound">F</a> <a id="2143" href="Categories.Functors.html#2000" class="InductiveConstructor Operator">⊕</a> <a id="2145" href="Categories.Functors.html#2145" class="Bound">G</a> <a id="2147" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2150" href="Categories.Functors.html#2150" class="Bound">B</a> <a id="2152" class="Symbol">=</a> <a id="2154" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2156" href="Categories.Functors.html#2141" class="Bound">F</a> <a id="2158" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2161" href="Categories.Functors.html#2150" class="Bound">B</a> <a id="2163" href="Data.Sum.Base.html#734" class="Datatype Operator">⊎</a> <a id="2165" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2167" href="Categories.Functors.html#2145" class="Bound">G</a> <a id="2169" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2172" href="Categories.Functors.html#2150" class="Bound">B</a>
<a id="2174" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2176" href="Categories.Functors.html#2176" class="Bound">F</a> <a id="2178" href="Categories.Functors.html#2038" class="InductiveConstructor Operator">⊗</a> <a id="2180" href="Categories.Functors.html#2180" class="Bound">G</a> <a id="2182" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2185" href="Categories.Functors.html#2185" class="Bound">B</a> <a id="2187" class="Symbol">=</a> <a id="2189" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2191" href="Categories.Functors.html#2176" class="Bound">F</a> <a id="2193" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2196" href="Categories.Functors.html#2185" class="Bound">B</a> <a id="2198" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="2200" href="Categories.Functors.html#2076" class="Function Operator">[</a> <a id="2202" href="Categories.Functors.html#2180" class="Bound">G</a> <a id="2204" href="Categories.Functors.html#2076" class="Function Operator">]₀</a> <a id="2207" href="Categories.Functors.html#2185" class="Bound">B</a>

<a id="2210" class="Keyword">data</a> <a id="Functor"></a><a id="2215" href="Categories.Functors.html#2215" class="Datatype">Functor</a> <a id="2223" class="Symbol">{</a><a id="2224" href="Categories.Functors.html#2224" class="Bound">ℓ</a> <a id="2226" class="Symbol">:</a> <a id="2228" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2233" class="Symbol">}</a> <a id="2235" class="Symbol">:</a> <a id="2237" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2242" class="Symbol">(</a><a id="2243" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2248" href="Categories.Functors.html#2224" class="Bound">ℓ</a><a id="2249" class="Symbol">)</a> <a id="2251" class="Keyword">where</a>
 <a id="Functor.Id"></a><a id="2258" href="Categories.Functors.html#2258" class="InductiveConstructor">Id</a> <a id="2261" class="Symbol">:</a> <a id="2263" href="Categories.Functors.html#2215" class="Datatype">Functor</a>
 <a id="Functor.Const"></a><a id="2272" href="Categories.Functors.html#2272" class="InductiveConstructor">Const</a> <a id="2278" class="Symbol">:</a> <a id="2280" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2285" href="Categories.Functors.html#2224" class="Bound">ℓ</a> <a id="2287" class="Symbol">→</a> <a id="2289" href="Categories.Functors.html#2215" class="Datatype">Functor</a>
 <a id="Functor._⊕_"></a><a id="2298" href="Categories.Functors.html#2298" class="InductiveConstructor Operator">_⊕_</a> <a id="2302" class="Symbol">:</a> <a id="2304" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="2311" class="Symbol">{</a><a id="2312" href="Categories.Functors.html#2224" class="Bound">ℓ</a><a id="2313" class="Symbol">}</a> <a id="2315" class="Symbol">→</a> <a id="2317" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="2324" class="Symbol">{</a><a id="2325" href="Categories.Functors.html#2224" class="Bound">ℓ</a><a id="2326" class="Symbol">}</a> <a id="2328" class="Symbol">→</a> <a id="2330" href="Categories.Functors.html#2215" class="Datatype">Functor</a>
 <a id="Functor._⊗_"></a><a id="2339" href="Categories.Functors.html#2339" class="InductiveConstructor Operator">_⊗_</a> <a id="2343" class="Symbol">:</a> <a id="2345" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="2352" class="Symbol">{</a><a id="2353" href="Categories.Functors.html#2224" class="Bound">ℓ</a><a id="2354" class="Symbol">}</a> <a id="2356" class="Symbol">→</a> <a id="2358" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="2365" class="Symbol">{</a><a id="2366" href="Categories.Functors.html#2224" class="Bound">ℓ</a><a id="2367" class="Symbol">}</a> <a id="2369" class="Symbol">→</a> <a id="2371" href="Categories.Functors.html#2215" class="Datatype">Functor</a>

<a id="[_]_"></a><a id="2380" href="Categories.Functors.html#2380" class="Function Operator">[_]_</a> <a id="2385" class="Symbol">:</a> <a id="2387" href="Categories.Functors.html#2215" class="Datatype">Functor</a> <a id="2395" class="Symbol">→</a> <a id="2397" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2402" href="Categories.Functors.html#1883" class="Generalizable">α</a> <a id="2404" class="Symbol">→</a> <a id="2406" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2411" href="Categories.Functors.html#1883" class="Generalizable">α</a>
<a id="2413" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2415" href="Categories.Functors.html#2258" class="InductiveConstructor">Id</a> <a id="2418" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2420" href="Categories.Functors.html#2420" class="Bound">B</a> <a id="2422" class="Symbol">=</a> <a id="2424" href="Categories.Functors.html#2420" class="Bound">B</a>
<a id="2426" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2428" href="Categories.Functors.html#2272" class="InductiveConstructor">Const</a> <a id="2434" href="Categories.Functors.html#2434" class="Bound">C</a> <a id="2436" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2438" href="Categories.Functors.html#2438" class="Bound">B</a> <a id="2440" class="Symbol">=</a> <a id="2442" href="Categories.Functors.html#2434" class="Bound">C</a>
<a id="2444" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2446" href="Categories.Functors.html#2446" class="Bound">F</a> <a id="2448" href="Categories.Functors.html#2298" class="InductiveConstructor Operator">⊕</a> <a id="2450" href="Categories.Functors.html#2450" class="Bound">G</a> <a id="2452" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2454" href="Categories.Functors.html#2454" class="Bound">B</a> <a id="2456" class="Symbol">=</a> <a id="2458" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2460" href="Categories.Functors.html#2446" class="Bound">F</a> <a id="2462" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2464" href="Categories.Functors.html#2454" class="Bound">B</a> <a id="2466" href="Data.Sum.Base.html#734" class="Datatype Operator">⊎</a> <a id="2468" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2470" href="Categories.Functors.html#2450" class="Bound">G</a> <a id="2472" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2474" href="Categories.Functors.html#2454" class="Bound">B</a>
<a id="2476" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2478" href="Categories.Functors.html#2478" class="Bound">F</a> <a id="2480" href="Categories.Functors.html#2339" class="InductiveConstructor Operator">⊗</a> <a id="2482" href="Categories.Functors.html#2482" class="Bound">G</a> <a id="2484" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2486" href="Categories.Functors.html#2486" class="Bound">B</a> <a id="2488" class="Symbol">=</a> <a id="2490" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2492" href="Categories.Functors.html#2478" class="Bound">F</a> <a id="2494" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2496" href="Categories.Functors.html#2486" class="Bound">B</a> <a id="2498" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="2500" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2502" href="Categories.Functors.html#2482" class="Bound">G</a> <a id="2504" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2506" href="Categories.Functors.html#2486" class="Bound">B</a>

<a id="2509" class="Comment">{- from Mimram&#39;s talk (MFPS 2021):
record Poly (I J : Type) : Type (lsuc ℓ₀) where
 field
  Op : J → Type
  Pm : (i : I) → {j : J} → Op j → Type
-}</a>

</pre>

The least fixed point of a polynomial function can then
be defined in Agda with the following datatype declaration.

<pre class="Agda">

<a id="2801" class="Keyword">data</a> <a id="μ_"></a><a id="2806" href="Categories.Functors.html#2806" class="Datatype Operator">μ_</a> <a id="2809" class="Symbol">(</a><a id="2810" href="Categories.Functors.html#2810" class="Bound">F</a> <a id="2812" class="Symbol">:</a> <a id="2814" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="2821" class="Symbol">)</a> <a id="2823" class="Symbol">:</a> <a id="2825" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="2830" class="Keyword">where</a>
 <a id="μ_.inn"></a><a id="2837" href="Categories.Functors.html#2837" class="InductiveConstructor">inn</a> <a id="2841" class="Symbol">:</a> <a id="2843" href="Categories.Functors.html#2380" class="Function Operator">[</a> <a id="2845" href="Categories.Functors.html#2810" class="Bound">F</a> <a id="2847" href="Categories.Functors.html#2380" class="Function Operator">]</a> <a id="2849" class="Symbol">(</a><a id="2850" href="Categories.Functors.html#2806" class="Datatype Operator">μ</a> <a id="2852" href="Categories.Functors.html#2810" class="Bound">F</a><a id="2853" class="Symbol">)</a> <a id="2855" class="Symbol">→</a> <a id="2857" href="Categories.Functors.html#2806" class="Datatype Operator">μ</a> <a id="2859" href="Categories.Functors.html#2810" class="Bound">F</a>

</pre>

An important example is the polymorphic list datatype. The standard way to define this in Agda is as follows:

<pre class="Agda">

<a id="2999" class="Keyword">data</a> <a id="list"></a><a id="3004" href="Categories.Functors.html#3004" class="Datatype">list</a> <a id="3009" class="Symbol">(</a><a id="3010" href="Categories.Functors.html#3010" class="Bound">A</a> <a id="3012" class="Symbol">:</a> <a id="3014" href="Categories.Functors.html#1442" class="Primitive">Type</a><a id="3018" class="Symbol">)</a> <a id="3020" class="Symbol">:</a> <a id="3022" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="3027" href="Categories.Functors.html#1458" class="Primitive">ℓ₀</a> <a id="3030" class="Keyword">where</a>
 <a id="list.[]"></a><a id="3037" href="Categories.Functors.html#3037" class="InductiveConstructor">[]</a> <a id="3040" class="Symbol">:</a> <a id="3042" href="Categories.Functors.html#3004" class="Datatype">list</a> <a id="3047" href="Categories.Functors.html#3010" class="Bound">A</a>
 <a id="list._∷_"></a><a id="3050" href="Categories.Functors.html#3050" class="InductiveConstructor Operator">_∷_</a> <a id="3054" class="Symbol">:</a> <a id="3056" href="Categories.Functors.html#3010" class="Bound">A</a> <a id="3058" class="Symbol">→</a> <a id="3060" href="Categories.Functors.html#3004" class="Datatype">list</a> <a id="3065" href="Categories.Functors.html#3010" class="Bound">A</a> <a id="3067" class="Symbol">→</a> <a id="3069" href="Categories.Functors.html#3004" class="Datatype">list</a> <a id="3074" href="Categories.Functors.html#3010" class="Bound">A</a>

</pre>

We could instead define a `List` datatype by applying `μ` to a polynomial functor `L` as follows:

<pre class="Agda">

<a id="L"></a><a id="3202" href="Categories.Functors.html#3202" class="Function">L</a> <a id="3204" class="Symbol">:</a> <a id="3206" class="Symbol">{</a><a id="3207" href="Categories.Functors.html#3207" class="Bound">ℓ</a> <a id="3209" class="Symbol">:</a> <a id="3211" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3216" class="Symbol">}(</a><a id="3218" href="Categories.Functors.html#3218" class="Bound">A</a> <a id="3220" class="Symbol">:</a> <a id="3222" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="3227" href="Categories.Functors.html#3207" class="Bound">ℓ</a><a id="3228" class="Symbol">)</a> <a id="3230" class="Symbol">→</a> <a id="3232" href="Categories.Functors.html#2215" class="Datatype">Functor</a><a id="3239" class="Symbol">{</a><a id="3240" href="Categories.Functors.html#3207" class="Bound">ℓ</a><a id="3241" class="Symbol">}</a>
<a id="3243" href="Categories.Functors.html#3202" class="Function">L</a> <a id="3245" href="Categories.Functors.html#3245" class="Bound">A</a> <a id="3247" class="Symbol">=</a> <a id="3249" href="Categories.Functors.html#2272" class="InductiveConstructor">Const</a> <a id="3255" href="Data.Unit.Polymorphic.Base.html#480" class="Function">⊤</a> <a id="3257" href="Categories.Functors.html#2298" class="InductiveConstructor Operator">⊕</a> <a id="3259" class="Symbol">(</a><a id="3260" href="Categories.Functors.html#2272" class="InductiveConstructor">Const</a> <a id="3266" href="Categories.Functors.html#3245" class="Bound">A</a> <a id="3268" href="Categories.Functors.html#2339" class="InductiveConstructor Operator">⊗</a> <a id="3270" href="Categories.Functors.html#2258" class="InductiveConstructor">Id</a><a id="3272" class="Symbol">)</a>

<a id="List"></a><a id="3275" href="Categories.Functors.html#3275" class="Function">List</a> <a id="3280" class="Symbol">:</a> <a id="3282" class="Symbol">(</a><a id="3283" href="Categories.Functors.html#3283" class="Bound">A</a> <a id="3285" class="Symbol">:</a> <a id="3287" href="Categories.Functors.html#1442" class="Primitive">Type</a><a id="3291" class="Symbol">)</a> <a id="3293" class="Symbol">→</a> <a id="3295" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="3300" href="Categories.Functors.html#1458" class="Primitive">ℓ₀</a>
<a id="3303" href="Categories.Functors.html#3275" class="Function">List</a> <a id="3308" href="Categories.Functors.html#3308" class="Bound">A</a> <a id="3310" class="Symbol">=</a> <a id="3312" href="Categories.Functors.html#2806" class="Datatype Operator">μ</a> <a id="3314" class="Symbol">(</a><a id="3315" href="Categories.Functors.html#3202" class="Function">L</a> <a id="3317" href="Categories.Functors.html#3308" class="Bound">A</a><a id="3318" class="Symbol">)</a>

</pre>

To see some examples demonstrating that both formulations of the polymorphic list type give what we expect, see the [Examples.Categories.Functors][] module. The examples will use "getter" functions, which take a list `l` and a natural number `n` and return the element of `l` at index `n`.  (Since such an element doesn't always exist, we first define the `Option` type.)

<pre class="Agda">

<a id="3720" class="Keyword">data</a> <a id="Option"></a><a id="3725" href="Categories.Functors.html#3725" class="Datatype">Option</a> <a id="3732" class="Symbol">(</a><a id="3733" href="Categories.Functors.html#3733" class="Bound">A</a> <a id="3735" class="Symbol">:</a> <a id="3737" href="Categories.Functors.html#1442" class="Primitive">Type</a><a id="3741" class="Symbol">)</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="Categories.Functors.html#1442" class="Primitive">Type</a> <a id="3750" class="Keyword">where</a>
 <a id="Option.some"></a><a id="3757" href="Categories.Functors.html#3757" class="InductiveConstructor">some</a> <a id="3762" class="Symbol">:</a> <a id="3764" href="Categories.Functors.html#3733" class="Bound">A</a> <a id="3766" class="Symbol">→</a> <a id="3768" href="Categories.Functors.html#3725" class="Datatype">Option</a> <a id="3775" href="Categories.Functors.html#3733" class="Bound">A</a>
 <a id="Option.none"></a><a id="3778" href="Categories.Functors.html#3778" class="InductiveConstructor">none</a> <a id="3783" class="Symbol">:</a> <a id="3785" href="Categories.Functors.html#3725" class="Datatype">Option</a> <a id="3792" href="Categories.Functors.html#3733" class="Bound">A</a>

<a id="_[_]"></a><a id="3795" href="Categories.Functors.html#3795" class="Function Operator">_[_]</a> <a id="3800" class="Symbol">:</a> <a id="3802" class="Symbol">{</a><a id="3803" href="Categories.Functors.html#3803" class="Bound">A</a> <a id="3805" class="Symbol">:</a> <a id="3807" href="Categories.Functors.html#1442" class="Primitive">Type</a><a id="3811" class="Symbol">}</a> <a id="3813" class="Symbol">→</a> <a id="3815" href="Categories.Functors.html#3275" class="Function">List</a> <a id="3820" href="Categories.Functors.html#3803" class="Bound">A</a> <a id="3822" class="Symbol">→</a> <a id="3824" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="3826" class="Symbol">→</a> <a id="3828" href="Categories.Functors.html#3725" class="Datatype">Option</a> <a id="3835" href="Categories.Functors.html#3803" class="Bound">A</a>
<a id="3837" href="Categories.Functors.html#2837" class="InductiveConstructor">inn</a> <a id="3841" class="Symbol">(</a><a id="3842" href="Categories.Functors.html#1581" class="InductiveConstructor">inl</a> <a id="3846" href="Categories.Functors.html#3846" class="Bound">x</a><a id="3847" class="Symbol">)</a> <a id="3849" href="Categories.Functors.html#3795" class="Function Operator">[</a> <a id="3851" href="Categories.Functors.html#3851" class="Bound">n</a> <a id="3853" href="Categories.Functors.html#3795" class="Function Operator">]</a> <a id="3855" class="Symbol">=</a> <a id="3857" href="Categories.Functors.html#3778" class="InductiveConstructor">none</a>
<a id="3862" href="Categories.Functors.html#2837" class="InductiveConstructor">inn</a> <a id="3866" class="Symbol">(</a><a id="3867" href="Categories.Functors.html#1596" class="InductiveConstructor">inr</a> <a id="3871" class="Symbol">(</a><a id="3872" href="Categories.Functors.html#3872" class="Bound">x</a> <a id="3874" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3876" href="Categories.Functors.html#3876" class="Bound">xs</a><a id="3878" class="Symbol">))</a> <a id="3881" href="Categories.Functors.html#3795" class="Function Operator">[</a> <a id="3883" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="3888" href="Categories.Functors.html#3795" class="Function Operator">]</a> <a id="3890" class="Symbol">=</a> <a id="3892" href="Categories.Functors.html#3757" class="InductiveConstructor">some</a> <a id="3897" href="Categories.Functors.html#3872" class="Bound">x</a>
<a id="3899" href="Categories.Functors.html#2837" class="InductiveConstructor">inn</a> <a id="3903" class="Symbol">(</a><a id="3904" href="Categories.Functors.html#1596" class="InductiveConstructor">inr</a> <a id="3908" class="Symbol">(</a><a id="3909" href="Categories.Functors.html#3909" class="Bound">x</a> <a id="3911" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3913" href="Categories.Functors.html#3913" class="Bound">xs</a><a id="3915" class="Symbol">))</a> <a id="3918" href="Categories.Functors.html#3795" class="Function Operator">[</a> <a id="3920" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="3924" href="Categories.Functors.html#3924" class="Bound">n</a> <a id="3926" href="Categories.Functors.html#3795" class="Function Operator">]</a> <a id="3928" class="Symbol">=</a> <a id="3930" href="Categories.Functors.html#3913" class="Bound">xs</a> <a id="3933" href="Categories.Functors.html#3795" class="Function Operator">[</a> <a id="3935" href="Categories.Functors.html#3924" class="Bound">n</a> <a id="3937" href="Categories.Functors.html#3795" class="Function Operator">]</a>

<a id="_⟦_⟧"></a><a id="3940" href="Categories.Functors.html#3940" class="Function Operator">_⟦_⟧</a> <a id="3945" class="Symbol">:</a> <a id="3947" class="Symbol">{</a><a id="3948" href="Categories.Functors.html#3948" class="Bound">A</a> <a id="3950" class="Symbol">:</a> <a id="3952" href="Categories.Functors.html#1442" class="Primitive">Type</a><a id="3956" class="Symbol">}</a> <a id="3958" class="Symbol">→</a> <a id="3960" href="Categories.Functors.html#3004" class="Datatype">list</a> <a id="3965" href="Categories.Functors.html#3948" class="Bound">A</a> <a id="3967" class="Symbol">→</a> <a id="3969" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="3971" class="Symbol">→</a> <a id="3973" href="Categories.Functors.html#3725" class="Datatype">Option</a> <a id="3980" href="Categories.Functors.html#3948" class="Bound">A</a>
<a id="3982" href="Categories.Functors.html#3037" class="InductiveConstructor">[]</a> <a id="3985" href="Categories.Functors.html#3940" class="Function Operator">⟦</a> <a id="3987" href="Categories.Functors.html#3987" class="Bound">n</a> <a id="3989" href="Categories.Functors.html#3940" class="Function Operator">⟧</a> <a id="3991" class="Symbol">=</a> <a id="3993" href="Categories.Functors.html#3778" class="InductiveConstructor">none</a>
<a id="3998" class="Symbol">(</a><a id="3999" href="Categories.Functors.html#3999" class="Bound">x</a> <a id="4001" href="Categories.Functors.html#3050" class="InductiveConstructor Operator">∷</a> <a id="4003" href="Categories.Functors.html#4003" class="Bound">l</a><a id="4004" class="Symbol">)</a> <a id="4006" href="Categories.Functors.html#3940" class="Function Operator">⟦</a> <a id="4008" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="4013" href="Categories.Functors.html#3940" class="Function Operator">⟧</a> <a id="4015" class="Symbol">=</a> <a id="4017" href="Categories.Functors.html#3757" class="InductiveConstructor">some</a> <a id="4022" href="Categories.Functors.html#3999" class="Bound">x</a>
<a id="4024" class="Symbol">(</a><a id="4025" href="Categories.Functors.html#4025" class="Bound">x</a> <a id="4027" href="Categories.Functors.html#3050" class="InductiveConstructor Operator">∷</a> <a id="4029" href="Categories.Functors.html#4029" class="Bound">l</a><a id="4030" class="Symbol">)</a> <a id="4032" href="Categories.Functors.html#3940" class="Function Operator">⟦</a> <a id="4034" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="4038" href="Categories.Functors.html#4038" class="Bound">n</a> <a id="4040" href="Categories.Functors.html#3940" class="Function Operator">⟧</a> <a id="4042" class="Symbol">=</a> <a id="4044" href="Categories.Functors.html#4029" class="Bound">l</a> <a id="4046" href="Categories.Functors.html#3940" class="Function Operator">⟦</a> <a id="4048" href="Categories.Functors.html#4038" class="Bound">n</a> <a id="4050" href="Categories.Functors.html#3940" class="Function Operator">⟧</a>

</pre>


--------------------------------

<span style="float:left;">[↑ Categories](Categories.html)</span>
<span style="float:right;">[Complexity →](Complexity.html)</span>

{% include UALib.Links.md %}





<!-- Some helpful excerpts from
     [Modular Type-Safety Proofs in Agda](https://doi.org/10.1145/2428116.2428120)
     by Schwaab and Siek (PLPV '07).

"Our technique is drawn from a solution to the expression problem where languages are defined as the disjoint sum of smaller
languages defined using parameterized recursion. We show that this idea can be recast from types and terms, to proofs."

2. Review of the Expression Problem
Extending both data structures and the functions that operate on them in a modular fashion is challenging, this is
sometimes referred to as the expression problem. In most functional languages, it is easy to add functions that
operate on existing data structures but it is difficult to extend a data type with new constructors.
On the other hand, in object-oriented languages, it is easy to extend data structures by subclassing, but it
is difficult to add new functions to existing classes.

While many solutions to the expression problem have been proposed over the years, here we make use of the
method described by Malcom [9] which generalizes recursion operators such as fold from lists to polynomial types.
The expression problem in functional languages arises as a result of algebraic data types being closed:
once the type has been declared, no new constructors for the type may be added without amending the original declaration.
Malcom's solution is to remove immediate recursion and split a monolithic datatype into parameterized components that
can later be collected under the umbrella of a disjoint sum (i.e., a tagged union)."



"Users of Coq might wonder why the definition of µ is accepted by Agda; Coq would reject the
above definition of µ because it does not pass Coq’s conservative check for positivity. In
this case, Agda's type-checker inspects the behavior of the second argument to [_]_ building
a usage graph and determines that µF will occur positively in [_]_, − ⊎ −, and − × −."
-->


<!--
@inproceedings{10.1145/2428116.2428120,
author = {Schwaab, Christopher and Siek, Jeremy G.},
title = {Modular Type-Safety Proofs in Agda},
year = {2013},
isbn = {9781450318600},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/2428116.2428120},
doi = {10.1145/2428116.2428120},
abstract = {Methods for reusing code are widespread and well researched, but methods for reusing
proofs are still emerging. We consider the use of dependent types for this purpose,
introducing a modular approach for composing mechanized proofs. We show that common
techniques for abstracting algorithms over data structures naturally translate to
abstractions over proofs. We introduce a language composed of a series of smaller
language components, each defined as functors, and tie them together by taking the
fixed point of their sum [Malcom, 1990]. We then give proofs of type preservation
for each language component and show how to compose these proofs into a proof for
the entire language, again by taking the fixed point of a sum of functors.},
booktitle = {Proceedings of the 7th Workshop on Programming Languages Meets Program Verification},
pages = {3–12},
numpages = {10},
keywords = {agda, meta-theory, modularity},
location = {Rome, Italy},
series = {PLPV '13}
} -->
