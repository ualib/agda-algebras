---
layout: default
title : "Base.Categories.Functors module (The Agda Universal Algebra Library)"
date : "2021-08-30"
author: "agda-algebras development team"
---

### <a id="functors">Functors</a>

This is the [Base.Categories.Functors][] module of the [Agda Universal Algebra Library][].

Recall, a *functor* `F` is a function that maps the objects and morphisms of one category `𝒞` to the objects and morphisms of a category `𝒟` in such a way that the following *functor laws* are satisfied:

* `∀ f g, F(f ∘ g) = F(f) ∘ F(g)`
* `∀ A, F(id A) = id (F A)`  (where `id X` denotes the identity morphism on X)


#### <a id="polynomial-functors">Polynomial functors</a>

The main reference for this section is [Modular Type-Safety Proofs in Agda](https://doi.org/10.1145/2428116.2428120) by Schwaab and Siek (PLPV '07).

An important class of functors for our domain is the class of so called *polynomial functors*. These are functors that are built up using the constant, identity, sum, and product functors.  To be precise, the actions of the latter on objects are as follows: `∀ A B` (objects), `∀ F G` (functors),

* `const B A = B`
* `Id A = A`
* `(F + G) A = F A + G A`
* `(F × G) A = F A × G A`

<pre class="Agda">

<a id="1217" class="Symbol">{-#</a> <a id="1221" class="Keyword">OPTIONS</a> <a id="1229" class="Pragma">--without-K</a> <a id="1241" class="Pragma">--exact-split</a> <a id="1255" class="Pragma">--safe</a> <a id="1262" class="Symbol">#-}</a>

<a id="1267" class="Keyword">module</a> <a id="1274" href="Base.Categories.Functors.html" class="Module">Base.Categories.Functors</a> <a id="1299" class="Keyword">where</a>

<a id="1306" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1398" class="Keyword">open</a> <a id="1403" class="Keyword">import</a> <a id="1410" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>                         <a id="1449" class="Keyword">using</a> <a id="1455" class="Symbol">(</a> <a id="1457" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="1461" class="Symbol">;</a> <a id="1463" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1468" class="Symbol">;</a> <a id="1470" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1476" class="Symbol">)</a>
                                                   <a id="1529" class="Keyword">renaming</a> <a id="1538" class="Symbol">(</a> <a id="1540" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1544" class="Symbol">to</a> <a id="1547" class="Primitive">Type</a> <a id="1552" class="Symbol">;</a> <a id="1554" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1560" class="Symbol">to</a> <a id="1563" class="Primitive">ℓ₀</a> <a id="1566" class="Symbol">)</a>
<a id="1568" class="Keyword">open</a> <a id="1573" class="Keyword">import</a> <a id="1580" href="Data.Nat.html" class="Module">Data.Nat</a>                               <a id="1619" class="Keyword">using</a> <a id="1625" class="Symbol">(</a> <a id="1627" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1629" class="Symbol">;</a> <a id="1631" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="1636" class="Symbol">;</a> <a id="1638" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1642" class="Symbol">;</a> <a id="1644" href="Data.Nat.Base.html#2289" class="Function Operator">_&gt;_</a> <a id="1648" class="Symbol">)</a>
<a id="1650" class="Keyword">open</a> <a id="1655" class="Keyword">import</a> <a id="1662" href="Data.Sum.Base.html" class="Module">Data.Sum.Base</a>                          <a id="1701" class="Keyword">using</a> <a id="1707" class="Symbol">(</a> <a id="1709" href="Data.Sum.Base.html#625" class="Datatype Operator">_⊎_</a> <a id="1713" class="Symbol">)</a> <a id="1715" class="Keyword">renaming</a> <a id="1724" class="Symbol">(</a> <a id="1726" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="1731" class="Symbol">to</a> <a id="1734" class="InductiveConstructor">inl</a> <a id="1738" class="Symbol">;</a>  <a id="1741" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="1746" class="Symbol">to</a> <a id="1749" class="InductiveConstructor">inr</a> <a id="1753" class="Symbol">)</a>
<a id="1755" class="Keyword">open</a> <a id="1760" class="Keyword">import</a> <a id="1767" href="Data.Product.html" class="Module">Data.Product</a>                           <a id="1806" class="Keyword">using</a> <a id="1812" class="Symbol">(</a> <a id="1814" href="Data.Product.Base.html#1244" class="Function">Σ-syntax</a> <a id="1823" class="Symbol">;</a> <a id="1825" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">_,_</a> <a id="1829" class="Symbol">;</a> <a id="1831" href="Data.Product.Base.html#1618" class="Function Operator">_×_</a> <a id="1835" class="Symbol">)</a>
<a id="1837" class="Keyword">open</a> <a id="1842" class="Keyword">import</a> <a id="1849" href="Data.Unit.html" class="Module">Data.Unit</a>                              <a id="1888" class="Keyword">using</a> <a id="1894" class="Symbol">(</a> <a id="1896" href="Agda.Builtin.Unit.html#212" class="InductiveConstructor">tt</a> <a id="1899" class="Symbol">)</a> <a id="1901" class="Keyword">renaming</a> <a id="1910" class="Symbol">(</a> <a id="1912" href="Agda.Builtin.Unit.html#175" class="Record">⊤</a> <a id="1914" class="Symbol">to</a> <a id="1917" class="Record">⊤₀</a> <a id="1920" class="Symbol">)</a>
<a id="1922" class="Keyword">open</a> <a id="1927" class="Keyword">import</a> <a id="1934" href="Data.Unit.Polymorphic.html" class="Module">Data.Unit.Polymorphic</a>                  <a id="1973" class="Keyword">using</a> <a id="1979" class="Symbol">(</a> <a id="1981" href="Data.Unit.Polymorphic.Base.html#489" class="Function">⊤</a> <a id="1983" class="Symbol">)</a>
<a id="1985" class="Keyword">open</a> <a id="1990" class="Keyword">import</a> <a id="1997" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>  <a id="2036" class="Keyword">using</a> <a id="2042" class="Symbol">(</a> <a id="2044" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="2048" class="Symbol">;</a> <a id="2050" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="2055" class="Symbol">;</a> <a id="2057" href="Relation.Binary.PropositionalEquality.Core.html#858" class="Function Operator">_≢_</a> <a id="2061" class="Symbol">)</a>
<a id="2063" class="Keyword">open</a> <a id="2068" class="Keyword">import</a> <a id="2075" href="Level.html" class="Module">Level</a>

<a id="2082" class="Keyword">private</a> <a id="2090" class="Keyword">variable</a> <a id="2099" href="Base.Categories.Functors.html#2099" class="Generalizable">α</a> <a id="2101" href="Base.Categories.Functors.html#2101" class="Generalizable">β</a> <a id="2103" class="Symbol">:</a> <a id="2105" href="Agda.Primitive.html#742" class="Postulate">Level</a>

<a id="2112" class="Keyword">infixl</a> <a id="2119" class="Number">6</a> <a id="2121" href="Base.Categories.Functors.html#2515" class="InductiveConstructor Operator">_⊕_</a>
<a id="2125" class="Keyword">infixr</a> <a id="2132" class="Number">7</a> <a id="2134" href="Base.Categories.Functors.html#2556" class="InductiveConstructor Operator">_⊗_</a>

<a id="2139" class="Keyword">data</a> <a id="Functor₀"></a><a id="2144" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2153" class="Symbol">:</a> <a id="2155" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2160" class="Symbol">(</a><a id="2161" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2166" href="Base.Categories.Functors.html#1563" class="Primitive">ℓ₀</a><a id="2168" class="Symbol">)</a> <a id="2170" class="Keyword">where</a>
 <a id="Functor₀.Id"></a><a id="2177" href="Base.Categories.Functors.html#2177" class="InductiveConstructor">Id</a> <a id="2180" class="Symbol">:</a> <a id="2182" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a>
 <a id="Functor₀.Const"></a><a id="2192" href="Base.Categories.Functors.html#2192" class="InductiveConstructor">Const</a> <a id="2198" class="Symbol">:</a> <a id="2200" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2205" class="Symbol">→</a> <a id="2207" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊕_"></a><a id="2217" href="Base.Categories.Functors.html#2217" class="InductiveConstructor Operator">_⊕_</a> <a id="2221" class="Symbol">:</a> <a id="2223" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2232" class="Symbol">→</a> <a id="2234" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2243" class="Symbol">→</a> <a id="2245" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊗_"></a><a id="2255" href="Base.Categories.Functors.html#2255" class="InductiveConstructor Operator">_⊗_</a> <a id="2259" class="Symbol">:</a> <a id="2261" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2270" class="Symbol">→</a> <a id="2272" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2281" class="Symbol">→</a> <a id="2283" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a>

<a id="[_]₀"></a><a id="2293" href="Base.Categories.Functors.html#2293" class="Function Operator">[_]₀</a> <a id="2298" class="Symbol">:</a> <a id="2300" href="Base.Categories.Functors.html#2144" class="Datatype">Functor₀</a> <a id="2309" class="Symbol">→</a> <a id="2311" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2316" class="Symbol">→</a> <a id="2318" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a>
<a id="2323" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2325" href="Base.Categories.Functors.html#2177" class="InductiveConstructor">Id</a> <a id="2328" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2331" href="Base.Categories.Functors.html#2331" class="Bound">B</a> <a id="2333" class="Symbol">=</a> <a id="2335" href="Base.Categories.Functors.html#2331" class="Bound">B</a>
<a id="2337" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2339" href="Base.Categories.Functors.html#2192" class="InductiveConstructor">Const</a> <a id="2345" href="Base.Categories.Functors.html#2345" class="Bound">C</a> <a id="2347" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2350" href="Base.Categories.Functors.html#2350" class="Bound">B</a> <a id="2352" class="Symbol">=</a> <a id="2354" href="Base.Categories.Functors.html#2345" class="Bound">C</a>
<a id="2356" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2358" href="Base.Categories.Functors.html#2358" class="Bound">F</a> <a id="2360" href="Base.Categories.Functors.html#2217" class="InductiveConstructor Operator">⊕</a> <a id="2362" href="Base.Categories.Functors.html#2362" class="Bound">G</a> <a id="2364" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2367" href="Base.Categories.Functors.html#2367" class="Bound">B</a> <a id="2369" class="Symbol">=</a> <a id="2371" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2373" href="Base.Categories.Functors.html#2358" class="Bound">F</a> <a id="2375" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2378" href="Base.Categories.Functors.html#2367" class="Bound">B</a> <a id="2380" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="2382" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2384" href="Base.Categories.Functors.html#2362" class="Bound">G</a> <a id="2386" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2389" href="Base.Categories.Functors.html#2367" class="Bound">B</a>
<a id="2391" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2393" href="Base.Categories.Functors.html#2393" class="Bound">F</a> <a id="2395" href="Base.Categories.Functors.html#2255" class="InductiveConstructor Operator">⊗</a> <a id="2397" href="Base.Categories.Functors.html#2397" class="Bound">G</a> <a id="2399" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2402" href="Base.Categories.Functors.html#2402" class="Bound">B</a> <a id="2404" class="Symbol">=</a> <a id="2406" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2408" href="Base.Categories.Functors.html#2393" class="Bound">F</a> <a id="2410" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2413" href="Base.Categories.Functors.html#2402" class="Bound">B</a> <a id="2415" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="2417" href="Base.Categories.Functors.html#2293" class="Function Operator">[</a> <a id="2419" href="Base.Categories.Functors.html#2397" class="Bound">G</a> <a id="2421" href="Base.Categories.Functors.html#2293" class="Function Operator">]₀</a> <a id="2424" href="Base.Categories.Functors.html#2402" class="Bound">B</a>

<a id="2427" class="Keyword">data</a> <a id="Functor"></a><a id="2432" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a> <a id="2440" class="Symbol">{</a><a id="2441" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a> <a id="2443" class="Symbol">:</a> <a id="2445" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2450" class="Symbol">}</a> <a id="2452" class="Symbol">:</a> <a id="2454" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2459" class="Symbol">(</a><a id="2460" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2465" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a><a id="2466" class="Symbol">)</a> <a id="2468" class="Keyword">where</a>
 <a id="Functor.Id"></a><a id="2475" href="Base.Categories.Functors.html#2475" class="InductiveConstructor">Id</a> <a id="2478" class="Symbol">:</a> <a id="2480" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a>
 <a id="Functor.Const"></a><a id="2489" href="Base.Categories.Functors.html#2489" class="InductiveConstructor">Const</a> <a id="2495" class="Symbol">:</a> <a id="2497" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2502" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a> <a id="2504" class="Symbol">→</a> <a id="2506" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a>
 <a id="Functor._⊕_"></a><a id="2515" href="Base.Categories.Functors.html#2515" class="InductiveConstructor Operator">_⊕_</a> <a id="2519" class="Symbol">:</a> <a id="2521" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="2528" class="Symbol">{</a><a id="2529" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a><a id="2530" class="Symbol">}</a> <a id="2532" class="Symbol">→</a> <a id="2534" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="2541" class="Symbol">{</a><a id="2542" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a><a id="2543" class="Symbol">}</a> <a id="2545" class="Symbol">→</a> <a id="2547" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a>
 <a id="Functor._⊗_"></a><a id="2556" href="Base.Categories.Functors.html#2556" class="InductiveConstructor Operator">_⊗_</a> <a id="2560" class="Symbol">:</a> <a id="2562" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="2569" class="Symbol">{</a><a id="2570" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a><a id="2571" class="Symbol">}</a> <a id="2573" class="Symbol">→</a> <a id="2575" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="2582" class="Symbol">{</a><a id="2583" href="Base.Categories.Functors.html#2441" class="Bound">ℓ</a><a id="2584" class="Symbol">}</a> <a id="2586" class="Symbol">→</a> <a id="2588" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a>

<a id="[_]_"></a><a id="2597" href="Base.Categories.Functors.html#2597" class="Function Operator">[_]_</a> <a id="2602" class="Symbol">:</a> <a id="2604" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a> <a id="2612" class="Symbol">→</a> <a id="2614" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2619" href="Base.Categories.Functors.html#2099" class="Generalizable">α</a> <a id="2621" class="Symbol">→</a> <a id="2623" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="2628" href="Base.Categories.Functors.html#2099" class="Generalizable">α</a>
<a id="2630" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2632" href="Base.Categories.Functors.html#2475" class="InductiveConstructor">Id</a> <a id="2635" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2637" href="Base.Categories.Functors.html#2637" class="Bound">B</a> <a id="2639" class="Symbol">=</a> <a id="2641" href="Base.Categories.Functors.html#2637" class="Bound">B</a>
<a id="2643" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2645" href="Base.Categories.Functors.html#2489" class="InductiveConstructor">Const</a> <a id="2651" href="Base.Categories.Functors.html#2651" class="Bound">C</a> <a id="2653" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2655" href="Base.Categories.Functors.html#2655" class="Bound">B</a> <a id="2657" class="Symbol">=</a> <a id="2659" href="Base.Categories.Functors.html#2651" class="Bound">C</a>
<a id="2661" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2663" href="Base.Categories.Functors.html#2663" class="Bound">F</a> <a id="2665" href="Base.Categories.Functors.html#2515" class="InductiveConstructor Operator">⊕</a> <a id="2667" href="Base.Categories.Functors.html#2667" class="Bound">G</a> <a id="2669" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2671" href="Base.Categories.Functors.html#2671" class="Bound">B</a> <a id="2673" class="Symbol">=</a> <a id="2675" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2677" href="Base.Categories.Functors.html#2663" class="Bound">F</a> <a id="2679" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2681" href="Base.Categories.Functors.html#2671" class="Bound">B</a> <a id="2683" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="2685" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2687" href="Base.Categories.Functors.html#2667" class="Bound">G</a> <a id="2689" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2691" href="Base.Categories.Functors.html#2671" class="Bound">B</a>
<a id="2693" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2695" href="Base.Categories.Functors.html#2695" class="Bound">F</a> <a id="2697" href="Base.Categories.Functors.html#2556" class="InductiveConstructor Operator">⊗</a> <a id="2699" href="Base.Categories.Functors.html#2699" class="Bound">G</a> <a id="2701" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2703" href="Base.Categories.Functors.html#2703" class="Bound">B</a> <a id="2705" class="Symbol">=</a> <a id="2707" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2709" href="Base.Categories.Functors.html#2695" class="Bound">F</a> <a id="2711" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2713" href="Base.Categories.Functors.html#2703" class="Bound">B</a> <a id="2715" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="2717" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="2719" href="Base.Categories.Functors.html#2699" class="Bound">G</a> <a id="2721" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="2723" href="Base.Categories.Functors.html#2703" class="Bound">B</a>

<a id="2726" class="Comment">{- from Mimram&#39;s talk (MFPS 2021):
record Poly (I J : Type) : Type (lsuc ℓ₀) where
 field
  Op : J → Type
  Pm : (i : I) → {j : J} → Op j → Type
-}</a>

</pre>

The least fixed point of a polynomial function can then
be defined in Agda with the following datatype declaration.

<pre class="Agda">

<a id="3018" class="Keyword">data</a> <a id="μ_"></a><a id="3023" href="Base.Categories.Functors.html#3023" class="Datatype Operator">μ_</a> <a id="3026" class="Symbol">(</a><a id="3027" href="Base.Categories.Functors.html#3027" class="Bound">F</a> <a id="3029" class="Symbol">:</a> <a id="3031" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="3038" class="Symbol">)</a> <a id="3040" class="Symbol">:</a> <a id="3042" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="3047" class="Keyword">where</a>
 <a id="μ_.inn"></a><a id="3054" href="Base.Categories.Functors.html#3054" class="InductiveConstructor">inn</a> <a id="3058" class="Symbol">:</a> <a id="3060" href="Base.Categories.Functors.html#2597" class="Function Operator">[</a> <a id="3062" href="Base.Categories.Functors.html#3027" class="Bound">F</a> <a id="3064" href="Base.Categories.Functors.html#2597" class="Function Operator">]</a> <a id="3066" class="Symbol">(</a><a id="3067" href="Base.Categories.Functors.html#3023" class="Datatype Operator">μ</a> <a id="3069" href="Base.Categories.Functors.html#3027" class="Bound">F</a><a id="3070" class="Symbol">)</a> <a id="3072" class="Symbol">→</a> <a id="3074" href="Base.Categories.Functors.html#3023" class="Datatype Operator">μ</a> <a id="3076" href="Base.Categories.Functors.html#3027" class="Bound">F</a>

</pre>

An important example is the polymorphic list datatype. The standard way to define this in Agda is as follows:

<pre class="Agda">

<a id="3216" class="Keyword">data</a> <a id="list"></a><a id="3221" href="Base.Categories.Functors.html#3221" class="Datatype">list</a> <a id="3226" class="Symbol">(</a><a id="3227" href="Base.Categories.Functors.html#3227" class="Bound">A</a> <a id="3229" class="Symbol">:</a> <a id="3231" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a><a id="3235" class="Symbol">)</a> <a id="3237" class="Symbol">:</a> <a id="3239" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="3244" href="Base.Categories.Functors.html#1563" class="Primitive">ℓ₀</a> <a id="3247" class="Keyword">where</a>
 <a id="list.[]"></a><a id="3254" href="Base.Categories.Functors.html#3254" class="InductiveConstructor">[]</a> <a id="3257" class="Symbol">:</a> <a id="3259" href="Base.Categories.Functors.html#3221" class="Datatype">list</a> <a id="3264" href="Base.Categories.Functors.html#3227" class="Bound">A</a>
 <a id="list._∷_"></a><a id="3267" href="Base.Categories.Functors.html#3267" class="InductiveConstructor Operator">_∷_</a> <a id="3271" class="Symbol">:</a> <a id="3273" href="Base.Categories.Functors.html#3227" class="Bound">A</a> <a id="3275" class="Symbol">→</a> <a id="3277" href="Base.Categories.Functors.html#3221" class="Datatype">list</a> <a id="3282" href="Base.Categories.Functors.html#3227" class="Bound">A</a> <a id="3284" class="Symbol">→</a> <a id="3286" href="Base.Categories.Functors.html#3221" class="Datatype">list</a> <a id="3291" href="Base.Categories.Functors.html#3227" class="Bound">A</a>

</pre>

We could instead define a `List` datatype by applying `μ` to a polynomial functor `L` as follows:

<pre class="Agda">

<a id="L"></a><a id="3419" href="Base.Categories.Functors.html#3419" class="Function">L</a> <a id="3421" class="Symbol">:</a> <a id="3423" class="Symbol">{</a><a id="3424" href="Base.Categories.Functors.html#3424" class="Bound">ℓ</a> <a id="3426" class="Symbol">:</a> <a id="3428" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3433" class="Symbol">}(</a><a id="3435" href="Base.Categories.Functors.html#3435" class="Bound">A</a> <a id="3437" class="Symbol">:</a> <a id="3439" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="3444" href="Base.Categories.Functors.html#3424" class="Bound">ℓ</a><a id="3445" class="Symbol">)</a> <a id="3447" class="Symbol">→</a> <a id="3449" href="Base.Categories.Functors.html#2432" class="Datatype">Functor</a><a id="3456" class="Symbol">{</a><a id="3457" href="Base.Categories.Functors.html#3424" class="Bound">ℓ</a><a id="3458" class="Symbol">}</a>
<a id="3460" href="Base.Categories.Functors.html#3419" class="Function">L</a> <a id="3462" href="Base.Categories.Functors.html#3462" class="Bound">A</a> <a id="3464" class="Symbol">=</a> <a id="3466" href="Base.Categories.Functors.html#2489" class="InductiveConstructor">Const</a> <a id="3472" href="Data.Unit.Polymorphic.Base.html#489" class="Function">⊤</a> <a id="3474" href="Base.Categories.Functors.html#2515" class="InductiveConstructor Operator">⊕</a> <a id="3476" class="Symbol">(</a><a id="3477" href="Base.Categories.Functors.html#2489" class="InductiveConstructor">Const</a> <a id="3483" href="Base.Categories.Functors.html#3462" class="Bound">A</a> <a id="3485" href="Base.Categories.Functors.html#2556" class="InductiveConstructor Operator">⊗</a> <a id="3487" href="Base.Categories.Functors.html#2475" class="InductiveConstructor">Id</a><a id="3489" class="Symbol">)</a>

<a id="List"></a><a id="3492" href="Base.Categories.Functors.html#3492" class="Function">List</a> <a id="3497" class="Symbol">:</a> <a id="3499" class="Symbol">(</a><a id="3500" href="Base.Categories.Functors.html#3500" class="Bound">A</a> <a id="3502" class="Symbol">:</a> <a id="3504" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a><a id="3508" class="Symbol">)</a> <a id="3510" class="Symbol">→</a> <a id="3512" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="3517" href="Base.Categories.Functors.html#1563" class="Primitive">ℓ₀</a>
<a id="3520" href="Base.Categories.Functors.html#3492" class="Function">List</a> <a id="3525" href="Base.Categories.Functors.html#3525" class="Bound">A</a> <a id="3527" class="Symbol">=</a> <a id="3529" href="Base.Categories.Functors.html#3023" class="Datatype Operator">μ</a> <a id="3531" class="Symbol">(</a><a id="3532" href="Base.Categories.Functors.html#3419" class="Function">L</a> <a id="3534" href="Base.Categories.Functors.html#3525" class="Bound">A</a><a id="3535" class="Symbol">)</a>

</pre>

To see some examples demonstrating that both formulations of the polymorphic list type give what we expect, see the [Examples.Categories.Functors][] module. The examples will use "getter" functions, which take a list `l` and a natural number `n` and return the element of `l` at index `n`.  (Since such an element doesn't always exist, we first define the `Option` type.)

<pre class="Agda">

<a id="3937" class="Keyword">data</a> <a id="Option"></a><a id="3942" href="Base.Categories.Functors.html#3942" class="Datatype">Option</a> <a id="3949" class="Symbol">(</a><a id="3950" href="Base.Categories.Functors.html#3950" class="Bound">A</a> <a id="3952" class="Symbol">:</a> <a id="3954" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a><a id="3958" class="Symbol">)</a> <a id="3960" class="Symbol">:</a> <a id="3962" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a> <a id="3967" class="Keyword">where</a>
 <a id="Option.some"></a><a id="3974" href="Base.Categories.Functors.html#3974" class="InductiveConstructor">some</a> <a id="3979" class="Symbol">:</a> <a id="3981" href="Base.Categories.Functors.html#3950" class="Bound">A</a> <a id="3983" class="Symbol">→</a> <a id="3985" href="Base.Categories.Functors.html#3942" class="Datatype">Option</a> <a id="3992" href="Base.Categories.Functors.html#3950" class="Bound">A</a>
 <a id="Option.none"></a><a id="3995" href="Base.Categories.Functors.html#3995" class="InductiveConstructor">none</a> <a id="4000" class="Symbol">:</a> <a id="4002" href="Base.Categories.Functors.html#3942" class="Datatype">Option</a> <a id="4009" href="Base.Categories.Functors.html#3950" class="Bound">A</a>

<a id="_[_]"></a><a id="4012" href="Base.Categories.Functors.html#4012" class="Function Operator">_[_]</a> <a id="4017" class="Symbol">:</a> <a id="4019" class="Symbol">{</a><a id="4020" href="Base.Categories.Functors.html#4020" class="Bound">A</a> <a id="4022" class="Symbol">:</a> <a id="4024" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a><a id="4028" class="Symbol">}</a> <a id="4030" class="Symbol">→</a> <a id="4032" href="Base.Categories.Functors.html#3492" class="Function">List</a> <a id="4037" href="Base.Categories.Functors.html#4020" class="Bound">A</a> <a id="4039" class="Symbol">→</a> <a id="4041" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4043" class="Symbol">→</a> <a id="4045" href="Base.Categories.Functors.html#3942" class="Datatype">Option</a> <a id="4052" href="Base.Categories.Functors.html#4020" class="Bound">A</a>
<a id="4054" href="Base.Categories.Functors.html#3054" class="InductiveConstructor">inn</a> <a id="4058" class="Symbol">(</a><a id="4059" href="Base.Categories.Functors.html#1734" class="InductiveConstructor">inl</a> <a id="4063" href="Base.Categories.Functors.html#4063" class="Bound">x</a><a id="4064" class="Symbol">)</a> <a id="4066" href="Base.Categories.Functors.html#4012" class="Function Operator">[</a> <a id="4068" href="Base.Categories.Functors.html#4068" class="Bound">n</a> <a id="4070" href="Base.Categories.Functors.html#4012" class="Function Operator">]</a> <a id="4072" class="Symbol">=</a> <a id="4074" href="Base.Categories.Functors.html#3995" class="InductiveConstructor">none</a>
<a id="4079" href="Base.Categories.Functors.html#3054" class="InductiveConstructor">inn</a> <a id="4083" class="Symbol">(</a><a id="4084" href="Base.Categories.Functors.html#1749" class="InductiveConstructor">inr</a> <a id="4088" class="Symbol">(</a><a id="4089" href="Base.Categories.Functors.html#4089" class="Bound">x</a> <a id="4091" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4093" href="Base.Categories.Functors.html#4093" class="Bound">xs</a><a id="4095" class="Symbol">))</a> <a id="4098" href="Base.Categories.Functors.html#4012" class="Function Operator">[</a> <a id="4100" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4105" href="Base.Categories.Functors.html#4012" class="Function Operator">]</a> <a id="4107" class="Symbol">=</a> <a id="4109" href="Base.Categories.Functors.html#3974" class="InductiveConstructor">some</a> <a id="4114" href="Base.Categories.Functors.html#4089" class="Bound">x</a>
<a id="4116" href="Base.Categories.Functors.html#3054" class="InductiveConstructor">inn</a> <a id="4120" class="Symbol">(</a><a id="4121" href="Base.Categories.Functors.html#1749" class="InductiveConstructor">inr</a> <a id="4125" class="Symbol">(</a><a id="4126" href="Base.Categories.Functors.html#4126" class="Bound">x</a> <a id="4128" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4130" href="Base.Categories.Functors.html#4130" class="Bound">xs</a><a id="4132" class="Symbol">))</a> <a id="4135" href="Base.Categories.Functors.html#4012" class="Function Operator">[</a> <a id="4137" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4141" href="Base.Categories.Functors.html#4141" class="Bound">n</a> <a id="4143" href="Base.Categories.Functors.html#4012" class="Function Operator">]</a> <a id="4145" class="Symbol">=</a> <a id="4147" href="Base.Categories.Functors.html#4130" class="Bound">xs</a> <a id="4150" href="Base.Categories.Functors.html#4012" class="Function Operator">[</a> <a id="4152" href="Base.Categories.Functors.html#4141" class="Bound">n</a> <a id="4154" href="Base.Categories.Functors.html#4012" class="Function Operator">]</a>

<a id="_⟦_⟧"></a><a id="4157" href="Base.Categories.Functors.html#4157" class="Function Operator">_⟦_⟧</a> <a id="4162" class="Symbol">:</a> <a id="4164" class="Symbol">{</a><a id="4165" href="Base.Categories.Functors.html#4165" class="Bound">A</a> <a id="4167" class="Symbol">:</a> <a id="4169" href="Base.Categories.Functors.html#1547" class="Primitive">Type</a><a id="4173" class="Symbol">}</a> <a id="4175" class="Symbol">→</a> <a id="4177" href="Base.Categories.Functors.html#3221" class="Datatype">list</a> <a id="4182" href="Base.Categories.Functors.html#4165" class="Bound">A</a> <a id="4184" class="Symbol">→</a> <a id="4186" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4188" class="Symbol">→</a> <a id="4190" href="Base.Categories.Functors.html#3942" class="Datatype">Option</a> <a id="4197" href="Base.Categories.Functors.html#4165" class="Bound">A</a>
<a id="4199" href="Base.Categories.Functors.html#3254" class="InductiveConstructor">[]</a> <a id="4202" href="Base.Categories.Functors.html#4157" class="Function Operator">⟦</a> <a id="4204" href="Base.Categories.Functors.html#4204" class="Bound">n</a> <a id="4206" href="Base.Categories.Functors.html#4157" class="Function Operator">⟧</a> <a id="4208" class="Symbol">=</a> <a id="4210" href="Base.Categories.Functors.html#3995" class="InductiveConstructor">none</a>
<a id="4215" class="Symbol">(</a><a id="4216" href="Base.Categories.Functors.html#4216" class="Bound">x</a> <a id="4218" href="Base.Categories.Functors.html#3267" class="InductiveConstructor Operator">∷</a> <a id="4220" href="Base.Categories.Functors.html#4220" class="Bound">l</a><a id="4221" class="Symbol">)</a> <a id="4223" href="Base.Categories.Functors.html#4157" class="Function Operator">⟦</a> <a id="4225" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4230" href="Base.Categories.Functors.html#4157" class="Function Operator">⟧</a> <a id="4232" class="Symbol">=</a> <a id="4234" href="Base.Categories.Functors.html#3974" class="InductiveConstructor">some</a> <a id="4239" href="Base.Categories.Functors.html#4216" class="Bound">x</a>
<a id="4241" class="Symbol">(</a><a id="4242" href="Base.Categories.Functors.html#4242" class="Bound">x</a> <a id="4244" href="Base.Categories.Functors.html#3267" class="InductiveConstructor Operator">∷</a> <a id="4246" href="Base.Categories.Functors.html#4246" class="Bound">l</a><a id="4247" class="Symbol">)</a> <a id="4249" href="Base.Categories.Functors.html#4157" class="Function Operator">⟦</a> <a id="4251" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4255" href="Base.Categories.Functors.html#4255" class="Bound">n</a> <a id="4257" href="Base.Categories.Functors.html#4157" class="Function Operator">⟧</a> <a id="4259" class="Symbol">=</a> <a id="4261" href="Base.Categories.Functors.html#4246" class="Bound">l</a> <a id="4263" href="Base.Categories.Functors.html#4157" class="Function Operator">⟦</a> <a id="4265" href="Base.Categories.Functors.html#4255" class="Bound">n</a> <a id="4267" href="Base.Categories.Functors.html#4157" class="Function Operator">⟧</a>

</pre>


--------------------------------

<span style="float:left;">[↑ Base.Categories](Base.Categories.html)</span>
<span style="float:right;">[Base.Complexity →](Base.Complexity.html)</span>

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
