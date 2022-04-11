---
layout: default
title : "Base.Categories.Functors module (The Agda Universal Algebra Library)"
date : "2021-08-30"
author: "agda-algebras development team"
---

### <a id="functors">Functors</a>

This is the [Base.Categories.Functors][] module of the [Agda Universal Algebra Library][].

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

<a id="1202" class="Symbol">{-#</a> <a id="1206" class="Keyword">OPTIONS</a> <a id="1214" class="Pragma">--without-K</a> <a id="1226" class="Pragma">--exact-split</a> <a id="1240" class="Pragma">--safe</a> <a id="1247" class="Symbol">#-}</a>

<a id="1252" class="Keyword">module</a> <a id="1259" href="Base.Categories.Functors.html" class="Module">Base.Categories.Functors</a> <a id="1284" class="Keyword">where</a>

<a id="1291" class="Comment">-- Imports from Agda and the Agda Standard Library  ---------------------------------------</a>
<a id="1383" class="Keyword">open</a> <a id="1388" class="Keyword">import</a> <a id="1395" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="1410" class="Keyword">using</a> <a id="1416" class="Symbol">(</a> <a id="1418" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="1422" class="Symbol">;</a> <a id="1424" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1429" class="Symbol">;</a> <a id="1431" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="1437" class="Symbol">)</a> <a id="1439" class="Keyword">renaming</a> <a id="1448" class="Symbol">(</a> <a id="1450" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="1454" class="Symbol">to</a> <a id="1457" class="Primitive">Type</a> <a id="1462" class="Symbol">;</a> <a id="1464" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="1470" class="Symbol">to</a> <a id="1473" class="Primitive">ℓ₀</a> <a id="1476" class="Symbol">)</a>
<a id="1478" class="Keyword">open</a> <a id="1483" class="Keyword">import</a> <a id="1490" href="Data.Nat.html" class="Module">Data.Nat</a>       <a id="1505" class="Keyword">using</a> <a id="1511" class="Symbol">(</a> <a id="1513" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="1515" class="Symbol">;</a> <a id="1517" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="1522" class="Symbol">;</a> <a id="1524" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="1528" class="Symbol">;</a> <a id="1530" href="Data.Nat.Base.html#1709" class="Function Operator">_&gt;_</a> <a id="1534" class="Symbol">)</a>
<a id="1536" class="Keyword">open</a> <a id="1541" class="Keyword">import</a> <a id="1548" href="Data.Sum.Base.html" class="Module">Data.Sum.Base</a>  <a id="1563" class="Keyword">using</a> <a id="1569" class="Symbol">(</a> <a id="1571" href="Data.Sum.Base.html#734" class="Datatype Operator">_⊎_</a> <a id="1575" class="Symbol">)</a> <a id="1577" class="Keyword">renaming</a> <a id="1586" class="Symbol">(</a> <a id="1588" href="Data.Sum.Base.html#784" class="InductiveConstructor">inj₁</a> <a id="1593" class="Symbol">to</a> <a id="1596" class="InductiveConstructor">inl</a> <a id="1600" class="Symbol">;</a>  <a id="1603" href="Data.Sum.Base.html#809" class="InductiveConstructor">inj₂</a> <a id="1608" class="Symbol">to</a> <a id="1611" class="InductiveConstructor">inr</a> <a id="1615" class="Symbol">)</a>
<a id="1617" class="Keyword">open</a> <a id="1622" class="Keyword">import</a> <a id="1629" href="Data.Product.html" class="Module">Data.Product</a>   <a id="1644" class="Keyword">using</a> <a id="1650" class="Symbol">(</a> <a id="1652" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="1661" class="Symbol">;</a> <a id="1663" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="1667" class="Symbol">;</a> <a id="1669" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="1673" class="Symbol">)</a>
<a id="1675" class="Keyword">open</a> <a id="1680" class="Keyword">import</a> <a id="1687" href="Data.Unit.html" class="Module">Data.Unit</a>      <a id="1702" class="Keyword">using</a> <a id="1708" class="Symbol">(</a> <a id="1710" href="Agda.Builtin.Unit.html#201" class="InductiveConstructor">tt</a> <a id="1713" class="Symbol">)</a> <a id="1715" class="Keyword">renaming</a> <a id="1724" class="Symbol">(</a> <a id="1726" href="Agda.Builtin.Unit.html#164" class="Record">⊤</a> <a id="1728" class="Symbol">to</a> <a id="1731" class="Record">⊤₀</a> <a id="1734" class="Symbol">)</a>
<a id="1736" class="Keyword">open</a> <a id="1741" class="Keyword">import</a> <a id="1748" href="Data.Unit.Polymorphic.html" class="Module">Data.Unit.Polymorphic</a>  <a id="1771" class="Keyword">using</a> <a id="1777" class="Symbol">(</a> <a id="1779" href="Data.Unit.Polymorphic.Base.html#480" class="Function">⊤</a> <a id="1781" class="Symbol">)</a>
<a id="1783" class="Keyword">open</a> <a id="1788" class="Keyword">import</a> <a id="1795" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>  <a id="1834" class="Keyword">using</a> <a id="1840" class="Symbol">(</a> <a id="1842" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="1846" class="Symbol">;</a> <a id="1848" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1853" class="Symbol">;</a> <a id="1855" href="Relation.Binary.PropositionalEquality.Core.html#830" class="Function Operator">_≢_</a> <a id="1859" class="Symbol">)</a>
<a id="1861" class="Keyword">open</a> <a id="1866" class="Keyword">import</a> <a id="1873" href="Level.html" class="Module">Level</a>

<a id="1880" class="Keyword">private</a> <a id="1888" class="Keyword">variable</a>
 <a id="1898" href="Base.Categories.Functors.html#1898" class="Generalizable">α</a> <a id="1900" href="Base.Categories.Functors.html#1900" class="Generalizable">β</a> <a id="1902" class="Symbol">:</a> <a id="1904" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="1911" class="Keyword">infixl</a> <a id="1918" class="Number">6</a> <a id="1920" href="Base.Categories.Functors.html#2313" class="InductiveConstructor Operator">_⊕_</a>
<a id="1924" class="Keyword">infixr</a> <a id="1931" class="Number">7</a> <a id="1933" href="Base.Categories.Functors.html#2354" class="InductiveConstructor Operator">_⊗_</a>
<a id="1937" class="Keyword">data</a> <a id="Functor₀"></a><a id="1942" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="1958" class="Symbol">(</a><a id="1959" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1964" href="Base.Categories.Functors.html#1473" class="Primitive">ℓ₀</a><a id="1966" class="Symbol">)</a> <a id="1968" class="Keyword">where</a>
 <a id="Functor₀.Id"></a><a id="1975" href="Base.Categories.Functors.html#1975" class="InductiveConstructor">Id</a> <a id="1978" class="Symbol">:</a> <a id="1980" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a>
 <a id="Functor₀.Const"></a><a id="1990" href="Base.Categories.Functors.html#1990" class="InductiveConstructor">Const</a> <a id="1996" class="Symbol">:</a> <a id="1998" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2003" class="Symbol">→</a> <a id="2005" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊕_"></a><a id="2015" href="Base.Categories.Functors.html#2015" class="InductiveConstructor Operator">_⊕_</a> <a id="2019" class="Symbol">:</a> <a id="2021" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="2030" class="Symbol">→</a> <a id="2032" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="2041" class="Symbol">→</a> <a id="2043" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a>
 <a id="Functor₀._⊗_"></a><a id="2053" href="Base.Categories.Functors.html#2053" class="InductiveConstructor Operator">_⊗_</a> <a id="2057" class="Symbol">:</a> <a id="2059" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="2068" class="Symbol">→</a> <a id="2070" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="2079" class="Symbol">→</a> <a id="2081" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a>

<a id="[_]₀"></a><a id="2091" href="Base.Categories.Functors.html#2091" class="Function Operator">[_]₀</a> <a id="2096" class="Symbol">:</a> <a id="2098" href="Base.Categories.Functors.html#1942" class="Datatype">Functor₀</a> <a id="2107" class="Symbol">→</a> <a id="2109" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2114" class="Symbol">→</a> <a id="2116" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a>
<a id="2121" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2123" href="Base.Categories.Functors.html#1975" class="InductiveConstructor">Id</a> <a id="2126" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2129" href="Base.Categories.Functors.html#2129" class="Bound">B</a> <a id="2131" class="Symbol">=</a> <a id="2133" href="Base.Categories.Functors.html#2129" class="Bound">B</a>
<a id="2135" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2137" href="Base.Categories.Functors.html#1990" class="InductiveConstructor">Const</a> <a id="2143" href="Base.Categories.Functors.html#2143" class="Bound">C</a> <a id="2145" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2148" href="Base.Categories.Functors.html#2148" class="Bound">B</a> <a id="2150" class="Symbol">=</a> <a id="2152" href="Base.Categories.Functors.html#2143" class="Bound">C</a>
<a id="2154" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2156" href="Base.Categories.Functors.html#2156" class="Bound">F</a> <a id="2158" href="Base.Categories.Functors.html#2015" class="InductiveConstructor Operator">⊕</a> <a id="2160" href="Base.Categories.Functors.html#2160" class="Bound">G</a> <a id="2162" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2165" href="Base.Categories.Functors.html#2165" class="Bound">B</a> <a id="2167" class="Symbol">=</a> <a id="2169" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2171" href="Base.Categories.Functors.html#2156" class="Bound">F</a> <a id="2173" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2176" href="Base.Categories.Functors.html#2165" class="Bound">B</a> <a id="2178" href="Data.Sum.Base.html#734" class="Datatype Operator">⊎</a> <a id="2180" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2182" href="Base.Categories.Functors.html#2160" class="Bound">G</a> <a id="2184" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2187" href="Base.Categories.Functors.html#2165" class="Bound">B</a>
<a id="2189" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2191" href="Base.Categories.Functors.html#2191" class="Bound">F</a> <a id="2193" href="Base.Categories.Functors.html#2053" class="InductiveConstructor Operator">⊗</a> <a id="2195" href="Base.Categories.Functors.html#2195" class="Bound">G</a> <a id="2197" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2200" href="Base.Categories.Functors.html#2200" class="Bound">B</a> <a id="2202" class="Symbol">=</a> <a id="2204" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2206" href="Base.Categories.Functors.html#2191" class="Bound">F</a> <a id="2208" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2211" href="Base.Categories.Functors.html#2200" class="Bound">B</a> <a id="2213" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="2215" href="Base.Categories.Functors.html#2091" class="Function Operator">[</a> <a id="2217" href="Base.Categories.Functors.html#2195" class="Bound">G</a> <a id="2219" href="Base.Categories.Functors.html#2091" class="Function Operator">]₀</a> <a id="2222" href="Base.Categories.Functors.html#2200" class="Bound">B</a>

<a id="2225" class="Keyword">data</a> <a id="Functor"></a><a id="2230" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a> <a id="2238" class="Symbol">{</a><a id="2239" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a> <a id="2241" class="Symbol">:</a> <a id="2243" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2248" class="Symbol">}</a> <a id="2250" class="Symbol">:</a> <a id="2252" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2257" class="Symbol">(</a><a id="2258" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2263" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a><a id="2264" class="Symbol">)</a> <a id="2266" class="Keyword">where</a>
 <a id="Functor.Id"></a><a id="2273" href="Base.Categories.Functors.html#2273" class="InductiveConstructor">Id</a> <a id="2276" class="Symbol">:</a> <a id="2278" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a>
 <a id="Functor.Const"></a><a id="2287" href="Base.Categories.Functors.html#2287" class="InductiveConstructor">Const</a> <a id="2293" class="Symbol">:</a> <a id="2295" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2300" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a> <a id="2302" class="Symbol">→</a> <a id="2304" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a>
 <a id="Functor._⊕_"></a><a id="2313" href="Base.Categories.Functors.html#2313" class="InductiveConstructor Operator">_⊕_</a> <a id="2317" class="Symbol">:</a> <a id="2319" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="2326" class="Symbol">{</a><a id="2327" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a><a id="2328" class="Symbol">}</a> <a id="2330" class="Symbol">→</a> <a id="2332" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="2339" class="Symbol">{</a><a id="2340" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a><a id="2341" class="Symbol">}</a> <a id="2343" class="Symbol">→</a> <a id="2345" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a>
 <a id="Functor._⊗_"></a><a id="2354" href="Base.Categories.Functors.html#2354" class="InductiveConstructor Operator">_⊗_</a> <a id="2358" class="Symbol">:</a> <a id="2360" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="2367" class="Symbol">{</a><a id="2368" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a><a id="2369" class="Symbol">}</a> <a id="2371" class="Symbol">→</a> <a id="2373" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="2380" class="Symbol">{</a><a id="2381" href="Base.Categories.Functors.html#2239" class="Bound">ℓ</a><a id="2382" class="Symbol">}</a> <a id="2384" class="Symbol">→</a> <a id="2386" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a>

<a id="[_]_"></a><a id="2395" href="Base.Categories.Functors.html#2395" class="Function Operator">[_]_</a> <a id="2400" class="Symbol">:</a> <a id="2402" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a> <a id="2410" class="Symbol">→</a> <a id="2412" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2417" href="Base.Categories.Functors.html#1898" class="Generalizable">α</a> <a id="2419" class="Symbol">→</a> <a id="2421" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2426" href="Base.Categories.Functors.html#1898" class="Generalizable">α</a>
<a id="2428" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2430" href="Base.Categories.Functors.html#2273" class="InductiveConstructor">Id</a> <a id="2433" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2435" href="Base.Categories.Functors.html#2435" class="Bound">B</a> <a id="2437" class="Symbol">=</a> <a id="2439" href="Base.Categories.Functors.html#2435" class="Bound">B</a>
<a id="2441" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2443" href="Base.Categories.Functors.html#2287" class="InductiveConstructor">Const</a> <a id="2449" href="Base.Categories.Functors.html#2449" class="Bound">C</a> <a id="2451" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2453" href="Base.Categories.Functors.html#2453" class="Bound">B</a> <a id="2455" class="Symbol">=</a> <a id="2457" href="Base.Categories.Functors.html#2449" class="Bound">C</a>
<a id="2459" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2461" href="Base.Categories.Functors.html#2461" class="Bound">F</a> <a id="2463" href="Base.Categories.Functors.html#2313" class="InductiveConstructor Operator">⊕</a> <a id="2465" href="Base.Categories.Functors.html#2465" class="Bound">G</a> <a id="2467" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2469" href="Base.Categories.Functors.html#2469" class="Bound">B</a> <a id="2471" class="Symbol">=</a> <a id="2473" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2475" href="Base.Categories.Functors.html#2461" class="Bound">F</a> <a id="2477" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2479" href="Base.Categories.Functors.html#2469" class="Bound">B</a> <a id="2481" href="Data.Sum.Base.html#734" class="Datatype Operator">⊎</a> <a id="2483" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2485" href="Base.Categories.Functors.html#2465" class="Bound">G</a> <a id="2487" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2489" href="Base.Categories.Functors.html#2469" class="Bound">B</a>
<a id="2491" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2493" href="Base.Categories.Functors.html#2493" class="Bound">F</a> <a id="2495" href="Base.Categories.Functors.html#2354" class="InductiveConstructor Operator">⊗</a> <a id="2497" href="Base.Categories.Functors.html#2497" class="Bound">G</a> <a id="2499" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2501" href="Base.Categories.Functors.html#2501" class="Bound">B</a> <a id="2503" class="Symbol">=</a> <a id="2505" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2507" href="Base.Categories.Functors.html#2493" class="Bound">F</a> <a id="2509" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2511" href="Base.Categories.Functors.html#2501" class="Bound">B</a> <a id="2513" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="2515" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2517" href="Base.Categories.Functors.html#2497" class="Bound">G</a> <a id="2519" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2521" href="Base.Categories.Functors.html#2501" class="Bound">B</a>

<a id="2524" class="Comment">{- from Mimram&#39;s talk (MFPS 2021):
record Poly (I J : Type) : Type (lsuc ℓ₀) where
 field
  Op : J → Type
  Pm : (i : I) → {j : J} → Op j → Type
-}</a>

</pre>

The least fixed point of a polynomial function can then
be defined in Agda with the following datatype declaration.

<pre class="Agda">

<a id="2816" class="Keyword">data</a> <a id="μ_"></a><a id="2821" href="Base.Categories.Functors.html#2821" class="Datatype Operator">μ_</a> <a id="2824" class="Symbol">(</a><a id="2825" href="Base.Categories.Functors.html#2825" class="Bound">F</a> <a id="2827" class="Symbol">:</a> <a id="2829" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="2836" class="Symbol">)</a> <a id="2838" class="Symbol">:</a> <a id="2840" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="2845" class="Keyword">where</a>
 <a id="μ_.inn"></a><a id="2852" href="Base.Categories.Functors.html#2852" class="InductiveConstructor">inn</a> <a id="2856" class="Symbol">:</a> <a id="2858" href="Base.Categories.Functors.html#2395" class="Function Operator">[</a> <a id="2860" href="Base.Categories.Functors.html#2825" class="Bound">F</a> <a id="2862" href="Base.Categories.Functors.html#2395" class="Function Operator">]</a> <a id="2864" class="Symbol">(</a><a id="2865" href="Base.Categories.Functors.html#2821" class="Datatype Operator">μ</a> <a id="2867" href="Base.Categories.Functors.html#2825" class="Bound">F</a><a id="2868" class="Symbol">)</a> <a id="2870" class="Symbol">→</a> <a id="2872" href="Base.Categories.Functors.html#2821" class="Datatype Operator">μ</a> <a id="2874" href="Base.Categories.Functors.html#2825" class="Bound">F</a>

</pre>

An important example is the polymorphic list datatype. The standard way to define this in Agda is as follows:

<pre class="Agda">

<a id="3014" class="Keyword">data</a> <a id="list"></a><a id="3019" href="Base.Categories.Functors.html#3019" class="Datatype">list</a> <a id="3024" class="Symbol">(</a><a id="3025" href="Base.Categories.Functors.html#3025" class="Bound">A</a> <a id="3027" class="Symbol">:</a> <a id="3029" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a><a id="3033" class="Symbol">)</a> <a id="3035" class="Symbol">:</a> <a id="3037" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="3042" href="Base.Categories.Functors.html#1473" class="Primitive">ℓ₀</a> <a id="3045" class="Keyword">where</a>
 <a id="list.[]"></a><a id="3052" href="Base.Categories.Functors.html#3052" class="InductiveConstructor">[]</a> <a id="3055" class="Symbol">:</a> <a id="3057" href="Base.Categories.Functors.html#3019" class="Datatype">list</a> <a id="3062" href="Base.Categories.Functors.html#3025" class="Bound">A</a>
 <a id="list._∷_"></a><a id="3065" href="Base.Categories.Functors.html#3065" class="InductiveConstructor Operator">_∷_</a> <a id="3069" class="Symbol">:</a> <a id="3071" href="Base.Categories.Functors.html#3025" class="Bound">A</a> <a id="3073" class="Symbol">→</a> <a id="3075" href="Base.Categories.Functors.html#3019" class="Datatype">list</a> <a id="3080" href="Base.Categories.Functors.html#3025" class="Bound">A</a> <a id="3082" class="Symbol">→</a> <a id="3084" href="Base.Categories.Functors.html#3019" class="Datatype">list</a> <a id="3089" href="Base.Categories.Functors.html#3025" class="Bound">A</a>

</pre>

We could instead define a `List` datatype by applying `μ` to a polynomial functor `L` as follows:

<pre class="Agda">

<a id="L"></a><a id="3217" href="Base.Categories.Functors.html#3217" class="Function">L</a> <a id="3219" class="Symbol">:</a> <a id="3221" class="Symbol">{</a><a id="3222" href="Base.Categories.Functors.html#3222" class="Bound">ℓ</a> <a id="3224" class="Symbol">:</a> <a id="3226" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3231" class="Symbol">}(</a><a id="3233" href="Base.Categories.Functors.html#3233" class="Bound">A</a> <a id="3235" class="Symbol">:</a> <a id="3237" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="3242" href="Base.Categories.Functors.html#3222" class="Bound">ℓ</a><a id="3243" class="Symbol">)</a> <a id="3245" class="Symbol">→</a> <a id="3247" href="Base.Categories.Functors.html#2230" class="Datatype">Functor</a><a id="3254" class="Symbol">{</a><a id="3255" href="Base.Categories.Functors.html#3222" class="Bound">ℓ</a><a id="3256" class="Symbol">}</a>
<a id="3258" href="Base.Categories.Functors.html#3217" class="Function">L</a> <a id="3260" href="Base.Categories.Functors.html#3260" class="Bound">A</a> <a id="3262" class="Symbol">=</a> <a id="3264" href="Base.Categories.Functors.html#2287" class="InductiveConstructor">Const</a> <a id="3270" href="Data.Unit.Polymorphic.Base.html#480" class="Function">⊤</a> <a id="3272" href="Base.Categories.Functors.html#2313" class="InductiveConstructor Operator">⊕</a> <a id="3274" class="Symbol">(</a><a id="3275" href="Base.Categories.Functors.html#2287" class="InductiveConstructor">Const</a> <a id="3281" href="Base.Categories.Functors.html#3260" class="Bound">A</a> <a id="3283" href="Base.Categories.Functors.html#2354" class="InductiveConstructor Operator">⊗</a> <a id="3285" href="Base.Categories.Functors.html#2273" class="InductiveConstructor">Id</a><a id="3287" class="Symbol">)</a>

<a id="List"></a><a id="3290" href="Base.Categories.Functors.html#3290" class="Function">List</a> <a id="3295" class="Symbol">:</a> <a id="3297" class="Symbol">(</a><a id="3298" href="Base.Categories.Functors.html#3298" class="Bound">A</a> <a id="3300" class="Symbol">:</a> <a id="3302" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a><a id="3306" class="Symbol">)</a> <a id="3308" class="Symbol">→</a> <a id="3310" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="3315" href="Base.Categories.Functors.html#1473" class="Primitive">ℓ₀</a>
<a id="3318" href="Base.Categories.Functors.html#3290" class="Function">List</a> <a id="3323" href="Base.Categories.Functors.html#3323" class="Bound">A</a> <a id="3325" class="Symbol">=</a> <a id="3327" href="Base.Categories.Functors.html#2821" class="Datatype Operator">μ</a> <a id="3329" class="Symbol">(</a><a id="3330" href="Base.Categories.Functors.html#3217" class="Function">L</a> <a id="3332" href="Base.Categories.Functors.html#3323" class="Bound">A</a><a id="3333" class="Symbol">)</a>

</pre>

To see some examples demonstrating that both formulations of the polymorphic list type give what we expect, see the [Examples.Categories.Functors][] module. The examples will use "getter" functions, which take a list `l` and a natural number `n` and return the element of `l` at index `n`.  (Since such an element doesn't always exist, we first define the `Option` type.)

<pre class="Agda">

<a id="3735" class="Keyword">data</a> <a id="Option"></a><a id="3740" href="Base.Categories.Functors.html#3740" class="Datatype">Option</a> <a id="3747" class="Symbol">(</a><a id="3748" href="Base.Categories.Functors.html#3748" class="Bound">A</a> <a id="3750" class="Symbol">:</a> <a id="3752" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a><a id="3756" class="Symbol">)</a> <a id="3758" class="Symbol">:</a> <a id="3760" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a> <a id="3765" class="Keyword">where</a>
 <a id="Option.some"></a><a id="3772" href="Base.Categories.Functors.html#3772" class="InductiveConstructor">some</a> <a id="3777" class="Symbol">:</a> <a id="3779" href="Base.Categories.Functors.html#3748" class="Bound">A</a> <a id="3781" class="Symbol">→</a> <a id="3783" href="Base.Categories.Functors.html#3740" class="Datatype">Option</a> <a id="3790" href="Base.Categories.Functors.html#3748" class="Bound">A</a>
 <a id="Option.none"></a><a id="3793" href="Base.Categories.Functors.html#3793" class="InductiveConstructor">none</a> <a id="3798" class="Symbol">:</a> <a id="3800" href="Base.Categories.Functors.html#3740" class="Datatype">Option</a> <a id="3807" href="Base.Categories.Functors.html#3748" class="Bound">A</a>

<a id="_[_]"></a><a id="3810" href="Base.Categories.Functors.html#3810" class="Function Operator">_[_]</a> <a id="3815" class="Symbol">:</a> <a id="3817" class="Symbol">{</a><a id="3818" href="Base.Categories.Functors.html#3818" class="Bound">A</a> <a id="3820" class="Symbol">:</a> <a id="3822" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a><a id="3826" class="Symbol">}</a> <a id="3828" class="Symbol">→</a> <a id="3830" href="Base.Categories.Functors.html#3290" class="Function">List</a> <a id="3835" href="Base.Categories.Functors.html#3818" class="Bound">A</a> <a id="3837" class="Symbol">→</a> <a id="3839" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="3841" class="Symbol">→</a> <a id="3843" href="Base.Categories.Functors.html#3740" class="Datatype">Option</a> <a id="3850" href="Base.Categories.Functors.html#3818" class="Bound">A</a>
<a id="3852" href="Base.Categories.Functors.html#2852" class="InductiveConstructor">inn</a> <a id="3856" class="Symbol">(</a><a id="3857" href="Base.Categories.Functors.html#1596" class="InductiveConstructor">inl</a> <a id="3861" href="Base.Categories.Functors.html#3861" class="Bound">x</a><a id="3862" class="Symbol">)</a> <a id="3864" href="Base.Categories.Functors.html#3810" class="Function Operator">[</a> <a id="3866" href="Base.Categories.Functors.html#3866" class="Bound">n</a> <a id="3868" href="Base.Categories.Functors.html#3810" class="Function Operator">]</a> <a id="3870" class="Symbol">=</a> <a id="3872" href="Base.Categories.Functors.html#3793" class="InductiveConstructor">none</a>
<a id="3877" href="Base.Categories.Functors.html#2852" class="InductiveConstructor">inn</a> <a id="3881" class="Symbol">(</a><a id="3882" href="Base.Categories.Functors.html#1611" class="InductiveConstructor">inr</a> <a id="3886" class="Symbol">(</a><a id="3887" href="Base.Categories.Functors.html#3887" class="Bound">x</a> <a id="3889" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3891" href="Base.Categories.Functors.html#3891" class="Bound">xs</a><a id="3893" class="Symbol">))</a> <a id="3896" href="Base.Categories.Functors.html#3810" class="Function Operator">[</a> <a id="3898" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="3903" href="Base.Categories.Functors.html#3810" class="Function Operator">]</a> <a id="3905" class="Symbol">=</a> <a id="3907" href="Base.Categories.Functors.html#3772" class="InductiveConstructor">some</a> <a id="3912" href="Base.Categories.Functors.html#3887" class="Bound">x</a>
<a id="3914" href="Base.Categories.Functors.html#2852" class="InductiveConstructor">inn</a> <a id="3918" class="Symbol">(</a><a id="3919" href="Base.Categories.Functors.html#1611" class="InductiveConstructor">inr</a> <a id="3923" class="Symbol">(</a><a id="3924" href="Base.Categories.Functors.html#3924" class="Bound">x</a> <a id="3926" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3928" href="Base.Categories.Functors.html#3928" class="Bound">xs</a><a id="3930" class="Symbol">))</a> <a id="3933" href="Base.Categories.Functors.html#3810" class="Function Operator">[</a> <a id="3935" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="3939" href="Base.Categories.Functors.html#3939" class="Bound">n</a> <a id="3941" href="Base.Categories.Functors.html#3810" class="Function Operator">]</a> <a id="3943" class="Symbol">=</a> <a id="3945" href="Base.Categories.Functors.html#3928" class="Bound">xs</a> <a id="3948" href="Base.Categories.Functors.html#3810" class="Function Operator">[</a> <a id="3950" href="Base.Categories.Functors.html#3939" class="Bound">n</a> <a id="3952" href="Base.Categories.Functors.html#3810" class="Function Operator">]</a>

<a id="_⟦_⟧"></a><a id="3955" href="Base.Categories.Functors.html#3955" class="Function Operator">_⟦_⟧</a> <a id="3960" class="Symbol">:</a> <a id="3962" class="Symbol">{</a><a id="3963" href="Base.Categories.Functors.html#3963" class="Bound">A</a> <a id="3965" class="Symbol">:</a> <a id="3967" href="Base.Categories.Functors.html#1457" class="Primitive">Type</a><a id="3971" class="Symbol">}</a> <a id="3973" class="Symbol">→</a> <a id="3975" href="Base.Categories.Functors.html#3019" class="Datatype">list</a> <a id="3980" href="Base.Categories.Functors.html#3963" class="Bound">A</a> <a id="3982" class="Symbol">→</a> <a id="3984" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a> <a id="3986" class="Symbol">→</a> <a id="3988" href="Base.Categories.Functors.html#3740" class="Datatype">Option</a> <a id="3995" href="Base.Categories.Functors.html#3963" class="Bound">A</a>
<a id="3997" href="Base.Categories.Functors.html#3052" class="InductiveConstructor">[]</a> <a id="4000" href="Base.Categories.Functors.html#3955" class="Function Operator">⟦</a> <a id="4002" href="Base.Categories.Functors.html#4002" class="Bound">n</a> <a id="4004" href="Base.Categories.Functors.html#3955" class="Function Operator">⟧</a> <a id="4006" class="Symbol">=</a> <a id="4008" href="Base.Categories.Functors.html#3793" class="InductiveConstructor">none</a>
<a id="4013" class="Symbol">(</a><a id="4014" href="Base.Categories.Functors.html#4014" class="Bound">x</a> <a id="4016" href="Base.Categories.Functors.html#3065" class="InductiveConstructor Operator">∷</a> <a id="4018" href="Base.Categories.Functors.html#4018" class="Bound">l</a><a id="4019" class="Symbol">)</a> <a id="4021" href="Base.Categories.Functors.html#3955" class="Function Operator">⟦</a> <a id="4023" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="4028" href="Base.Categories.Functors.html#3955" class="Function Operator">⟧</a> <a id="4030" class="Symbol">=</a> <a id="4032" href="Base.Categories.Functors.html#3772" class="InductiveConstructor">some</a> <a id="4037" href="Base.Categories.Functors.html#4014" class="Bound">x</a>
<a id="4039" class="Symbol">(</a><a id="4040" href="Base.Categories.Functors.html#4040" class="Bound">x</a> <a id="4042" href="Base.Categories.Functors.html#3065" class="InductiveConstructor Operator">∷</a> <a id="4044" href="Base.Categories.Functors.html#4044" class="Bound">l</a><a id="4045" class="Symbol">)</a> <a id="4047" href="Base.Categories.Functors.html#3955" class="Function Operator">⟦</a> <a id="4049" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="4053" href="Base.Categories.Functors.html#4053" class="Bound">n</a> <a id="4055" href="Base.Categories.Functors.html#3955" class="Function Operator">⟧</a> <a id="4057" class="Symbol">=</a> <a id="4059" href="Base.Categories.Functors.html#4044" class="Bound">l</a> <a id="4061" href="Base.Categories.Functors.html#3955" class="Function Operator">⟦</a> <a id="4063" href="Base.Categories.Functors.html#4053" class="Bound">n</a> <a id="4065" href="Base.Categories.Functors.html#3955" class="Function Operator">⟧</a>

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
