---
layout: default
title : "Homomorphisms.Func.Factor module (The Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="factoring-homomorphisms-of-setoidalgebra">Factoring Homomorphism of SetoidAlgebras</a>

This is the [Homomorphisms.Func.Factor][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="374" class="Symbol">{-#</a> <a id="378" class="Keyword">OPTIONS</a> <a id="386" class="Pragma">--without-K</a> <a id="398" class="Pragma">--exact-split</a> <a id="412" class="Pragma">--safe</a> <a id="419" class="Symbol">#-}</a>

<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="451" class="Keyword">using</a> <a id="457" class="Symbol">(</a><a id="458" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="460" class="Symbol">;</a> <a id="462" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a> <a id="464" class="Symbol">;</a> <a id="466" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="476" class="Symbol">)</a>

<a id="479" class="Keyword">module</a> <a id="486" href="Homomorphisms.Func.Factor.html" class="Module">Homomorphisms.Func.Factor</a> <a id="512" class="Symbol">{</a><a id="513" href="Homomorphisms.Func.Factor.html#513" class="Bound">𝑆</a> <a id="515" class="Symbol">:</a> <a id="517" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="527" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="529" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a><a id="530" class="Symbol">}</a> <a id="532" class="Keyword">where</a>

<a id="539" class="Comment">-- Imports from Agda and the Agda Standard Library -------------------------------------------------</a>
<a id="640" class="Keyword">open</a> <a id="645" class="Keyword">import</a> <a id="652" href="Data.Product.html" class="Module">Data.Product</a>    <a id="668" class="Keyword">using</a> <a id="674" class="Symbol">(</a> <a id="676" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="680" class="Symbol">;</a> <a id="682" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="691" class="Symbol">)</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="Function.html" class="Module">Function</a>        <a id="721" class="Keyword">using</a> <a id="727" class="Symbol">(</a> <a id="729" href="Function.Bundles.html#1868" class="Record">Func</a> <a id="734" class="Symbol">;</a> <a id="736" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="740" class="Symbol">)</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="Level.html" class="Module">Level</a>           <a id="770" class="Keyword">using</a> <a id="776" class="Symbol">(</a> <a id="778" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="784" class="Symbol">)</a>
<a id="786" class="Keyword">open</a> <a id="791" class="Keyword">import</a> <a id="798" href="Relation.Binary.html" class="Module">Relation.Binary</a> <a id="814" class="Keyword">using</a> <a id="820" class="Symbol">(</a> <a id="822" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="829" class="Symbol">)</a>
<a id="831" class="Keyword">open</a> <a id="836" class="Keyword">import</a> <a id="843" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="859" class="Keyword">using</a> <a id="865" class="Symbol">(</a> <a id="867" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="871" class="Symbol">)</a>
<a id="873" class="Keyword">open</a> <a id="878" class="Keyword">import</a> <a id="885" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="923" class="Symbol">as</a> <a id="926" class="Module">≡</a> <a id="928" class="Keyword">using</a> <a id="934" class="Symbol">()</a>
<a id="937" class="Keyword">import</a> <a id="944" href="Relation.Binary.Reasoning.Setoid.html" class="Module">Relation.Binary.Reasoning.Setoid</a> <a id="977" class="Symbol">as</a> <a id="980" class="Module">SetoidReasoning</a>

<a id="997" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------------------------</a>
<a id="1097" class="Keyword">open</a> <a id="1102" class="Keyword">import</a> <a id="1109" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>           <a id="1142" class="Keyword">using</a> <a id="1148" class="Symbol">(</a> <a id="1150" href="Overture.Preliminaries.html#4383" class="Function Operator">∣_∣</a> <a id="1154" class="Symbol">;</a> <a id="1156" href="Overture.Preliminaries.html#4421" class="Function Operator">∥_∥</a> <a id="1160" class="Symbol">)</a>
<a id="1162" class="Keyword">open</a> <a id="1167" class="Keyword">import</a> <a id="1174" href="Overture.Func.Preliminaries.html" class="Module">Overture.Func.Preliminaries</a>      <a id="1207" class="Keyword">using</a> <a id="1213" class="Symbol">(</a> <a id="1215" href="Overture.Func.Preliminaries.html#803" class="Function Operator">_⟶_</a> <a id="1219" class="Symbol">)</a>
<a id="1221" class="Keyword">open</a> <a id="1226" class="Keyword">import</a> <a id="1233" href="Overture.Inverses.html" class="Module">Overture.Inverses</a>                <a id="1266" class="Keyword">using</a> <a id="1272" class="Symbol">(</a> <a id="1274" href="Overture.Inverses.html#1077" class="Datatype Operator">Image_∋_</a> <a id="1283" class="Symbol">)</a>
<a id="1285" class="Keyword">open</a> <a id="1290" class="Keyword">import</a> <a id="1297" href="Overture.Func.Surjective.html" class="Module">Overture.Func.Surjective</a>         <a id="1330" class="Keyword">using</a> <a id="1336" class="Symbol">(</a> <a id="1338" href="Overture.Func.Surjective.html#1783" class="Function">IsSurjective</a> <a id="1351" class="Symbol">;</a> <a id="1353" href="Overture.Func.Surjective.html#2493" class="Function">SurjInv</a> <a id="1361" class="Symbol">;</a> <a id="1363" href="Overture.Func.Surjective.html#2767" class="Function">SurjInvIsInverseʳ</a> <a id="1381" class="Symbol">)</a>
<a id="1383" class="Keyword">open</a> <a id="1388" class="Keyword">import</a> <a id="1395" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>               <a id="1428" class="Keyword">using</a> <a id="1434" class="Symbol">(</a> <a id="1436" href="Relations.Discrete.html#4019" class="Function">kernelRel</a> <a id="1446" class="Symbol">)</a>
<a id="1448" class="Keyword">open</a> <a id="1453" class="Keyword">import</a> <a id="1460" href="Algebras.Func.Basic.html" class="Module">Algebras.Func.Basic</a>      <a id="1485" class="Symbol">{</a><a id="1486" class="Argument">𝑆</a> <a id="1488" class="Symbol">=</a> <a id="1490" href="Homomorphisms.Func.Factor.html#513" class="Bound">𝑆</a><a id="1491" class="Symbol">}</a> <a id="1493" class="Keyword">using</a> <a id="1499" class="Symbol">(</a> <a id="1501" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1515" class="Symbol">;</a> <a id="1517" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[_]</a> <a id="1522" class="Symbol">;</a> <a id="1524" href="Algebras.Func.Basic.html#4078" class="Function Operator">_̂_</a> <a id="1528" class="Symbol">)</a>
<a id="1530" class="Keyword">open</a> <a id="1535" class="Keyword">import</a> <a id="1542" href="Homomorphisms.Func.Basic.html" class="Module">Homomorphisms.Func.Basic</a> <a id="1567" class="Symbol">{</a><a id="1568" class="Argument">𝑆</a> <a id="1570" class="Symbol">=</a> <a id="1572" href="Homomorphisms.Func.Factor.html#513" class="Bound">𝑆</a><a id="1573" class="Symbol">}</a> <a id="1575" class="Keyword">using</a> <a id="1581" class="Symbol">(</a> <a id="1583" href="Homomorphisms.Func.Basic.html#2125" class="Function">hom</a> <a id="1587" class="Symbol">;</a> <a id="1589" href="Homomorphisms.Func.Basic.html#1999" class="Record">IsHom</a> <a id="1595" class="Symbol">;</a> <a id="1597" href="Homomorphisms.Func.Basic.html#1849" class="Function">compatible-map</a> <a id="1612" class="Symbol">)</a>

<a id="1615" class="Keyword">private</a> <a id="1623" class="Keyword">variable</a>
 <a id="1633" href="Homomorphisms.Func.Factor.html#1633" class="Generalizable">α</a> <a id="1635" href="Homomorphisms.Func.Factor.html#1635" class="Generalizable">ρᵃ</a> <a id="1638" href="Homomorphisms.Func.Factor.html#1638" class="Generalizable">β</a> <a id="1640" href="Homomorphisms.Func.Factor.html#1640" class="Generalizable">ρᵇ</a> <a id="1643" href="Homomorphisms.Func.Factor.html#1643" class="Generalizable">γ</a> <a id="1645" href="Homomorphisms.Func.Factor.html#1645" class="Generalizable">ρᶜ</a> <a id="1648" class="Symbol">:</a> <a id="1650" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ ∘ h` so the following diagram commutes:

```
𝑨 --- h -->> 𝑪
 \         .
  \       .
   g     φ
    \   .
     \ .
      V
      𝑩
```

We will prove this in case h is both surjective and injective.

<pre class="Agda">

<a id="2005" class="Keyword">module</a> <a id="2012" href="Homomorphisms.Func.Factor.html#2012" class="Module">_</a> <a id="2014" class="Symbol">{</a><a id="2015" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2033" href="Homomorphisms.Func.Factor.html#1633" class="Generalizable">α</a> <a id="2035" href="Homomorphisms.Func.Factor.html#1635" class="Generalizable">ρᵃ</a><a id="2037" class="Symbol">}</a>
         <a id="2048" class="Symbol">(</a><a id="2049" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a> <a id="2051" class="Symbol">:</a> <a id="2053" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2067" href="Homomorphisms.Func.Factor.html#1638" class="Generalizable">β</a> <a id="2069" href="Homomorphisms.Func.Factor.html#1640" class="Generalizable">ρᵇ</a><a id="2071" class="Symbol">)</a>
         <a id="2082" class="Symbol">{</a><a id="2083" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="2085" class="Symbol">:</a> <a id="2087" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2101" href="Homomorphisms.Func.Factor.html#1643" class="Generalizable">γ</a> <a id="2103" href="Homomorphisms.Func.Factor.html#1645" class="Generalizable">ρᶜ</a><a id="2105" class="Symbol">}</a>
         <a id="2116" class="Symbol">(</a><a id="2117" href="Homomorphisms.Func.Factor.html#2117" class="Bound">gh</a> <a id="2120" class="Symbol">:</a> <a id="2122" href="Homomorphisms.Func.Basic.html#2125" class="Function">hom</a> <a id="2126" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a> <a id="2128" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a><a id="2129" class="Symbol">)(</a><a id="2131" href="Homomorphisms.Func.Factor.html#2131" class="Bound">hh</a> <a id="2134" class="Symbol">:</a> <a id="2136" href="Homomorphisms.Func.Basic.html#2125" class="Function">hom</a> <a id="2140" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a> <a id="2142" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a><a id="2143" class="Symbol">)</a> <a id="2145" class="Keyword">where</a>

 <a id="2153" class="Keyword">open</a> <a id="2158" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a> <a id="2172" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a> <a id="2174" class="Keyword">using</a> <a id="2180" class="Symbol">()</a> <a id="2183" class="Keyword">renaming</a> <a id="2192" class="Symbol">(</a><a id="2193" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="2200" class="Symbol">to</a> <a id="2203" class="Field">B</a> <a id="2205" class="Symbol">)</a>
 <a id="2208" class="Keyword">open</a> <a id="2213" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a> <a id="2227" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="2229" class="Keyword">using</a> <a id="2235" class="Symbol">(</a> <a id="2237" href="Algebras.Func.Basic.html#2960" class="Field">Interp</a> <a id="2244" class="Symbol">)</a> <a id="2246" class="Keyword">renaming</a> <a id="2255" class="Symbol">(</a><a id="2256" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="2263" class="Symbol">to</a> <a id="2266" class="Field">C</a> <a id="2268" class="Symbol">)</a>
 <a id="2271" class="Keyword">open</a> <a id="2276" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a> <a id="2283" href="Homomorphisms.Func.Factor.html#2203" class="Function">B</a> <a id="2285" class="Keyword">using</a> <a id="2291" class="Symbol">()</a> <a id="2294" class="Keyword">renaming</a> <a id="2303" class="Symbol">(</a> <a id="2305" href="Relation.Binary.Bundles.html#1098" class="Field Operator">_≈_</a> <a id="2309" class="Symbol">to</a> <a id="2312" class="Field Operator">_≈₂_</a> <a id="2317" class="Symbol">;</a> <a id="2319" href="Relation.Binary.Structures.html#1594" class="Function">sym</a> <a id="2323" class="Symbol">to</a> <a id="2326" class="Function">sym₂</a> <a id="2331" class="Symbol">)</a>
 <a id="2334" class="Keyword">open</a> <a id="2339" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a> <a id="2346" href="Homomorphisms.Func.Factor.html#2266" class="Function">C</a> <a id="2348" class="Keyword">using</a> <a id="2354" class="Symbol">(</a> <a id="2356" href="Relation.Binary.Structures.html#1620" class="Function">trans</a> <a id="2362" class="Symbol">)</a> <a id="2364" class="Keyword">renaming</a> <a id="2373" class="Symbol">(</a> <a id="2375" href="Relation.Binary.Bundles.html#1098" class="Field Operator">_≈_</a> <a id="2379" class="Symbol">to</a> <a id="2382" class="Field Operator">_≈₃_</a> <a id="2387" class="Symbol">;</a> <a id="2389" href="Relation.Binary.Structures.html#1594" class="Function">sym</a> <a id="2393" class="Symbol">to</a> <a id="2396" class="Function">sym₃</a> <a id="2401" class="Symbol">)</a>
 <a id="2404" class="Keyword">open</a> <a id="2409" href="Relation.Binary.Reasoning.Setoid.html" class="Module">SetoidReasoning</a> <a id="2425" href="Homomorphisms.Func.Factor.html#2203" class="Function">B</a>
 <a id="2428" class="Keyword">open</a> <a id="2433" href="Function.Bundles.html#1868" class="Module">Func</a> <a id="2438" class="Keyword">using</a> <a id="2444" class="Symbol">(</a> <a id="2446" href="Function.Bundles.html#1938" class="Field">cong</a> <a id="2451" class="Symbol">)</a> <a id="2453" class="Keyword">renaming</a> <a id="2462" class="Symbol">(</a><a id="2463" href="Function.Bundles.html#1919" class="Field">f</a> <a id="2465" class="Symbol">to</a> <a id="2468" class="Field">_⟨$⟩_</a> <a id="2474" class="Symbol">)</a>

 <a id="2478" class="Keyword">private</a>
  <a id="2488" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="2490" class="Symbol">=</a> <a id="2492" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">_⟨$⟩_</a> <a id="2498" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="2500" href="Homomorphisms.Func.Factor.html#2117" class="Bound">gh</a> <a id="2503" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a>
  <a id="2507" href="Homomorphisms.Func.Factor.html#2507" class="Function">hfunc</a> <a id="2513" class="Symbol">=</a> <a id="2515" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="2517" href="Homomorphisms.Func.Factor.html#2131" class="Bound">hh</a> <a id="2520" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a>
  <a id="2524" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2526" class="Symbol">=</a> <a id="2528" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">_⟨$⟩_</a> <a id="2534" href="Homomorphisms.Func.Factor.html#2507" class="Function">hfunc</a>

 <a id="2542" class="Keyword">open</a> <a id="2547" href="Homomorphisms.Func.Basic.html#1999" class="Module">IsHom</a>
 <a id="2554" class="Keyword">open</a> <a id="2559" href="Overture.Inverses.html#1077" class="Module Operator">Image_∋_</a>

 <a id="2570" href="Homomorphisms.Func.Factor.html#2570" class="Function">hom-factor</a> <a id="2581" class="Symbol">:</a> <a id="2583" href="Relations.Discrete.html#4019" class="Function">kernelRel</a> <a id="2593" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">_≈₃_</a> <a id="2598" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2600" href="Relation.Unary.html#1742" class="Function Operator">⊆</a> <a id="2602" href="Relations.Discrete.html#4019" class="Function">kernelRel</a> <a id="2612" href="Homomorphisms.Func.Factor.html#2312" class="Function Operator">_≈₂_</a> <a id="2617" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="2619" class="Symbol">→</a> <a id="2621" href="Overture.Func.Surjective.html#1783" class="Function">IsSurjective</a> <a id="2634" href="Homomorphisms.Func.Factor.html#2507" class="Function">hfunc</a>
              <a id="2654" class="Comment">---------------------------------------------------------</a>
  <a id="2714" class="Symbol">→</a>           <a id="2726" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2729" href="Homomorphisms.Func.Factor.html#2729" class="Bound">φ</a> <a id="2731" href="Data.Product.html#916" class="Function">∈</a> <a id="2733" href="Homomorphisms.Func.Basic.html#2125" class="Function">hom</a> <a id="2737" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="2739" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a> <a id="2741" href="Data.Product.html#916" class="Function">]</a> <a id="2743" class="Symbol">∀</a> <a id="2745" href="Homomorphisms.Func.Factor.html#2745" class="Bound">a</a> <a id="2747" class="Symbol">→</a> <a id="2749" class="Symbol">(</a><a id="2750" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="2752" href="Homomorphisms.Func.Factor.html#2745" class="Bound">a</a><a id="2753" class="Symbol">)</a> <a id="2755" href="Homomorphisms.Func.Factor.html#2312" class="Function Operator">≈₂</a> <a id="2758" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="2760" href="Homomorphisms.Func.Factor.html#2729" class="Bound">φ</a> <a id="2762" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="2764" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">⟨$⟩</a> <a id="2768" class="Symbol">(</a><a id="2769" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2771" href="Homomorphisms.Func.Factor.html#2745" class="Bound">a</a><a id="2772" class="Symbol">)</a>

 <a id="2776" href="Homomorphisms.Func.Factor.html#2570" class="Function">hom-factor</a> <a id="2787" href="Homomorphisms.Func.Factor.html#2787" class="Bound">Khg</a> <a id="2791" href="Homomorphisms.Func.Factor.html#2791" class="Bound">hE</a> <a id="2794" class="Symbol">=</a> <a id="2796" class="Symbol">(</a><a id="2797" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="2802" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2804" href="Homomorphisms.Func.Factor.html#3697" class="Function">φhom</a><a id="2808" class="Symbol">)</a> <a id="2810" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2812" href="Homomorphisms.Func.Factor.html#3221" class="Function">gφh</a>
  <a id="2818" class="Keyword">where</a>
  <a id="2826" href="Homomorphisms.Func.Factor.html#2826" class="Function">kerpres</a> <a id="2834" class="Symbol">:</a> <a id="2836" class="Symbol">∀</a> <a id="2838" href="Homomorphisms.Func.Factor.html#2838" class="Bound">a₀</a> <a id="2841" href="Homomorphisms.Func.Factor.html#2841" class="Bound">a₁</a> <a id="2844" class="Symbol">→</a> <a id="2846" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2848" href="Homomorphisms.Func.Factor.html#2838" class="Bound">a₀</a> <a id="2851" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">≈₃</a> <a id="2854" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2856" href="Homomorphisms.Func.Factor.html#2841" class="Bound">a₁</a> <a id="2859" class="Symbol">→</a> <a id="2861" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="2863" href="Homomorphisms.Func.Factor.html#2838" class="Bound">a₀</a> <a id="2866" href="Homomorphisms.Func.Factor.html#2312" class="Function Operator">≈₂</a> <a id="2869" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="2871" href="Homomorphisms.Func.Factor.html#2841" class="Bound">a₁</a>
  <a id="2876" href="Homomorphisms.Func.Factor.html#2826" class="Function">kerpres</a> <a id="2884" href="Homomorphisms.Func.Factor.html#2884" class="Bound">a₀</a> <a id="2887" href="Homomorphisms.Func.Factor.html#2887" class="Bound">a₁</a> <a id="2890" href="Homomorphisms.Func.Factor.html#2890" class="Bound">hyp</a> <a id="2894" class="Symbol">=</a> <a id="2896" href="Homomorphisms.Func.Factor.html#2787" class="Bound">Khg</a> <a id="2900" href="Homomorphisms.Func.Factor.html#2890" class="Bound">hyp</a>

  <a id="2907" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="2911" class="Symbol">:</a> <a id="2913" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="2916" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="2918" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="2920" class="Symbol">→</a> <a id="2922" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="2925" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a> <a id="2927" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a>
  <a id="2931" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="2935" class="Symbol">=</a> <a id="2937" href="Overture.Func.Surjective.html#2493" class="Function">SurjInv</a> <a id="2945" href="Homomorphisms.Func.Factor.html#2507" class="Function">hfunc</a> <a id="2951" href="Homomorphisms.Func.Factor.html#2791" class="Bound">hE</a>

  <a id="2957" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a> <a id="2959" class="Symbol">:</a> <a id="2961" class="Symbol">∀</a> <a id="2963" class="Symbol">{</a><a id="2964" href="Homomorphisms.Func.Factor.html#2964" class="Bound">c</a><a id="2965" class="Symbol">}</a> <a id="2967" class="Symbol">→</a> <a id="2969" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="2971" class="Symbol">(</a><a id="2972" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="2976" href="Homomorphisms.Func.Factor.html#2964" class="Bound">c</a><a id="2977" class="Symbol">)</a> <a id="2979" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">≈₃</a> <a id="2982" href="Homomorphisms.Func.Factor.html#2964" class="Bound">c</a>
  <a id="2986" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a> <a id="2988" class="Symbol">=</a> <a id="2990" href="Overture.Func.Surjective.html#2767" class="Function">SurjInvIsInverseʳ</a> <a id="3008" href="Homomorphisms.Func.Factor.html#2507" class="Function">hfunc</a> <a id="3014" href="Homomorphisms.Func.Factor.html#2791" class="Bound">hE</a>

  <a id="3020" href="Homomorphisms.Func.Factor.html#3020" class="Function">ξ</a> <a id="3022" class="Symbol">:</a> <a id="3024" class="Symbol">∀</a> <a id="3026" class="Symbol">{</a><a id="3027" href="Homomorphisms.Func.Factor.html#3027" class="Bound">a</a><a id="3028" class="Symbol">}</a> <a id="3030" class="Symbol">→</a> <a id="3032" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3034" href="Homomorphisms.Func.Factor.html#3027" class="Bound">a</a> <a id="3036" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">≈₃</a> <a id="3039" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3041" class="Symbol">(</a><a id="3042" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3046" class="Symbol">(</a><a id="3047" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3049" href="Homomorphisms.Func.Factor.html#3027" class="Bound">a</a><a id="3050" class="Symbol">))</a>
  <a id="3055" href="Homomorphisms.Func.Factor.html#3020" class="Function">ξ</a> <a id="3057" class="Symbol">=</a> <a id="3059" href="Homomorphisms.Func.Factor.html#2396" class="Function">sym₃</a> <a id="3064" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a>

  <a id="3069" href="Homomorphisms.Func.Factor.html#3069" class="Function">ζ</a> <a id="3071" class="Symbol">:</a> <a id="3073" class="Symbol">∀{</a><a id="3075" href="Homomorphisms.Func.Factor.html#3075" class="Bound">x</a> <a id="3077" href="Homomorphisms.Func.Factor.html#3077" class="Bound">y</a><a id="3078" class="Symbol">}</a> <a id="3080" class="Symbol">→</a> <a id="3082" href="Homomorphisms.Func.Factor.html#3075" class="Bound">x</a> <a id="3084" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">≈₃</a> <a id="3087" href="Homomorphisms.Func.Factor.html#3077" class="Bound">y</a> <a id="3089" class="Symbol">→</a> <a id="3091" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3093" class="Symbol">(</a><a id="3094" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3098" href="Homomorphisms.Func.Factor.html#3075" class="Bound">x</a><a id="3099" class="Symbol">)</a> <a id="3101" href="Homomorphisms.Func.Factor.html#2382" class="Function Operator">≈₃</a> <a id="3104" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3106" class="Symbol">(</a><a id="3107" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3111" href="Homomorphisms.Func.Factor.html#3077" class="Bound">y</a><a id="3112" class="Symbol">)</a>
  <a id="3116" href="Homomorphisms.Func.Factor.html#3069" class="Function">ζ</a> <a id="3118" href="Homomorphisms.Func.Factor.html#3118" class="Bound">xy</a> <a id="3121" class="Symbol">=</a> <a id="3123" href="Relation.Binary.Structures.html#1620" class="Function">trans</a> <a id="3129" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a> <a id="3131" class="Symbol">(</a><a id="3132" href="Relation.Binary.Structures.html#1620" class="Function">trans</a> <a id="3138" href="Homomorphisms.Func.Factor.html#3118" class="Bound">xy</a> <a id="3141" class="Symbol">(</a><a id="3142" href="Homomorphisms.Func.Factor.html#2396" class="Function">sym₃</a> <a id="3147" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a><a id="3148" class="Symbol">))</a>


  <a id="3155" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3160" class="Symbol">:</a> <a id="3162" href="Homomorphisms.Func.Factor.html#2266" class="Function">C</a> <a id="3164" href="Overture.Func.Preliminaries.html#803" class="Function Operator">⟶</a> <a id="3166" href="Homomorphisms.Func.Factor.html#2203" class="Function">B</a>
  <a id="3170" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">_⟨$⟩_</a> <a id="3176" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3181" class="Symbol">=</a> <a id="3183" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3185" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3187" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a>
  <a id="3193" href="Function.Bundles.html#1938" class="Field">Func.cong</a> <a id="3203" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3208" class="Symbol">=</a> <a id="3210" href="Homomorphisms.Func.Factor.html#2787" class="Bound">Khg</a> <a id="3214" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3216" href="Homomorphisms.Func.Factor.html#3069" class="Function">ζ</a>

  <a id="3221" href="Homomorphisms.Func.Factor.html#3221" class="Function">gφh</a> <a id="3225" class="Symbol">:</a> <a id="3227" class="Symbol">(</a><a id="3228" href="Homomorphisms.Func.Factor.html#3228" class="Bound">a</a> <a id="3230" class="Symbol">:</a> <a id="3232" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="3235" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a> <a id="3237" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a><a id="3238" class="Symbol">)</a> <a id="3240" class="Symbol">→</a> <a id="3242" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3244" href="Homomorphisms.Func.Factor.html#3228" class="Bound">a</a> <a id="3246" href="Homomorphisms.Func.Factor.html#2312" class="Function Operator">≈₂</a> <a id="3249" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3254" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">⟨$⟩</a> <a id="3258" class="Symbol">(</a><a id="3259" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3261" href="Homomorphisms.Func.Factor.html#3228" class="Bound">a</a><a id="3262" class="Symbol">)</a>
  <a id="3266" href="Homomorphisms.Func.Factor.html#3221" class="Function">gφh</a> <a id="3270" href="Homomorphisms.Func.Factor.html#3270" class="Bound">a</a> <a id="3272" class="Symbol">=</a> <a id="3274" href="Homomorphisms.Func.Factor.html#2787" class="Bound">Khg</a> <a id="3278" href="Homomorphisms.Func.Factor.html#3020" class="Function">ξ</a>


  <a id="3284" class="Keyword">open</a> <a id="3289" href="Function.Bundles.html#1868" class="Module">Func</a> <a id="3294" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3299" class="Keyword">using</a> <a id="3305" class="Symbol">()</a> <a id="3308" class="Keyword">renaming</a> <a id="3317" class="Symbol">(</a><a id="3318" href="Function.Bundles.html#1938" class="Field">cong</a> <a id="3323" class="Symbol">to</a> <a id="3326" class="Field">φcong</a><a id="3331" class="Symbol">)</a>
  <a id="3335" href="Homomorphisms.Func.Factor.html#3335" class="Function">φcomp</a> <a id="3341" class="Symbol">:</a> <a id="3343" href="Homomorphisms.Func.Basic.html#1849" class="Function">compatible-map</a> <a id="3358" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="3360" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a> <a id="3362" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a>
  <a id="3369" href="Homomorphisms.Func.Factor.html#3335" class="Function">φcomp</a> <a id="3375" class="Symbol">{</a><a id="3376" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a><a id="3377" class="Symbol">}{</a><a id="3379" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3380" class="Symbol">}</a> <a id="3382" class="Symbol">=</a> <a id="3384" href="Relation.Binary.Reasoning.Base.Single.html#1916" class="Function Operator">begin</a>
    <a id="3394" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3399" href="Homomorphisms.Func.Factor.html#2468" class="Field Operator">⟨$⟩</a> <a id="3403" class="Symbol">((</a><a id="3405" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3407" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3409" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a><a id="3410" class="Symbol">)</a> <a id="3412" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3413" class="Symbol">)</a>   <a id="3417" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">≈˘⟨</a> <a id="3421" href="Homomorphisms.Func.Factor.html#3326" class="Function">φcong</a> <a id="3427" class="Symbol">(</a><a id="3428" href="Function.Bundles.html#1938" class="Field">Func.cong</a> <a id="3438" href="Algebras.Func.Basic.html#2960" class="Function">Interp</a> <a id="3445" class="Symbol">(</a><a id="3446" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">≡.refl</a> <a id="3453" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3455" class="Symbol">(λ</a> <a id="3458" href="Homomorphisms.Func.Factor.html#3458" class="Bound">_</a> <a id="3460" class="Symbol">→</a> <a id="3462" href="Homomorphisms.Func.Factor.html#2957" class="Function">η</a><a id="3463" class="Symbol">)))</a> <a id="3467" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">⟩</a>
    <a id="3473" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3475" class="Symbol">(</a><a id="3476" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3480" class="Symbol">((</a><a id="3482" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3484" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3486" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a><a id="3487" class="Symbol">)(</a><a id="3489" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3491" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3493" class="Symbol">(</a><a id="3494" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3498" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3500" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3501" class="Symbol">))))</a>   <a id="3508" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">≈˘⟨</a> <a id="3512" href="Homomorphisms.Func.Factor.html#3326" class="Function">φcong</a> <a id="3518" class="Symbol">(</a><a id="3519" href="Homomorphisms.Func.Basic.html#2063" class="Field">compatible</a> <a id="3530" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="3532" href="Homomorphisms.Func.Factor.html#2131" class="Bound">hh</a> <a id="3535" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a><a id="3536" class="Symbol">)</a> <a id="3538" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">⟩</a>
    <a id="3544" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3546" class="Symbol">(</a><a id="3547" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3551" class="Symbol">(</a><a id="3552" href="Homomorphisms.Func.Factor.html#2524" class="Function">h</a> <a id="3554" class="Symbol">((</a><a id="3556" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3558" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3560" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a><a id="3561" class="Symbol">)(</a><a id="3563" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3567" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3569" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3570" class="Symbol">))))</a>   <a id="3577" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">≈˘⟨</a> <a id="3581" href="Homomorphisms.Func.Factor.html#3221" class="Function">gφh</a> <a id="3585" class="Symbol">((</a><a id="3587" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3589" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3591" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a><a id="3592" class="Symbol">)(</a><a id="3594" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3598" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3600" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3601" class="Symbol">))</a> <a id="3604" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">⟩</a>
    <a id="3610" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3612" class="Symbol">((</a><a id="3614" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3616" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3618" href="Homomorphisms.Func.Factor.html#2015" class="Bound">𝑨</a><a id="3619" class="Symbol">)(</a><a id="3621" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3625" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3627" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3628" class="Symbol">))</a>    <a id="3634" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">≈˘⟨</a> <a id="3638" href="Homomorphisms.Func.Factor.html#2326" class="Function">sym₂</a> <a id="3643" class="Symbol">(</a><a id="3644" href="Homomorphisms.Func.Basic.html#2063" class="Field">compatible</a> <a id="3655" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="3657" href="Homomorphisms.Func.Factor.html#2117" class="Bound">gh</a> <a id="3660" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a><a id="3661" class="Symbol">)</a> <a id="3663" href="Relation.Binary.Reasoning.Setoid.html#1153" class="Function">⟩</a>
    <a id="3669" class="Symbol">(</a><a id="3670" href="Homomorphisms.Func.Factor.html#3376" class="Bound">f</a> <a id="3672" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="3674" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a><a id="3675" class="Symbol">)(</a><a id="3677" href="Homomorphisms.Func.Factor.html#2488" class="Function">g</a> <a id="3679" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3681" class="Symbol">(</a><a id="3682" href="Homomorphisms.Func.Factor.html#2907" class="Function">h⁻¹</a> <a id="3686" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="3688" href="Homomorphisms.Func.Factor.html#3379" class="Bound">c</a><a id="3689" class="Symbol">))</a> <a id="3692" href="Relation.Binary.Reasoning.Base.Single.html#2555" class="Function Operator">∎</a>

  <a id="3697" href="Homomorphisms.Func.Factor.html#3697" class="Function">φhom</a> <a id="3702" class="Symbol">:</a> <a id="3704" href="Homomorphisms.Func.Basic.html#1999" class="Record">IsHom</a> <a id="3710" href="Homomorphisms.Func.Factor.html#2083" class="Bound">𝑪</a> <a id="3712" href="Homomorphisms.Func.Factor.html#2049" class="Bound">𝑩</a> <a id="3714" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a>
  <a id="3721" href="Homomorphisms.Func.Factor.html#3697" class="Function">φhom</a> <a id="3726" class="Symbol">=</a> <a id="3728" class="Keyword">record</a> <a id="3735" class="Symbol">{</a> <a id="3737" href="Homomorphisms.Func.Basic.html#2063" class="Field">compatible</a> <a id="3748" class="Symbol">=</a> <a id="3750" href="Homomorphisms.Func.Factor.html#3335" class="Function">φcomp</a>
                <a id="3772" class="Symbol">;</a> <a id="3774" href="Homomorphisms.Func.Basic.html#2096" class="Field">preserves≈</a> <a id="3785" class="Symbol">=</a> <a id="3787" href="Function.Bundles.html#1938" class="Field">Func.cong</a> <a id="3797" href="Homomorphisms.Func.Factor.html#3155" class="Function">φmap</a> <a id="3802" class="Symbol">}</a>

</pre>

--------------------------------

<span style="float:left;">[← Homomorphisms.Func.Kernels](Homomorphisms.Func.Kernels.html)</span>
<span style="float:right;">[Homomorphisms.Func.Isomorphisms →](Homomorphisms.Func.Isomorphisms.html)</span>

{% include UALib.Links.md %}
