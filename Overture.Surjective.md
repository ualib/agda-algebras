---
layout: default
title : "Overture.Surjective module"
date : "2021-01-12"
author: "the agda-algebras development team"
---

### <a id="surjective-functions">Surjective functions</a>

This is the [Overture.Surjective][] module of the [agda-algebras][] library.
<pre class="Agda">

<a id="278" class="Symbol">{-#</a> <a id="282" class="Keyword">OPTIONS</a> <a id="290" class="Pragma">--without-K</a> <a id="302" class="Pragma">--exact-split</a> <a id="316" class="Pragma">--safe</a> <a id="323" class="Symbol">#-}</a>
<a id="327" class="Keyword">module</a> <a id="334" href="Overture.Surjective.html" class="Module">Overture.Surjective</a> <a id="354" class="Keyword">where</a>

<a id="361" class="Comment">-- Imports from Agda and the Agda Standard Library -------------------------------------------</a>
<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>                        <a id="506" class="Keyword">using</a> <a id="512" class="Symbol">(</a> <a id="514" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="518" class="Symbol">;</a> <a id="520" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="526" class="Symbol">)</a> <a id="528" class="Keyword">renaming</a> <a id="537" class="Symbol">(</a> <a id="539" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="543" class="Symbol">to</a> <a id="546" class="Primitive">Type</a> <a id="551" class="Symbol">)</a>
<a id="553" class="Keyword">open</a> <a id="558" class="Keyword">import</a> <a id="565" href="Data.Product.html" class="Module">Data.Product</a>                          <a id="603" class="Keyword">using</a> <a id="609" class="Symbol">(</a> <a id="611" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="615" class="Symbol">;</a> <a id="617" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="619" class="Symbol">)</a>
<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="Function.Base.html" class="Module">Function.Base</a>                         <a id="671" class="Keyword">using</a> <a id="677" class="Symbol">(</a> <a id="679" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="683" class="Symbol">)</a>
<a id="685" class="Keyword">open</a> <a id="690" class="Keyword">import</a> <a id="697" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="735" class="Keyword">using</a> <a id="741" class="Symbol">(</a> <a id="743" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="747" class="Symbol">;</a> <a id="749" class="Keyword">module</a> <a id="756" href="Relation.Binary.PropositionalEquality.Core.html#2708" class="Module">≡-Reasoning</a> <a id="768" class="Symbol">;</a> <a id="770" href="Relation.Binary.PropositionalEquality.Core.html#1461" class="Function">cong-app</a> <a id="779" class="Symbol">)</a>

<a id="782" class="Comment">-- Imports from agda-algebras ----------------------------------------------------------------</a>
<a id="877" class="Keyword">open</a> <a id="882" class="Keyword">import</a> <a id="889" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="912" class="Keyword">using</a> <a id="918" class="Symbol">(</a> <a id="920" href="Overture.Preliminaries.html#9744" class="Function Operator">_≈_</a> <a id="924" class="Symbol">;</a> <a id="926" href="Overture.Preliminaries.html#5086" class="Function Operator">_⁻¹</a> <a id="930" class="Symbol">;</a> <a id="932" href="Overture.Preliminaries.html#5410" class="Function Operator">_∙_</a> <a id="936" class="Symbol">)</a>
<a id="938" class="Keyword">open</a> <a id="943" class="Keyword">import</a> <a id="950" href="Overture.Inverses.html" class="Module">Overture.Inverses</a>      <a id="973" class="Keyword">using</a> <a id="979" class="Symbol">(</a> <a id="981" href="Overture.Inverses.html#1077" class="Datatype Operator">Image_∋_</a> <a id="990" class="Symbol">;</a> <a id="992" href="Overture.Inverses.html#2190" class="Function">Inv</a> <a id="996" class="Symbol">;</a> <a id="998" href="Overture.Inverses.html#2437" class="Function">InvIsInverseʳ</a> <a id="1012" class="Symbol">)</a>

<a id="1015" class="Keyword">private</a> <a id="1023" class="Keyword">variable</a> <a id="1032" href="Overture.Surjective.html#1032" class="Generalizable">α</a> <a id="1034" href="Overture.Surjective.html#1034" class="Generalizable">β</a> <a id="1036" href="Overture.Surjective.html#1036" class="Generalizable">γ</a> <a id="1038" class="Symbol">:</a> <a id="1040" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

<pre class="Agda">

<a id="1350" class="Keyword">module</a> <a id="1357" href="Overture.Surjective.html#1357" class="Module">_</a> <a id="1359" class="Symbol">{</a><a id="1360" href="Overture.Surjective.html#1360" class="Bound">A</a> <a id="1362" class="Symbol">:</a> <a id="1364" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1369" href="Overture.Surjective.html#1032" class="Generalizable">α</a><a id="1370" class="Symbol">}{</a><a id="1372" href="Overture.Surjective.html#1372" class="Bound">B</a> <a id="1374" class="Symbol">:</a> <a id="1376" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1381" href="Overture.Surjective.html#1034" class="Generalizable">β</a><a id="1382" class="Symbol">}</a> <a id="1384" class="Keyword">where</a>
 <a id="1391" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="1404" class="Symbol">:</a> <a id="1406" class="Symbol">(</a><a id="1407" href="Overture.Surjective.html#1360" class="Bound">A</a> <a id="1409" class="Symbol">→</a> <a id="1411" href="Overture.Surjective.html#1372" class="Bound">B</a><a id="1412" class="Symbol">)</a> <a id="1414" class="Symbol">→</a>  <a id="1417" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1422" class="Symbol">(</a><a id="1423" href="Overture.Surjective.html#1369" class="Bound">α</a> <a id="1425" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1427" href="Overture.Surjective.html#1381" class="Bound">β</a><a id="1428" class="Symbol">)</a>
 <a id="1431" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="1444" href="Overture.Surjective.html#1444" class="Bound">f</a> <a id="1446" class="Symbol">=</a> <a id="1448" class="Symbol">∀</a> <a id="1450" href="Overture.Surjective.html#1450" class="Bound">y</a> <a id="1452" class="Symbol">→</a> <a id="1454" href="Overture.Inverses.html#1077" class="Datatype Operator">Image</a> <a id="1460" href="Overture.Surjective.html#1444" class="Bound">f</a> <a id="1462" href="Overture.Inverses.html#1077" class="Datatype Operator">∋</a> <a id="1464" href="Overture.Surjective.html#1450" class="Bound">y</a>

 <a id="1468" href="Overture.Surjective.html#1468" class="Function">Surjective</a> <a id="1479" class="Symbol">:</a> <a id="1481" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1486" class="Symbol">(</a><a id="1487" href="Overture.Surjective.html#1369" class="Bound">α</a> <a id="1489" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1491" href="Overture.Surjective.html#1381" class="Bound">β</a><a id="1492" class="Symbol">)</a>
 <a id="1495" href="Overture.Surjective.html#1468" class="Function">Surjective</a> <a id="1506" class="Symbol">=</a> <a id="1508" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="1510" class="Symbol">(</a><a id="1511" href="Overture.Surjective.html#1360" class="Bound">A</a> <a id="1513" class="Symbol">→</a> <a id="1515" href="Overture.Surjective.html#1372" class="Bound">B</a><a id="1516" class="Symbol">)</a> <a id="1518" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a>

</pre>
With the next definition, we can represent a *right-inverse* of a surjective function.
<pre class="Agda">

 <a id="1645" href="Overture.Surjective.html#1645" class="Function">SurjInv</a> <a id="1653" class="Symbol">:</a> <a id="1655" class="Symbol">(</a><a id="1656" href="Overture.Surjective.html#1656" class="Bound">f</a> <a id="1658" class="Symbol">:</a> <a id="1660" href="Overture.Surjective.html#1360" class="Bound">A</a> <a id="1662" class="Symbol">→</a> <a id="1664" href="Overture.Surjective.html#1372" class="Bound">B</a><a id="1665" class="Symbol">)</a> <a id="1667" class="Symbol">→</a> <a id="1669" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="1682" href="Overture.Surjective.html#1656" class="Bound">f</a> <a id="1684" class="Symbol">→</a> <a id="1686" href="Overture.Surjective.html#1372" class="Bound">B</a> <a id="1688" class="Symbol">→</a> <a id="1690" href="Overture.Surjective.html#1360" class="Bound">A</a>
 <a id="1693" href="Overture.Surjective.html#1645" class="Function">SurjInv</a> <a id="1701" href="Overture.Surjective.html#1701" class="Bound">f</a> <a id="1703" href="Overture.Surjective.html#1703" class="Bound">fE</a> <a id="1706" href="Overture.Surjective.html#1706" class="Bound">b</a> <a id="1708" class="Symbol">=</a> <a id="1710" href="Overture.Inverses.html#2190" class="Function">Inv</a> <a id="1714" href="Overture.Surjective.html#1701" class="Bound">f</a> <a id="1716" class="Symbol">(</a><a id="1717" href="Overture.Surjective.html#1703" class="Bound">fE</a> <a id="1720" href="Overture.Surjective.html#1706" class="Bound">b</a><a id="1721" class="Symbol">)</a>

</pre>
Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.
<pre class="Agda">

<a id="1913" class="Keyword">module</a> <a id="1920" href="Overture.Surjective.html#1920" class="Module">_</a> <a id="1922" class="Symbol">{</a><a id="1923" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1932" href="Overture.Surjective.html#1032" class="Generalizable">α</a><a id="1933" class="Symbol">}{</a><a id="1935" href="Overture.Surjective.html#1935" class="Bound">B</a> <a id="1937" class="Symbol">:</a> <a id="1939" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="1944" href="Overture.Surjective.html#1034" class="Generalizable">β</a><a id="1945" class="Symbol">}</a> <a id="1947" class="Keyword">where</a>

 <a id="1955" href="Overture.Surjective.html#1955" class="Function">SurjInvIsInverseʳ</a> <a id="1973" class="Symbol">:</a> <a id="1975" class="Symbol">(</a><a id="1976" href="Overture.Surjective.html#1976" class="Bound">f</a> <a id="1978" class="Symbol">:</a> <a id="1980" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="1982" class="Symbol">→</a> <a id="1984" href="Overture.Surjective.html#1935" class="Bound">B</a><a id="1985" class="Symbol">)(</a><a id="1987" href="Overture.Surjective.html#1987" class="Bound">fE</a> <a id="1990" class="Symbol">:</a> <a id="1992" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="2005" href="Overture.Surjective.html#1976" class="Bound">f</a><a id="2006" class="Symbol">)</a> <a id="2008" class="Symbol">→</a> <a id="2010" class="Symbol">∀</a> <a id="2012" href="Overture.Surjective.html#2012" class="Bound">b</a> <a id="2014" class="Symbol">→</a> <a id="2016" href="Overture.Surjective.html#1976" class="Bound">f</a> <a id="2018" class="Symbol">((</a><a id="2020" href="Overture.Surjective.html#1645" class="Function">SurjInv</a> <a id="2028" href="Overture.Surjective.html#1976" class="Bound">f</a> <a id="2030" href="Overture.Surjective.html#1987" class="Bound">fE</a><a id="2032" class="Symbol">)</a> <a id="2034" href="Overture.Surjective.html#2012" class="Bound">b</a><a id="2035" class="Symbol">)</a> <a id="2037" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2039" href="Overture.Surjective.html#2012" class="Bound">b</a>
 <a id="2042" href="Overture.Surjective.html#1955" class="Function">SurjInvIsInverseʳ</a> <a id="2060" href="Overture.Surjective.html#2060" class="Bound">f</a> <a id="2062" href="Overture.Surjective.html#2062" class="Bound">fE</a> <a id="2065" href="Overture.Surjective.html#2065" class="Bound">b</a> <a id="2067" class="Symbol">=</a> <a id="2069" href="Overture.Inverses.html#2437" class="Function">InvIsInverseʳ</a> <a id="2083" class="Symbol">(</a><a id="2084" href="Overture.Surjective.html#2062" class="Bound">fE</a> <a id="2087" href="Overture.Surjective.html#2065" class="Bound">b</a><a id="2088" class="Symbol">)</a>

 <a id="2092" class="Keyword">open</a> <a id="2097" href="Relation.Binary.PropositionalEquality.Core.html#2708" class="Module">≡-Reasoning</a>
 <a id="2110" class="Keyword">open</a> <a id="2115" href="Overture.Inverses.html#1077" class="Module Operator">Image_∋_</a>

 <a id="2126" class="Comment">-- composition law for epics</a>
 <a id="2156" href="Overture.Surjective.html#2156" class="Function">epic-factor</a> <a id="2168" class="Symbol">:</a> <a id="2170" class="Symbol">{</a><a id="2171" href="Overture.Surjective.html#2171" class="Bound">C</a> <a id="2173" class="Symbol">:</a> <a id="2175" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="2180" href="Overture.Surjective.html#1036" class="Generalizable">γ</a><a id="2181" class="Symbol">}(</a><a id="2183" href="Overture.Surjective.html#2183" class="Bound">f</a> <a id="2185" class="Symbol">:</a> <a id="2187" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="2189" class="Symbol">→</a> <a id="2191" href="Overture.Surjective.html#1935" class="Bound">B</a><a id="2192" class="Symbol">)(</a><a id="2194" href="Overture.Surjective.html#2194" class="Bound">g</a> <a id="2196" class="Symbol">:</a> <a id="2198" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="2200" class="Symbol">→</a> <a id="2202" href="Overture.Surjective.html#2171" class="Bound">C</a><a id="2203" class="Symbol">)(</a><a id="2205" href="Overture.Surjective.html#2205" class="Bound">h</a> <a id="2207" class="Symbol">:</a> <a id="2209" href="Overture.Surjective.html#2171" class="Bound">C</a> <a id="2211" class="Symbol">→</a> <a id="2213" href="Overture.Surjective.html#1935" class="Bound">B</a><a id="2214" class="Symbol">)</a>
  <a id="2218" class="Symbol">→</a>            <a id="2231" href="Overture.Surjective.html#2183" class="Bound">f</a> <a id="2233" href="Overture.Preliminaries.html#9744" class="Function Operator">≈</a> <a id="2235" href="Overture.Surjective.html#2205" class="Bound">h</a> <a id="2237" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2239" href="Overture.Surjective.html#2194" class="Bound">g</a> <a id="2241" class="Symbol">→</a> <a id="2243" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="2256" href="Overture.Surjective.html#2183" class="Bound">f</a> <a id="2258" class="Symbol">→</a> <a id="2260" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="2273" href="Overture.Surjective.html#2205" class="Bound">h</a>

 <a id="2277" href="Overture.Surjective.html#2156" class="Function">epic-factor</a> <a id="2289" href="Overture.Surjective.html#2289" class="Bound">f</a> <a id="2291" href="Overture.Surjective.html#2291" class="Bound">g</a> <a id="2293" href="Overture.Surjective.html#2293" class="Bound">h</a> <a id="2295" href="Overture.Surjective.html#2295" class="Bound">compId</a> <a id="2302" href="Overture.Surjective.html#2302" class="Bound">fe</a> <a id="2305" href="Overture.Surjective.html#2305" class="Bound">y</a> <a id="2307" class="Symbol">=</a> <a id="2309" href="Overture.Surjective.html#2480" class="Function">Goal</a>
  <a id="2316" class="Keyword">where</a>
   <a id="2325" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2330" class="Symbol">:</a> <a id="2332" href="Overture.Surjective.html#1935" class="Bound">B</a> <a id="2334" class="Symbol">→</a> <a id="2336" href="Overture.Surjective.html#1923" class="Bound">A</a>
   <a id="2341" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2346" class="Symbol">=</a> <a id="2348" href="Overture.Surjective.html#1645" class="Function">SurjInv</a> <a id="2356" href="Overture.Surjective.html#2289" class="Bound">f</a> <a id="2358" href="Overture.Surjective.html#2302" class="Bound">fe</a>

   <a id="2365" href="Overture.Surjective.html#2365" class="Function">ζ</a> <a id="2367" class="Symbol">:</a> <a id="2369" href="Overture.Surjective.html#2305" class="Bound">y</a> <a id="2371" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2373" href="Overture.Surjective.html#2289" class="Bound">f</a> <a id="2375" class="Symbol">(</a><a id="2376" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2381" href="Overture.Surjective.html#2305" class="Bound">y</a><a id="2382" class="Symbol">)</a>
   <a id="2387" href="Overture.Surjective.html#2365" class="Function">ζ</a> <a id="2389" class="Symbol">=</a> <a id="2391" class="Symbol">(</a><a id="2392" href="Overture.Surjective.html#1955" class="Function">SurjInvIsInverseʳ</a> <a id="2410" href="Overture.Surjective.html#2289" class="Bound">f</a> <a id="2412" href="Overture.Surjective.html#2302" class="Bound">fe</a> <a id="2415" href="Overture.Surjective.html#2305" class="Bound">y</a><a id="2416" class="Symbol">)</a><a id="2417" href="Overture.Preliminaries.html#5086" class="Function Operator">⁻¹</a>

   <a id="2424" href="Overture.Surjective.html#2424" class="Function">η</a> <a id="2426" class="Symbol">:</a> <a id="2428" href="Overture.Surjective.html#2305" class="Bound">y</a> <a id="2430" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2432" class="Symbol">(</a><a id="2433" href="Overture.Surjective.html#2293" class="Bound">h</a> <a id="2435" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2437" href="Overture.Surjective.html#2291" class="Bound">g</a><a id="2438" class="Symbol">)</a> <a id="2440" class="Symbol">(</a><a id="2441" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2446" href="Overture.Surjective.html#2305" class="Bound">y</a><a id="2447" class="Symbol">)</a>
   <a id="2452" href="Overture.Surjective.html#2424" class="Function">η</a> <a id="2454" class="Symbol">=</a> <a id="2456" href="Overture.Surjective.html#2365" class="Function">ζ</a> <a id="2458" href="Overture.Preliminaries.html#5410" class="Function Operator">∙</a> <a id="2460" href="Overture.Surjective.html#2295" class="Bound">compId</a> <a id="2467" class="Symbol">(</a><a id="2468" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2473" href="Overture.Surjective.html#2305" class="Bound">y</a><a id="2474" class="Symbol">)</a>

   <a id="2480" href="Overture.Surjective.html#2480" class="Function">Goal</a> <a id="2485" class="Symbol">:</a> <a id="2487" href="Overture.Inverses.html#1077" class="Datatype Operator">Image</a> <a id="2493" href="Overture.Surjective.html#2293" class="Bound">h</a> <a id="2495" href="Overture.Inverses.html#1077" class="Datatype Operator">∋</a> <a id="2497" href="Overture.Surjective.html#2305" class="Bound">y</a>
   <a id="2502" href="Overture.Surjective.html#2480" class="Function">Goal</a> <a id="2507" class="Symbol">=</a> <a id="2509" href="Overture.Inverses.html#1125" class="InductiveConstructor">eq</a> <a id="2512" class="Symbol">(</a><a id="2513" href="Overture.Surjective.html#2291" class="Bound">g</a> <a id="2515" class="Symbol">(</a><a id="2516" href="Overture.Surjective.html#2325" class="Function">finv</a> <a id="2521" href="Overture.Surjective.html#2305" class="Bound">y</a><a id="2522" class="Symbol">))</a> <a id="2525" href="Overture.Surjective.html#2424" class="Function">η</a>

 <a id="2529" href="Overture.Surjective.html#2529" class="Function">epic-factor-intensional</a> <a id="2553" class="Symbol">:</a> <a id="2555" class="Symbol">{</a><a id="2556" href="Overture.Surjective.html#2556" class="Bound">C</a> <a id="2558" class="Symbol">:</a> <a id="2560" href="Overture.Surjective.html#546" class="Primitive">Type</a> <a id="2565" href="Overture.Surjective.html#1036" class="Generalizable">γ</a><a id="2566" class="Symbol">}(</a><a id="2568" href="Overture.Surjective.html#2568" class="Bound">f</a> <a id="2570" class="Symbol">:</a> <a id="2572" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="2574" class="Symbol">→</a> <a id="2576" href="Overture.Surjective.html#1935" class="Bound">B</a><a id="2577" class="Symbol">)(</a><a id="2579" href="Overture.Surjective.html#2579" class="Bound">g</a> <a id="2581" class="Symbol">:</a> <a id="2583" href="Overture.Surjective.html#1923" class="Bound">A</a> <a id="2585" class="Symbol">→</a> <a id="2587" href="Overture.Surjective.html#2556" class="Bound">C</a><a id="2588" class="Symbol">)(</a><a id="2590" href="Overture.Surjective.html#2590" class="Bound">h</a> <a id="2592" class="Symbol">:</a> <a id="2594" href="Overture.Surjective.html#2556" class="Bound">C</a> <a id="2596" class="Symbol">→</a> <a id="2598" href="Overture.Surjective.html#1935" class="Bound">B</a><a id="2599" class="Symbol">)</a>
  <a id="2603" class="Symbol">→</a>                        <a id="2628" href="Overture.Surjective.html#2568" class="Bound">f</a> <a id="2630" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2632" href="Overture.Surjective.html#2590" class="Bound">h</a> <a id="2634" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2636" href="Overture.Surjective.html#2579" class="Bound">g</a> <a id="2638" class="Symbol">→</a> <a id="2640" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="2653" href="Overture.Surjective.html#2568" class="Bound">f</a> <a id="2655" class="Symbol">→</a> <a id="2657" href="Overture.Surjective.html#1391" class="Function">IsSurjective</a> <a id="2670" href="Overture.Surjective.html#2590" class="Bound">h</a>

 <a id="2674" href="Overture.Surjective.html#2529" class="Function">epic-factor-intensional</a> <a id="2698" href="Overture.Surjective.html#2698" class="Bound">f</a> <a id="2700" href="Overture.Surjective.html#2700" class="Bound">g</a> <a id="2702" href="Overture.Surjective.html#2702" class="Bound">h</a> <a id="2704" href="Overture.Surjective.html#2704" class="Bound">compId</a> <a id="2711" href="Overture.Surjective.html#2711" class="Bound">fe</a> <a id="2714" href="Overture.Surjective.html#2714" class="Bound">y</a> <a id="2716" class="Symbol">=</a> <a id="2718" href="Overture.Surjective.html#2900" class="Function">Goal</a>
  <a id="2725" class="Keyword">where</a>
   <a id="2734" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2739" class="Symbol">:</a> <a id="2741" href="Overture.Surjective.html#1935" class="Bound">B</a> <a id="2743" class="Symbol">→</a> <a id="2745" href="Overture.Surjective.html#1923" class="Bound">A</a>
   <a id="2750" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2755" class="Symbol">=</a> <a id="2757" href="Overture.Surjective.html#1645" class="Function">SurjInv</a> <a id="2765" href="Overture.Surjective.html#2698" class="Bound">f</a> <a id="2767" href="Overture.Surjective.html#2711" class="Bound">fe</a>

   <a id="2774" href="Overture.Surjective.html#2774" class="Function">ζ</a> <a id="2776" class="Symbol">:</a> <a id="2778" href="Overture.Surjective.html#2698" class="Bound">f</a> <a id="2780" class="Symbol">(</a><a id="2781" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2786" href="Overture.Surjective.html#2714" class="Bound">y</a><a id="2787" class="Symbol">)</a> <a id="2789" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2791" href="Overture.Surjective.html#2714" class="Bound">y</a>
   <a id="2796" href="Overture.Surjective.html#2774" class="Function">ζ</a> <a id="2798" class="Symbol">=</a> <a id="2800" href="Overture.Surjective.html#1955" class="Function">SurjInvIsInverseʳ</a> <a id="2818" href="Overture.Surjective.html#2698" class="Bound">f</a> <a id="2820" href="Overture.Surjective.html#2711" class="Bound">fe</a> <a id="2823" href="Overture.Surjective.html#2714" class="Bound">y</a>

   <a id="2829" href="Overture.Surjective.html#2829" class="Function">η</a> <a id="2831" class="Symbol">:</a> <a id="2833" class="Symbol">(</a><a id="2834" href="Overture.Surjective.html#2702" class="Bound">h</a> <a id="2836" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2838" href="Overture.Surjective.html#2700" class="Bound">g</a><a id="2839" class="Symbol">)</a> <a id="2841" class="Symbol">(</a><a id="2842" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2847" href="Overture.Surjective.html#2714" class="Bound">y</a><a id="2848" class="Symbol">)</a> <a id="2850" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2852" href="Overture.Surjective.html#2714" class="Bound">y</a>
   <a id="2857" href="Overture.Surjective.html#2829" class="Function">η</a> <a id="2859" class="Symbol">=</a> <a id="2861" class="Symbol">(</a><a id="2862" href="Relation.Binary.PropositionalEquality.Core.html#1461" class="Function">cong-app</a> <a id="2871" class="Symbol">(</a><a id="2872" href="Overture.Surjective.html#2704" class="Bound">compId</a> <a id="2879" href="Overture.Preliminaries.html#5086" class="Function Operator">⁻¹</a><a id="2881" class="Symbol">)(</a><a id="2883" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2888" href="Overture.Surjective.html#2714" class="Bound">y</a><a id="2889" class="Symbol">))</a> <a id="2892" href="Overture.Preliminaries.html#5410" class="Function Operator">∙</a> <a id="2894" href="Overture.Surjective.html#2774" class="Function">ζ</a>

   <a id="2900" href="Overture.Surjective.html#2900" class="Function">Goal</a> <a id="2905" class="Symbol">:</a> <a id="2907" href="Overture.Inverses.html#1077" class="Datatype Operator">Image</a> <a id="2913" href="Overture.Surjective.html#2702" class="Bound">h</a> <a id="2915" href="Overture.Inverses.html#1077" class="Datatype Operator">∋</a> <a id="2917" href="Overture.Surjective.html#2714" class="Bound">y</a>
   <a id="2922" href="Overture.Surjective.html#2900" class="Function">Goal</a> <a id="2927" class="Symbol">=</a> <a id="2929" href="Overture.Inverses.html#1125" class="InductiveConstructor">eq</a> <a id="2932" class="Symbol">(</a><a id="2933" href="Overture.Surjective.html#2700" class="Bound">g</a> <a id="2935" class="Symbol">(</a><a id="2936" href="Overture.Surjective.html#2734" class="Function">finv</a> <a id="2941" href="Overture.Surjective.html#2714" class="Bound">y</a><a id="2942" class="Symbol">))</a> <a id="2945" class="Symbol">(</a><a id="2946" href="Overture.Surjective.html#2829" class="Function">η</a> <a id="2948" href="Overture.Preliminaries.html#5086" class="Function Operator">⁻¹</a><a id="2950" class="Symbol">)</a>

</pre>

--------------------------------------

<span style="float:left;">[← Overture.Injective](Overture.Injective.html)</span>
<span style="float:right;">[Overture.Transformers →](Overture.Transformers.html)</span>

{% include UALib.Links.md %}

