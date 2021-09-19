---
layout: default
title : "Homomorphisms.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

### <a id="properties-of-homomorphisms">Properties of Homomorphisms</a>

This is the [Homomorphisms.Properties] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="343" class="Symbol">{-#</a> <a id="347" class="Keyword">OPTIONS</a> <a id="355" class="Pragma">--without-K</a> <a id="367" class="Pragma">--exact-split</a> <a id="381" class="Pragma">--safe</a> <a id="388" class="Symbol">#-}</a>

<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="Algebras.Basic.html" class="Module">Algebras.Basic</a>

<a id="421" class="Keyword">module</a> <a id="428" href="Homomorphisms.Properties.html" class="Module">Homomorphisms.Properties</a> <a id="453" class="Symbol">{</a><a id="454" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a> <a id="456" class="Symbol">:</a> <a id="458" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="468" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="470" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a><a id="471" class="Symbol">}</a> <a id="473" class="Keyword">where</a>

<a id="480" class="Comment">-- Imports from Agda and the Agda Standard Library --------------------------------</a>
<a id="564" class="Keyword">open</a> <a id="569" class="Keyword">import</a> <a id="576" href="Data.Product.html" class="Module">Data.Product</a>   <a id="591" class="Keyword">using</a> <a id="597" class="Symbol">(</a> <a id="599" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="603" class="Symbol">)</a>
<a id="605" class="Keyword">open</a> <a id="610" class="Keyword">import</a> <a id="617" href="Function.Base.html" class="Module">Function.Base</a>  <a id="632" class="Keyword">using</a> <a id="638" class="Symbol">(</a> <a id="640" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="644" class="Symbol">)</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="Level.html" class="Module">Level</a>          <a id="673" class="Keyword">using</a> <a id="679" class="Symbol">(</a> <a id="681" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="687" class="Symbol">)</a>
<a id="689" class="Keyword">open</a> <a id="694" class="Keyword">import</a> <a id="701" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                           <a id="766" class="Keyword">using</a> <a id="772" class="Symbol">(</a> <a id="774" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="778" class="Symbol">;</a> <a id="780" class="Keyword">module</a> <a id="787" href="Relation.Binary.PropositionalEquality.Core.html#2708" class="Module">≡-Reasoning</a> <a id="799" class="Symbol">;</a> <a id="801" href="Relation.Binary.PropositionalEquality.Core.html#1130" class="Function">cong</a> <a id="806" class="Symbol">;</a> <a id="808" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="813" class="Symbol">)</a>

<a id="816" class="Comment">-- -- Imports from the Agda Universal Algebras Library --------------------------------</a>
<a id="904" class="Keyword">open</a> <a id="909" class="Keyword">import</a> <a id="916" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>       <a id="945" class="Keyword">using</a> <a id="951" class="Symbol">(</a> <a id="953" href="Overture.Preliminaries.html#4383" class="Function Operator">∣_∣</a> <a id="957" class="Symbol">;</a> <a id="959" href="Overture.Preliminaries.html#4421" class="Function Operator">∥_∥</a> <a id="963" class="Symbol">)</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="Homomorphisms.Basic.html" class="Module">Homomorphisms.Basic</a>  <a id="998" class="Symbol">{</a><a id="999" class="Argument">𝑆</a> <a id="1001" class="Symbol">=</a> <a id="1003" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="1004" class="Symbol">}</a> <a id="1006" class="Keyword">using</a> <a id="1012" class="Symbol">(</a> <a id="1014" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="1018" class="Symbol">;</a> <a id="1020" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a> <a id="1036" class="Symbol">)</a>
<a id="1038" class="Keyword">private</a> <a id="1046" class="Keyword">variable</a> <a id="1055" href="Homomorphisms.Properties.html#1055" class="Generalizable">α</a> <a id="1057" href="Homomorphisms.Properties.html#1057" class="Generalizable">β</a> <a id="1059" href="Homomorphisms.Properties.html#1059" class="Generalizable">γ</a> <a id="1061" href="Homomorphisms.Properties.html#1061" class="Generalizable">ρ</a> <a id="1063" class="Symbol">:</a> <a id="1065" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>


#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

<pre class="Agda">

<a id="1278" class="Keyword">open</a> <a id="1283" href="Relation.Binary.PropositionalEquality.Core.html#2708" class="Module">≡-Reasoning</a>

<a id="1296" class="Keyword">module</a> <a id="1303" href="Homomorphisms.Properties.html#1303" class="Module">_</a> <a id="1305" class="Symbol">(</a><a id="1306" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1308" class="Symbol">:</a> <a id="1310" href="Algebras.Basic.html#6222" class="Function">Algebra</a> <a id="1318" href="Homomorphisms.Properties.html#1055" class="Generalizable">α</a> <a id="1320" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="1321" class="Symbol">){</a><a id="1323" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1325" class="Symbol">:</a> <a id="1327" href="Algebras.Basic.html#6222" class="Function">Algebra</a> <a id="1335" href="Homomorphisms.Properties.html#1057" class="Generalizable">β</a> <a id="1337" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="1338" class="Symbol">}(</a><a id="1340" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a> <a id="1342" class="Symbol">:</a> <a id="1344" href="Algebras.Basic.html#6222" class="Function">Algebra</a> <a id="1352" href="Homomorphisms.Properties.html#1059" class="Generalizable">γ</a> <a id="1354" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="1355" class="Symbol">)</a> <a id="1357" class="Keyword">where</a>

  <a id="1366" href="Homomorphisms.Properties.html#1366" class="Function">∘-hom</a> <a id="1372" class="Symbol">:</a> <a id="1374" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="1378" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1380" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a>  <a id="1383" class="Symbol">→</a>  <a id="1386" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="1390" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1392" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a>  <a id="1395" class="Symbol">→</a>  <a id="1398" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="1402" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1404" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a>
  <a id="1408" href="Homomorphisms.Properties.html#1366" class="Function">∘-hom</a> <a id="1414" class="Symbol">(</a><a id="1415" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1417" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1419" href="Homomorphisms.Properties.html#1419" class="Bound">ghom</a><a id="1423" class="Symbol">)</a> <a id="1425" class="Symbol">(</a><a id="1426" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1428" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1430" href="Homomorphisms.Properties.html#1430" class="Bound">hhom</a><a id="1434" class="Symbol">)</a> <a id="1436" class="Symbol">=</a> <a id="1438" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1440" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1442" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1444" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1446" href="Homomorphisms.Properties.html#1461" class="Function">Goal</a> <a id="1451" class="Keyword">where</a>

   <a id="1461" href="Homomorphisms.Properties.html#1461" class="Function">Goal</a> <a id="1466" class="Symbol">:</a> <a id="1468" class="Symbol">∀</a> <a id="1470" href="Homomorphisms.Properties.html#1470" class="Bound">𝑓</a> <a id="1472" href="Homomorphisms.Properties.html#1472" class="Bound">a</a> <a id="1474" class="Symbol">→</a> <a id="1476" class="Symbol">(</a><a id="1477" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1479" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1481" href="Homomorphisms.Properties.html#1415" class="Bound">g</a><a id="1482" class="Symbol">)((</a><a id="1485" href="Homomorphisms.Properties.html#1470" class="Bound">𝑓</a> <a id="1487" href="Algebras.Basic.html#9397" class="Function Operator">̂</a> <a id="1489" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a><a id="1490" class="Symbol">)</a> <a id="1492" href="Homomorphisms.Properties.html#1472" class="Bound">a</a><a id="1493" class="Symbol">)</a> <a id="1495" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1497" class="Symbol">(</a><a id="1498" href="Homomorphisms.Properties.html#1470" class="Bound">𝑓</a> <a id="1500" href="Algebras.Basic.html#9397" class="Function Operator">̂</a> <a id="1502" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a><a id="1503" class="Symbol">)(</a><a id="1505" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1507" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1509" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1511" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1513" href="Homomorphisms.Properties.html#1472" class="Bound">a</a><a id="1514" class="Symbol">)</a>
   <a id="1519" href="Homomorphisms.Properties.html#1461" class="Function">Goal</a> <a id="1524" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1526" href="Homomorphisms.Properties.html#1526" class="Bound">a</a> <a id="1528" class="Symbol">=</a> <a id="1530" class="Symbol">(</a><a id="1531" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1533" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1535" href="Homomorphisms.Properties.html#1415" class="Bound">g</a><a id="1536" class="Symbol">)((</a><a id="1539" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1541" href="Algebras.Basic.html#9397" class="Function Operator">̂</a> <a id="1543" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a><a id="1544" class="Symbol">)</a> <a id="1546" href="Homomorphisms.Properties.html#1526" class="Bound">a</a><a id="1547" class="Symbol">)</a>     <a id="1553" href="Relation.Binary.PropositionalEquality.Core.html#2923" class="Function">≡⟨</a> <a id="1556" href="Relation.Binary.PropositionalEquality.Core.html#1130" class="Function">cong</a> <a id="1561" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1563" class="Symbol">(</a> <a id="1565" href="Homomorphisms.Properties.html#1419" class="Bound">ghom</a> <a id="1570" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1572" href="Homomorphisms.Properties.html#1526" class="Bound">a</a> <a id="1574" class="Symbol">)</a> <a id="1576" href="Relation.Binary.PropositionalEquality.Core.html#2923" class="Function">⟩</a>
              <a id="1592" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1594" class="Symbol">((</a><a id="1596" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1598" href="Algebras.Basic.html#9397" class="Function Operator">̂</a> <a id="1600" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a><a id="1601" class="Symbol">)(</a><a id="1603" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1605" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1607" href="Homomorphisms.Properties.html#1526" class="Bound">a</a><a id="1608" class="Symbol">))</a>     <a id="1615" href="Relation.Binary.PropositionalEquality.Core.html#2923" class="Function">≡⟨</a> <a id="1618" href="Homomorphisms.Properties.html#1430" class="Bound">hhom</a> <a id="1623" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1625" class="Symbol">(</a> <a id="1627" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1629" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1631" href="Homomorphisms.Properties.html#1526" class="Bound">a</a> <a id="1633" class="Symbol">)</a> <a id="1635" href="Relation.Binary.PropositionalEquality.Core.html#2923" class="Function">⟩</a>
              <a id="1651" class="Symbol">(</a><a id="1652" href="Homomorphisms.Properties.html#1524" class="Bound">𝑓</a> <a id="1654" href="Algebras.Basic.html#9397" class="Function Operator">̂</a> <a id="1656" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a><a id="1657" class="Symbol">)(</a><a id="1659" href="Homomorphisms.Properties.html#1426" class="Bound">h</a> <a id="1661" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1663" href="Homomorphisms.Properties.html#1415" class="Bound">g</a> <a id="1665" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1667" href="Homomorphisms.Properties.html#1526" class="Bound">a</a><a id="1668" class="Symbol">)</a>     <a id="1674" href="Relation.Binary.PropositionalEquality.Core.html#3105" class="Function Operator">∎</a>


  <a id="1680" href="Homomorphisms.Properties.html#1680" class="Function">∘-is-hom</a> <a id="1689" class="Symbol">:</a> <a id="1691" class="Symbol">{</a><a id="1692" href="Homomorphisms.Properties.html#1692" class="Bound">f</a> <a id="1694" class="Symbol">:</a> <a id="1696" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1698" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1700" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1702" class="Symbol">→</a> <a id="1704" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1706" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1708" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a><a id="1709" class="Symbol">}{</a><a id="1711" href="Homomorphisms.Properties.html#1711" class="Bound">g</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1717" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1719" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1721" class="Symbol">→</a> <a id="1723" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1725" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a> <a id="1727" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a><a id="1728" class="Symbol">}</a>
   <a id="1733" class="Symbol">→</a>         <a id="1743" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a> <a id="1759" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1761" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1763" href="Homomorphisms.Properties.html#1692" class="Bound">f</a> <a id="1765" class="Symbol">→</a> <a id="1767" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a> <a id="1783" href="Homomorphisms.Properties.html#1323" class="Bound">𝑩</a> <a id="1785" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a> <a id="1787" href="Homomorphisms.Properties.html#1711" class="Bound">g</a> <a id="1789" class="Symbol">→</a> <a id="1791" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a> <a id="1807" href="Homomorphisms.Properties.html#1306" class="Bound">𝑨</a> <a id="1809" href="Homomorphisms.Properties.html#1340" class="Bound">𝑪</a> <a id="1811" class="Symbol">(</a><a id="1812" href="Homomorphisms.Properties.html#1711" class="Bound">g</a> <a id="1814" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1816" href="Homomorphisms.Properties.html#1692" class="Bound">f</a><a id="1817" class="Symbol">)</a>
  <a id="1821" href="Homomorphisms.Properties.html#1680" class="Function">∘-is-hom</a> <a id="1830" class="Symbol">{</a><a id="1831" href="Homomorphisms.Properties.html#1831" class="Bound">f</a><a id="1832" class="Symbol">}</a> <a id="1834" class="Symbol">{</a><a id="1835" href="Homomorphisms.Properties.html#1835" class="Bound">g</a><a id="1836" class="Symbol">}</a> <a id="1838" href="Homomorphisms.Properties.html#1838" class="Bound">fhom</a> <a id="1843" href="Homomorphisms.Properties.html#1843" class="Bound">ghom</a> <a id="1848" class="Symbol">=</a> <a id="1850" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="1852" href="Homomorphisms.Properties.html#1366" class="Function">∘-hom</a> <a id="1858" class="Symbol">(</a><a id="1859" href="Homomorphisms.Properties.html#1831" class="Bound">f</a> <a id="1861" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1863" href="Homomorphisms.Properties.html#1838" class="Bound">fhom</a><a id="1867" class="Symbol">)</a> <a id="1869" class="Symbol">(</a><a id="1870" href="Homomorphisms.Properties.html#1835" class="Bound">g</a> <a id="1872" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1874" href="Homomorphisms.Properties.html#1843" class="Bound">ghom</a><a id="1878" class="Symbol">)</a> <a id="1880" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a>

</pre>

A homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

<pre class="Agda">

<a id="2014" class="Keyword">open</a> <a id="2019" href="Level.html" class="Module">Level</a>

<a id="Lift-hom"></a><a id="2026" href="Homomorphisms.Properties.html#2026" class="Function">Lift-hom</a> <a id="2035" class="Symbol">:</a> <a id="2037" class="Symbol">{</a><a id="2038" href="Homomorphisms.Properties.html#2038" class="Bound">𝑨</a> <a id="2040" class="Symbol">:</a> <a id="2042" href="Algebras.Basic.html#6222" class="Function">Algebra</a> <a id="2050" href="Homomorphisms.Properties.html#1055" class="Generalizable">α</a> <a id="2052" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="2053" class="Symbol">}(</a><a id="2055" href="Homomorphisms.Properties.html#2055" class="Bound">ℓᵃ</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2065" class="Symbol">){</a><a id="2067" href="Homomorphisms.Properties.html#2067" class="Bound">𝑩</a> <a id="2069" class="Symbol">:</a> <a id="2071" href="Algebras.Basic.html#6222" class="Function">Algebra</a> <a id="2079" href="Homomorphisms.Properties.html#1057" class="Generalizable">β</a> <a id="2081" href="Homomorphisms.Properties.html#454" class="Bound">𝑆</a><a id="2082" class="Symbol">}</a> <a id="2084" class="Symbol">(</a><a id="2085" href="Homomorphisms.Properties.html#2085" class="Bound">ℓᵇ</a> <a id="2088" class="Symbol">:</a> <a id="2090" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2095" class="Symbol">)</a>
 <a id="2098" class="Symbol">→</a>         <a id="2108" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="2112" href="Homomorphisms.Properties.html#2038" class="Bound">𝑨</a> <a id="2114" href="Homomorphisms.Properties.html#2067" class="Bound">𝑩</a>  <a id="2117" class="Symbol">→</a>  <a id="2120" href="Homomorphisms.Basic.html#2647" class="Function">hom</a> <a id="2124" class="Symbol">(</a><a id="2125" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2134" href="Homomorphisms.Properties.html#2038" class="Bound">𝑨</a> <a id="2136" href="Homomorphisms.Properties.html#2055" class="Bound">ℓᵃ</a><a id="2138" class="Symbol">)</a> <a id="2140" class="Symbol">(</a><a id="2141" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2150" href="Homomorphisms.Properties.html#2067" class="Bound">𝑩</a> <a id="2152" href="Homomorphisms.Properties.html#2085" class="Bound">ℓᵇ</a><a id="2154" class="Symbol">)</a>

<a id="2157" href="Homomorphisms.Properties.html#2026" class="Function">Lift-hom</a> <a id="2166" class="Symbol">{</a><a id="2167" class="Argument">𝑨</a> <a id="2169" class="Symbol">=</a> <a id="2171" href="Homomorphisms.Properties.html#2171" class="Bound">𝑨</a><a id="2172" class="Symbol">}</a> <a id="2174" href="Homomorphisms.Properties.html#2174" class="Bound">ℓᵃ</a> <a id="2177" class="Symbol">{</a><a id="2178" href="Homomorphisms.Properties.html#2178" class="Bound">𝑩</a><a id="2179" class="Symbol">}</a> <a id="2181" href="Homomorphisms.Properties.html#2181" class="Bound">ℓᵇ</a> <a id="2184" class="Symbol">(</a><a id="2185" href="Homomorphisms.Properties.html#2185" class="Bound">f</a> <a id="2187" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2189" href="Homomorphisms.Properties.html#2189" class="Bound">fhom</a><a id="2193" class="Symbol">)</a> <a id="2195" class="Symbol">=</a> <a id="2197" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="2202" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2204" href="Homomorphisms.Properties.html#2185" class="Bound">f</a> <a id="2206" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2208" href="Level.html#470" class="Field">lower</a> <a id="2214" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2216" href="Homomorphisms.Properties.html#2350" class="Function">Goal</a>
 <a id="2222" class="Keyword">where</a>
 <a id="2229" href="Homomorphisms.Properties.html#2229" class="Function">lABh</a> <a id="2234" class="Symbol">:</a> <a id="2236" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a> <a id="2252" class="Symbol">(</a><a id="2253" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2262" href="Homomorphisms.Properties.html#2171" class="Bound">𝑨</a> <a id="2264" href="Homomorphisms.Properties.html#2174" class="Bound">ℓᵃ</a><a id="2266" class="Symbol">)</a> <a id="2268" href="Homomorphisms.Properties.html#2178" class="Bound">𝑩</a> <a id="2270" class="Symbol">(</a><a id="2271" href="Homomorphisms.Properties.html#2185" class="Bound">f</a> <a id="2273" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2275" href="Level.html#470" class="Field">lower</a><a id="2280" class="Symbol">)</a>
 <a id="2283" href="Homomorphisms.Properties.html#2229" class="Function">lABh</a> <a id="2288" class="Symbol">=</a> <a id="2290" href="Homomorphisms.Properties.html#1680" class="Function">∘-is-hom</a> <a id="2299" class="Symbol">(</a><a id="2300" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2309" href="Homomorphisms.Properties.html#2171" class="Bound">𝑨</a> <a id="2311" href="Homomorphisms.Properties.html#2174" class="Bound">ℓᵃ</a><a id="2313" class="Symbol">)</a> <a id="2315" href="Homomorphisms.Properties.html#2178" class="Bound">𝑩</a> <a id="2317" class="Symbol">{</a><a id="2318" href="Level.html#470" class="Field">lower</a><a id="2323" class="Symbol">}{</a><a id="2325" href="Homomorphisms.Properties.html#2185" class="Bound">f</a><a id="2326" class="Symbol">}</a> <a id="2328" class="Symbol">(λ</a> <a id="2331" href="Homomorphisms.Properties.html#2331" class="Bound">_</a> <a id="2333" href="Homomorphisms.Properties.html#2333" class="Bound">_</a> <a id="2335" class="Symbol">→</a> <a id="2337" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="2341" class="Symbol">)</a> <a id="2343" href="Homomorphisms.Properties.html#2189" class="Bound">fhom</a>

 <a id="2350" href="Homomorphisms.Properties.html#2350" class="Function">Goal</a> <a id="2355" class="Symbol">:</a> <a id="2357" href="Homomorphisms.Basic.html#2538" class="Function">is-homomorphism</a><a id="2372" class="Symbol">(</a><a id="2373" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2382" href="Homomorphisms.Properties.html#2171" class="Bound">𝑨</a> <a id="2384" href="Homomorphisms.Properties.html#2174" class="Bound">ℓᵃ</a><a id="2386" class="Symbol">)(</a><a id="2388" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2397" href="Homomorphisms.Properties.html#2178" class="Bound">𝑩</a> <a id="2399" href="Homomorphisms.Properties.html#2181" class="Bound">ℓᵇ</a><a id="2401" class="Symbol">)</a> <a id="2403" class="Symbol">(</a><a id="2404" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="2409" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2411" class="Symbol">(</a><a id="2412" href="Homomorphisms.Properties.html#2185" class="Bound">f</a> <a id="2414" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2416" href="Level.html#470" class="Field">lower</a><a id="2421" class="Symbol">))</a>
 <a id="2425" href="Homomorphisms.Properties.html#2350" class="Function">Goal</a> <a id="2430" class="Symbol">=</a> <a id="2432" href="Homomorphisms.Properties.html#1680" class="Function">∘-is-hom</a> <a id="2441" class="Symbol">(</a><a id="2442" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2451" href="Homomorphisms.Properties.html#2171" class="Bound">𝑨</a> <a id="2453" href="Homomorphisms.Properties.html#2174" class="Bound">ℓᵃ</a><a id="2455" class="Symbol">)</a> <a id="2457" class="Symbol">(</a><a id="2458" href="Algebras.Basic.html#10858" class="Function">Lift-Alg</a> <a id="2467" href="Homomorphisms.Properties.html#2178" class="Bound">𝑩</a> <a id="2469" href="Homomorphisms.Properties.html#2181" class="Bound">ℓᵇ</a><a id="2471" class="Symbol">){</a><a id="2473" href="Homomorphisms.Properties.html#2185" class="Bound">f</a> <a id="2475" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2477" href="Level.html#470" class="Field">lower</a><a id="2482" class="Symbol">}{</a><a id="2484" href="Level.html#457" class="InductiveConstructor">lift</a><a id="2488" class="Symbol">}</a> <a id="2490" href="Homomorphisms.Properties.html#2229" class="Function">lABh</a> <a id="2495" class="Symbol">λ</a> <a id="2497" href="Homomorphisms.Properties.html#2497" class="Bound">_</a> <a id="2499" href="Homomorphisms.Properties.html#2499" class="Bound">_</a> <a id="2501" class="Symbol">→</a> <a id="2503" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

We should probably point out that while the lifting and lowering homomorphisms are important for our formal treatment of algebras in type theory, they never arise---in fact, they are not even definable---in classical universal algebra based on set theory.

---------------------------------

<span style="float:left;">[← Homomorphisms.Basic](Homomorphisms.Basic.html)</span>
<span style="float:right;">[Homomorphisms.Kernels →](Homomorphisms.Kernels.html)</span>

{% include UALib.Links.md %}