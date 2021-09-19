---
layout: default
title : "Varieties.Func.Closure module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

#### <a id="closure-operators-for-setoid-algebras">Closure Operators for Setoid Algebras</a>

Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

<pre class="Agda">

<a id="526" class="Symbol">{-#</a> <a id="530" class="Keyword">OPTIONS</a> <a id="538" class="Pragma">--without-K</a> <a id="550" class="Pragma">--exact-split</a> <a id="564" class="Pragma">--safe</a> <a id="571" class="Symbol">#-}</a>

<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="603" class="Keyword">using</a> <a id="609" class="Symbol">(</a> <a id="611" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="613" class="Symbol">;</a> <a id="615" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a> <a id="617" class="Symbol">;</a> <a id="619" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="629" class="Symbol">)</a>

<a id="632" class="Keyword">module</a> <a id="639" href="Varieties.Func.Closure.html" class="Module">Varieties.Func.Closure</a> <a id="662" class="Symbol">{</a><a id="663" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a> <a id="665" class="Symbol">:</a> <a id="667" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="677" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="679" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a><a id="680" class="Symbol">}</a> <a id="682" class="Keyword">where</a>

<a id="689" class="Comment">-- imports from Agda and the Agda Standard Library -------------------------------------------</a>
<a id="784" class="Keyword">open</a> <a id="789" class="Keyword">import</a> <a id="796" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="811" class="Keyword">using</a> <a id="817" class="Symbol">(</a> <a id="819" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="823" class="Symbol">;</a> <a id="825" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="830" class="Symbol">;</a> <a id="832" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="838" class="Symbol">)</a> <a id="840" class="Keyword">renaming</a> <a id="849" class="Symbol">(</a> <a id="851" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="855" class="Symbol">to</a> <a id="858" class="Primitive">Type</a> <a id="863" class="Symbol">)</a>
<a id="865" class="Keyword">open</a> <a id="870" class="Keyword">import</a> <a id="877" href="Data.Product.html" class="Module">Data.Product</a>   <a id="892" class="Keyword">using</a> <a id="898" class="Symbol">(</a> <a id="900" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="904" class="Symbol">;</a> <a id="906" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="915" class="Symbol">)</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="944" class="Keyword">using</a> <a id="950" class="Symbol">(</a> <a id="952" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="957" class="Symbol">;</a> <a id="959" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="963" class="Symbol">;</a> <a id="965" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a> <a id="969" class="Symbol">)</a>

<a id="972" class="Comment">-- Imports from the Agda Universal Algebra Library ---------------------------------------------</a>
<a id="1069" class="Keyword">open</a> <a id="1074" class="Keyword">import</a> <a id="1081" href="Algebras.Func.Products.html" class="Module">Algebras.Func.Products</a>               <a id="1118" class="Symbol">{</a><a id="1119" class="Argument">𝑆</a> <a id="1121" class="Symbol">=</a> <a id="1123" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a><a id="1124" class="Symbol">}</a> <a id="1126" class="Keyword">using</a> <a id="1132" class="Symbol">(</a> <a id="1134" href="Algebras.Func.Products.html#1526" class="Function">⨅</a> <a id="1136" class="Symbol">)</a>
<a id="1138" class="Keyword">open</a> <a id="1143" class="Keyword">import</a> <a id="1150" href="Algebras.Func.Basic.html" class="Module">Algebras.Func.Basic</a>                  <a id="1187" class="Symbol">{</a><a id="1188" class="Argument">𝑆</a> <a id="1190" class="Symbol">=</a> <a id="1192" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a><a id="1193" class="Symbol">}</a> <a id="1195" class="Keyword">using</a> <a id="1201" class="Symbol">(</a> <a id="1203" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1217" class="Symbol">;</a> <a id="1219" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="1222" class="Symbol">)</a>
<a id="1224" class="Keyword">open</a> <a id="1229" class="Keyword">import</a> <a id="1236" href="Homomorphisms.Func.Isomorphisms.html" class="Module">Homomorphisms.Func.Isomorphisms</a>      <a id="1273" class="Symbol">{</a><a id="1274" class="Argument">𝑆</a> <a id="1276" class="Symbol">=</a> <a id="1278" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a><a id="1279" class="Symbol">}</a> <a id="1281" class="Keyword">using</a> <a id="1287" class="Symbol">(</a> <a id="1289" href="Homomorphisms.Func.Isomorphisms.html#2502" class="Record Operator">_≅_</a> <a id="1293" class="Symbol">)</a>
<a id="1295" class="Keyword">open</a> <a id="1300" class="Keyword">import</a> <a id="1307" href="Homomorphisms.Func.HomomorphicImages.html" class="Module">Homomorphisms.Func.HomomorphicImages</a> <a id="1344" class="Symbol">{</a><a id="1345" class="Argument">𝑆</a> <a id="1347" class="Symbol">=</a> <a id="1349" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a><a id="1350" class="Symbol">}</a> <a id="1352" class="Keyword">using</a> <a id="1358" class="Symbol">(</a> <a id="1360" href="Homomorphisms.Func.HomomorphicImages.html#2289" class="Function">HomImages</a> <a id="1370" class="Symbol">)</a>
<a id="1372" class="Keyword">open</a> <a id="1377" class="Keyword">import</a> <a id="1384" href="Subalgebras.Func.Subalgebras.html" class="Module">Subalgebras.Func.Subalgebras</a>         <a id="1421" class="Symbol">{</a><a id="1422" class="Argument">𝑆</a> <a id="1424" class="Symbol">=</a> <a id="1426" href="Varieties.Func.Closure.html#663" class="Bound">𝑆</a><a id="1427" class="Symbol">}</a> <a id="1429" class="Keyword">using</a> <a id="1435" class="Symbol">(</a> <a id="1437" href="Subalgebras.Func.Subalgebras.html#1455" class="Function Operator">_≤_</a> <a id="1441" class="Symbol">)</a>

<a id="1444" class="Comment">-- The inductive type H</a>
<a id="1468" class="Keyword">data</a> <a id="H"></a><a id="1473" href="Varieties.Func.Closure.html#1473" class="Datatype">H</a> <a id="1475" class="Symbol">{</a><a id="1476" href="Varieties.Func.Closure.html#1476" class="Bound">α</a> <a id="1478" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a> <a id="1480" class="Symbol">:</a> <a id="1482" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1487" class="Symbol">}</a> <a id="1489" class="Symbol">(</a><a id="1490" href="Varieties.Func.Closure.html#1490" class="Bound">𝒦</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1499" class="Symbol">(</a><a id="1500" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1514" href="Varieties.Func.Closure.html#1476" class="Bound">α</a> <a id="1516" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a><a id="1517" class="Symbol">)(</a><a id="1519" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="1522" href="Varieties.Func.Closure.html#1476" class="Bound">α</a><a id="1523" class="Symbol">))</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1533" class="Symbol">(</a><a id="1534" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1548" href="Varieties.Func.Closure.html#1476" class="Bound">α</a> <a id="1550" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a><a id="1551" class="Symbol">)</a> <a id="1553" class="Symbol">(</a><a id="1554" href="Algebras.Func.Basic.html#1172" class="Function">ov</a><a id="1556" class="Symbol">(</a><a id="1557" href="Varieties.Func.Closure.html#1476" class="Bound">α</a> <a id="1559" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1561" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a><a id="1562" class="Symbol">))</a>
 <a id="1566" class="Keyword">where</a>
 <a id="H.hbase"></a><a id="1573" href="Varieties.Func.Closure.html#1573" class="InductiveConstructor">hbase</a> <a id="1579" class="Symbol">:</a> <a id="1581" class="Symbol">{</a><a id="1582" href="Varieties.Func.Closure.html#1582" class="Bound">𝑨</a> <a id="1584" class="Symbol">:</a> <a id="1586" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1600" href="Varieties.Func.Closure.html#1476" class="Bound">α</a> <a id="1602" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a><a id="1603" class="Symbol">}</a> <a id="1605" class="Symbol">→</a> <a id="1607" href="Varieties.Func.Closure.html#1582" class="Bound">𝑨</a> <a id="1609" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1611" href="Varieties.Func.Closure.html#1490" class="Bound">𝒦</a> <a id="1613" class="Symbol">→</a> <a id="1615" href="Varieties.Func.Closure.html#1582" class="Bound">𝑨</a> <a id="1617" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1619" href="Varieties.Func.Closure.html#1473" class="Datatype">H</a> <a id="1621" href="Varieties.Func.Closure.html#1490" class="Bound">𝒦</a>
 <a id="H.hhimg"></a><a id="1624" href="Varieties.Func.Closure.html#1624" class="InductiveConstructor">hhimg</a> <a id="1630" class="Symbol">:</a> <a id="1632" class="Symbol">{</a><a id="1633" href="Varieties.Func.Closure.html#1633" class="Bound">𝑨</a> <a id="1635" href="Varieties.Func.Closure.html#1635" class="Bound">𝑩</a> <a id="1637" class="Symbol">:</a> <a id="1639" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1653" class="Symbol">_</a> <a id="1655" href="Varieties.Func.Closure.html#1478" class="Bound">ρ</a><a id="1656" class="Symbol">}</a> <a id="1658" class="Symbol">→</a> <a id="1660" href="Varieties.Func.Closure.html#1633" class="Bound">𝑨</a> <a id="1662" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1664" href="Varieties.Func.Closure.html#1473" class="Datatype">H</a> <a id="1666" href="Varieties.Func.Closure.html#1490" class="Bound">𝒦</a> <a id="1668" class="Symbol">→</a> <a id="1670" class="Symbol">(</a><a id="1671" href="Varieties.Func.Closure.html#1671" class="Bound">(</a><a id="1672" href="Varieties.Func.Closure.html#1672" class="Bound">𝑩</a> <a id="1674" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1676" href="Varieties.Func.Closure.html#1671" class="Bound">_)</a> <a id="1679" class="Symbol">:</a> <a id="1681" href="Homomorphisms.Func.HomomorphicImages.html#2289" class="Function">HomImages</a> <a id="1691" href="Varieties.Func.Closure.html#1633" class="Bound">𝑨</a><a id="1692" class="Symbol">)</a> <a id="1694" class="Symbol">→</a> <a id="1696" href="Varieties.Func.Closure.html#1672" class="Bound">𝑩</a> <a id="1698" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1700" href="Varieties.Func.Closure.html#1473" class="Datatype">H</a> <a id="1702" href="Varieties.Func.Closure.html#1490" class="Bound">𝒦</a>

<a id="1705" class="Comment">-- The inductive type S</a>
<a id="1729" class="Keyword">data</a> <a id="S"></a><a id="1734" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="1736" class="Symbol">{</a><a id="1737" href="Varieties.Func.Closure.html#1737" class="Bound">α</a> <a id="1739" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a> <a id="1741" class="Symbol">:</a> <a id="1743" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1748" class="Symbol">}(</a><a id="1750" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a> <a id="1752" class="Symbol">:</a> <a id="1754" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="1758" class="Symbol">(</a><a id="1759" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1773" href="Varieties.Func.Closure.html#1737" class="Bound">α</a> <a id="1775" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1776" class="Symbol">)(</a><a id="1778" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="1781" href="Varieties.Func.Closure.html#1737" class="Bound">α</a><a id="1782" class="Symbol">))</a> <a id="1785" class="Symbol">:</a> <a id="1787" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="1791" class="Symbol">(</a><a id="1792" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1806" href="Varieties.Func.Closure.html#1737" class="Bound">α</a> <a id="1808" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1809" class="Symbol">)(</a><a id="1811" href="Algebras.Func.Basic.html#1172" class="Function">ov</a><a id="1813" class="Symbol">(</a><a id="1814" href="Varieties.Func.Closure.html#1737" class="Bound">α</a> <a id="1816" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1818" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1819" class="Symbol">))</a>
 <a id="1823" class="Keyword">where</a>
 <a id="S.sbase"></a><a id="1830" href="Varieties.Func.Closure.html#1830" class="InductiveConstructor">sbase</a> <a id="1836" class="Symbol">:</a> <a id="1838" class="Symbol">{</a><a id="1839" href="Varieties.Func.Closure.html#1839" class="Bound">𝑨</a> <a id="1841" class="Symbol">:</a> <a id="1843" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1857" href="Varieties.Func.Closure.html#1737" class="Bound">α</a> <a id="1859" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1860" class="Symbol">}</a> <a id="1862" class="Symbol">→</a> <a id="1864" href="Varieties.Func.Closure.html#1839" class="Bound">𝑨</a> <a id="1866" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1868" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a> <a id="1870" class="Symbol">→</a> <a id="1872" href="Varieties.Func.Closure.html#1839" class="Bound">𝑨</a> <a id="1874" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1876" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="1878" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a>
 <a id="S.ssub"></a><a id="1881" href="Varieties.Func.Closure.html#1881" class="InductiveConstructor">ssub</a>  <a id="1887" class="Symbol">:</a> <a id="1889" class="Symbol">{</a><a id="1890" href="Varieties.Func.Closure.html#1890" class="Bound">𝑨</a> <a id="1892" href="Varieties.Func.Closure.html#1892" class="Bound">𝑩</a> <a id="1894" class="Symbol">:</a> <a id="1896" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1910" class="Symbol">_</a> <a id="1912" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1913" class="Symbol">}</a> <a id="1915" class="Symbol">→</a> <a id="1917" href="Varieties.Func.Closure.html#1890" class="Bound">𝑨</a> <a id="1919" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1921" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="1923" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a> <a id="1925" class="Symbol">→</a> <a id="1927" href="Varieties.Func.Closure.html#1892" class="Bound">𝑩</a> <a id="1929" href="Subalgebras.Func.Subalgebras.html#1455" class="Function Operator">≤</a> <a id="1931" href="Varieties.Func.Closure.html#1890" class="Bound">𝑨</a> <a id="1933" class="Symbol">→</a> <a id="1935" href="Varieties.Func.Closure.html#1892" class="Bound">𝑩</a> <a id="1937" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1939" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="1941" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a>
 <a id="S.siso"></a><a id="1944" href="Varieties.Func.Closure.html#1944" class="InductiveConstructor">siso</a>  <a id="1950" class="Symbol">:</a> <a id="1952" class="Symbol">{</a><a id="1953" href="Varieties.Func.Closure.html#1953" class="Bound">𝑨</a> <a id="1955" href="Varieties.Func.Closure.html#1955" class="Bound">𝑩</a> <a id="1957" class="Symbol">:</a> <a id="1959" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1973" class="Symbol">_</a> <a id="1975" href="Varieties.Func.Closure.html#1739" class="Bound">ρ</a><a id="1976" class="Symbol">}</a> <a id="1978" class="Symbol">→</a> <a id="1980" href="Varieties.Func.Closure.html#1953" class="Bound">𝑨</a> <a id="1982" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1984" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="1986" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a> <a id="1988" class="Symbol">→</a> <a id="1990" href="Varieties.Func.Closure.html#1953" class="Bound">𝑨</a> <a id="1992" href="Homomorphisms.Func.Isomorphisms.html#2502" class="Record Operator">≅</a> <a id="1994" href="Varieties.Func.Closure.html#1955" class="Bound">𝑩</a> <a id="1996" class="Symbol">→</a> <a id="1998" href="Varieties.Func.Closure.html#1955" class="Bound">𝑩</a> <a id="2000" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2002" href="Varieties.Func.Closure.html#1734" class="Datatype">S</a> <a id="2004" href="Varieties.Func.Closure.html#1750" class="Bound">𝒦</a>

<a id="2007" class="Comment">-- The inductive type P</a>
<a id="2031" class="Keyword">data</a> <a id="P"></a><a id="2036" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2038" class="Symbol">{</a><a id="2039" href="Varieties.Func.Closure.html#2039" class="Bound">α</a> <a id="2041" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a> <a id="2043" class="Symbol">:</a> <a id="2045" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2050" class="Symbol">}(</a><a id="2052" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a> <a id="2054" class="Symbol">:</a> <a id="2056" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="2060" class="Symbol">(</a><a id="2061" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2075" href="Varieties.Func.Closure.html#2039" class="Bound">α</a> <a id="2077" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2078" class="Symbol">)(</a><a id="2080" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="2083" href="Varieties.Func.Closure.html#2039" class="Bound">α</a><a id="2084" class="Symbol">))</a> <a id="2087" class="Symbol">:</a> <a id="2089" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="2093" class="Symbol">(</a><a id="2094" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2108" href="Varieties.Func.Closure.html#2039" class="Bound">α</a> <a id="2110" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2111" class="Symbol">)(</a><a id="2113" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="2116" class="Symbol">(</a><a id="2117" href="Varieties.Func.Closure.html#2039" class="Bound">α</a> <a id="2119" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2121" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2122" class="Symbol">))</a>
 <a id="2126" class="Keyword">where</a>
 <a id="P.pbase"></a><a id="2133" href="Varieties.Func.Closure.html#2133" class="InductiveConstructor">pbase</a>  <a id="2140" class="Symbol">:</a> <a id="2142" class="Symbol">{</a><a id="2143" href="Varieties.Func.Closure.html#2143" class="Bound">𝑨</a> <a id="2145" class="Symbol">:</a> <a id="2147" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2161" href="Varieties.Func.Closure.html#2039" class="Bound">α</a> <a id="2163" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2164" class="Symbol">}</a> <a id="2166" class="Symbol">→</a> <a id="2168" href="Varieties.Func.Closure.html#2143" class="Bound">𝑨</a> <a id="2170" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2172" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a> <a id="2174" class="Symbol">→</a> <a id="2176" href="Varieties.Func.Closure.html#2143" class="Bound">𝑨</a> <a id="2178" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2180" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2182" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a>
 <a id="P.pprod"></a><a id="2185" href="Varieties.Func.Closure.html#2185" class="InductiveConstructor">pprod</a>  <a id="2192" class="Symbol">:</a> <a id="2194" class="Symbol">{</a><a id="2195" href="Varieties.Func.Closure.html#2195" class="Bound">I</a> <a id="2197" class="Symbol">:</a> <a id="2199" href="Varieties.Func.Closure.html#858" class="Primitive">Type</a><a id="2203" class="Symbol">}{</a><a id="2205" href="Varieties.Func.Closure.html#2205" class="Bound">𝒜</a> <a id="2207" class="Symbol">:</a> <a id="2209" href="Varieties.Func.Closure.html#2195" class="Bound">I</a> <a id="2211" class="Symbol">→</a> <a id="2213" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2227" class="Symbol">_</a> <a id="2229" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2230" class="Symbol">}</a> <a id="2232" class="Symbol">→</a> <a id="2234" class="Symbol">(∀</a> <a id="2237" href="Varieties.Func.Closure.html#2237" class="Bound">i</a> <a id="2239" class="Symbol">→</a> <a id="2241" class="Symbol">(</a><a id="2242" href="Varieties.Func.Closure.html#2205" class="Bound">𝒜</a> <a id="2244" href="Varieties.Func.Closure.html#2237" class="Bound">i</a><a id="2245" class="Symbol">)</a> <a id="2247" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2249" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2251" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a><a id="2252" class="Symbol">)</a> <a id="2254" class="Symbol">→</a> <a id="2256" href="Algebras.Func.Products.html#1526" class="Function">⨅</a> <a id="2258" href="Varieties.Func.Closure.html#2205" class="Bound">𝒜</a> <a id="2260" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2262" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2264" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a>
 <a id="P.piso"></a><a id="2267" href="Varieties.Func.Closure.html#2267" class="InductiveConstructor">piso</a>  <a id="2273" class="Symbol">:</a> <a id="2275" class="Symbol">{</a><a id="2276" href="Varieties.Func.Closure.html#2276" class="Bound">𝑨</a> <a id="2278" href="Varieties.Func.Closure.html#2278" class="Bound">𝑩</a> <a id="2280" class="Symbol">:</a> <a id="2282" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2296" class="Symbol">_</a> <a id="2298" href="Varieties.Func.Closure.html#2041" class="Bound">ρ</a><a id="2299" class="Symbol">}</a> <a id="2301" class="Symbol">→</a> <a id="2303" href="Varieties.Func.Closure.html#2276" class="Bound">𝑨</a> <a id="2305" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2307" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2309" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a> <a id="2311" class="Symbol">→</a> <a id="2313" href="Varieties.Func.Closure.html#2276" class="Bound">𝑨</a> <a id="2315" href="Homomorphisms.Func.Isomorphisms.html#2502" class="Record Operator">≅</a> <a id="2317" href="Varieties.Func.Closure.html#2278" class="Bound">𝑩</a> <a id="2319" class="Symbol">→</a> <a id="2321" href="Varieties.Func.Closure.html#2278" class="Bound">𝑩</a> <a id="2323" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2325" href="Varieties.Func.Closure.html#2036" class="Datatype">P</a> <a id="2327" href="Varieties.Func.Closure.html#2052" class="Bound">𝒦</a>

<a id="2330" class="Comment">-- The inductive types V</a>
<a id="2355" class="Keyword">data</a> <a id="V"></a><a id="2360" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2362" class="Symbol">{</a><a id="2363" href="Varieties.Func.Closure.html#2363" class="Bound">α</a> <a id="2365" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a> <a id="2367" class="Symbol">:</a> <a id="2369" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2374" class="Symbol">}(</a><a id="2376" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a> <a id="2378" class="Symbol">:</a> <a id="2380" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="2384" class="Symbol">(</a><a id="2385" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2399" href="Varieties.Func.Closure.html#2363" class="Bound">α</a> <a id="2401" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2402" class="Symbol">)(</a><a id="2404" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="2407" href="Varieties.Func.Closure.html#2363" class="Bound">α</a><a id="2408" class="Symbol">))</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="Relation.Unary.html#1101" class="Function">Pred</a><a id="2417" class="Symbol">(</a><a id="2418" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2432" href="Varieties.Func.Closure.html#2363" class="Bound">α</a> <a id="2434" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2435" class="Symbol">)(</a><a id="2437" href="Algebras.Func.Basic.html#1172" class="Function">ov</a><a id="2439" class="Symbol">(</a><a id="2440" href="Varieties.Func.Closure.html#2363" class="Bound">α</a> <a id="2442" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2444" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2445" class="Symbol">))</a>
 <a id="2449" class="Keyword">where</a>
 <a id="V.vbase"></a><a id="2456" href="Varieties.Func.Closure.html#2456" class="InductiveConstructor">vbase</a>  <a id="2463" class="Symbol">:</a> <a id="2465" class="Symbol">{</a><a id="2466" href="Varieties.Func.Closure.html#2466" class="Bound">𝑨</a> <a id="2468" class="Symbol">:</a> <a id="2470" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2484" href="Varieties.Func.Closure.html#2363" class="Bound">α</a> <a id="2486" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2487" class="Symbol">}</a> <a id="2489" class="Symbol">→</a> <a id="2491" href="Varieties.Func.Closure.html#2466" class="Bound">𝑨</a> <a id="2493" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2495" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a> <a id="2497" class="Symbol">→</a> <a id="2499" href="Varieties.Func.Closure.html#2466" class="Bound">𝑨</a> <a id="2501" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2503" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2505" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a>
 <a id="V.vhimg"></a><a id="2508" href="Varieties.Func.Closure.html#2508" class="InductiveConstructor">vhimg</a>  <a id="2515" class="Symbol">:</a> <a id="2517" class="Symbol">{</a><a id="2518" href="Varieties.Func.Closure.html#2518" class="Bound">𝑨</a> <a id="2520" href="Varieties.Func.Closure.html#2520" class="Bound">𝑩</a> <a id="2522" class="Symbol">:</a> <a id="2524" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2538" class="Symbol">_</a> <a id="2540" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2541" class="Symbol">}</a> <a id="2543" class="Symbol">→</a> <a id="2545" href="Varieties.Func.Closure.html#2518" class="Bound">𝑨</a> <a id="2547" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2549" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2551" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a> <a id="2553" class="Symbol">→</a> <a id="2555" class="Symbol">(</a><a id="2556" href="Varieties.Func.Closure.html#2556" class="Bound">(</a><a id="2557" href="Varieties.Func.Closure.html#2557" class="Bound">𝑩</a> <a id="2559" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2561" href="Varieties.Func.Closure.html#2556" class="Bound">_)</a> <a id="2564" class="Symbol">:</a> <a id="2566" href="Homomorphisms.Func.HomomorphicImages.html#2289" class="Function">HomImages</a> <a id="2576" href="Varieties.Func.Closure.html#2518" class="Bound">𝑨</a><a id="2577" class="Symbol">)</a> <a id="2579" class="Symbol">→</a> <a id="2581" href="Varieties.Func.Closure.html#2557" class="Bound">𝑩</a> <a id="2583" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2585" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2587" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a>
 <a id="V.vssub"></a><a id="2590" href="Varieties.Func.Closure.html#2590" class="InductiveConstructor">vssub</a>  <a id="2597" class="Symbol">:</a> <a id="2599" class="Symbol">{</a><a id="2600" href="Varieties.Func.Closure.html#2600" class="Bound">𝑨</a> <a id="2602" href="Varieties.Func.Closure.html#2602" class="Bound">𝑩</a> <a id="2604" class="Symbol">:</a> <a id="2606" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2620" class="Symbol">_</a> <a id="2622" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2623" class="Symbol">}</a> <a id="2625" class="Symbol">→</a> <a id="2627" href="Varieties.Func.Closure.html#2600" class="Bound">𝑨</a> <a id="2629" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2631" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2633" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a> <a id="2635" class="Symbol">→</a> <a id="2637" href="Varieties.Func.Closure.html#2602" class="Bound">𝑩</a> <a id="2639" href="Subalgebras.Func.Subalgebras.html#1455" class="Function Operator">≤</a> <a id="2641" href="Varieties.Func.Closure.html#2600" class="Bound">𝑨</a> <a id="2643" class="Symbol">→</a> <a id="2645" href="Varieties.Func.Closure.html#2602" class="Bound">𝑩</a> <a id="2647" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2649" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2651" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a>
 <a id="V.vpprod"></a><a id="2654" href="Varieties.Func.Closure.html#2654" class="InductiveConstructor">vpprod</a> <a id="2661" class="Symbol">:</a> <a id="2663" class="Symbol">{</a><a id="2664" href="Varieties.Func.Closure.html#2664" class="Bound">I</a> <a id="2666" class="Symbol">:</a> <a id="2668" href="Varieties.Func.Closure.html#858" class="Primitive">Type</a><a id="2672" class="Symbol">}{</a><a id="2674" href="Varieties.Func.Closure.html#2674" class="Bound">𝒜</a> <a id="2676" class="Symbol">:</a> <a id="2678" href="Varieties.Func.Closure.html#2664" class="Bound">I</a> <a id="2680" class="Symbol">→</a> <a id="2682" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2696" class="Symbol">_</a> <a id="2698" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2699" class="Symbol">}</a> <a id="2701" class="Symbol">→</a> <a id="2703" class="Symbol">(∀</a> <a id="2706" href="Varieties.Func.Closure.html#2706" class="Bound">i</a> <a id="2708" class="Symbol">→</a> <a id="2710" class="Symbol">(</a><a id="2711" href="Varieties.Func.Closure.html#2674" class="Bound">𝒜</a> <a id="2713" href="Varieties.Func.Closure.html#2706" class="Bound">i</a><a id="2714" class="Symbol">)</a> <a id="2716" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2718" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2720" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a><a id="2721" class="Symbol">)</a> <a id="2723" class="Symbol">→</a> <a id="2725" href="Algebras.Func.Products.html#1526" class="Function">⨅</a> <a id="2727" href="Varieties.Func.Closure.html#2674" class="Bound">𝒜</a> <a id="2729" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2731" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2733" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a>
 <a id="V.viso"></a><a id="2736" href="Varieties.Func.Closure.html#2736" class="InductiveConstructor">viso</a>   <a id="2743" class="Symbol">:</a> <a id="2745" class="Symbol">{</a><a id="2746" href="Varieties.Func.Closure.html#2746" class="Bound">𝑨</a> <a id="2748" href="Varieties.Func.Closure.html#2748" class="Bound">𝑩</a> <a id="2750" class="Symbol">:</a> <a id="2752" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2766" class="Symbol">_</a> <a id="2768" href="Varieties.Func.Closure.html#2365" class="Bound">ρ</a><a id="2769" class="Symbol">}</a> <a id="2771" class="Symbol">→</a> <a id="2773" href="Varieties.Func.Closure.html#2746" class="Bound">𝑨</a> <a id="2775" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2777" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2779" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a> <a id="2781" class="Symbol">→</a> <a id="2783" href="Varieties.Func.Closure.html#2746" class="Bound">𝑨</a> <a id="2785" href="Homomorphisms.Func.Isomorphisms.html#2502" class="Record Operator">≅</a> <a id="2787" href="Varieties.Func.Closure.html#2748" class="Bound">𝑩</a> <a id="2789" class="Symbol">→</a> <a id="2791" href="Varieties.Func.Closure.html#2748" class="Bound">𝑩</a> <a id="2793" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="2795" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="2797" href="Varieties.Func.Closure.html#2376" class="Bound">𝒦</a>

</pre>

Thus, if 𝒦 is a class of 𝑆-algebras, then the *variety generated by* 𝒦 is denoted by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under `H`, `S`, and `P`.

With the closure operator V representing closure under HSP, we represent formally what it means to be a variety of algebras as follows.

<pre class="Agda">

<a id="is-variety"></a><a id="3147" href="Varieties.Func.Closure.html#3147" class="Function">is-variety</a> <a id="3158" class="Symbol">:</a> <a id="3160" class="Symbol">{</a><a id="3161" href="Varieties.Func.Closure.html#3161" class="Bound">α</a> <a id="3163" href="Varieties.Func.Closure.html#3163" class="Bound">ρ</a> <a id="3165" class="Symbol">:</a> <a id="3167" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3172" class="Symbol">}(</a><a id="3174" href="Varieties.Func.Closure.html#3174" class="Bound">𝒱</a> <a id="3176" class="Symbol">:</a> <a id="3178" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3183" class="Symbol">(</a><a id="3184" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="3198" href="Varieties.Func.Closure.html#3161" class="Bound">α</a> <a id="3200" href="Varieties.Func.Closure.html#3163" class="Bound">ρ</a><a id="3201" class="Symbol">)_)</a> <a id="3205" class="Symbol">→</a> <a id="3207" href="Varieties.Func.Closure.html#858" class="Primitive">Type</a> <a id="3212" class="Symbol">_</a>
<a id="3214" href="Varieties.Func.Closure.html#3147" class="Function">is-variety</a><a id="3224" class="Symbol">{</a><a id="3225" href="Varieties.Func.Closure.html#3225" class="Bound">α</a><a id="3226" class="Symbol">}{</a><a id="3228" href="Varieties.Func.Closure.html#3228" class="Bound">ρ</a><a id="3229" class="Symbol">}</a> <a id="3231" href="Varieties.Func.Closure.html#3231" class="Bound">𝒱</a> <a id="3233" class="Symbol">=</a> <a id="3235" href="Varieties.Func.Closure.html#2360" class="Datatype">V</a> <a id="3237" href="Varieties.Func.Closure.html#3231" class="Bound">𝒱</a> <a id="3239" href="Relation.Unary.html#1742" class="Function Operator">⊆</a> <a id="3241" href="Varieties.Func.Closure.html#3231" class="Bound">𝒱</a>

<a id="variety"></a><a id="3244" href="Varieties.Func.Closure.html#3244" class="Function">variety</a> <a id="3252" class="Symbol">:</a> <a id="3254" class="Symbol">(</a><a id="3255" href="Varieties.Func.Closure.html#3255" class="Bound">α</a> <a id="3257" href="Varieties.Func.Closure.html#3257" class="Bound">ρ</a> <a id="3259" class="Symbol">:</a> <a id="3261" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3266" class="Symbol">)</a> <a id="3268" class="Symbol">→</a> <a id="3270" href="Varieties.Func.Closure.html#858" class="Primitive">Type</a> <a id="3275" class="Symbol">_</a>
<a id="3277" href="Varieties.Func.Closure.html#3244" class="Function">variety</a> <a id="3285" href="Varieties.Func.Closure.html#3285" class="Bound">α</a> <a id="3287" href="Varieties.Func.Closure.html#3287" class="Bound">ρ</a> <a id="3289" class="Symbol">=</a> <a id="3291" href="Data.Product.html#916" class="Function">Σ[</a> <a id="3294" href="Varieties.Func.Closure.html#3294" class="Bound">𝒱</a> <a id="3296" href="Data.Product.html#916" class="Function">∈</a> <a id="3298" class="Symbol">(</a><a id="3299" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3304" class="Symbol">(</a><a id="3305" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="3319" href="Varieties.Func.Closure.html#3285" class="Bound">α</a> <a id="3321" href="Varieties.Func.Closure.html#3287" class="Bound">ρ</a><a id="3322" class="Symbol">)_)</a> <a id="3326" href="Data.Product.html#916" class="Function">]</a> <a id="3328" href="Varieties.Func.Closure.html#3147" class="Function">is-variety</a> <a id="3339" href="Varieties.Func.Closure.html#3294" class="Bound">𝒱</a>

</pre>

--------------------------------

<span style="float:left;">[← Varieties.Func.EquationalLogic](Varieties.Func.EquationalLogic.html)</span>
<span style="float:right;">[Varieties.Func.FreeAlgebras →](Varieties.Func.FreeAlgebras.html)</span>

{% include UALib.Links.md %}