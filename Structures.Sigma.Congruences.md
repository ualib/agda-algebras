---
layout: default
title : Structures.Sigma.Congruences module
date : 2021-05-12
author: [agda-algebras development team][]
---

## <a id="congruences-of-general-structures">Congruences of general structures</a>

<pre class="Agda">

<a id="229" class="Symbol">{-#</a> <a id="233" class="Keyword">OPTIONS</a> <a id="241" class="Pragma">--without-K</a> <a id="253" class="Pragma">--exact-split</a> <a id="267" class="Pragma">--safe</a> <a id="274" class="Symbol">#-}</a> <a id="278" class="Comment">-- cubical #-}</a>


<a id="295" class="Keyword">module</a> <a id="302" href="Structures.Sigma.Congruences.html" class="Module">Structures.Sigma.Congruences</a> <a id="331" class="Keyword">where</a>

<a id="338" class="Comment">-- Imports from the Agda Standard Library ------------------------------------------------</a>
<a id="429" class="Keyword">open</a> <a id="434" class="Keyword">import</a> <a id="441" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="457" class="Keyword">using</a> <a id="463" class="Symbol">(</a> <a id="465" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="469" class="Symbol">;</a> <a id="471" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="476" class="Symbol">)</a> <a id="478" class="Keyword">renaming</a> <a id="487" class="Symbol">(</a> <a id="489" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="493" class="Symbol">to</a> <a id="496" class="Primitive">Type</a> <a id="501" class="Symbol">;</a> <a id="503" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="509" class="Symbol">to</a> <a id="512" class="Primitive">ℓ₀</a> <a id="515" class="Symbol">)</a>
<a id="517" class="Keyword">open</a> <a id="522" class="Keyword">import</a> <a id="529" href="Data.Product.html" class="Module">Data.Product</a>    <a id="545" class="Keyword">using</a> <a id="551" class="Symbol">(</a> <a id="553" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="557" class="Symbol">;</a> <a id="559" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="563" class="Symbol">;</a> <a id="565" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="574" class="Symbol">)</a> <a id="576" class="Keyword">renaming</a> <a id="585" class="Symbol">(</a> <a id="587" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="593" class="Symbol">to</a> <a id="596" class="Field">fst</a> <a id="600" class="Symbol">)</a>
<a id="602" class="Keyword">open</a> <a id="607" class="Keyword">import</a> <a id="614" href="Function.Base.html" class="Module">Function.Base</a>   <a id="630" class="Keyword">using</a> <a id="636" class="Symbol">(</a> <a id="638" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="642" class="Symbol">)</a>
<a id="644" class="Keyword">open</a> <a id="649" class="Keyword">import</a> <a id="656" href="Level.html" class="Module">Level</a>           <a id="672" class="Keyword">using</a> <a id="678" class="Symbol">(</a> <a id="680" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="686" class="Symbol">;</a> <a id="688" href="Level.html#400" class="Record">Lift</a> <a id="693" class="Symbol">;</a> <a id="695" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="700" class="Symbol">;</a> <a id="702" href="Level.html#470" class="Field">lower</a> <a id="708" class="Symbol">)</a>
<a id="710" class="Keyword">open</a> <a id="715" class="Keyword">import</a> <a id="722" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="738" class="Keyword">using</a> <a id="744" class="Symbol">(</a> <a id="746" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="751" class="Symbol">;</a> <a id="753" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="757" class="Symbol">)</a>
<a id="759" class="Keyword">open</a> <a id="764" class="Keyword">import</a> <a id="771" href="Relation.Binary.html" class="Module">Relation.Binary</a> <a id="787" class="Keyword">using</a> <a id="793" class="Symbol">(</a> <a id="795" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="809" class="Symbol">)</a> <a id="811" class="Keyword">renaming</a> <a id="820" class="Symbol">(</a> <a id="822" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="826" class="Symbol">to</a> <a id="829" class="Function">BinRel</a> <a id="836" class="Symbol">)</a>
<a id="838" class="Keyword">open</a> <a id="843" class="Keyword">import</a> <a id="850" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                            <a id="916" class="Keyword">using</a> <a id="922" class="Symbol">(</a> <a id="924" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="928" class="Symbol">)</a>

<a id="931" class="Comment">-- Imports from the Agda Universal Algebra Library ---------------------------------------</a>
<a id="1022" class="Keyword">open</a> <a id="1027" class="Keyword">import</a> <a id="1034" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>  <a id="1058" class="Keyword">using</a> <a id="1064" class="Symbol">(</a> <a id="1066" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a> <a id="1070" class="Symbol">)</a>
<a id="1072" class="Keyword">open</a> <a id="1077" class="Keyword">import</a> <a id="1084" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>      <a id="1108" class="Keyword">using</a> <a id="1114" class="Symbol">(</a> <a id="1116" href="Relations.Discrete.html#6528" class="Function Operator">_|:_</a> <a id="1121" class="Symbol">;</a> <a id="1123" href="Relations.Discrete.html#4183" class="Function Operator">0[_]</a> <a id="1128" class="Symbol">)</a>
<a id="1130" class="Keyword">open</a> <a id="1135" class="Keyword">import</a> <a id="1142" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>     <a id="1166" class="Keyword">using</a> <a id="1172" class="Symbol">(</a> <a id="1174" href="Relations.Quotients.html#1798" class="Function">Equivalence</a> <a id="1186" class="Symbol">;</a> <a id="1188" href="Relations.Quotients.html#5374" class="Function Operator">⟪_⟫</a> <a id="1192" class="Symbol">;</a> <a id="1194" href="Relations.Quotients.html#5567" class="Function Operator">⌞_⌟</a> <a id="1198" class="Symbol">;</a> <a id="1200" href="Relations.Quotients.html#7088" class="Function Operator">0[_]Equivalence</a>
                                          <a id="1258" class="Symbol">;</a> <a id="1260" href="Relations.Quotients.html#5146" class="Function Operator">_/_</a> <a id="1264" class="Symbol">;</a> <a id="1266" href="Relations.Quotients.html#7214" class="Function Operator">⟪_∼_⟫-elim</a> <a id="1277" class="Symbol">;</a> <a id="1279" href="Relations.Quotients.html#5021" class="Function">Quotient</a> <a id="1288" class="Symbol">)</a>
<a id="1290" class="Keyword">open</a> <a id="1295" class="Keyword">import</a> <a id="1302" href="Foundations.Welldefined.html" class="Module">Foundations.Welldefined</a> <a id="1326" class="Keyword">using</a> <a id="1332" class="Symbol">(</a> <a id="1334" href="Foundations.Welldefined.html#2648" class="Function">swelldef</a> <a id="1343" class="Symbol">)</a>
<a id="1345" class="Keyword">open</a> <a id="1350" class="Keyword">import</a> <a id="1357" href="Structures.Sigma.Basic.html" class="Module">Structures.Sigma.Basic</a>  <a id="1381" class="Keyword">using</a> <a id="1387" class="Symbol">(</a> <a id="1389" href="Structures.Sigma.Basic.html#1170" class="Function">Signature</a> <a id="1399" class="Symbol">;</a> <a id="1401" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="1411" class="Symbol">;</a> <a id="1413" href="Structures.Sigma.Basic.html#2577" class="Function Operator">_ᵒ_</a> <a id="1417" class="Symbol">;</a> <a id="1419" href="Structures.Sigma.Basic.html#2671" class="Function">Compatible</a> <a id="1430" class="Symbol">;</a> <a id="1432" href="Structures.Sigma.Basic.html#2481" class="Function Operator">_ʳ_</a> <a id="1436" class="Symbol">)</a>

<a id="1439" class="Keyword">private</a> <a id="1447" class="Keyword">variable</a> <a id="1456" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="1458" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="1460" class="Symbol">:</a> <a id="1462" href="Structures.Sigma.Basic.html#1170" class="Function">Signature</a>

<a id="1473" class="Keyword">module</a> <a id="1480" href="Structures.Sigma.Congruences.html#1480" class="Module">_</a> <a id="1482" class="Symbol">{</a><a id="1483" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="1485" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a> <a id="1487" class="Symbol">:</a> <a id="1489" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1494" class="Symbol">}</a> <a id="1496" class="Keyword">where</a>

 <a id="1504" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="1508" class="Symbol">:</a> <a id="1510" class="Symbol">(</a><a id="1511" href="Structures.Sigma.Congruences.html#1511" class="Bound">𝑨</a> <a id="1513" class="Symbol">:</a> <a id="1515" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="1525" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="1527" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="1529" class="Symbol">{</a><a id="1530" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="1531" class="Symbol">}{</a><a id="1533" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1534" class="Symbol">})</a> <a id="1537" class="Symbol">→</a> <a id="1539" href="Structures.Sigma.Congruences.html#496" class="Primitive">Type</a> <a id="1544" class="Symbol">(</a><a id="1545" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1550" class="Symbol">(</a><a id="1551" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="1553" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1555" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1556" class="Symbol">))</a>
 <a id="1560" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="1564" href="Structures.Sigma.Congruences.html#1564" class="Bound">𝑨</a> <a id="1566" class="Symbol">=</a> <a id="1568" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1571" href="Structures.Sigma.Congruences.html#1571" class="Bound">θ</a> <a id="1573" href="Data.Product.html#916" class="Function">∈</a> <a id="1575" href="Relations.Quotients.html#1798" class="Function">Equivalence</a> <a id="1587" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1589" href="Structures.Sigma.Congruences.html#1564" class="Bound">𝑨</a> <a id="1591" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="1592" class="Symbol">{</a><a id="1593" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="1595" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1597" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1598" class="Symbol">}</a> <a id="1600" href="Data.Product.html#916" class="Function">]</a> <a id="1602" class="Symbol">(</a><a id="1603" href="Structures.Sigma.Basic.html#2671" class="Function">Compatible</a> <a id="1614" href="Structures.Sigma.Congruences.html#1564" class="Bound">𝑨</a> <a id="1616" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1618" href="Structures.Sigma.Congruences.html#1571" class="Bound">θ</a> <a id="1620" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="1621" class="Symbol">)</a>

 <a id="1625" class="Comment">-- The zero congruence of a structure.</a>
 <a id="1665" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">0[_]Compatible</a> <a id="1680" class="Symbol">:</a> <a id="1682" class="Symbol">(</a><a id="1683" href="Structures.Sigma.Congruences.html#1683" class="Bound">𝑨</a> <a id="1685" class="Symbol">:</a> <a id="1687" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="1697" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="1699" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="1701" class="Symbol">{</a><a id="1702" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="1703" class="Symbol">}{</a><a id="1705" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1706" class="Symbol">})</a> <a id="1709" class="Symbol">→</a> <a id="1711" href="Foundations.Welldefined.html#2648" class="Function">swelldef</a> <a id="1720" href="Structures.Sigma.Congruences.html#512" class="Primitive">ℓ₀</a> <a id="1723" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a>
  <a id="1727" class="Symbol">→</a>               <a id="1743" class="Symbol">(</a><a id="1744" href="Structures.Sigma.Congruences.html#1744" class="Bound">𝑓</a> <a id="1746" class="Symbol">:</a> <a id="1748" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1750" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="1752" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="1753" class="Symbol">)</a> <a id="1755" class="Symbol">→</a> <a id="1757" class="Symbol">(</a><a id="1758" href="Structures.Sigma.Congruences.html#1744" class="Bound">𝑓</a> <a id="1760" href="Structures.Sigma.Basic.html#2577" class="Function Operator">ᵒ</a> <a id="1762" href="Structures.Sigma.Congruences.html#1683" class="Bound">𝑨</a><a id="1763" class="Symbol">)</a> <a id="1765" href="Relations.Discrete.html#6528" class="Function Operator">|:</a> <a id="1768" class="Symbol">(</a><a id="1769" href="Relations.Discrete.html#4183" class="Function Operator">0[</a> <a id="1772" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1774" href="Structures.Sigma.Congruences.html#1683" class="Bound">𝑨</a> <a id="1776" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1778" href="Relations.Discrete.html#4183" class="Function Operator">]</a><a id="1779" class="Symbol">{</a><a id="1780" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1781" class="Symbol">})</a>

 <a id="1786" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">0[</a> <a id="1789" href="Structures.Sigma.Congruences.html#1789" class="Bound">𝑨</a> <a id="1791" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">]Compatible</a> <a id="1803" href="Structures.Sigma.Congruences.html#1803" class="Bound">wd</a> <a id="1806" href="Structures.Sigma.Congruences.html#1806" class="Bound">𝑓</a> <a id="1808" class="Symbol">{</a><a id="1809" href="Structures.Sigma.Congruences.html#1809" class="Bound">i</a><a id="1810" class="Symbol">}{</a><a id="1812" href="Structures.Sigma.Congruences.html#1812" class="Bound">j</a><a id="1813" class="Symbol">}</a> <a id="1815" href="Structures.Sigma.Congruences.html#1815" class="Bound">ptws0</a>  <a id="1822" class="Symbol">=</a> <a id="1824" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="1829" href="Structures.Sigma.Congruences.html#1841" class="Function">γ</a>
  <a id="1833" class="Keyword">where</a>
  <a id="1841" href="Structures.Sigma.Congruences.html#1841" class="Function">γ</a> <a id="1843" class="Symbol">:</a> <a id="1845" class="Symbol">(</a><a id="1846" href="Structures.Sigma.Congruences.html#1806" class="Bound">𝑓</a> <a id="1848" href="Structures.Sigma.Basic.html#2577" class="Function Operator">ᵒ</a> <a id="1850" href="Structures.Sigma.Congruences.html#1789" class="Bound">𝑨</a><a id="1851" class="Symbol">)</a> <a id="1853" href="Structures.Sigma.Congruences.html#1809" class="Bound">i</a> <a id="1855" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1857" class="Symbol">(</a><a id="1858" href="Structures.Sigma.Congruences.html#1806" class="Bound">𝑓</a> <a id="1860" href="Structures.Sigma.Basic.html#2577" class="Function Operator">ᵒ</a> <a id="1862" href="Structures.Sigma.Congruences.html#1789" class="Bound">𝑨</a><a id="1863" class="Symbol">)</a> <a id="1865" href="Structures.Sigma.Congruences.html#1812" class="Bound">j</a>
  <a id="1869" href="Structures.Sigma.Congruences.html#1841" class="Function">γ</a> <a id="1871" class="Symbol">=</a> <a id="1873" href="Structures.Sigma.Congruences.html#1803" class="Bound">wd</a> <a id="1876" class="Symbol">(</a><a id="1877" href="Structures.Sigma.Congruences.html#1806" class="Bound">𝑓</a> <a id="1879" href="Structures.Sigma.Basic.html#2577" class="Function Operator">ᵒ</a> <a id="1881" href="Structures.Sigma.Congruences.html#1789" class="Bound">𝑨</a><a id="1882" class="Symbol">)</a> <a id="1884" href="Structures.Sigma.Congruences.html#1809" class="Bound">i</a> <a id="1886" href="Structures.Sigma.Congruences.html#1812" class="Bound">j</a> <a id="1888" class="Symbol">(</a><a id="1889" href="Level.html#470" class="Field">lower</a> <a id="1895" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1897" href="Structures.Sigma.Congruences.html#1815" class="Bound">ptws0</a><a id="1902" class="Symbol">)</a>

 <a id="1906" href="Structures.Sigma.Congruences.html#1906" class="Function Operator">0Con[_]</a> <a id="1914" class="Symbol">:</a> <a id="1916" class="Symbol">(</a><a id="1917" href="Structures.Sigma.Congruences.html#1917" class="Bound">𝑨</a> <a id="1919" class="Symbol">:</a> <a id="1921" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="1931" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="1933" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="1935" class="Symbol">{</a><a id="1936" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="1937" class="Symbol">}{</a><a id="1939" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="1940" class="Symbol">})</a> <a id="1943" class="Symbol">→</a> <a id="1945" href="Foundations.Welldefined.html#2648" class="Function">swelldef</a> <a id="1954" href="Structures.Sigma.Congruences.html#512" class="Primitive">ℓ₀</a> <a id="1957" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="1959" class="Symbol">→</a> <a id="1961" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="1965" href="Structures.Sigma.Congruences.html#1917" class="Bound">𝑨</a>
 <a id="1968" href="Structures.Sigma.Congruences.html#1906" class="Function Operator">0Con[</a> <a id="1974" href="Structures.Sigma.Congruences.html#1974" class="Bound">𝑨</a> <a id="1976" href="Structures.Sigma.Congruences.html#1906" class="Function Operator">]</a> <a id="1978" href="Structures.Sigma.Congruences.html#1978" class="Bound">wd</a> <a id="1981" class="Symbol">=</a> <a id="1983" href="Relations.Quotients.html#7088" class="Function Operator">0[</a> <a id="1986" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1988" href="Structures.Sigma.Congruences.html#1974" class="Bound">𝑨</a> <a id="1990" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="1992" href="Relations.Quotients.html#7088" class="Function Operator">]Equivalence</a> <a id="2005" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2007" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">0[</a> <a id="2010" href="Structures.Sigma.Congruences.html#1974" class="Bound">𝑨</a> <a id="2012" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">]Compatible</a> <a id="2024" href="Structures.Sigma.Congruences.html#1978" class="Bound">wd</a>

</pre>

### <a id="quotient-structures">Quotient structures</a>

<pre class="Agda">

 <a id="2112" href="Structures.Sigma.Congruences.html#2112" class="Function Operator">_╱_</a> <a id="2116" class="Symbol">:</a> <a id="2118" class="Symbol">(</a><a id="2119" href="Structures.Sigma.Congruences.html#2119" class="Bound">𝑨</a> <a id="2121" class="Symbol">:</a> <a id="2123" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="2133" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="2135" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="2137" class="Symbol">{</a><a id="2138" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="2139" class="Symbol">}{</a><a id="2141" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2142" class="Symbol">})</a> <a id="2145" class="Symbol">→</a> <a id="2147" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="2151" href="Structures.Sigma.Congruences.html#2119" class="Bound">𝑨</a> <a id="2153" class="Symbol">→</a> <a id="2155" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="2165" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="2167" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="2169" class="Symbol">{</a><a id="2170" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2175" class="Symbol">(</a><a id="2176" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="2178" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2180" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2181" class="Symbol">)}{</a><a id="2184" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2185" class="Symbol">}</a>

 <a id="2189" href="Structures.Sigma.Congruences.html#2189" class="Bound">𝑨</a> <a id="2191" href="Structures.Sigma.Congruences.html#2112" class="Function Operator">╱</a> <a id="2193" href="Structures.Sigma.Congruences.html#2193" class="Bound">θ</a> <a id="2195" class="Symbol">=</a> <a id="2197" class="Symbol">(</a><a id="2198" href="Relations.Quotients.html#5021" class="Function">Quotient</a> <a id="2207" class="Symbol">(</a><a id="2208" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2210" href="Structures.Sigma.Congruences.html#2189" class="Bound">𝑨</a> <a id="2212" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2213" class="Symbol">)</a> <a id="2215" class="Symbol">{</a><a id="2216" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="2218" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2220" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2221" class="Symbol">}</a> <a id="2223" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2225" href="Structures.Sigma.Congruences.html#2193" class="Bound">θ</a> <a id="2227" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2228" class="Symbol">)</a>        <a id="2237" class="Comment">-- domain of quotient structure</a>
          <a id="2279" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2281" class="Symbol">(λ</a> <a id="2284" href="Structures.Sigma.Congruences.html#2284" class="Bound">r</a> <a id="2286" href="Structures.Sigma.Congruences.html#2286" class="Bound">x</a> <a id="2288" class="Symbol">→</a> <a id="2290" class="Symbol">(</a><a id="2291" href="Structures.Sigma.Congruences.html#2284" class="Bound">r</a> <a id="2293" href="Structures.Sigma.Basic.html#2481" class="Function Operator">ʳ</a> <a id="2295" href="Structures.Sigma.Congruences.html#2189" class="Bound">𝑨</a><a id="2296" class="Symbol">)</a> <a id="2298" class="Symbol">λ</a> <a id="2300" href="Structures.Sigma.Congruences.html#2300" class="Bound">i</a> <a id="2302" class="Symbol">→</a> <a id="2304" href="Relations.Quotients.html#5567" class="Function Operator">⌞</a> <a id="2306" href="Structures.Sigma.Congruences.html#2286" class="Bound">x</a> <a id="2308" href="Structures.Sigma.Congruences.html#2300" class="Bound">i</a> <a id="2310" href="Relations.Quotients.html#5567" class="Function Operator">⌟</a><a id="2311" class="Symbol">)</a>      <a id="2318" class="Comment">-- interpretation of relations</a>
          <a id="2359" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2361" class="Symbol">λ</a> <a id="2363" href="Structures.Sigma.Congruences.html#2363" class="Bound">f</a> <a id="2365" href="Structures.Sigma.Congruences.html#2365" class="Bound">b</a> <a id="2367" class="Symbol">→</a> <a id="2369" href="Relations.Quotients.html#5374" class="Function Operator">⟪</a> <a id="2371" class="Symbol">(</a><a id="2372" href="Structures.Sigma.Congruences.html#2363" class="Bound">f</a> <a id="2374" href="Structures.Sigma.Basic.html#2577" class="Function Operator">ᵒ</a> <a id="2376" href="Structures.Sigma.Congruences.html#2189" class="Bound">𝑨</a><a id="2377" class="Symbol">)</a> <a id="2379" class="Symbol">(λ</a> <a id="2382" href="Structures.Sigma.Congruences.html#2382" class="Bound">i</a> <a id="2384" class="Symbol">→</a> <a id="2386" href="Relations.Quotients.html#5567" class="Function Operator">⌞</a> <a id="2388" href="Structures.Sigma.Congruences.html#2365" class="Bound">b</a> <a id="2390" href="Structures.Sigma.Congruences.html#2382" class="Bound">i</a> <a id="2392" href="Relations.Quotients.html#5567" class="Function Operator">⌟</a><a id="2393" class="Symbol">)</a>  <a id="2396" href="Relations.Quotients.html#5374" class="Function Operator">⟫</a> <a id="2398" class="Comment">-- interp of operations</a>

 <a id="2424" href="Structures.Sigma.Congruences.html#2424" class="Function">/≡-elim</a> <a id="2432" class="Symbol">:</a> <a id="2434" class="Symbol">{</a><a id="2435" href="Structures.Sigma.Congruences.html#2435" class="Bound">𝑨</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="2449" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="2451" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="2453" class="Symbol">{</a><a id="2454" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="2455" class="Symbol">}{</a><a id="2457" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2458" class="Symbol">}}(</a> <a id="2462" href="Structures.Sigma.Congruences.html#2462" class="Symbol">(</a><a id="2463" href="Structures.Sigma.Congruences.html#2463" class="Bound">θ</a> <a id="2465" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2467" href="Structures.Sigma.Congruences.html#2462" class="Symbol">_</a> <a id="2469" href="Structures.Sigma.Congruences.html#2462" class="Symbol">)</a> <a id="2471" class="Symbol">:</a> <a id="2473" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="2477" href="Structures.Sigma.Congruences.html#2435" class="Bound">𝑨</a><a id="2478" class="Symbol">){</a><a id="2480" href="Structures.Sigma.Congruences.html#2480" class="Bound">u</a> <a id="2482" href="Structures.Sigma.Congruences.html#2482" class="Bound">v</a> <a id="2484" class="Symbol">:</a> <a id="2486" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2488" href="Structures.Sigma.Congruences.html#2435" class="Bound">𝑨</a> <a id="2490" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2491" class="Symbol">}</a>
  <a id="2495" class="Symbol">→</a>    <a id="2500" href="Relations.Quotients.html#5374" class="Function Operator">⟪</a> <a id="2502" href="Structures.Sigma.Congruences.html#2480" class="Bound">u</a> <a id="2504" href="Relations.Quotients.html#5374" class="Function Operator">⟫</a><a id="2505" class="Symbol">{</a><a id="2506" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2508" href="Structures.Sigma.Congruences.html#2463" class="Bound">θ</a> <a id="2510" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2511" class="Symbol">}</a> <a id="2513" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2515" href="Relations.Quotients.html#5374" class="Function Operator">⟪</a> <a id="2517" href="Structures.Sigma.Congruences.html#2482" class="Bound">v</a> <a id="2519" href="Relations.Quotients.html#5374" class="Function Operator">⟫</a> <a id="2521" class="Symbol">→</a> <a id="2523" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2525" href="Structures.Sigma.Congruences.html#2463" class="Bound">θ</a> <a id="2527" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2529" href="Structures.Sigma.Congruences.html#2480" class="Bound">u</a> <a id="2531" href="Structures.Sigma.Congruences.html#2482" class="Bound">v</a>
 <a id="2534" href="Structures.Sigma.Congruences.html#2424" class="Function">/≡-elim</a> <a id="2542" href="Structures.Sigma.Congruences.html#2542" class="Bound">θ</a> <a id="2544" class="Symbol">{</a><a id="2545" href="Structures.Sigma.Congruences.html#2545" class="Bound">u</a><a id="2546" class="Symbol">}{</a><a id="2548" href="Structures.Sigma.Congruences.html#2548" class="Bound">v</a><a id="2549" class="Symbol">}</a> <a id="2551" href="Structures.Sigma.Congruences.html#2551" class="Bound">x</a> <a id="2553" class="Symbol">=</a>  <a id="2556" href="Relations.Quotients.html#7214" class="Function Operator">⟪</a> <a id="2558" href="Structures.Sigma.Congruences.html#2545" class="Bound">u</a> <a id="2560" href="Relations.Quotients.html#7214" class="Function Operator">∼</a> <a id="2562" href="Structures.Sigma.Congruences.html#2548" class="Bound">v</a> <a id="2564" href="Relations.Quotients.html#7214" class="Function Operator">⟫-elim</a> <a id="2571" class="Symbol">{</a><a id="2572" class="Argument">R</a> <a id="2574" class="Symbol">=</a> <a id="2576" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2578" href="Structures.Sigma.Congruences.html#2542" class="Bound">θ</a> <a id="2580" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2581" class="Symbol">}</a> <a id="2583" href="Structures.Sigma.Congruences.html#2551" class="Bound">x</a>

</pre>

Example. The zero congruence of an arbitrary structure.

<pre class="Agda">

 <a id="2670" href="Structures.Sigma.Congruences.html#2670" class="Function Operator">𝟘[_╱_]</a> <a id="2677" class="Symbol">:</a> <a id="2679" class="Symbol">(</a><a id="2680" href="Structures.Sigma.Congruences.html#2680" class="Bound">𝑨</a> <a id="2682" class="Symbol">:</a> <a id="2684" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="2694" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="2696" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="2698" class="Symbol">{</a><a id="2699" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a><a id="2700" class="Symbol">}{</a><a id="2702" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2703" class="Symbol">})(</a><a id="2706" href="Structures.Sigma.Congruences.html#2706" class="Bound">θ</a> <a id="2708" class="Symbol">:</a> <a id="2710" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="2714" href="Structures.Sigma.Congruences.html#2680" class="Bound">𝑨</a><a id="2715" class="Symbol">)</a> <a id="2717" class="Symbol">→</a> <a id="2719" href="Structures.Sigma.Congruences.html#829" class="Function">BinRel</a> <a id="2726" class="Symbol">(</a><a id="2727" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2729" href="Structures.Sigma.Congruences.html#2680" class="Bound">𝑨</a> <a id="2731" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2733" href="Relations.Quotients.html#5146" class="Function Operator">/</a> <a id="2735" class="Symbol">(</a><a id="2736" href="Structures.Sigma.Congruences.html#596" class="Field">fst</a> <a id="2740" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2742" href="Structures.Sigma.Congruences.html#2706" class="Bound">θ</a> <a id="2744" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a><a id="2745" class="Symbol">))</a> <a id="2748" class="Symbol">(</a><a id="2749" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2754" class="Symbol">(</a><a id="2755" href="Structures.Sigma.Congruences.html#1483" class="Bound">α</a> <a id="2757" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2759" href="Structures.Sigma.Congruences.html#1485" class="Bound">ρ</a><a id="2760" class="Symbol">))</a>
 <a id="2764" href="Structures.Sigma.Congruences.html#2670" class="Function Operator">𝟘[</a> <a id="2767" href="Structures.Sigma.Congruences.html#2767" class="Bound">𝑨</a> <a id="2769" href="Structures.Sigma.Congruences.html#2670" class="Function Operator">╱</a> <a id="2771" href="Structures.Sigma.Congruences.html#2771" class="Bound">θ</a> <a id="2773" href="Structures.Sigma.Congruences.html#2670" class="Function Operator">]</a> <a id="2775" class="Symbol">=</a> <a id="2777" class="Symbol">λ</a> <a id="2779" href="Structures.Sigma.Congruences.html#2779" class="Bound">u</a> <a id="2781" href="Structures.Sigma.Congruences.html#2781" class="Bound">v</a> <a id="2783" class="Symbol">→</a> <a id="2785" href="Structures.Sigma.Congruences.html#2779" class="Bound">u</a> <a id="2787" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="2789" href="Structures.Sigma.Congruences.html#2781" class="Bound">v</a>

<a id="𝟎[_╱_]"></a><a id="2792" href="Structures.Sigma.Congruences.html#2792" class="Function Operator">𝟎[_╱_]</a> <a id="2799" class="Symbol">:</a> <a id="2801" class="Symbol">{</a><a id="2802" href="Structures.Sigma.Congruences.html#2802" class="Bound">α</a> <a id="2804" href="Structures.Sigma.Congruences.html#2804" class="Bound">ρ</a> <a id="2806" class="Symbol">:</a> <a id="2808" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2813" class="Symbol">}(</a><a id="2815" href="Structures.Sigma.Congruences.html#2815" class="Bound">𝑨</a> <a id="2817" class="Symbol">:</a> <a id="2819" href="Structures.Sigma.Basic.html#1331" class="Function">Structure</a> <a id="2829" href="Structures.Sigma.Congruences.html#1456" class="Generalizable">𝑅</a> <a id="2831" href="Structures.Sigma.Congruences.html#1458" class="Generalizable">𝐹</a> <a id="2833" class="Symbol">{</a><a id="2834" href="Structures.Sigma.Congruences.html#2802" class="Bound">α</a><a id="2835" class="Symbol">}{</a><a id="2837" href="Structures.Sigma.Congruences.html#2804" class="Bound">ρ</a><a id="2838" class="Symbol">})(</a><a id="2841" href="Structures.Sigma.Congruences.html#2841" class="Bound">θ</a> <a id="2843" class="Symbol">:</a> <a id="2845" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="2849" href="Structures.Sigma.Congruences.html#2815" class="Bound">𝑨</a><a id="2850" class="Symbol">)</a> <a id="2852" class="Symbol">→</a> <a id="2854" href="Foundations.Welldefined.html#2648" class="Function">swelldef</a> <a id="2863" href="Structures.Sigma.Congruences.html#512" class="Primitive">ℓ₀</a> <a id="2866" class="Symbol">(</a><a id="2867" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2872" class="Symbol">(</a><a id="2873" href="Structures.Sigma.Congruences.html#2802" class="Bound">α</a> <a id="2875" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2877" href="Structures.Sigma.Congruences.html#2804" class="Bound">ρ</a><a id="2878" class="Symbol">))</a> <a id="2881" class="Symbol">→</a> <a id="2883" href="Structures.Sigma.Congruences.html#1504" class="Function">Con</a> <a id="2887" class="Symbol">(</a><a id="2888" href="Structures.Sigma.Congruences.html#2815" class="Bound">𝑨</a> <a id="2890" href="Structures.Sigma.Congruences.html#2112" class="Function Operator">╱</a> <a id="2892" href="Structures.Sigma.Congruences.html#2841" class="Bound">θ</a><a id="2893" class="Symbol">)</a>
<a id="2895" href="Structures.Sigma.Congruences.html#2792" class="Function Operator">𝟎[</a> <a id="2898" href="Structures.Sigma.Congruences.html#2898" class="Bound">𝑨</a> <a id="2900" href="Structures.Sigma.Congruences.html#2792" class="Function Operator">╱</a> <a id="2902" href="Structures.Sigma.Congruences.html#2902" class="Bound">θ</a> <a id="2904" href="Structures.Sigma.Congruences.html#2792" class="Function Operator">]</a> <a id="2906" href="Structures.Sigma.Congruences.html#2906" class="Bound">wd</a> <a id="2909" class="Symbol">=</a> <a id="2911" href="Relations.Quotients.html#7088" class="Function Operator">0[</a> <a id="2914" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2916" href="Structures.Sigma.Congruences.html#2898" class="Bound">𝑨</a> <a id="2918" href="Structures.Sigma.Congruences.html#2112" class="Function Operator">╱</a> <a id="2920" href="Structures.Sigma.Congruences.html#2902" class="Bound">θ</a> <a id="2922" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="2924" href="Relations.Quotients.html#7088" class="Function Operator">]Equivalence</a> <a id="2937" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="2939" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">0[</a> <a id="2942" href="Structures.Sigma.Congruences.html#2898" class="Bound">𝑨</a> <a id="2944" href="Structures.Sigma.Congruences.html#2112" class="Function Operator">╱</a> <a id="2946" href="Structures.Sigma.Congruences.html#2902" class="Bound">θ</a> <a id="2948" href="Structures.Sigma.Congruences.html#1665" class="Function Operator">]Compatible</a> <a id="2960" href="Structures.Sigma.Congruences.html#2906" class="Bound">wd</a>

</pre>

--------------------------------

<span style="float:left;">[← Structures.Sigma.Products](Structures.Sigma.Products.html)</span>
<span style="float:right;">[Structures.Sigma.Homs →](Structures.Sigma.Homs.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team