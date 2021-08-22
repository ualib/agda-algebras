---
layout: default
title : Sturctures.Products module
date : 2021-05-11
author: [agda-algebras development team][]
---

### Products for structures as records

This module is similar to Products.lagda but for structures represented using records rather than
dependent pair type.

<pre class="Agda">

<a id="296" class="Symbol">{-#</a> <a id="300" class="Keyword">OPTIONS</a> <a id="308" class="Pragma">--without-K</a> <a id="320" class="Pragma">--exact-split</a> <a id="334" class="Pragma">--safe</a> <a id="341" class="Symbol">#-}</a> <a id="345" class="Comment">-- cubical #-}</a>

<a id="361" class="Keyword">module</a> <a id="368" href="Structures.Products.html" class="Module">Structures.Products</a> <a id="388" class="Keyword">where</a>

<a id="395" class="Comment">-- Imports from the Agda Standard Library ----------------------------------</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="499" class="Keyword">using</a> <a id="505" class="Symbol">(</a> <a id="507" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="511" class="Symbol">;</a> <a id="513" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="518" class="Symbol">)</a> <a id="520" class="Keyword">renaming</a> <a id="529" class="Symbol">(</a> <a id="531" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="535" class="Symbol">to</a> <a id="538" class="Primitive">Type</a> <a id="543" class="Symbol">)</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="Data.Product.html" class="Module">Data.Product</a>   <a id="572" class="Keyword">using</a> <a id="578" class="Symbol">(</a> <a id="580" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="584" class="Symbol">;</a> <a id="586" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="595" class="Symbol">)</a>
<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="Level.html" class="Module">Level</a>          <a id="624" class="Keyword">using</a> <a id="630" class="Symbol">(</a> <a id="632" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="638" class="Symbol">)</a>
<a id="640" class="Keyword">open</a> <a id="645" class="Keyword">import</a> <a id="652" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="667" class="Keyword">using</a> <a id="673" class="Symbol">(</a> <a id="675" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="679" class="Symbol">;</a> <a id="681" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="686" class="Symbol">)</a>

<a id="689" class="Comment">-- Imports from agda-algebras ----------------------------------------------</a>
<a id="766" class="Keyword">open</a> <a id="771" class="Keyword">import</a> <a id="778" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="801" class="Keyword">using</a> <a id="807" class="Symbol">(</a> <a id="809" href="Overture.Preliminaries.html#4155" class="Function Operator">∣_∣</a> <a id="813" class="Symbol">;</a> <a id="815" href="Overture.Preliminaries.html#5743" class="Function">Π-syntax</a> <a id="824" class="Symbol">)</a>
<a id="826" class="Keyword">open</a> <a id="831" class="Keyword">import</a> <a id="838" href="Structures.Basic.html" class="Module">Structures.Basic</a>       <a id="861" class="Keyword">using</a> <a id="867" class="Symbol">(</a> <a id="869" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="879" class="Symbol">;</a> <a id="881" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="891" class="Symbol">)</a>


<a id="895" class="Keyword">private</a> <a id="903" class="Keyword">variable</a>
 <a id="913" href="Structures.Products.html#913" class="Generalizable">𝓞₀</a> <a id="916" href="Structures.Products.html#916" class="Generalizable">𝓥₀</a> <a id="919" href="Structures.Products.html#919" class="Generalizable">𝓞₁</a> <a id="922" href="Structures.Products.html#922" class="Generalizable">𝓥₁</a> <a id="925" class="Symbol">:</a> <a id="927" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="934" href="Structures.Products.html#934" class="Generalizable">𝐹</a> <a id="936" class="Symbol">:</a> <a id="938" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="948" href="Structures.Products.html#913" class="Generalizable">𝓞₀</a> <a id="951" href="Structures.Products.html#916" class="Generalizable">𝓥₀</a>
 <a id="955" href="Structures.Products.html#955" class="Generalizable">𝑅</a> <a id="957" class="Symbol">:</a> <a id="959" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="969" href="Structures.Products.html#919" class="Generalizable">𝓞₁</a> <a id="972" href="Structures.Products.html#922" class="Generalizable">𝓥₁</a>
 <a id="976" href="Structures.Products.html#976" class="Generalizable">α</a> <a id="978" href="Structures.Products.html#978" class="Generalizable">ρ</a> <a id="980" href="Structures.Products.html#980" class="Generalizable">ℓ</a> <a id="982" class="Symbol">:</a> <a id="984" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="991" class="Keyword">open</a> <a id="996" href="Structures.Basic.html#1458" class="Module">structure</a>

<a id="⨅"></a><a id="1007" href="Structures.Products.html#1007" class="Function">⨅</a> <a id="1009" class="Symbol">:</a> <a id="1011" class="Symbol">{</a><a id="1012" href="Structures.Products.html#1012" class="Bound">ℑ</a> <a id="1014" class="Symbol">:</a> <a id="1016" href="Structures.Products.html#538" class="Primitive">Type</a> <a id="1021" href="Structures.Products.html#980" class="Generalizable">ℓ</a><a id="1022" class="Symbol">}(</a><a id="1024" href="Structures.Products.html#1024" class="Bound">𝒜</a> <a id="1026" class="Symbol">:</a> <a id="1028" href="Structures.Products.html#1012" class="Bound">ℑ</a> <a id="1030" class="Symbol">→</a> <a id="1032" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1042" href="Structures.Products.html#934" class="Generalizable">𝐹</a> <a id="1044" href="Structures.Products.html#955" class="Generalizable">𝑅</a> <a id="1046" class="Symbol">{</a><a id="1047" href="Structures.Products.html#976" class="Generalizable">α</a><a id="1048" class="Symbol">}{</a><a id="1050" href="Structures.Products.html#978" class="Generalizable">ρ</a><a id="1051" class="Symbol">}</a> <a id="1053" class="Symbol">)</a> <a id="1055" class="Symbol">→</a> <a id="1057" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1067" href="Structures.Products.html#934" class="Generalizable">𝐹</a> <a id="1069" href="Structures.Products.html#955" class="Generalizable">𝑅</a>
<a id="1071" href="Structures.Products.html#1007" class="Function">⨅</a> <a id="1073" class="Symbol">{</a><a id="1074" class="Argument">ℑ</a> <a id="1076" class="Symbol">=</a> <a id="1078" href="Structures.Products.html#1078" class="Bound">ℑ</a><a id="1079" class="Symbol">}</a> <a id="1081" href="Structures.Products.html#1081" class="Bound">𝒜</a> <a id="1083" class="Symbol">=</a>
 <a id="1086" class="Keyword">record</a> <a id="1093" class="Symbol">{</a> <a id="1095" href="Structures.Basic.html#1610" class="Field">carrier</a> <a id="1103" class="Symbol">=</a> <a id="1105" href="Overture.Preliminaries.html#5743" class="Function">Π[</a> <a id="1108" href="Structures.Products.html#1108" class="Bound">i</a> <a id="1110" href="Overture.Preliminaries.html#5743" class="Function">∈</a> <a id="1112" href="Structures.Products.html#1078" class="Bound">ℑ</a> <a id="1114" href="Overture.Preliminaries.html#5743" class="Function">]</a> <a id="1116" href="Structures.Basic.html#1610" class="Field">carrier</a> <a id="1124" class="Symbol">(</a><a id="1125" href="Structures.Products.html#1081" class="Bound">𝒜</a> <a id="1127" href="Structures.Products.html#1108" class="Bound">i</a><a id="1128" class="Symbol">)</a>            <a id="1141" class="Comment">-- domain of the product structure</a>
        <a id="1184" class="Symbol">;</a> <a id="1186" href="Structures.Basic.html#1629" class="Field">op</a> <a id="1189" class="Symbol">=</a> <a id="1191" class="Symbol">λ</a> <a id="1193" href="Structures.Products.html#1193" class="Bound">𝑓</a> <a id="1195" href="Structures.Products.html#1195" class="Bound">a</a> <a id="1197" href="Structures.Products.html#1197" class="Bound">i</a> <a id="1199" class="Symbol">→</a> <a id="1201" class="Symbol">(</a><a id="1202" href="Structures.Basic.html#1629" class="Field">op</a> <a id="1205" class="Symbol">(</a><a id="1206" href="Structures.Products.html#1081" class="Bound">𝒜</a> <a id="1208" href="Structures.Products.html#1197" class="Bound">i</a><a id="1209" class="Symbol">)</a> <a id="1211" href="Structures.Products.html#1193" class="Bound">𝑓</a><a id="1212" class="Symbol">)</a> <a id="1214" class="Symbol">λ</a> <a id="1216" href="Structures.Products.html#1216" class="Bound">x</a> <a id="1218" class="Symbol">→</a> <a id="1220" href="Structures.Products.html#1195" class="Bound">a</a> <a id="1222" href="Structures.Products.html#1216" class="Bound">x</a> <a id="1224" href="Structures.Products.html#1197" class="Bound">i</a>       <a id="1232" class="Comment">-- interpretation of  operations</a>
        <a id="1273" class="Symbol">;</a> <a id="1275" href="Structures.Basic.html#1713" class="Field">rel</a> <a id="1279" class="Symbol">=</a> <a id="1281" class="Symbol">λ</a> <a id="1283" href="Structures.Products.html#1283" class="Bound">r</a> <a id="1285" href="Structures.Products.html#1285" class="Bound">a</a> <a id="1287" class="Symbol">→</a> <a id="1289" class="Symbol">∀</a> <a id="1291" href="Structures.Products.html#1291" class="Bound">i</a> <a id="1293" class="Symbol">→</a> <a id="1295" class="Symbol">(</a><a id="1296" href="Structures.Basic.html#1713" class="Field">rel</a> <a id="1300" class="Symbol">(</a><a id="1301" href="Structures.Products.html#1081" class="Bound">𝒜</a> <a id="1303" href="Structures.Products.html#1291" class="Bound">i</a><a id="1304" class="Symbol">)</a> <a id="1306" href="Structures.Products.html#1283" class="Bound">r</a><a id="1307" class="Symbol">)</a> <a id="1309" class="Symbol">λ</a> <a id="1311" href="Structures.Products.html#1311" class="Bound">x</a> <a id="1313" class="Symbol">→</a> <a id="1315" href="Structures.Products.html#1285" class="Bound">a</a> <a id="1317" href="Structures.Products.html#1311" class="Bound">x</a> <a id="1319" href="Structures.Products.html#1291" class="Bound">i</a> <a id="1321" class="Comment">-- interpretation of relations</a>
        <a id="1360" class="Symbol">}</a>


<a id="1364" class="Keyword">module</a> <a id="1371" href="Structures.Products.html#1371" class="Module">_</a> <a id="1373" class="Symbol">{</a><a id="1374" href="Structures.Products.html#1374" class="Bound">𝒦</a> <a id="1376" class="Symbol">:</a> <a id="1378" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1383" class="Symbol">(</a><a id="1384" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1394" href="Structures.Products.html#934" class="Generalizable">𝐹</a> <a id="1396" href="Structures.Products.html#955" class="Generalizable">𝑅</a> <a id="1398" class="Symbol">{</a><a id="1399" href="Structures.Products.html#976" class="Generalizable">α</a><a id="1400" class="Symbol">}{</a><a id="1402" href="Structures.Products.html#978" class="Generalizable">ρ</a><a id="1403" class="Symbol">})</a> <a id="1406" href="Structures.Products.html#980" class="Generalizable">ℓ</a><a id="1407" class="Symbol">}</a> <a id="1409" class="Keyword">where</a>

  <a id="1418" href="Structures.Products.html#1418" class="Function">ℓp</a> <a id="1421" class="Symbol">:</a> <a id="1423" href="Agda.Primitive.html#597" class="Postulate">Level</a>
  <a id="1431" href="Structures.Products.html#1418" class="Function">ℓp</a> <a id="1434" class="Symbol">=</a> <a id="1436" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1441" class="Symbol">(</a><a id="1442" href="Structures.Products.html#1399" class="Bound">α</a> <a id="1444" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1446" href="Structures.Products.html#1402" class="Bound">ρ</a><a id="1447" class="Symbol">)</a> <a id="1449" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1451" href="Structures.Products.html#1406" class="Bound">ℓ</a>

  <a id="1456" href="Structures.Products.html#1456" class="Function">ℑ</a> <a id="1458" class="Symbol">:</a> <a id="1460" href="Structures.Products.html#538" class="Primitive">Type</a> <a id="1465" class="Symbol">_</a>
  <a id="1469" href="Structures.Products.html#1456" class="Function">ℑ</a> <a id="1471" class="Symbol">=</a> <a id="1473" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1476" href="Structures.Products.html#1476" class="Bound">𝑨</a> <a id="1478" href="Data.Product.html#916" class="Function">∈</a> <a id="1480" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1490" href="Structures.Products.html#1394" class="Bound">𝐹</a> <a id="1492" href="Structures.Products.html#1396" class="Bound">𝑅</a>  <a id="1495" class="Symbol">{</a><a id="1496" href="Structures.Products.html#1399" class="Bound">α</a><a id="1497" class="Symbol">}{</a><a id="1499" href="Structures.Products.html#1402" class="Bound">ρ</a><a id="1500" class="Symbol">}</a><a id="1501" href="Data.Product.html#916" class="Function">]</a> <a id="1503" href="Structures.Products.html#1476" class="Bound">𝑨</a> <a id="1505" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1507" href="Structures.Products.html#1374" class="Bound">𝒦</a>

  <a id="1512" href="Structures.Products.html#1512" class="Function">𝔄</a> <a id="1514" class="Symbol">:</a> <a id="1516" href="Structures.Products.html#1456" class="Function">ℑ</a> <a id="1518" class="Symbol">→</a> <a id="1520" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1530" href="Structures.Products.html#1394" class="Bound">𝐹</a> <a id="1532" href="Structures.Products.html#1396" class="Bound">𝑅</a> <a id="1534" class="Symbol">{</a><a id="1535" href="Structures.Products.html#1399" class="Bound">α</a><a id="1536" class="Symbol">}{</a><a id="1538" href="Structures.Products.html#1402" class="Bound">ρ</a><a id="1539" class="Symbol">}</a>
  <a id="1543" href="Structures.Products.html#1512" class="Function">𝔄</a> <a id="1545" href="Structures.Products.html#1545" class="Bound">𝔦</a> <a id="1547" class="Symbol">=</a> <a id="1549" href="Overture.Preliminaries.html#4155" class="Function Operator">∣</a> <a id="1551" href="Structures.Products.html#1545" class="Bound">𝔦</a> <a id="1553" href="Overture.Preliminaries.html#4155" class="Function Operator">∣</a>

  <a id="1558" href="Structures.Products.html#1558" class="Function">class-product</a> <a id="1572" class="Symbol">:</a> <a id="1574" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1584" href="Structures.Products.html#1394" class="Bound">𝐹</a> <a id="1586" href="Structures.Products.html#1396" class="Bound">𝑅</a>
  <a id="1590" href="Structures.Products.html#1558" class="Function">class-product</a> <a id="1604" class="Symbol">=</a> <a id="1606" href="Structures.Products.html#1007" class="Function">⨅</a> <a id="1608" href="Structures.Products.html#1512" class="Function">𝔄</a>

</pre>

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Unary using (Pred; _∈_)

-- Imports from the Agda Universal Algebra Library
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
-- open import Algebras.Basic


-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Binary.PropositionalEquality.Core using (trans)

-- open import Agda.Primitive using (_⊔_; lsuc)
-- open import Relation.Unary using (Pred; _∈_)

-- open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
-- open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_)
-- open import Cubical.Foundations.Function using (_∘_)
-- open import Cubical.Data.Sigma.Base using (_×_)

-- -- Imports from the Agda Universal Algebra Library
-- open import overture.preliminaries using (Π; Π-syntax; _⁻¹; id; ∣_∣)
-- open import structures.basic using (Signature; Structure; _ʳ_; _ᵒ_; signature; structure)
-- open import overture.inverses using (IsInjective; IsSurjective)
-- open import relations.discrete using (ker)


