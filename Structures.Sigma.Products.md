---
layout: default
title : "Structures.Sigma.Products module"
date : "2021-05-11"
author: "agda-algebras development team"
---

#### <a id="product-structures">Product structures</a>

<pre class="Agda">

<a id="200" class="Symbol">{-#</a> <a id="204" class="Keyword">OPTIONS</a> <a id="212" class="Pragma">--without-K</a> <a id="224" class="Pragma">--exact-split</a> <a id="238" class="Pragma">--safe</a> <a id="245" class="Symbol">#-}</a>

<a id="250" class="Keyword">module</a> <a id="257" href="Structures.Sigma.Products.html" class="Module">Structures.Sigma.Products</a> <a id="283" class="Keyword">where</a>

<a id="290" class="Comment">-- Imports from the Agda Standard Library ------------------------------------</a>
<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="396" class="Keyword">using</a> <a id="402" class="Symbol">(</a> <a id="404" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="408" class="Symbol">;</a> <a id="410" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="415" class="Symbol">)</a> <a id="417" class="Keyword">renaming</a> <a id="426" class="Symbol">(</a> <a id="428" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="432" class="Symbol">to</a> <a id="435" class="Primitive">Type</a> <a id="440" class="Symbol">)</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="Data.Product.html" class="Module">Data.Product</a>   <a id="469" class="Keyword">using</a> <a id="475" class="Symbol">(</a> <a id="477" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="481" class="Symbol">;</a> <a id="483" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="487" class="Symbol">;</a> <a id="489" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="498" class="Symbol">)</a>
<a id="500" class="Keyword">open</a> <a id="505" class="Keyword">import</a> <a id="512" href="Level.html" class="Module">Level</a>          <a id="527" class="Keyword">using</a> <a id="533" class="Symbol">(</a> <a id="535" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="541" class="Symbol">;</a> <a id="543" href="Level.html#400" class="Record">Lift</a> <a id="548" class="Symbol">)</a>
<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="577" class="Keyword">using</a> <a id="583" class="Symbol">(</a> <a id="585" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="589" class="Symbol">;</a> <a id="591" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="596" class="Symbol">)</a>

<a id="599" class="Comment">-- Imports from the Agda Universal Algebra Library ---------------------------</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="713" class="Keyword">using</a> <a id="719" class="Symbol">(</a> <a id="721" href="Overture.Preliminaries.html#4383" class="Function Operator">∣_∣</a> <a id="725" class="Symbol">;</a> <a id="727" href="Overture.Preliminaries.html#4421" class="Function Operator">∥_∥</a> <a id="731" class="Symbol">;</a> <a id="733" href="Overture.Preliminaries.html#6099" class="Function">Π</a> <a id="735" class="Symbol">;</a> <a id="737" href="Overture.Preliminaries.html#6179" class="Function">Π-syntax</a> <a id="746" class="Symbol">)</a>
<a id="748" class="Keyword">open</a> <a id="753" class="Keyword">import</a> <a id="760" href="Structures.Sigma.Basic.html" class="Module">Structures.Sigma.Basic</a> <a id="783" class="Keyword">using</a> <a id="789" class="Symbol">(</a> <a id="791" href="Structures.Sigma.Basic.html#1174" class="Function">Signature</a> <a id="801" class="Symbol">;</a> <a id="803" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="813" class="Symbol">;</a> <a id="815" href="Structures.Sigma.Basic.html#2485" class="Function Operator">_ʳ_</a> <a id="819" class="Symbol">;</a> <a id="821" href="Structures.Sigma.Basic.html#2581" class="Function Operator">_ᵒ_</a> <a id="825" class="Symbol">)</a>

<a id="828" class="Keyword">private</a> <a id="836" class="Keyword">variable</a>
 <a id="846" href="Structures.Sigma.Products.html#846" class="Generalizable">𝑅</a> <a id="848" href="Structures.Sigma.Products.html#848" class="Generalizable">𝐹</a> <a id="850" class="Symbol">:</a> <a id="852" href="Structures.Sigma.Basic.html#1174" class="Function">Signature</a>
 <a id="863" href="Structures.Sigma.Products.html#863" class="Generalizable">α</a> <a id="865" href="Structures.Sigma.Products.html#865" class="Generalizable">ρ</a> <a id="867" href="Structures.Sigma.Products.html#867" class="Generalizable">ι</a> <a id="869" class="Symbol">:</a> <a id="871" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="⨅"></a><a id="878" href="Structures.Sigma.Products.html#878" class="Function">⨅</a> <a id="880" class="Symbol">:</a> <a id="882" class="Symbol">{</a><a id="883" href="Structures.Sigma.Products.html#883" class="Bound">ℑ</a> <a id="885" class="Symbol">:</a> <a id="887" href="Structures.Sigma.Products.html#435" class="Primitive">Type</a> <a id="892" href="Structures.Sigma.Products.html#867" class="Generalizable">ι</a><a id="893" class="Symbol">}(</a><a id="895" href="Structures.Sigma.Products.html#895" class="Bound">𝒜</a> <a id="897" class="Symbol">:</a> <a id="899" href="Structures.Sigma.Products.html#883" class="Bound">ℑ</a> <a id="901" class="Symbol">→</a> <a id="903" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a>  <a id="914" href="Structures.Sigma.Products.html#846" class="Generalizable">𝑅</a> <a id="916" href="Structures.Sigma.Products.html#848" class="Generalizable">𝐹</a><a id="917" class="Symbol">{</a><a id="918" href="Structures.Sigma.Products.html#863" class="Generalizable">α</a><a id="919" class="Symbol">}{</a><a id="921" href="Structures.Sigma.Products.html#865" class="Generalizable">ρ</a><a id="922" class="Symbol">})</a> <a id="925" class="Symbol">→</a> <a id="927" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="937" href="Structures.Sigma.Products.html#846" class="Generalizable">𝑅</a> <a id="939" href="Structures.Sigma.Products.html#848" class="Generalizable">𝐹</a> <a id="941" class="Symbol">{</a><a id="942" href="Structures.Sigma.Products.html#863" class="Generalizable">α</a> <a id="944" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="946" href="Structures.Sigma.Products.html#867" class="Generalizable">ι</a><a id="947" class="Symbol">}</a> <a id="949" class="Symbol">{</a><a id="950" href="Structures.Sigma.Products.html#865" class="Generalizable">ρ</a> <a id="952" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="954" href="Structures.Sigma.Products.html#867" class="Generalizable">ι</a><a id="955" class="Symbol">}</a>
<a id="957" href="Structures.Sigma.Products.html#878" class="Function">⨅</a> <a id="959" class="Symbol">{</a><a id="960" class="Argument">ℑ</a> <a id="962" class="Symbol">=</a> <a id="964" href="Structures.Sigma.Products.html#964" class="Bound">ℑ</a><a id="965" class="Symbol">}</a> <a id="967" href="Structures.Sigma.Products.html#967" class="Bound">𝒜</a> <a id="969" class="Symbol">=</a> <a id="971" href="Overture.Preliminaries.html#6179" class="Function">Π[</a> <a id="974" href="Structures.Sigma.Products.html#974" class="Bound">𝔦</a> <a id="976" href="Overture.Preliminaries.html#6179" class="Function">∈</a> <a id="978" href="Structures.Sigma.Products.html#964" class="Bound">ℑ</a> <a id="980" href="Overture.Preliminaries.html#6179" class="Function">]</a> <a id="982" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="984" href="Structures.Sigma.Products.html#967" class="Bound">𝒜</a> <a id="986" href="Structures.Sigma.Products.html#974" class="Bound">𝔦</a> <a id="988" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="990" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a>               <a id="1006" class="Comment">-- domain of the product structure</a>
         <a id="1050" class="Symbol">(</a> <a id="1052" class="Symbol">λ</a> <a id="1054" href="Structures.Sigma.Products.html#1054" class="Bound">r</a> <a id="1056" href="Structures.Sigma.Products.html#1056" class="Bound">a</a> <a id="1058" class="Symbol">→</a> <a id="1060" class="Symbol">∀</a> <a id="1062" href="Structures.Sigma.Products.html#1062" class="Bound">𝔦</a> <a id="1064" class="Symbol">→</a> <a id="1066" class="Symbol">(</a><a id="1067" href="Structures.Sigma.Products.html#1054" class="Bound">r</a> <a id="1069" href="Structures.Sigma.Basic.html#2485" class="Function Operator">ʳ</a> <a id="1071" href="Structures.Sigma.Products.html#967" class="Bound">𝒜</a> <a id="1073" href="Structures.Sigma.Products.html#1062" class="Bound">𝔦</a><a id="1074" class="Symbol">)</a> <a id="1076" class="Symbol">λ</a> <a id="1078" href="Structures.Sigma.Products.html#1078" class="Bound">x</a> <a id="1080" class="Symbol">→</a> <a id="1082" href="Structures.Sigma.Products.html#1056" class="Bound">a</a> <a id="1084" href="Structures.Sigma.Products.html#1078" class="Bound">x</a> <a id="1086" href="Structures.Sigma.Products.html#1062" class="Bound">𝔦</a> <a id="1088" class="Symbol">)</a> <a id="1090" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1092" class="Comment">-- interpretations of relations</a>
         <a id="1133" class="Symbol">(</a> <a id="1135" class="Symbol">λ</a> <a id="1137" href="Structures.Sigma.Products.html#1137" class="Bound">𝑓</a> <a id="1139" href="Structures.Sigma.Products.html#1139" class="Bound">a</a> <a id="1141" href="Structures.Sigma.Products.html#1141" class="Bound">𝔦</a> <a id="1143" class="Symbol">→</a> <a id="1145" class="Symbol">(</a><a id="1146" href="Structures.Sigma.Products.html#1137" class="Bound">𝑓</a> <a id="1148" href="Structures.Sigma.Basic.html#2581" class="Function Operator">ᵒ</a> <a id="1150" href="Structures.Sigma.Products.html#967" class="Bound">𝒜</a> <a id="1152" href="Structures.Sigma.Products.html#1141" class="Bound">𝔦</a><a id="1153" class="Symbol">)</a> <a id="1155" class="Symbol">λ</a> <a id="1157" href="Structures.Sigma.Products.html#1157" class="Bound">x</a> <a id="1159" class="Symbol">→</a> <a id="1161" href="Structures.Sigma.Products.html#1139" class="Bound">a</a> <a id="1163" href="Structures.Sigma.Products.html#1157" class="Bound">x</a> <a id="1165" href="Structures.Sigma.Products.html#1141" class="Bound">𝔦</a> <a id="1167" class="Symbol">)</a>        <a id="1176" class="Comment">-- interpretations of  operations</a>

<a id="1211" class="Keyword">module</a> <a id="1218" href="Structures.Sigma.Products.html#1218" class="Module">_</a> <a id="1220" class="Symbol">{</a><a id="1221" href="Structures.Sigma.Products.html#1221" class="Bound">α</a> <a id="1223" href="Structures.Sigma.Products.html#1223" class="Bound">ρ</a> <a id="1225" href="Structures.Sigma.Products.html#1225" class="Bound">τ</a> <a id="1227" class="Symbol">:</a> <a id="1229" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="1234" class="Symbol">}{</a><a id="1236" href="Structures.Sigma.Products.html#1236" class="Bound">𝒦</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="1245" class="Symbol">(</a><a id="1246" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="1256" href="Structures.Sigma.Products.html#846" class="Generalizable">𝑅</a> <a id="1258" href="Structures.Sigma.Products.html#848" class="Generalizable">𝐹</a> <a id="1260" class="Symbol">{</a><a id="1261" href="Structures.Sigma.Products.html#1221" class="Bound">α</a><a id="1262" class="Symbol">}{</a><a id="1264" href="Structures.Sigma.Products.html#1223" class="Bound">ρ</a><a id="1265" class="Symbol">})</a> <a id="1268" href="Structures.Sigma.Products.html#1225" class="Bound">τ</a><a id="1269" class="Symbol">}</a> <a id="1271" class="Keyword">where</a>

 <a id="1279" href="Structures.Sigma.Products.html#1279" class="Function">ℓp</a> <a id="1282" class="Symbol">:</a> <a id="1284" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1291" href="Structures.Sigma.Products.html#1279" class="Function">ℓp</a> <a id="1294" class="Symbol">=</a> <a id="1296" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="1301" class="Symbol">(</a><a id="1302" href="Structures.Sigma.Products.html#1221" class="Bound">α</a> <a id="1304" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1306" href="Structures.Sigma.Products.html#1223" class="Bound">ρ</a><a id="1307" class="Symbol">)</a> <a id="1309" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1311" href="Structures.Sigma.Products.html#1225" class="Bound">τ</a>

 <a id="1315" href="Structures.Sigma.Products.html#1315" class="Function">ℑ</a> <a id="1317" class="Symbol">:</a> <a id="1319" href="Structures.Sigma.Products.html#435" class="Primitive">Type</a> <a id="1324" href="Structures.Sigma.Products.html#1279" class="Function">ℓp</a>
 <a id="1328" href="Structures.Sigma.Products.html#1315" class="Function">ℑ</a> <a id="1330" class="Symbol">=</a> <a id="1332" href="Data.Product.html#916" class="Function">Σ[</a> <a id="1335" href="Structures.Sigma.Products.html#1335" class="Bound">𝑨</a> <a id="1337" href="Data.Product.html#916" class="Function">∈</a> <a id="1339" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="1349" href="Structures.Sigma.Products.html#1256" class="Bound">𝑅</a> <a id="1351" href="Structures.Sigma.Products.html#1258" class="Bound">𝐹</a> <a id="1353" href="Data.Product.html#916" class="Function">]</a> <a id="1355" class="Symbol">(</a><a id="1356" href="Structures.Sigma.Products.html#1335" class="Bound">𝑨</a> <a id="1358" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="1360" href="Structures.Sigma.Products.html#1236" class="Bound">𝒦</a><a id="1361" class="Symbol">)</a>

 <a id="1365" href="Structures.Sigma.Products.html#1365" class="Function">𝔖</a> <a id="1367" class="Symbol">:</a> <a id="1369" href="Structures.Sigma.Products.html#1315" class="Function">ℑ</a> <a id="1371" class="Symbol">→</a> <a id="1373" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="1383" href="Structures.Sigma.Products.html#1256" class="Bound">𝑅</a> <a id="1385" href="Structures.Sigma.Products.html#1258" class="Bound">𝐹</a>        <a id="1394" class="Comment">-- (type \MfS to get 𝔖)</a>
 <a id="1419" href="Structures.Sigma.Products.html#1365" class="Function">𝔖</a> <a id="1421" href="Structures.Sigma.Products.html#1421" class="Bound">𝔦</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="1427" href="Structures.Sigma.Products.html#1421" class="Bound">𝔦</a> <a id="1429" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a>

 <a id="1433" href="Structures.Sigma.Products.html#1433" class="Function">class-prod</a> <a id="1444" class="Symbol">:</a> <a id="1446" href="Structures.Sigma.Basic.html#1335" class="Function">Structure</a> <a id="1456" href="Structures.Sigma.Products.html#1256" class="Bound">𝑅</a> <a id="1458" href="Structures.Sigma.Products.html#1258" class="Bound">𝐹</a>
 <a id="1461" href="Structures.Sigma.Products.html#1433" class="Function">class-prod</a> <a id="1472" class="Symbol">=</a> <a id="1474" href="Structures.Sigma.Products.html#878" class="Function">⨅</a> <a id="1476" href="Structures.Sigma.Products.html#1365" class="Function">𝔖</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

--------------------------------

<span style="float:left;">[← Structures.Sigma.Basic](Structures.Sigma.Basic.html)</span>
<span style="float:right;">[Structures.Sigma.Congruences →](Structures.Sigma.Congruences.html)</span>

{% include UALib.Links.md %}