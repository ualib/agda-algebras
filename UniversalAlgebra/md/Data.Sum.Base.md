---
layout: default
---

<pre class="Agda">
<a id="1" class="Comment">------------------------------------------------------------------------</a>
<a id="74" class="Comment">-- The Agda standard library</a>
<a id="103" class="Comment">--</a>
<a id="106" class="Comment">-- Sums (disjoint unions)</a>
<a id="132" class="Comment">------------------------------------------------------------------------</a>

<a id="206" class="Symbol">{-#</a> <a id="210" class="Keyword">OPTIONS</a> <a id="218" class="Pragma">--without-K</a> <a id="230" class="Pragma">--safe</a> <a id="237" class="Symbol">#-}</a>

<a id="242" class="Keyword">module</a> <a id="249" href="Data.Sum.Base.html" class="Module">Data.Sum.Base</a> <a id="263" class="Keyword">where</a>

<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="Function.html" class="Module">Function</a> <a id="291" class="Keyword">using</a> <a id="297" class="Symbol">(</a><a id="298" href="Function.html#1099" class="Function Operator">_∘_</a><a id="301" class="Symbol">;</a> <a id="303" href="Function.html#4171" class="Function Operator">_-[_]-_</a> <a id="311" class="Symbol">;</a> <a id="313" href="Function.html#708" class="Function">id</a><a id="315" class="Symbol">)</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="346" class="Keyword">using</a> <a id="352" class="Symbol">(</a><a id="353" href="Relation.Nullary.html#605" class="Datatype">Dec</a><a id="356" class="Symbol">;</a> <a id="358" href="Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="361" class="Symbol">;</a> <a id="363" href="Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="365" class="Symbol">;</a> <a id="367" href="Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="369" class="Symbol">)</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="Level.html" class="Module">Level</a> <a id="389" class="Keyword">using</a> <a id="395" class="Symbol">(</a><a id="396" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="401" class="Symbol">;</a> <a id="403" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="406" class="Symbol">)</a>

<a id="409" class="Keyword">private</a>
  <a id="419" class="Keyword">variable</a>
    <a id="432" href="Data.Sum.Base.html#432" class="Generalizable">a</a> <a id="434" href="Data.Sum.Base.html#434" class="Generalizable">b</a> <a id="436" href="Data.Sum.Base.html#436" class="Generalizable">c</a> <a id="438" href="Data.Sum.Base.html#438" class="Generalizable">d</a> <a id="440" class="Symbol">:</a> <a id="442" href="Agda.Primitive.html#423" class="Postulate">Level</a>
    <a id="452" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="454" class="Symbol">:</a> <a id="456" class="PrimitiveType">Set</a> <a id="460" href="Data.Sum.Base.html#432" class="Generalizable">a</a>
    <a id="466" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="468" class="Symbol">:</a> <a id="470" class="PrimitiveType">Set</a> <a id="474" href="Data.Sum.Base.html#434" class="Generalizable">b</a>
    <a id="480" href="Data.Sum.Base.html#480" class="Generalizable">C</a> <a id="482" class="Symbol">:</a> <a id="484" class="PrimitiveType">Set</a> <a id="488" href="Data.Sum.Base.html#436" class="Generalizable">c</a>
    <a id="494" href="Data.Sum.Base.html#494" class="Generalizable">D</a> <a id="496" class="Symbol">:</a> <a id="498" class="PrimitiveType">Set</a> <a id="502" href="Data.Sum.Base.html#438" class="Generalizable">d</a>

<a id="505" class="Comment">------------------------------------------------------------------------</a>
<a id="578" class="Comment">-- Definition</a>

<a id="593" class="Keyword">infixr</a> <a id="600" class="Number">1</a> <a id="602" href="Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a>

<a id="607" class="Keyword">data</a> <a id="_⊎_"></a><a id="612" href="Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a> <a id="616" class="Symbol">(</a><a id="617" href="Data.Sum.Base.html#617" class="Bound">A</a> <a id="619" class="Symbol">:</a> <a id="621" class="PrimitiveType">Set</a> <a id="625" href="Data.Sum.Base.html#432" class="Generalizable">a</a><a id="626" class="Symbol">)</a> <a id="628" class="Symbol">(</a><a id="629" href="Data.Sum.Base.html#629" class="Bound">B</a> <a id="631" class="Symbol">:</a> <a id="633" class="PrimitiveType">Set</a> <a id="637" href="Data.Sum.Base.html#434" class="Generalizable">b</a><a id="638" class="Symbol">)</a> <a id="640" class="Symbol">:</a> <a id="642" class="PrimitiveType">Set</a> <a id="646" class="Symbol">(</a><a id="647" href="Data.Sum.Base.html#625" class="Bound">a</a> <a id="649" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="651" href="Data.Sum.Base.html#637" class="Bound">b</a><a id="652" class="Symbol">)</a> <a id="654" class="Keyword">where</a>
  <a id="_⊎_.inj₁"></a><a id="662" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="667" class="Symbol">:</a> <a id="669" class="Symbol">(</a><a id="670" href="Data.Sum.Base.html#670" class="Bound">x</a> <a id="672" class="Symbol">:</a> <a id="674" href="Data.Sum.Base.html#617" class="Bound">A</a><a id="675" class="Symbol">)</a> <a id="677" class="Symbol">→</a> <a id="679" href="Data.Sum.Base.html#617" class="Bound">A</a> <a id="681" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="683" href="Data.Sum.Base.html#629" class="Bound">B</a>
  <a id="_⊎_.inj₂"></a><a id="687" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="692" class="Symbol">:</a> <a id="694" class="Symbol">(</a><a id="695" href="Data.Sum.Base.html#695" class="Bound">y</a> <a id="697" class="Symbol">:</a> <a id="699" href="Data.Sum.Base.html#629" class="Bound">B</a><a id="700" class="Symbol">)</a> <a id="702" class="Symbol">→</a> <a id="704" href="Data.Sum.Base.html#617" class="Bound">A</a> <a id="706" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="708" href="Data.Sum.Base.html#629" class="Bound">B</a>

<a id="711" class="Comment">------------------------------------------------------------------------</a>
<a id="784" class="Comment">-- Functions</a>

<a id="[_,_]"></a><a id="798" href="Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="804" class="Symbol">:</a> <a id="806" class="Symbol">∀</a> <a id="808" class="Symbol">{</a><a id="809" href="Data.Sum.Base.html#809" class="Bound">C</a> <a id="811" class="Symbol">:</a> <a id="813" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="815" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="817" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="819" class="Symbol">→</a> <a id="821" class="PrimitiveType">Set</a> <a id="825" href="Data.Sum.Base.html#436" class="Generalizable">c</a><a id="826" class="Symbol">}</a> <a id="828" class="Symbol">→</a>
        <a id="838" class="Symbol">((</a><a id="840" href="Data.Sum.Base.html#840" class="Bound">x</a> <a id="842" class="Symbol">:</a> <a id="844" href="Data.Sum.Base.html#452" class="Generalizable">A</a><a id="845" class="Symbol">)</a> <a id="847" class="Symbol">→</a> <a id="849" href="Data.Sum.Base.html#809" class="Bound">C</a> <a id="851" class="Symbol">(</a><a id="852" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="857" href="Data.Sum.Base.html#840" class="Bound">x</a><a id="858" class="Symbol">))</a> <a id="861" class="Symbol">→</a> <a id="863" class="Symbol">((</a><a id="865" href="Data.Sum.Base.html#865" class="Bound">x</a> <a id="867" class="Symbol">:</a> <a id="869" href="Data.Sum.Base.html#466" class="Generalizable">B</a><a id="870" class="Symbol">)</a> <a id="872" class="Symbol">→</a> <a id="874" href="Data.Sum.Base.html#809" class="Bound">C</a> <a id="876" class="Symbol">(</a><a id="877" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="882" href="Data.Sum.Base.html#865" class="Bound">x</a><a id="883" class="Symbol">))</a> <a id="886" class="Symbol">→</a>
        <a id="896" class="Symbol">((</a><a id="898" href="Data.Sum.Base.html#898" class="Bound">x</a> <a id="900" class="Symbol">:</a> <a id="902" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="904" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="906" href="Data.Sum.Base.html#466" class="Generalizable">B</a><a id="907" class="Symbol">)</a> <a id="909" class="Symbol">→</a> <a id="911" href="Data.Sum.Base.html#809" class="Bound">C</a> <a id="913" href="Data.Sum.Base.html#898" class="Bound">x</a><a id="914" class="Symbol">)</a>
<a id="916" href="Data.Sum.Base.html#798" class="Function Operator">[</a> <a id="918" href="Data.Sum.Base.html#918" class="Bound">f</a> <a id="920" href="Data.Sum.Base.html#798" class="Function Operator">,</a> <a id="922" href="Data.Sum.Base.html#922" class="Bound">g</a> <a id="924" href="Data.Sum.Base.html#798" class="Function Operator">]</a> <a id="926" class="Symbol">(</a><a id="927" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="932" href="Data.Sum.Base.html#932" class="Bound">x</a><a id="933" class="Symbol">)</a> <a id="935" class="Symbol">=</a> <a id="937" href="Data.Sum.Base.html#918" class="Bound">f</a> <a id="939" href="Data.Sum.Base.html#932" class="Bound">x</a>
<a id="941" href="Data.Sum.Base.html#798" class="Function Operator">[</a> <a id="943" href="Data.Sum.Base.html#943" class="Bound">f</a> <a id="945" href="Data.Sum.Base.html#798" class="Function Operator">,</a> <a id="947" href="Data.Sum.Base.html#947" class="Bound">g</a> <a id="949" href="Data.Sum.Base.html#798" class="Function Operator">]</a> <a id="951" class="Symbol">(</a><a id="952" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="957" href="Data.Sum.Base.html#957" class="Bound">y</a><a id="958" class="Symbol">)</a> <a id="960" class="Symbol">=</a> <a id="962" href="Data.Sum.Base.html#947" class="Bound">g</a> <a id="964" href="Data.Sum.Base.html#957" class="Bound">y</a>

<a id="[_,_]′"></a><a id="967" href="Data.Sum.Base.html#967" class="Function Operator">[_,_]′</a> <a id="974" class="Symbol">:</a> <a id="976" class="Symbol">(</a><a id="977" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="979" class="Symbol">→</a> <a id="981" href="Data.Sum.Base.html#480" class="Generalizable">C</a><a id="982" class="Symbol">)</a> <a id="984" class="Symbol">→</a> <a id="986" class="Symbol">(</a><a id="987" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="989" class="Symbol">→</a> <a id="991" href="Data.Sum.Base.html#480" class="Generalizable">C</a><a id="992" class="Symbol">)</a> <a id="994" class="Symbol">→</a> <a id="996" class="Symbol">(</a><a id="997" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="999" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1001" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1003" class="Symbol">→</a> <a id="1005" href="Data.Sum.Base.html#480" class="Generalizable">C</a><a id="1006" class="Symbol">)</a>
<a id="1008" href="Data.Sum.Base.html#967" class="Function Operator">[_,_]′</a> <a id="1015" class="Symbol">=</a> <a id="1017" href="Data.Sum.Base.html#798" class="Function Operator">[_,_]</a>

<a id="swap"></a><a id="1024" href="Data.Sum.Base.html#1024" class="Function">swap</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1033" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1035" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1037" class="Symbol">→</a> <a id="1039" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1041" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1043" href="Data.Sum.Base.html#452" class="Generalizable">A</a>
<a id="1045" href="Data.Sum.Base.html#1024" class="Function">swap</a> <a id="1050" class="Symbol">(</a><a id="1051" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="1056" href="Data.Sum.Base.html#1056" class="Bound">x</a><a id="1057" class="Symbol">)</a> <a id="1059" class="Symbol">=</a> <a id="1061" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="1066" href="Data.Sum.Base.html#1056" class="Bound">x</a>
<a id="1068" href="Data.Sum.Base.html#1024" class="Function">swap</a> <a id="1073" class="Symbol">(</a><a id="1074" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="1079" href="Data.Sum.Base.html#1079" class="Bound">x</a><a id="1080" class="Symbol">)</a> <a id="1082" class="Symbol">=</a> <a id="1084" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="1089" href="Data.Sum.Base.html#1079" class="Bound">x</a>

<a id="map"></a><a id="1092" href="Data.Sum.Base.html#1092" class="Function">map</a> <a id="1096" class="Symbol">:</a> <a id="1098" class="Symbol">(</a><a id="1099" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1101" class="Symbol">→</a> <a id="1103" href="Data.Sum.Base.html#480" class="Generalizable">C</a><a id="1104" class="Symbol">)</a> <a id="1106" class="Symbol">→</a> <a id="1108" class="Symbol">(</a><a id="1109" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1111" class="Symbol">→</a> <a id="1113" href="Data.Sum.Base.html#494" class="Generalizable">D</a><a id="1114" class="Symbol">)</a> <a id="1116" class="Symbol">→</a> <a id="1118" class="Symbol">(</a><a id="1119" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1121" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1123" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1125" class="Symbol">→</a> <a id="1127" href="Data.Sum.Base.html#480" class="Generalizable">C</a> <a id="1129" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1131" href="Data.Sum.Base.html#494" class="Generalizable">D</a><a id="1132" class="Symbol">)</a>
<a id="1134" href="Data.Sum.Base.html#1092" class="Function">map</a> <a id="1138" href="Data.Sum.Base.html#1138" class="Bound">f</a> <a id="1140" href="Data.Sum.Base.html#1140" class="Bound">g</a> <a id="1142" class="Symbol">=</a> <a id="1144" href="Data.Sum.Base.html#798" class="Function Operator">[</a> <a id="1146" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="1151" href="Function.html#1099" class="Function Operator">∘</a> <a id="1153" href="Data.Sum.Base.html#1138" class="Bound">f</a> <a id="1155" href="Data.Sum.Base.html#798" class="Function Operator">,</a> <a id="1157" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="1162" href="Function.html#1099" class="Function Operator">∘</a> <a id="1164" href="Data.Sum.Base.html#1140" class="Bound">g</a> <a id="1166" href="Data.Sum.Base.html#798" class="Function Operator">]</a>

<a id="map₁"></a><a id="1169" href="Data.Sum.Base.html#1169" class="Function">map₁</a> <a id="1174" class="Symbol">:</a> <a id="1176" class="Symbol">(</a><a id="1177" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1179" class="Symbol">→</a> <a id="1181" href="Data.Sum.Base.html#480" class="Generalizable">C</a><a id="1182" class="Symbol">)</a> <a id="1184" class="Symbol">→</a> <a id="1186" class="Symbol">(</a><a id="1187" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1189" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1191" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1193" class="Symbol">→</a> <a id="1195" href="Data.Sum.Base.html#480" class="Generalizable">C</a> <a id="1197" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1199" href="Data.Sum.Base.html#466" class="Generalizable">B</a><a id="1200" class="Symbol">)</a>
<a id="1202" href="Data.Sum.Base.html#1169" class="Function">map₁</a> <a id="1207" href="Data.Sum.Base.html#1207" class="Bound">f</a> <a id="1209" class="Symbol">=</a> <a id="1211" href="Data.Sum.Base.html#1092" class="Function">map</a> <a id="1215" href="Data.Sum.Base.html#1207" class="Bound">f</a> <a id="1217" href="Function.html#708" class="Function">id</a>

<a id="map₂"></a><a id="1221" href="Data.Sum.Base.html#1221" class="Function">map₂</a> <a id="1226" class="Symbol">:</a> <a id="1228" class="Symbol">(</a><a id="1229" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1231" class="Symbol">→</a> <a id="1233" href="Data.Sum.Base.html#494" class="Generalizable">D</a><a id="1234" class="Symbol">)</a> <a id="1236" class="Symbol">→</a> <a id="1238" class="Symbol">(</a><a id="1239" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1241" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1243" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1245" class="Symbol">→</a> <a id="1247" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1249" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1251" href="Data.Sum.Base.html#494" class="Generalizable">D</a><a id="1252" class="Symbol">)</a>
<a id="1254" href="Data.Sum.Base.html#1221" class="Function">map₂</a> <a id="1259" class="Symbol">=</a> <a id="1261" href="Data.Sum.Base.html#1092" class="Function">map</a> <a id="1265" href="Function.html#708" class="Function">id</a>

<a id="1269" class="Keyword">infixr</a> <a id="1276" class="Number">1</a> <a id="1278" href="Data.Sum.Base.html#1284" class="Function Operator">_-⊎-_</a>
<a id="_-⊎-_"></a><a id="1284" href="Data.Sum.Base.html#1284" class="Function Operator">_-⊎-_</a> <a id="1290" class="Symbol">:</a> <a id="1292" class="Symbol">(</a><a id="1293" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1295" class="Symbol">→</a> <a id="1297" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1299" class="Symbol">→</a> <a id="1301" class="PrimitiveType">Set</a> <a id="1305" href="Data.Sum.Base.html#436" class="Generalizable">c</a><a id="1306" class="Symbol">)</a> <a id="1308" class="Symbol">→</a> <a id="1310" class="Symbol">(</a><a id="1311" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1313" class="Symbol">→</a> <a id="1315" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1317" class="Symbol">→</a> <a id="1319" class="PrimitiveType">Set</a> <a id="1323" href="Data.Sum.Base.html#438" class="Generalizable">d</a><a id="1324" class="Symbol">)</a> <a id="1326" class="Symbol">→</a> <a id="1328" class="Symbol">(</a><a id="1329" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1331" class="Symbol">→</a> <a id="1333" href="Data.Sum.Base.html#466" class="Generalizable">B</a> <a id="1335" class="Symbol">→</a> <a id="1337" class="PrimitiveType">Set</a> <a id="1341" class="Symbol">(</a><a id="1342" href="Data.Sum.Base.html#436" class="Generalizable">c</a> <a id="1344" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1346" href="Data.Sum.Base.html#438" class="Generalizable">d</a><a id="1347" class="Symbol">))</a>
<a id="1350" href="Data.Sum.Base.html#1350" class="Bound">f</a> <a id="1352" href="Data.Sum.Base.html#1284" class="Function Operator">-⊎-</a> <a id="1356" href="Data.Sum.Base.html#1356" class="Bound">g</a> <a id="1358" class="Symbol">=</a> <a id="1360" href="Data.Sum.Base.html#1350" class="Bound">f</a> <a id="1362" href="Function.html#4171" class="Function Operator">-[</a> <a id="1365" href="Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a> <a id="1369" href="Function.html#4171" class="Function Operator">]-</a> <a id="1372" href="Data.Sum.Base.html#1356" class="Bound">g</a>

<a id="1375" class="Comment">-- Conversion back and forth with Dec</a>

<a id="fromDec"></a><a id="1414" href="Data.Sum.Base.html#1414" class="Function">fromDec</a> <a id="1422" class="Symbol">:</a> <a id="1424" href="Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="1428" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1430" class="Symbol">→</a> <a id="1432" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1434" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1436" href="Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="1438" href="Data.Sum.Base.html#452" class="Generalizable">A</a>
<a id="1440" href="Data.Sum.Base.html#1414" class="Function">fromDec</a> <a id="1448" class="Symbol">(</a><a id="1449" href="Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="1453" href="Data.Sum.Base.html#1453" class="Bound">p</a><a id="1454" class="Symbol">)</a> <a id="1456" class="Symbol">=</a> <a id="1458" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="1463" href="Data.Sum.Base.html#1453" class="Bound">p</a>
<a id="1465" href="Data.Sum.Base.html#1414" class="Function">fromDec</a> <a id="1473" class="Symbol">(</a><a id="1474" href="Relation.Nullary.html#668" class="InductiveConstructor">no</a> <a id="1477" href="Data.Sum.Base.html#1477" class="Bound">¬p</a><a id="1479" class="Symbol">)</a> <a id="1481" class="Symbol">=</a> <a id="1483" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="1488" href="Data.Sum.Base.html#1477" class="Bound">¬p</a>

<a id="toDec"></a><a id="1492" href="Data.Sum.Base.html#1492" class="Function">toDec</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1502" href="Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="1504" href="Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="1506" href="Data.Sum.Base.html#452" class="Generalizable">A</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="1514" href="Data.Sum.Base.html#452" class="Generalizable">A</a>
<a id="1516" href="Data.Sum.Base.html#1492" class="Function">toDec</a> <a id="1522" class="Symbol">(</a><a id="1523" href="Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="1528" href="Data.Sum.Base.html#1528" class="Bound">p</a><a id="1529" class="Symbol">)</a>  <a id="1532" class="Symbol">=</a> <a id="1534" href="Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="1538" href="Data.Sum.Base.html#1528" class="Bound">p</a>
<a id="1540" href="Data.Sum.Base.html#1492" class="Function">toDec</a> <a id="1546" class="Symbol">(</a><a id="1547" href="Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="1552" href="Data.Sum.Base.html#1552" class="Bound">¬p</a><a id="1554" class="Symbol">)</a> <a id="1556" class="Symbol">=</a> <a id="1558" href="Relation.Nullary.html#668" class="InductiveConstructor">no</a> <a id="1561" href="Data.Sum.Base.html#1552" class="Bound">¬p</a>
</pre>