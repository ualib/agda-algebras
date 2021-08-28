---
layout: default
title : Structures.Terms.Operations
date : 2021-07-23
author: [agda-algebras development team][]
---

When we interpret a term in a structure we call the resulting
function a *term operation*. Given a term `p` and a structure `𝑨`,
we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.
This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and
   if `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then
   define `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = f t`, where `f : ∣ 𝑆 ∣` is an operation symbol,
   if `t : (arity 𝐹) f → 𝑻 X` is a tuple of terms, and
   if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then
   define `𝑨 ⟦ p ⟧ a := (f ᵒ 𝑨) (λ i → 𝑨 ⟦ t i ⟧ a)`.

Thus interpretation of a term is defined by structural induction.

<pre class="Agda">

<a id="786" class="Symbol">{-#</a> <a id="790" class="Keyword">OPTIONS</a> <a id="798" class="Pragma">--without-K</a> <a id="810" class="Pragma">--exact-split</a> <a id="824" class="Pragma">--safe</a> <a id="831" class="Symbol">#-}</a>

<a id="836" class="Keyword">module</a> <a id="843" href="Structures.Terms.Operations.html" class="Module">Structures.Terms.Operations</a> <a id="871" class="Keyword">where</a>

<a id="878" class="Keyword">open</a> <a id="883" class="Keyword">import</a> <a id="890" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="908" class="Keyword">using</a> <a id="914" class="Symbol">(</a> <a id="916" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="921" class="Symbol">;</a> <a id="923" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="927" class="Symbol">;</a> <a id="929" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="935" class="Symbol">)</a> <a id="937" class="Keyword">renaming</a> <a id="946" class="Symbol">(</a> <a id="948" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="952" class="Symbol">to</a> <a id="955" class="Primitive">Type</a> <a id="960" class="Symbol">)</a>
<a id="962" class="Keyword">open</a> <a id="967" class="Keyword">import</a> <a id="974" href="Structures.Basic.html" class="Module">Structures.Basic</a>  <a id="992" class="Keyword">using</a> <a id="998" class="Symbol">(</a> <a id="1000" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="1010" class="Symbol">;</a> <a id="1012" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1022" class="Symbol">;</a> <a id="1024" href="Structures.Basic.html#2090" class="Function Operator">_ᵒ_</a> <a id="1028" class="Symbol">)</a>
<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="Structures.Terms.Basic.html" class="Module">Structures.Terms.Basic</a>


<a id="1067" class="Keyword">private</a> <a id="1075" class="Keyword">variable</a>
 <a id="1085" href="Structures.Terms.Operations.html#1085" class="Generalizable">𝓞₀</a> <a id="1088" href="Structures.Terms.Operations.html#1088" class="Generalizable">𝓥₀</a> <a id="1091" href="Structures.Terms.Operations.html#1091" class="Generalizable">𝓞₁</a> <a id="1094" href="Structures.Terms.Operations.html#1094" class="Generalizable">𝓥₁</a> <a id="1097" href="Structures.Terms.Operations.html#1097" class="Generalizable">χ</a> <a id="1099" href="Structures.Terms.Operations.html#1099" class="Generalizable">α</a> <a id="1101" href="Structures.Terms.Operations.html#1101" class="Generalizable">ρ</a> <a id="1103" class="Symbol">:</a> <a id="1105" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="1112" href="Structures.Terms.Operations.html#1112" class="Generalizable">𝐹</a> <a id="1114" class="Symbol">:</a> <a id="1116" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="1126" href="Structures.Terms.Operations.html#1085" class="Generalizable">𝓞₀</a> <a id="1129" href="Structures.Terms.Operations.html#1088" class="Generalizable">𝓥₀</a>
 <a id="1133" href="Structures.Terms.Operations.html#1133" class="Generalizable">𝑅</a> <a id="1135" class="Symbol">:</a> <a id="1137" href="Structures.Basic.html#1124" class="Record">signature</a> <a id="1147" href="Structures.Terms.Operations.html#1091" class="Generalizable">𝓞₁</a> <a id="1150" href="Structures.Terms.Operations.html#1094" class="Generalizable">𝓥₁</a>
 <a id="1154" href="Structures.Terms.Operations.html#1154" class="Generalizable">X</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="Structures.Terms.Operations.html#955" class="Primitive">Type</a> <a id="1163" href="Structures.Terms.Operations.html#1097" class="Generalizable">χ</a>

<a id="1166" class="Keyword">open</a> <a id="1171" href="Structures.Basic.html#1124" class="Module">signature</a>
<a id="1181" class="Keyword">open</a> <a id="1186" href="Structures.Basic.html#1458" class="Module">structure</a>

<a id="_⟦_⟧"></a><a id="1197" href="Structures.Terms.Operations.html#1197" class="Function Operator">_⟦_⟧</a> <a id="1202" class="Symbol">:</a> <a id="1204" class="Symbol">(</a><a id="1205" href="Structures.Terms.Operations.html#1205" class="Bound">𝑨</a> <a id="1207" class="Symbol">:</a> <a id="1209" href="Structures.Basic.html#1458" class="Record">structure</a> <a id="1219" href="Structures.Terms.Operations.html#1112" class="Generalizable">𝐹</a> <a id="1221" href="Structures.Terms.Operations.html#1133" class="Generalizable">𝑅</a> <a id="1223" class="Symbol">{</a><a id="1224" href="Structures.Terms.Operations.html#1099" class="Generalizable">α</a><a id="1225" class="Symbol">}</a> <a id="1227" class="Symbol">{</a><a id="1228" href="Structures.Terms.Operations.html#1101" class="Generalizable">ρ</a><a id="1229" class="Symbol">})</a> <a id="1232" class="Symbol">→</a> <a id="1234" href="Structures.Terms.Basic.html#443" class="Datatype">Term</a> <a id="1239" href="Structures.Terms.Operations.html#1154" class="Generalizable">X</a> <a id="1241" class="Symbol">→</a> <a id="1243" class="Symbol">(</a><a id="1244" href="Structures.Terms.Operations.html#1154" class="Generalizable">X</a> <a id="1246" class="Symbol">→</a> <a id="1248" href="Structures.Basic.html#1610" class="Field">carrier</a> <a id="1256" href="Structures.Terms.Operations.html#1205" class="Bound">𝑨</a><a id="1257" class="Symbol">)</a> <a id="1259" class="Symbol">→</a> <a id="1261" href="Structures.Basic.html#1610" class="Field">carrier</a> <a id="1269" href="Structures.Terms.Operations.html#1205" class="Bound">𝑨</a>
<a id="1271" href="Structures.Terms.Operations.html#1271" class="Bound">𝑨</a> <a id="1273" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟦</a> <a id="1275" href="Structures.Terms.Basic.html#509" class="InductiveConstructor">ℊ</a> <a id="1277" href="Structures.Terms.Operations.html#1277" class="Bound">x</a> <a id="1279" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟧</a> <a id="1281" class="Symbol">=</a> <a id="1283" class="Symbol">λ</a> <a id="1285" href="Structures.Terms.Operations.html#1285" class="Bound">a</a> <a id="1287" class="Symbol">→</a> <a id="1289" href="Structures.Terms.Operations.html#1285" class="Bound">a</a> <a id="1291" href="Structures.Terms.Operations.html#1277" class="Bound">x</a>
<a id="1293" href="Structures.Terms.Operations.html#1293" class="Bound">𝑨</a> <a id="1295" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟦</a> <a id="1297" href="Structures.Terms.Basic.html#551" class="InductiveConstructor">node</a> <a id="1302" href="Structures.Terms.Operations.html#1302" class="Bound">f</a> <a id="1304" href="Structures.Terms.Operations.html#1304" class="Bound">t</a> <a id="1306" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟧</a> <a id="1308" class="Symbol">=</a> <a id="1310" class="Symbol">λ</a> <a id="1312" href="Structures.Terms.Operations.html#1312" class="Bound">a</a> <a id="1314" class="Symbol">→</a> <a id="1316" class="Symbol">(</a><a id="1317" href="Structures.Terms.Operations.html#1302" class="Bound">f</a> <a id="1319" href="Structures.Basic.html#2090" class="Function Operator">ᵒ</a> <a id="1321" href="Structures.Terms.Operations.html#1293" class="Bound">𝑨</a><a id="1322" class="Symbol">)</a> <a id="1324" class="Symbol">(λ</a> <a id="1327" href="Structures.Terms.Operations.html#1327" class="Bound">i</a> <a id="1329" class="Symbol">→</a> <a id="1331" class="Symbol">(</a><a id="1332" href="Structures.Terms.Operations.html#1293" class="Bound">𝑨</a> <a id="1334" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟦</a> <a id="1336" href="Structures.Terms.Operations.html#1304" class="Bound">t</a> <a id="1338" href="Structures.Terms.Operations.html#1327" class="Bound">i</a> <a id="1340" href="Structures.Terms.Operations.html#1197" class="Function Operator">⟧</a> <a id="1342" class="Symbol">)</a> <a id="1344" href="Structures.Terms.Operations.html#1312" class="Bound">a</a><a id="1345" class="Symbol">)</a>

</pre>

--------------------------------

<br>
<br>

[← Structures.Terms.Basic](Structures.Terms.Basic.html)
<span style="float:right;">[Structures.Substructures →](Structures.Substructures.html)</span>

{% include UALib.Links.md %}