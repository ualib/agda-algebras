---
layout: default
title : UALib.Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic definitions</a>

This section presents the [UALib.Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="302" class="Symbol">{-#</a> <a id="306" class="Keyword">OPTIONS</a> <a id="314" class="Pragma">--without-K</a> <a id="326" class="Pragma">--exact-split</a> <a id="340" class="Pragma">--safe</a> <a id="347" class="Symbol">#-}</a>

<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="UALib.Algebras.html" class="Module">UALib.Algebras</a> <a id="379" class="Keyword">using</a> <a id="385" class="Symbol">(</a><a id="386" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a><a id="395" class="Symbol">;</a> <a id="397" href="universes.html#613" class="Generalizable">𝓞</a><a id="398" class="Symbol">;</a> <a id="400" href="universes.html#617" class="Generalizable">𝓥</a><a id="401" class="Symbol">;</a> <a id="403" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a><a id="410" class="Symbol">;</a> <a id="412" href="UALib.Algebras.Algebras.html#3925" class="Function Operator">_↠_</a><a id="415" class="Symbol">)</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="457" class="Keyword">using</a> <a id="463" class="Symbol">(</a><a id="464" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="478" class="Symbol">;</a> <a id="480" href="universes.html#551" class="Postulate">Universe</a><a id="488" class="Symbol">;</a> <a id="490" href="universes.html#758" class="Function Operator">_̇</a><a id="492" class="Symbol">)</a>


<a id="496" class="Keyword">module</a> <a id="503" href="UALib.Terms.Basic.html" class="Module">UALib.Terms.Basic</a>
 <a id="522" class="Symbol">{</a><a id="523" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="525" class="Symbol">:</a> <a id="527" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="537" href="universes.html#613" class="Generalizable">𝓞</a> <a id="539" href="universes.html#617" class="Generalizable">𝓥</a><a id="540" class="Symbol">}{</a><a id="542" href="UALib.Terms.Basic.html#542" class="Bound">gfe</a> <a id="546" class="Symbol">:</a> <a id="548" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="562" class="Symbol">}</a>
 <a id="565" class="Symbol">{</a><a id="566" href="UALib.Terms.Basic.html#566" class="Bound">𝕏</a> <a id="568" class="Symbol">:</a> <a id="570" class="Symbol">{</a><a id="571" href="UALib.Terms.Basic.html#571" class="Bound">𝓤</a> <a id="573" href="UALib.Terms.Basic.html#573" class="Bound">𝓧</a> <a id="575" class="Symbol">:</a> <a id="577" href="universes.html#551" class="Postulate">Universe</a><a id="585" class="Symbol">}{</a><a id="587" href="UALib.Terms.Basic.html#587" class="Bound">X</a> <a id="589" class="Symbol">:</a> <a id="591" href="UALib.Terms.Basic.html#573" class="Bound">𝓧</a> <a id="593" href="universes.html#758" class="Function Operator">̇</a> <a id="595" class="Symbol">}(</a><a id="597" href="UALib.Terms.Basic.html#597" class="Bound">𝑨</a> <a id="599" class="Symbol">:</a> <a id="601" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="609" href="UALib.Terms.Basic.html#571" class="Bound">𝓤</a> <a id="611" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a><a id="612" class="Symbol">)</a> <a id="614" class="Symbol">→</a> <a id="616" href="UALib.Terms.Basic.html#587" class="Bound">X</a> <a id="618" href="UALib.Algebras.Algebras.html#3925" class="Function Operator">↠</a> <a id="620" href="UALib.Terms.Basic.html#597" class="Bound">𝑨</a><a id="621" class="Symbol">}</a>
 <a id="624" class="Keyword">where</a>


<a id="632" class="Keyword">open</a> <a id="637" class="Keyword">import</a> <a id="644" href="UALib.Homomorphisms.HomomorphicImages.html" class="Module">UALib.Homomorphisms.HomomorphicImages</a><a id="681" class="Symbol">{</a><a id="682" class="Argument">𝑆</a> <a id="684" class="Symbol">=</a> <a id="686" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a><a id="687" class="Symbol">}{</a><a id="689" href="UALib.Terms.Basic.html#542" class="Bound">gfe</a><a id="692" class="Symbol">}</a> <a id="694" class="Keyword">hiding</a> <a id="701" class="Symbol">(</a>Universe<a id="710" class="Symbol">;</a> _̇<a id="714" class="Symbol">)</a> <a id="716" class="Keyword">public</a>

</pre>

-----------------------------------------------

#### <a id="the-inductive-type-of-terms">The inductive type of terms</a>

We define a type called `Term` which, not surprisingly, represents the type of terms. The type `X : 𝓧 ̇` represents an arbitrary collection of variable symbols.

<pre class="Agda">

<a id="1035" class="Keyword">data</a> <a id="Term"></a><a id="1040" href="UALib.Terms.Basic.html#1040" class="Datatype">Term</a> <a id="1045" class="Symbol">{</a><a id="1046" href="UALib.Terms.Basic.html#1046" class="Bound">𝓧</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="universes.html#551" class="Postulate">Universe</a><a id="1058" class="Symbol">}{</a><a id="1060" href="UALib.Terms.Basic.html#1060" class="Bound">X</a> <a id="1062" class="Symbol">:</a> <a id="1064" href="UALib.Terms.Basic.html#1046" class="Bound">𝓧</a> <a id="1066" href="universes.html#758" class="Function Operator">̇</a><a id="1067" class="Symbol">}</a> <a id="1069" class="Symbol">:</a> <a id="1071" href="UALib.Terms.Basic.html#537" class="Bound">𝓞</a> <a id="1073" href="Agda.Primitive.html#636" class="Function Operator">⊔</a> <a id="1075" href="UALib.Terms.Basic.html#539" class="Bound">𝓥</a> <a id="1077" href="Agda.Primitive.html#636" class="Function Operator">⊔</a> <a id="1079" href="UALib.Terms.Basic.html#1046" class="Bound">𝓧</a> <a id="1081" href="universes.html#527" class="Function Operator">⁺</a> <a id="1083" href="universes.html#758" class="Function Operator">̇</a>  <a id="1086" class="Keyword">where</a>
  <a id="Term.generator"></a><a id="1094" href="UALib.Terms.Basic.html#1094" class="InductiveConstructor">generator</a> <a id="1104" class="Symbol">:</a> <a id="1106" href="UALib.Terms.Basic.html#1060" class="Bound">X</a> <a id="1108" class="Symbol">→</a> <a id="1110" href="UALib.Terms.Basic.html#1040" class="Datatype">Term</a><a id="1114" class="Symbol">{</a><a id="1115" href="UALib.Terms.Basic.html#1046" class="Bound">𝓧</a><a id="1116" class="Symbol">}{</a><a id="1118" href="UALib.Terms.Basic.html#1060" class="Bound">X</a><a id="1119" class="Symbol">}</a>
  <a id="Term.node"></a><a id="1123" href="UALib.Terms.Basic.html#1123" class="InductiveConstructor">node</a> <a id="1128" class="Symbol">:</a> <a id="1130" class="Symbol">(</a><a id="1131" href="UALib.Terms.Basic.html#1131" class="Bound">f</a> <a id="1133" class="Symbol">:</a> <a id="1135" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="1137" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="1139" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="1140" class="Symbol">)(</a><a id="1142" href="UALib.Terms.Basic.html#1142" class="Bound">args</a> <a id="1147" class="Symbol">:</a> <a id="1149" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="1151" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="1153" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="1155" href="UALib.Terms.Basic.html#1131" class="Bound">f</a> <a id="1157" class="Symbol">→</a> <a id="1159" href="UALib.Terms.Basic.html#1040" class="Datatype">Term</a><a id="1163" class="Symbol">{</a><a id="1164" href="UALib.Terms.Basic.html#1046" class="Bound">𝓧</a><a id="1165" class="Symbol">}{</a><a id="1167" href="UALib.Terms.Basic.html#1060" class="Bound">X</a><a id="1168" class="Symbol">})</a> <a id="1171" class="Symbol">→</a> <a id="1173" href="UALib.Terms.Basic.html#1040" class="Datatype">Term</a>

<a id="1179" class="Keyword">open</a> <a id="1184" href="UALib.Terms.Basic.html#1040" class="Module">Term</a>

</pre>

--------------------------------------

[↑ UALib.Terms](UALib.Terms.html)
<span style="float:right;">[UALib.Terms.Free →](UALib.Terms.Free.html)</span>

{% include UALib.Links.md %}
