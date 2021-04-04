---
layout: default
title : Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="operations-and-signatures">Operations and Signatures</a>

This section presents the [Algebras.Signatures][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="318" class="Symbol">{-#</a> <a id="322" class="Keyword">OPTIONS</a> <a id="330" class="Pragma">--without-K</a> <a id="342" class="Pragma">--exact-split</a> <a id="356" class="Pragma">--safe</a> <a id="363" class="Symbol">#-}</a>

<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="Universes.html" class="Module">Universes</a> <a id="390" class="Keyword">using</a> <a id="396" class="Symbol">(</a><a id="397" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a><a id="399" class="Symbol">)</a>

<a id="402" class="Keyword">module</a> <a id="409" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="429" class="Keyword">where</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="469" class="Keyword">public</a>

</pre>



#### <a id="operation-type">Operation type</a>

We define the type of *operations* as follows.

<pre class="Agda">

<a id="601" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="626" href="Algebras.Signatures.html#626" class="Function">Op</a> <a id="629" class="Symbol">:</a> <a id="631" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="633" href="Universes.html#403" class="Function Operator">̇</a> <a id="635" class="Symbol">→</a> <a id="637" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="639" href="Universes.html#403" class="Function Operator">̇</a> <a id="641" class="Symbol">→</a> <a id="643" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="645" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="647" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="649" href="Universes.html#403" class="Function Operator">̇</a>
<a id="651" href="Algebras.Signatures.html#626" class="Function">Op</a> <a id="654" href="Algebras.Signatures.html#654" class="Bound">I</a> <a id="656" href="Algebras.Signatures.html#656" class="Bound">A</a> <a id="658" class="Symbol">=</a> <a id="660" class="Symbol">(</a><a id="661" href="Algebras.Signatures.html#654" class="Bound">I</a> <a id="663" class="Symbol">→</a> <a id="665" href="Algebras.Signatures.html#656" class="Bound">A</a><a id="666" class="Symbol">)</a> <a id="668" class="Symbol">→</a> <a id="670" href="Algebras.Signatures.html#656" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

<pre class="Agda">

<a id="π"></a><a id="1040" href="Algebras.Signatures.html#1040" class="Function">π</a> <a id="1042" class="Symbol">:</a> <a id="1044" class="Symbol">{</a><a id="1045" href="Algebras.Signatures.html#1045" class="Bound">I</a> <a id="1047" class="Symbol">:</a> <a id="1049" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="1051" href="Universes.html#403" class="Function Operator">̇</a> <a id="1053" class="Symbol">}</a> <a id="1055" class="Symbol">{</a><a id="1056" href="Algebras.Signatures.html#1056" class="Bound">A</a> <a id="1058" class="Symbol">:</a> <a id="1060" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1062" href="Universes.html#403" class="Function Operator">̇</a> <a id="1064" class="Symbol">}</a> <a id="1066" class="Symbol">→</a> <a id="1068" href="Algebras.Signatures.html#1045" class="Bound">I</a> <a id="1070" class="Symbol">→</a> <a id="1072" href="Algebras.Signatures.html#626" class="Function">Op</a> <a id="1075" href="Algebras.Signatures.html#1045" class="Bound">I</a> <a id="1077" href="Algebras.Signatures.html#1056" class="Bound">A</a>
<a id="1079" href="Algebras.Signatures.html#1040" class="Function">π</a> <a id="1081" href="Algebras.Signatures.html#1081" class="Bound">i</a> <a id="1083" href="Algebras.Signatures.html#1083" class="Bound">x</a> <a id="1085" class="Symbol">=</a> <a id="1087" href="Algebras.Signatures.html#1083" class="Bound">x</a> <a id="1089" href="Algebras.Signatures.html#1081" class="Bound">i</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1238" href="Algebras.Signatures.html#1238" class="Function">Signature</a> <a id="1248" class="Symbol">:</a> <a id="1250" class="Symbol">(</a><a id="1251" href="Algebras.Signatures.html#1251" class="Bound">𝓞</a> <a id="1253" href="Algebras.Signatures.html#1253" class="Bound">𝓥</a> <a id="1255" class="Symbol">:</a> <a id="1257" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1265" class="Symbol">)</a> <a id="1267" class="Symbol">→</a> <a id="1269" class="Symbol">(</a><a id="1270" href="Algebras.Signatures.html#1251" class="Bound">𝓞</a> <a id="1272" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1274" href="Algebras.Signatures.html#1253" class="Bound">𝓥</a><a id="1275" class="Symbol">)</a> <a id="1277" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1279" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1281" href="Algebras.Signatures.html#1238" class="Function">Signature</a> <a id="1291" href="Algebras.Signatures.html#1291" class="Bound">𝓞</a> <a id="1293" href="Algebras.Signatures.html#1293" class="Bound">𝓥</a> <a id="1295" class="Symbol">=</a> <a id="1297" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1299" href="Algebras.Signatures.html#1299" class="Bound">F</a> <a id="1301" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1303" href="Algebras.Signatures.html#1291" class="Bound">𝓞</a> <a id="1305" href="Universes.html#403" class="Function Operator">̇</a> <a id="1307" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1309" class="Symbol">(</a><a id="1310" href="Algebras.Signatures.html#1299" class="Bound">F</a> <a id="1312" class="Symbol">→</a> <a id="1314" href="Algebras.Signatures.html#1293" class="Bound">𝓥</a> <a id="1316" href="Universes.html#403" class="Function Operator">̇</a><a id="1317" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1987" class="Keyword">data</a> <a id="monoid-op"></a><a id="1992" href="Algebras.Signatures.html#1992" class="Datatype">monoid-op</a> <a id="2002" class="Symbol">{</a><a id="2003" href="Algebras.Signatures.html#2003" class="Bound">𝓞</a> <a id="2005" class="Symbol">:</a> <a id="2007" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2015" class="Symbol">}</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="Algebras.Signatures.html#2003" class="Bound">𝓞</a> <a id="2021" href="Universes.html#403" class="Function Operator">̇</a> <a id="2023" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2030" href="Algebras.Signatures.html#2030" class="InductiveConstructor">e</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Algebras.Signatures.html#1992" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2045" href="Algebras.Signatures.html#2045" class="InductiveConstructor">·</a> <a id="2047" class="Symbol">:</a> <a id="2049" href="Algebras.Signatures.html#1992" class="Datatype">monoid-op</a>

<a id="2060" class="Keyword">open</a> <a id="2065" class="Keyword">import</a> <a id="2072" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2081" class="Keyword">using</a> <a id="2087" class="Symbol">(</a><a id="2088" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2089" class="Symbol">;</a> <a id="2091" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2092" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="2095" href="Algebras.Signatures.html#2095" class="Function">monoid-sig</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="Algebras.Signatures.html#1238" class="Function">Signature</a> <a id="2118" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="2120" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="2123" href="Algebras.Signatures.html#2095" class="Function">monoid-sig</a> <a id="2134" class="Symbol">=</a> <a id="2136" href="Algebras.Signatures.html#1992" class="Datatype">monoid-op</a> <a id="2146" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="2148" class="Symbol">λ</a> <a id="2150" class="Symbol">{</a> <a id="2152" href="Algebras.Signatures.html#2030" class="InductiveConstructor">e</a> <a id="2154" class="Symbol">→</a> <a id="2156" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2157" class="Symbol">;</a> <a id="2159" href="Algebras.Signatures.html#2045" class="InductiveConstructor">·</a> <a id="2161" class="Symbol">→</a> <a id="2163" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2165" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

