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

We define the type of *operations*, as follows.

<pre class="Agda">

<a id="602" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="627" href="Algebras.Signatures.html#627" class="Function">Op</a> <a id="630" class="Symbol">:</a> <a id="632" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="634" href="Universes.html#403" class="Function Operator">̇</a> <a id="636" class="Symbol">→</a> <a id="638" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="640" href="Universes.html#403" class="Function Operator">̇</a> <a id="642" class="Symbol">→</a> <a id="644" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="646" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="648" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="650" href="Universes.html#403" class="Function Operator">̇</a>
<a id="652" href="Algebras.Signatures.html#627" class="Function">Op</a> <a id="655" href="Algebras.Signatures.html#655" class="Bound">I</a> <a id="657" href="Algebras.Signatures.html#657" class="Bound">A</a> <a id="659" class="Symbol">=</a> <a id="661" class="Symbol">(</a><a id="662" href="Algebras.Signatures.html#655" class="Bound">I</a> <a id="664" class="Symbol">→</a> <a id="666" href="Algebras.Signatures.html#657" class="Bound">A</a><a id="667" class="Symbol">)</a> <a id="669" class="Symbol">→</a> <a id="671" href="Algebras.Signatures.html#657" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

<pre class="Agda">

<a id="π"></a><a id="1041" href="Algebras.Signatures.html#1041" class="Function">π</a> <a id="1043" class="Symbol">:</a> <a id="1045" class="Symbol">{</a><a id="1046" href="Algebras.Signatures.html#1046" class="Bound">I</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="1052" href="Universes.html#403" class="Function Operator">̇</a> <a id="1054" class="Symbol">}</a> <a id="1056" class="Symbol">{</a><a id="1057" href="Algebras.Signatures.html#1057" class="Bound">A</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1063" href="Universes.html#403" class="Function Operator">̇</a> <a id="1065" class="Symbol">}</a> <a id="1067" class="Symbol">→</a> <a id="1069" href="Algebras.Signatures.html#1046" class="Bound">I</a> <a id="1071" class="Symbol">→</a> <a id="1073" href="Algebras.Signatures.html#627" class="Function">Op</a> <a id="1076" href="Algebras.Signatures.html#1046" class="Bound">I</a> <a id="1078" href="Algebras.Signatures.html#1057" class="Bound">A</a>
<a id="1080" href="Algebras.Signatures.html#1041" class="Function">π</a> <a id="1082" href="Algebras.Signatures.html#1082" class="Bound">i</a> <a id="1084" href="Algebras.Signatures.html#1084" class="Bound">x</a> <a id="1086" class="Symbol">=</a> <a id="1088" href="Algebras.Signatures.html#1084" class="Bound">x</a> <a id="1090" href="Algebras.Signatures.html#1082" class="Bound">i</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1239" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="1249" class="Symbol">:</a> <a id="1251" class="Symbol">(</a><a id="1252" href="Algebras.Signatures.html#1252" class="Bound">𝓞</a> <a id="1254" href="Algebras.Signatures.html#1254" class="Bound">𝓥</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1266" class="Symbol">)</a> <a id="1268" class="Symbol">→</a> <a id="1270" class="Symbol">(</a><a id="1271" href="Algebras.Signatures.html#1252" class="Bound">𝓞</a> <a id="1273" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1275" href="Algebras.Signatures.html#1254" class="Bound">𝓥</a><a id="1276" class="Symbol">)</a> <a id="1278" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1280" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1282" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="1292" href="Algebras.Signatures.html#1292" class="Bound">𝓞</a> <a id="1294" href="Algebras.Signatures.html#1294" class="Bound">𝓥</a> <a id="1296" class="Symbol">=</a> <a id="1298" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1300" href="Algebras.Signatures.html#1300" class="Bound">F</a> <a id="1302" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1304" href="Algebras.Signatures.html#1292" class="Bound">𝓞</a> <a id="1306" href="Universes.html#403" class="Function Operator">̇</a> <a id="1308" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1310" class="Symbol">(</a><a id="1311" href="Algebras.Signatures.html#1300" class="Bound">F</a> <a id="1313" class="Symbol">→</a> <a id="1315" href="Algebras.Signatures.html#1294" class="Bound">𝓥</a> <a id="1317" href="Universes.html#403" class="Function Operator">̇</a><a id="1318" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1988" class="Keyword">data</a> <a id="monoid-op"></a><a id="1993" href="Algebras.Signatures.html#1993" class="Datatype">monoid-op</a> <a id="2003" class="Symbol">{</a><a id="2004" href="Algebras.Signatures.html#2004" class="Bound">𝓞</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2016" class="Symbol">}</a> <a id="2018" class="Symbol">:</a> <a id="2020" href="Algebras.Signatures.html#2004" class="Bound">𝓞</a> <a id="2022" href="Universes.html#403" class="Function Operator">̇</a> <a id="2024" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2031" href="Algebras.Signatures.html#2031" class="InductiveConstructor">e</a> <a id="2033" class="Symbol">:</a> <a id="2035" href="Algebras.Signatures.html#1993" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2046" href="Algebras.Signatures.html#2046" class="InductiveConstructor">·</a> <a id="2048" class="Symbol">:</a> <a id="2050" href="Algebras.Signatures.html#1993" class="Datatype">monoid-op</a>

<a id="2061" class="Keyword">open</a> <a id="2066" class="Keyword">import</a> <a id="2073" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2082" class="Keyword">using</a> <a id="2088" class="Symbol">(</a><a id="2089" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2090" class="Symbol">;</a> <a id="2092" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2093" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="2096" href="Algebras.Signatures.html#2096" class="Function">monoid-sig</a> <a id="2107" class="Symbol">:</a> <a id="2109" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="2119" href="Overture.Preliminaries.html#6850" class="Generalizable">𝓞</a> <a id="2121" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="2124" href="Algebras.Signatures.html#2096" class="Function">monoid-sig</a> <a id="2135" class="Symbol">=</a> <a id="2137" href="Algebras.Signatures.html#1993" class="Datatype">monoid-op</a> <a id="2147" href="Overture.Preliminaries.html#11706" class="InductiveConstructor Operator">,</a> <a id="2149" class="Symbol">λ</a> <a id="2151" class="Symbol">{</a> <a id="2153" href="Algebras.Signatures.html#2031" class="InductiveConstructor">e</a> <a id="2155" class="Symbol">→</a> <a id="2157" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2158" class="Symbol">;</a> <a id="2160" href="Algebras.Signatures.html#2046" class="InductiveConstructor">·</a> <a id="2162" class="Symbol">→</a> <a id="2164" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2166" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

