---
layout: default
title : UALib.Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="operations-and-signatures">Operations and Signatures</a>

This section presents the [UALib.Algebras.Signatures][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="330" class="Symbol">{-#</a> <a id="334" class="Keyword">OPTIONS</a> <a id="342" class="Pragma">--without-K</a> <a id="354" class="Pragma">--exact-split</a> <a id="368" class="Pragma">--safe</a> <a id="375" class="Symbol">#-}</a>

<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="Universes.html" class="Module">Universes</a> <a id="402" class="Keyword">using</a> <a id="408" class="Symbol">(</a><a id="409" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a><a id="411" class="Symbol">)</a>

<a id="414" class="Keyword">module</a> <a id="421" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="441" class="Keyword">where</a>

<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="481" class="Keyword">public</a>

</pre>



#### <a id="operation-type">Operation type</a>

We define the type of *operations*, as follows.

<pre class="Agda">

<a id="614" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="639" href="Algebras.Signatures.html#639" class="Function">Op</a> <a id="642" class="Symbol">:</a> <a id="644" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="646" href="Universes.html#403" class="Function Operator">̇</a> <a id="648" class="Symbol">→</a> <a id="650" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="652" href="Universes.html#403" class="Function Operator">̇</a> <a id="654" class="Symbol">→</a> <a id="656" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="658" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="660" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="662" href="Universes.html#403" class="Function Operator">̇</a>
<a id="664" href="Algebras.Signatures.html#639" class="Function">Op</a> <a id="667" href="Algebras.Signatures.html#667" class="Bound">I</a> <a id="669" href="Algebras.Signatures.html#669" class="Bound">A</a> <a id="671" class="Symbol">=</a> <a id="673" class="Symbol">(</a><a id="674" href="Algebras.Signatures.html#667" class="Bound">I</a> <a id="676" class="Symbol">→</a> <a id="678" href="Algebras.Signatures.html#669" class="Bound">A</a><a id="679" class="Symbol">)</a> <a id="681" class="Symbol">→</a> <a id="683" href="Algebras.Signatures.html#669" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

<pre class="Agda">

<a id="π"></a><a id="1053" href="Algebras.Signatures.html#1053" class="Function">π</a> <a id="1055" class="Symbol">:</a> <a id="1057" class="Symbol">{</a><a id="1058" href="Algebras.Signatures.html#1058" class="Bound">I</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="1064" href="Universes.html#403" class="Function Operator">̇</a> <a id="1066" class="Symbol">}</a> <a id="1068" class="Symbol">{</a><a id="1069" href="Algebras.Signatures.html#1069" class="Bound">A</a> <a id="1071" class="Symbol">:</a> <a id="1073" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1075" href="Universes.html#403" class="Function Operator">̇</a> <a id="1077" class="Symbol">}</a> <a id="1079" class="Symbol">→</a> <a id="1081" href="Algebras.Signatures.html#1058" class="Bound">I</a> <a id="1083" class="Symbol">→</a> <a id="1085" href="Algebras.Signatures.html#639" class="Function">Op</a> <a id="1088" href="Algebras.Signatures.html#1058" class="Bound">I</a> <a id="1090" href="Algebras.Signatures.html#1069" class="Bound">A</a>
<a id="1092" href="Algebras.Signatures.html#1053" class="Function">π</a> <a id="1094" href="Algebras.Signatures.html#1094" class="Bound">i</a> <a id="1096" href="Algebras.Signatures.html#1096" class="Bound">x</a> <a id="1098" class="Symbol">=</a> <a id="1100" href="Algebras.Signatures.html#1096" class="Bound">x</a> <a id="1102" href="Algebras.Signatures.html#1094" class="Bound">i</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1251" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="1261" class="Symbol">:</a> <a id="1263" class="Symbol">(</a><a id="1264" href="Algebras.Signatures.html#1264" class="Bound">𝓞</a> <a id="1266" href="Algebras.Signatures.html#1266" class="Bound">𝓥</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1278" class="Symbol">)</a> <a id="1280" class="Symbol">→</a> <a id="1282" class="Symbol">(</a><a id="1283" href="Algebras.Signatures.html#1264" class="Bound">𝓞</a> <a id="1285" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1287" href="Algebras.Signatures.html#1266" class="Bound">𝓥</a><a id="1288" class="Symbol">)</a> <a id="1290" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1292" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1294" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="1304" href="Algebras.Signatures.html#1304" class="Bound">𝓞</a> <a id="1306" href="Algebras.Signatures.html#1306" class="Bound">𝓥</a> <a id="1308" class="Symbol">=</a> <a id="1310" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1312" href="Algebras.Signatures.html#1312" class="Bound">F</a> <a id="1314" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1316" href="Algebras.Signatures.html#1304" class="Bound">𝓞</a> <a id="1318" href="Universes.html#403" class="Function Operator">̇</a> <a id="1320" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1322" class="Symbol">(</a><a id="1323" href="Algebras.Signatures.html#1312" class="Bound">F</a> <a id="1325" class="Symbol">→</a> <a id="1327" href="Algebras.Signatures.html#1306" class="Bound">𝓥</a> <a id="1329" href="Universes.html#403" class="Function Operator">̇</a><a id="1330" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1999" class="Keyword">data</a> <a id="monoid-op"></a><a id="2004" href="Algebras.Signatures.html#2004" class="Datatype">monoid-op</a> <a id="2014" class="Symbol">{</a><a id="2015" href="Algebras.Signatures.html#2015" class="Bound">𝓞</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2027" class="Symbol">}</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="Algebras.Signatures.html#2015" class="Bound">𝓞</a> <a id="2033" href="Universes.html#403" class="Function Operator">̇</a> <a id="2035" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2042" href="Algebras.Signatures.html#2042" class="InductiveConstructor">e</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="Algebras.Signatures.html#2004" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2057" href="Algebras.Signatures.html#2057" class="InductiveConstructor">·</a> <a id="2059" class="Symbol">:</a> <a id="2061" href="Algebras.Signatures.html#2004" class="Datatype">monoid-op</a>

<a id="2072" class="Keyword">open</a> <a id="2077" class="Keyword">import</a> <a id="2084" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2093" class="Keyword">using</a> <a id="2099" class="Symbol">(</a><a id="2100" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2101" class="Symbol">;</a> <a id="2103" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2104" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="2107" href="Algebras.Signatures.html#2107" class="Function">monoid-sig</a> <a id="2118" class="Symbol">:</a> <a id="2120" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="2130" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="2132" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="2135" href="Algebras.Signatures.html#2107" class="Function">monoid-sig</a> <a id="2146" class="Symbol">=</a> <a id="2148" href="Algebras.Signatures.html#2004" class="Datatype">monoid-op</a> <a id="2158" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="2160" class="Symbol">λ</a> <a id="2162" class="Symbol">{</a> <a id="2164" href="Algebras.Signatures.html#2042" class="InductiveConstructor">e</a> <a id="2166" class="Symbol">→</a> <a id="2168" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2169" class="Symbol">;</a> <a id="2171" href="Algebras.Signatures.html#2057" class="InductiveConstructor">·</a> <a id="2173" class="Symbol">→</a> <a id="2175" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2177" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

