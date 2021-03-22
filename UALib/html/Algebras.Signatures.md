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

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="643" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="668" href="Algebras.Signatures.html#668" class="Function">Op</a> <a id="671" class="Symbol">:</a> <a id="673" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="675" href="Universes.html#403" class="Function Operator">̇</a> <a id="677" class="Symbol">→</a> <a id="679" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="681" href="Universes.html#403" class="Function Operator">̇</a> <a id="683" class="Symbol">→</a> <a id="685" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="687" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="689" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="691" href="Universes.html#403" class="Function Operator">̇</a>
<a id="693" href="Algebras.Signatures.html#668" class="Function">Op</a> <a id="696" href="Algebras.Signatures.html#696" class="Bound">I</a> <a id="698" href="Algebras.Signatures.html#698" class="Bound">A</a> <a id="700" class="Symbol">=</a> <a id="702" class="Symbol">(</a><a id="703" href="Algebras.Signatures.html#696" class="Bound">I</a> <a id="705" class="Symbol">→</a> <a id="707" href="Algebras.Signatures.html#698" class="Bound">A</a><a id="708" class="Symbol">)</a> <a id="710" class="Symbol">→</a> <a id="712" href="Algebras.Signatures.html#698" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.



For example, the `i`-th `I`-ary projection operation on `A` is represented for all `i : I` as follows.

<pre class="Agda">

<a id="π"></a><a id="1068" href="Algebras.Signatures.html#1068" class="Function">π</a> <a id="1070" class="Symbol">:</a> <a id="1072" class="Symbol">{</a><a id="1073" href="Algebras.Signatures.html#1073" class="Bound">I</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="1079" href="Universes.html#403" class="Function Operator">̇</a> <a id="1081" class="Symbol">}</a> <a id="1083" class="Symbol">{</a><a id="1084" href="Algebras.Signatures.html#1084" class="Bound">A</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1090" href="Universes.html#403" class="Function Operator">̇</a> <a id="1092" class="Symbol">}</a> <a id="1094" class="Symbol">→</a> <a id="1096" href="Algebras.Signatures.html#1073" class="Bound">I</a> <a id="1098" class="Symbol">→</a> <a id="1100" href="Algebras.Signatures.html#668" class="Function">Op</a> <a id="1103" href="Algebras.Signatures.html#1073" class="Bound">I</a> <a id="1105" href="Algebras.Signatures.html#1084" class="Bound">A</a>
<a id="1107" href="Algebras.Signatures.html#1068" class="Function">π</a> <a id="1109" href="Algebras.Signatures.html#1109" class="Bound">i</a> <a id="1111" href="Algebras.Signatures.html#1111" class="Bound">x</a> <a id="1113" class="Symbol">=</a> <a id="1115" href="Algebras.Signatures.html#1111" class="Bound">x</a> <a id="1117" href="Algebras.Signatures.html#1109" class="Bound">i</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1266" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="1276" class="Symbol">:</a> <a id="1278" class="Symbol">(</a><a id="1279" href="Algebras.Signatures.html#1279" class="Bound">𝓞</a> <a id="1281" href="Algebras.Signatures.html#1281" class="Bound">𝓥</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1293" class="Symbol">)</a> <a id="1295" class="Symbol">→</a> <a id="1297" class="Symbol">(</a><a id="1298" href="Algebras.Signatures.html#1279" class="Bound">𝓞</a> <a id="1300" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1302" href="Algebras.Signatures.html#1281" class="Bound">𝓥</a><a id="1303" class="Symbol">)</a> <a id="1305" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1307" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1309" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="1319" href="Algebras.Signatures.html#1319" class="Bound">𝓞</a> <a id="1321" href="Algebras.Signatures.html#1321" class="Bound">𝓥</a> <a id="1323" class="Symbol">=</a> <a id="1325" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1327" href="Algebras.Signatures.html#1327" class="Bound">F</a> <a id="1329" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1331" href="Algebras.Signatures.html#1319" class="Bound">𝓞</a> <a id="1333" href="Universes.html#403" class="Function Operator">̇</a> <a id="1335" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1337" class="Symbol">(</a><a id="1338" href="Algebras.Signatures.html#1327" class="Bound">F</a> <a id="1340" class="Symbol">→</a> <a id="1342" href="Algebras.Signatures.html#1321" class="Bound">𝓥</a> <a id="1344" href="Universes.html#403" class="Function Operator">̇</a><a id="1345" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2014" class="Keyword">data</a> <a id="monoid-op"></a><a id="2019" href="Algebras.Signatures.html#2019" class="Datatype">monoid-op</a> <a id="2029" class="Symbol">{</a><a id="2030" href="Algebras.Signatures.html#2030" class="Bound">𝓞</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2042" class="Symbol">}</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="Algebras.Signatures.html#2030" class="Bound">𝓞</a> <a id="2048" href="Universes.html#403" class="Function Operator">̇</a> <a id="2050" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2057" href="Algebras.Signatures.html#2057" class="InductiveConstructor">e</a> <a id="2059" class="Symbol">:</a> <a id="2061" href="Algebras.Signatures.html#2019" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2072" href="Algebras.Signatures.html#2072" class="InductiveConstructor">·</a> <a id="2074" class="Symbol">:</a> <a id="2076" href="Algebras.Signatures.html#2019" class="Datatype">monoid-op</a>

<a id="2087" class="Keyword">open</a> <a id="2092" class="Keyword">import</a> <a id="2099" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2108" class="Keyword">using</a> <a id="2114" class="Symbol">(</a><a id="2115" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2116" class="Symbol">;</a> <a id="2118" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2119" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="2122" href="Algebras.Signatures.html#2122" class="Function">monoid-sig</a> <a id="2133" class="Symbol">:</a> <a id="2135" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="2145" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="2147" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="2150" href="Algebras.Signatures.html#2122" class="Function">monoid-sig</a> <a id="2161" class="Symbol">=</a> <a id="2163" href="Algebras.Signatures.html#2019" class="Datatype">monoid-op</a> <a id="2173" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="2175" class="Symbol">λ</a> <a id="2177" class="Symbol">{</a> <a id="2179" href="Algebras.Signatures.html#2057" class="InductiveConstructor">e</a> <a id="2181" class="Symbol">→</a> <a id="2183" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2184" class="Symbol">;</a> <a id="2186" href="Algebras.Signatures.html#2072" class="InductiveConstructor">·</a> <a id="2188" class="Symbol">→</a> <a id="2190" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2192" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

