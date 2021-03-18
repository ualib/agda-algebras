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

<a id="643" class="Keyword">module</a> <a id="650" href="Algebras.Signatures.html#650" class="Module">_</a> <a id="652" class="Symbol">{</a><a id="653" href="Algebras.Signatures.html#653" class="Bound">𝓤</a> <a id="655" class="Symbol">:</a> <a id="657" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="665" class="Symbol">}</a> <a id="667" class="Keyword">where</a>

 <a id="675" class="Comment">--The type of operations</a>
 <a id="701" href="Algebras.Signatures.html#701" class="Function">Op</a> <a id="704" class="Symbol">:</a> <a id="706" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="708" href="Universes.html#403" class="Function Operator">̇</a> <a id="710" class="Symbol">→</a> <a id="712" href="Algebras.Signatures.html#653" class="Bound">𝓤</a> <a id="714" href="Universes.html#403" class="Function Operator">̇</a> <a id="716" class="Symbol">→</a> <a id="718" href="Algebras.Signatures.html#653" class="Bound">𝓤</a> <a id="720" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="722" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="724" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="727" href="Algebras.Signatures.html#701" class="Function">Op</a> <a id="730" href="Algebras.Signatures.html#730" class="Bound">I</a> <a id="732" href="Algebras.Signatures.html#732" class="Bound">A</a> <a id="734" class="Symbol">=</a> <a id="736" class="Symbol">(</a><a id="737" href="Algebras.Signatures.html#730" class="Bound">I</a> <a id="739" class="Symbol">→</a> <a id="741" href="Algebras.Signatures.html#732" class="Bound">A</a><a id="742" class="Symbol">)</a> <a id="744" class="Symbol">→</a> <a id="746" href="Algebras.Signatures.html#732" class="Bound">A</a>

 <a id="750" class="Comment">--Example. the projections</a>
 <a id="778" href="Algebras.Signatures.html#778" class="Function">π</a> <a id="780" class="Symbol">:</a> <a id="782" class="Symbol">{</a><a id="783" href="Algebras.Signatures.html#783" class="Bound">I</a> <a id="785" class="Symbol">:</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="789" href="Universes.html#403" class="Function Operator">̇</a> <a id="791" class="Symbol">}</a> <a id="793" class="Symbol">{</a><a id="794" href="Algebras.Signatures.html#794" class="Bound">A</a> <a id="796" class="Symbol">:</a> <a id="798" href="Algebras.Signatures.html#653" class="Bound">𝓤</a> <a id="800" href="Universes.html#403" class="Function Operator">̇</a> <a id="802" class="Symbol">}</a> <a id="804" class="Symbol">→</a> <a id="806" href="Algebras.Signatures.html#783" class="Bound">I</a> <a id="808" class="Symbol">→</a> <a id="810" href="Algebras.Signatures.html#701" class="Function">Op</a> <a id="813" href="Algebras.Signatures.html#783" class="Bound">I</a> <a id="815" href="Algebras.Signatures.html#794" class="Bound">A</a>
 <a id="818" href="Algebras.Signatures.html#778" class="Function">π</a> <a id="820" href="Algebras.Signatures.html#820" class="Bound">i</a> <a id="822" href="Algebras.Signatures.html#822" class="Bound">x</a> <a id="824" class="Symbol">=</a> <a id="826" href="Algebras.Signatures.html#822" class="Bound">x</a> <a id="828" href="Algebras.Signatures.html#820" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.




#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1299" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="1309" class="Symbol">:</a> <a id="1311" class="Symbol">(</a><a id="1312" href="Algebras.Signatures.html#1312" class="Bound">𝓞</a> <a id="1314" href="Algebras.Signatures.html#1314" class="Bound">𝓥</a> <a id="1316" class="Symbol">:</a> <a id="1318" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1326" class="Symbol">)</a> <a id="1328" class="Symbol">→</a> <a id="1330" class="Symbol">(</a><a id="1331" href="Algebras.Signatures.html#1312" class="Bound">𝓞</a> <a id="1333" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1335" href="Algebras.Signatures.html#1314" class="Bound">𝓥</a><a id="1336" class="Symbol">)</a> <a id="1338" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1340" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1342" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="1352" href="Algebras.Signatures.html#1352" class="Bound">𝓞</a> <a id="1354" href="Algebras.Signatures.html#1354" class="Bound">𝓥</a> <a id="1356" class="Symbol">=</a> <a id="1358" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1360" href="Algebras.Signatures.html#1360" class="Bound">F</a> <a id="1362" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1364" href="Algebras.Signatures.html#1352" class="Bound">𝓞</a> <a id="1366" href="Universes.html#403" class="Function Operator">̇</a> <a id="1368" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1370" class="Symbol">(</a><a id="1371" href="Algebras.Signatures.html#1360" class="Bound">F</a> <a id="1373" class="Symbol">→</a> <a id="1375" href="Algebras.Signatures.html#1354" class="Bound">𝓥</a> <a id="1377" href="Universes.html#403" class="Function Operator">̇</a><a id="1378" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.

For reference, we recall the definition of the Sigma type, `Σ`, which is

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```



#### <a id="Example">Example</a>

Here is how we might define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2201" class="Keyword">module</a> <a id="2208" href="Algebras.Signatures.html#2208" class="Module">_</a> <a id="2210" class="Symbol">{</a><a id="2211" href="Algebras.Signatures.html#2211" class="Bound">𝓞</a> <a id="2213" class="Symbol">:</a> <a id="2215" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2223" class="Symbol">}</a> <a id="2225" class="Keyword">where</a>

 <a id="2233" class="Keyword">data</a> <a id="2238" href="Algebras.Signatures.html#2238" class="Datatype">monoid-op</a> <a id="2248" class="Symbol">:</a> <a id="2250" href="Algebras.Signatures.html#2211" class="Bound">𝓞</a> <a id="2252" href="Universes.html#403" class="Function Operator">̇</a> <a id="2254" class="Keyword">where</a>
  <a id="2262" href="Algebras.Signatures.html#2262" class="InductiveConstructor">e</a> <a id="2264" class="Symbol">:</a> <a id="2266" href="Algebras.Signatures.html#2238" class="Datatype">monoid-op</a>
  <a id="2278" href="Algebras.Signatures.html#2278" class="InductiveConstructor">·</a> <a id="2280" class="Symbol">:</a> <a id="2282" href="Algebras.Signatures.html#2238" class="Datatype">monoid-op</a>

 <a id="2294" class="Keyword">open</a> <a id="2299" class="Keyword">import</a> <a id="2306" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2315" class="Keyword">using</a> <a id="2321" class="Symbol">(</a><a id="2322" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2323" class="Symbol">;</a> <a id="2325" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2326" class="Symbol">)</a>

 <a id="2330" href="Algebras.Signatures.html#2330" class="Function">monoid-sig</a> <a id="2341" class="Symbol">:</a> <a id="2343" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="2353" href="Algebras.Signatures.html#2211" class="Bound">𝓞</a> <a id="2355" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
 <a id="2359" href="Algebras.Signatures.html#2330" class="Function">monoid-sig</a> <a id="2370" class="Symbol">=</a> <a id="2372" href="Algebras.Signatures.html#2238" class="Datatype">monoid-op</a> <a id="2382" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">,</a> <a id="2384" class="Symbol">λ</a> <a id="2386" class="Symbol">{</a> <a id="2388" href="Algebras.Signatures.html#2262" class="InductiveConstructor">e</a> <a id="2390" class="Symbol">→</a> <a id="2392" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2393" class="Symbol">;</a> <a id="2395" href="Algebras.Signatures.html#2278" class="InductiveConstructor">·</a> <a id="2397" class="Symbol">→</a> <a id="2399" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2401" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

