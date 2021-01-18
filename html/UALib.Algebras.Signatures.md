---
layout: default
title : UALib.Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="operation-and-signature-types">Operation and Signature Types</a>

This section presents the [UALib.Algebras.Signatures][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="338" class="Symbol">{-#</a> <a id="342" class="Keyword">OPTIONS</a> <a id="350" class="Pragma">--without-K</a> <a id="362" class="Pragma">--exact-split</a> <a id="376" class="Pragma">--safe</a> <a id="383" class="Symbol">#-}</a>

<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="universes.html" class="Module">universes</a> <a id="410" class="Keyword">using</a> <a id="416" class="Symbol">(</a><a id="417" href="universes.html#504" class="Primitive">𝓤₀</a><a id="419" class="Symbol">)</a>

<a id="422" class="Keyword">module</a> <a id="429" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="455" class="Keyword">where</a>

<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="UALib.Prelude.Extensionality.html" class="Module">UALib.Prelude.Extensionality</a> <a id="503" class="Keyword">public</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="550" class="Keyword">using</a> <a id="556" class="Symbol">(</a><a id="557" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="558" class="Symbol">;</a> <a id="560" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="561" class="Symbol">)</a> <a id="563" class="Keyword">public</a>

</pre>

#### Operation type

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="696" class="Keyword">module</a> <a id="703" href="UALib.Algebras.Signatures.html#703" class="Module">_</a> <a id="705" class="Symbol">{</a><a id="706" href="UALib.Algebras.Signatures.html#706" class="Bound">𝓤</a> <a id="708" href="UALib.Algebras.Signatures.html#708" class="Bound">𝓥</a> <a id="710" class="Symbol">:</a> <a id="712" href="universes.html#551" class="Postulate">Universe</a><a id="720" class="Symbol">}</a> <a id="722" class="Keyword">where</a>

 <a id="730" class="Comment">--The type of operations</a>
 <a id="756" href="UALib.Algebras.Signatures.html#756" class="Function">Op</a> <a id="759" class="Symbol">:</a> <a id="761" href="UALib.Algebras.Signatures.html#708" class="Bound">𝓥</a> <a id="763" href="universes.html#758" class="Function Operator">̇</a> <a id="765" class="Symbol">→</a> <a id="767" href="UALib.Algebras.Signatures.html#706" class="Bound">𝓤</a> <a id="769" href="universes.html#758" class="Function Operator">̇</a> <a id="771" class="Symbol">→</a> <a id="773" href="UALib.Algebras.Signatures.html#706" class="Bound">𝓤</a> <a id="775" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="777" href="UALib.Algebras.Signatures.html#708" class="Bound">𝓥</a> <a id="779" href="universes.html#758" class="Function Operator">̇</a>
 <a id="782" href="UALib.Algebras.Signatures.html#756" class="Function">Op</a> <a id="785" href="UALib.Algebras.Signatures.html#785" class="Bound">I</a> <a id="787" href="UALib.Algebras.Signatures.html#787" class="Bound">A</a> <a id="789" class="Symbol">=</a> <a id="791" class="Symbol">(</a><a id="792" href="UALib.Algebras.Signatures.html#785" class="Bound">I</a> <a id="794" class="Symbol">→</a> <a id="796" href="UALib.Algebras.Signatures.html#787" class="Bound">A</a><a id="797" class="Symbol">)</a> <a id="799" class="Symbol">→</a> <a id="801" href="UALib.Algebras.Signatures.html#787" class="Bound">A</a>

 <a id="805" class="Comment">--Example. the projections</a>
 <a id="833" href="UALib.Algebras.Signatures.html#833" class="Function">π</a> <a id="835" class="Symbol">:</a> <a id="837" class="Symbol">{</a><a id="838" href="UALib.Algebras.Signatures.html#838" class="Bound">I</a> <a id="840" class="Symbol">:</a> <a id="842" href="UALib.Algebras.Signatures.html#708" class="Bound">𝓥</a> <a id="844" href="universes.html#758" class="Function Operator">̇</a> <a id="846" class="Symbol">}</a> <a id="848" class="Symbol">{</a><a id="849" href="UALib.Algebras.Signatures.html#849" class="Bound">A</a> <a id="851" class="Symbol">:</a> <a id="853" href="UALib.Algebras.Signatures.html#706" class="Bound">𝓤</a> <a id="855" href="universes.html#758" class="Function Operator">̇</a> <a id="857" class="Symbol">}</a> <a id="859" class="Symbol">→</a> <a id="861" href="UALib.Algebras.Signatures.html#838" class="Bound">I</a> <a id="863" class="Symbol">→</a> <a id="865" href="UALib.Algebras.Signatures.html#756" class="Function">Op</a> <a id="868" href="UALib.Algebras.Signatures.html#838" class="Bound">I</a> <a id="870" href="UALib.Algebras.Signatures.html#849" class="Bound">A</a>
 <a id="873" href="UALib.Algebras.Signatures.html#833" class="Function">π</a> <a id="875" href="UALib.Algebras.Signatures.html#875" class="Bound">i</a> <a id="877" href="UALib.Algebras.Signatures.html#877" class="Bound">x</a> <a id="879" class="Symbol">=</a> <a id="881" href="UALib.Algebras.Signatures.html#877" class="Bound">x</a> <a id="883" href="UALib.Algebras.Signatures.html#875" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.

#### Signature type

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1324" href="UALib.Algebras.Signatures.html#1324" class="Function">Signature</a> <a id="1334" class="Symbol">:</a> <a id="1336" class="Symbol">(</a><a id="1337" href="UALib.Algebras.Signatures.html#1337" class="Bound">𝓞</a> <a id="1339" href="UALib.Algebras.Signatures.html#1339" class="Bound">𝓥</a> <a id="1341" class="Symbol">:</a> <a id="1343" href="universes.html#551" class="Postulate">Universe</a><a id="1351" class="Symbol">)</a> <a id="1353" class="Symbol">→</a> <a id="1355" class="Symbol">(</a><a id="1356" href="UALib.Algebras.Signatures.html#1337" class="Bound">𝓞</a> <a id="1358" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1360" href="UALib.Algebras.Signatures.html#1339" class="Bound">𝓥</a><a id="1361" class="Symbol">)</a> <a id="1363" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1365" href="universes.html#758" class="Function Operator">̇</a>
<a id="1367" href="UALib.Algebras.Signatures.html#1324" class="Function">Signature</a> <a id="1377" href="UALib.Algebras.Signatures.html#1377" class="Bound">𝓞</a> <a id="1379" href="UALib.Algebras.Signatures.html#1379" class="Bound">𝓥</a> <a id="1381" class="Symbol">=</a> <a id="1383" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1385" href="UALib.Algebras.Signatures.html#1385" class="Bound">F</a> <a id="1387" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1389" href="UALib.Algebras.Signatures.html#1377" class="Bound">𝓞</a> <a id="1391" href="universes.html#758" class="Function Operator">̇</a> <a id="1393" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1395" class="Symbol">(</a><a id="1396" href="UALib.Algebras.Signatures.html#1385" class="Bound">F</a> <a id="1398" class="Symbol">→</a> <a id="1400" href="UALib.Algebras.Signatures.html#1379" class="Bound">𝓥</a> <a id="1402" href="universes.html#758" class="Function Operator">̇</a><a id="1403" class="Symbol">)</a>

</pre>

Here 𝓞 is the universe level of operation symbol types, while 𝓥 is the universe level of arity types.

In the [UALib.Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.

For reference, we recall the definition of the Sigma type, `Σ`, which is

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```

#### Example

Here is how we might define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2154" class="Keyword">module</a> <a id="2161" href="UALib.Algebras.Signatures.html#2161" class="Module">_</a> <a id="2163" class="Symbol">{</a><a id="2164" href="UALib.Algebras.Signatures.html#2164" class="Bound">𝓞</a> <a id="2166" class="Symbol">:</a> <a id="2168" href="universes.html#551" class="Postulate">Universe</a><a id="2176" class="Symbol">}</a> <a id="2178" class="Keyword">where</a>

 <a id="2186" class="Keyword">data</a> <a id="2191" href="UALib.Algebras.Signatures.html#2191" class="Datatype">monoid-op</a> <a id="2201" class="Symbol">:</a> <a id="2203" href="UALib.Algebras.Signatures.html#2164" class="Bound">𝓞</a> <a id="2205" href="universes.html#758" class="Function Operator">̇</a> <a id="2207" class="Keyword">where</a>
  <a id="2215" href="UALib.Algebras.Signatures.html#2215" class="InductiveConstructor">e</a> <a id="2217" class="Symbol">:</a> <a id="2219" href="UALib.Algebras.Signatures.html#2191" class="Datatype">monoid-op</a>
  <a id="2231" href="UALib.Algebras.Signatures.html#2231" class="InductiveConstructor">·</a> <a id="2233" class="Symbol">:</a> <a id="2235" href="UALib.Algebras.Signatures.html#2191" class="Datatype">monoid-op</a>

 <a id="2247" href="UALib.Algebras.Signatures.html#2247" class="Function">monoid-sig</a> <a id="2258" class="Symbol">:</a> <a id="2260" href="UALib.Algebras.Signatures.html#1324" class="Function">Signature</a> <a id="2270" href="UALib.Algebras.Signatures.html#2164" class="Bound">𝓞</a> <a id="2272" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2276" href="UALib.Algebras.Signatures.html#2247" class="Function">monoid-sig</a> <a id="2287" class="Symbol">=</a> <a id="2289" href="UALib.Algebras.Signatures.html#2191" class="Datatype">monoid-op</a> <a id="2299" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">,</a> <a id="2301" class="Symbol">λ</a> <a id="2303" class="Symbol">{</a> <a id="2305" href="UALib.Algebras.Signatures.html#2215" class="InductiveConstructor">e</a> <a id="2307" class="Symbol">→</a> <a id="2309" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2310" class="Symbol">;</a> <a id="2312" href="UALib.Algebras.Signatures.html#2231" class="InductiveConstructor">·</a> <a id="2314" class="Symbol">→</a> <a id="2316" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2318" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Prelude.Extensionality](UALib.Prelude.Extensionality.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

