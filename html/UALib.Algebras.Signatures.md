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

-----------------------------------

#### <a id="operation-type">Operation type</a>

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="760" class="Keyword">module</a> <a id="767" href="UALib.Algebras.Signatures.html#767" class="Module">_</a> <a id="769" class="Symbol">{</a><a id="770" href="UALib.Algebras.Signatures.html#770" class="Bound">𝓤</a> <a id="772" href="UALib.Algebras.Signatures.html#772" class="Bound">𝓥</a> <a id="774" class="Symbol">:</a> <a id="776" href="universes.html#551" class="Postulate">Universe</a><a id="784" class="Symbol">}</a> <a id="786" class="Keyword">where</a>

 <a id="794" class="Comment">--The type of operations</a>
 <a id="820" href="UALib.Algebras.Signatures.html#820" class="Function">Op</a> <a id="823" class="Symbol">:</a> <a id="825" href="UALib.Algebras.Signatures.html#772" class="Bound">𝓥</a> <a id="827" href="universes.html#758" class="Function Operator">̇</a> <a id="829" class="Symbol">→</a> <a id="831" href="UALib.Algebras.Signatures.html#770" class="Bound">𝓤</a> <a id="833" href="universes.html#758" class="Function Operator">̇</a> <a id="835" class="Symbol">→</a> <a id="837" href="UALib.Algebras.Signatures.html#770" class="Bound">𝓤</a> <a id="839" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="841" href="UALib.Algebras.Signatures.html#772" class="Bound">𝓥</a> <a id="843" href="universes.html#758" class="Function Operator">̇</a>
 <a id="846" href="UALib.Algebras.Signatures.html#820" class="Function">Op</a> <a id="849" href="UALib.Algebras.Signatures.html#849" class="Bound">I</a> <a id="851" href="UALib.Algebras.Signatures.html#851" class="Bound">A</a> <a id="853" class="Symbol">=</a> <a id="855" class="Symbol">(</a><a id="856" href="UALib.Algebras.Signatures.html#849" class="Bound">I</a> <a id="858" class="Symbol">→</a> <a id="860" href="UALib.Algebras.Signatures.html#851" class="Bound">A</a><a id="861" class="Symbol">)</a> <a id="863" class="Symbol">→</a> <a id="865" href="UALib.Algebras.Signatures.html#851" class="Bound">A</a>

 <a id="869" class="Comment">--Example. the projections</a>
 <a id="897" href="UALib.Algebras.Signatures.html#897" class="Function">π</a> <a id="899" class="Symbol">:</a> <a id="901" class="Symbol">{</a><a id="902" href="UALib.Algebras.Signatures.html#902" class="Bound">I</a> <a id="904" class="Symbol">:</a> <a id="906" href="UALib.Algebras.Signatures.html#772" class="Bound">𝓥</a> <a id="908" href="universes.html#758" class="Function Operator">̇</a> <a id="910" class="Symbol">}</a> <a id="912" class="Symbol">{</a><a id="913" href="UALib.Algebras.Signatures.html#913" class="Bound">A</a> <a id="915" class="Symbol">:</a> <a id="917" href="UALib.Algebras.Signatures.html#770" class="Bound">𝓤</a> <a id="919" href="universes.html#758" class="Function Operator">̇</a> <a id="921" class="Symbol">}</a> <a id="923" class="Symbol">→</a> <a id="925" href="UALib.Algebras.Signatures.html#902" class="Bound">I</a> <a id="927" class="Symbol">→</a> <a id="929" href="UALib.Algebras.Signatures.html#820" class="Function">Op</a> <a id="932" href="UALib.Algebras.Signatures.html#902" class="Bound">I</a> <a id="934" href="UALib.Algebras.Signatures.html#913" class="Bound">A</a>
 <a id="937" href="UALib.Algebras.Signatures.html#897" class="Function">π</a> <a id="939" href="UALib.Algebras.Signatures.html#939" class="Bound">i</a> <a id="941" href="UALib.Algebras.Signatures.html#941" class="Bound">x</a> <a id="943" class="Symbol">=</a> <a id="945" href="UALib.Algebras.Signatures.html#941" class="Bound">x</a> <a id="947" href="UALib.Algebras.Signatures.html#939" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.

-----------------------------------

#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1452" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="1462" class="Symbol">:</a> <a id="1464" class="Symbol">(</a><a id="1465" href="UALib.Algebras.Signatures.html#1465" class="Bound">𝓞</a> <a id="1467" href="UALib.Algebras.Signatures.html#1467" class="Bound">𝓥</a> <a id="1469" class="Symbol">:</a> <a id="1471" href="universes.html#551" class="Postulate">Universe</a><a id="1479" class="Symbol">)</a> <a id="1481" class="Symbol">→</a> <a id="1483" class="Symbol">(</a><a id="1484" href="UALib.Algebras.Signatures.html#1465" class="Bound">𝓞</a> <a id="1486" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1488" href="UALib.Algebras.Signatures.html#1467" class="Bound">𝓥</a><a id="1489" class="Symbol">)</a> <a id="1491" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1493" href="universes.html#758" class="Function Operator">̇</a>
<a id="1495" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="1505" href="UALib.Algebras.Signatures.html#1505" class="Bound">𝓞</a> <a id="1507" href="UALib.Algebras.Signatures.html#1507" class="Bound">𝓥</a> <a id="1509" class="Symbol">=</a> <a id="1511" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1513" href="UALib.Algebras.Signatures.html#1513" class="Bound">F</a> <a id="1515" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1517" href="UALib.Algebras.Signatures.html#1505" class="Bound">𝓞</a> <a id="1519" href="universes.html#758" class="Function Operator">̇</a> <a id="1521" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1523" class="Symbol">(</a><a id="1524" href="UALib.Algebras.Signatures.html#1513" class="Bound">F</a> <a id="1526" class="Symbol">→</a> <a id="1528" href="UALib.Algebras.Signatures.html#1507" class="Bound">𝓥</a> <a id="1530" href="universes.html#758" class="Function Operator">̇</a><a id="1531" class="Symbol">)</a>

</pre>

Here 𝓞 is the universe level of operation symbol types, while 𝓥 is the universe level of arity types.

In the [UALib.Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.

For reference, we recall the definition of the Sigma type, `Σ`, which is

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```

------------------------------------

#### <a id="Example">Example</a>

Here is how we might define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2340" class="Keyword">module</a> <a id="2347" href="UALib.Algebras.Signatures.html#2347" class="Module">_</a> <a id="2349" class="Symbol">{</a><a id="2350" href="UALib.Algebras.Signatures.html#2350" class="Bound">𝓞</a> <a id="2352" class="Symbol">:</a> <a id="2354" href="universes.html#551" class="Postulate">Universe</a><a id="2362" class="Symbol">}</a> <a id="2364" class="Keyword">where</a>

 <a id="2372" class="Keyword">data</a> <a id="2377" href="UALib.Algebras.Signatures.html#2377" class="Datatype">monoid-op</a> <a id="2387" class="Symbol">:</a> <a id="2389" href="UALib.Algebras.Signatures.html#2350" class="Bound">𝓞</a> <a id="2391" href="universes.html#758" class="Function Operator">̇</a> <a id="2393" class="Keyword">where</a>
  <a id="2401" href="UALib.Algebras.Signatures.html#2401" class="InductiveConstructor">e</a> <a id="2403" class="Symbol">:</a> <a id="2405" href="UALib.Algebras.Signatures.html#2377" class="Datatype">monoid-op</a>
  <a id="2417" href="UALib.Algebras.Signatures.html#2417" class="InductiveConstructor">·</a> <a id="2419" class="Symbol">:</a> <a id="2421" href="UALib.Algebras.Signatures.html#2377" class="Datatype">monoid-op</a>

 <a id="2433" href="UALib.Algebras.Signatures.html#2433" class="Function">monoid-sig</a> <a id="2444" class="Symbol">:</a> <a id="2446" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="2456" href="UALib.Algebras.Signatures.html#2350" class="Bound">𝓞</a> <a id="2458" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2462" href="UALib.Algebras.Signatures.html#2433" class="Function">monoid-sig</a> <a id="2473" class="Symbol">=</a> <a id="2475" href="UALib.Algebras.Signatures.html#2377" class="Datatype">monoid-op</a> <a id="2485" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="2487" class="Symbol">λ</a> <a id="2489" class="Symbol">{</a> <a id="2491" href="UALib.Algebras.Signatures.html#2401" class="InductiveConstructor">e</a> <a id="2493" class="Symbol">→</a> <a id="2495" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2496" class="Symbol">;</a> <a id="2498" href="UALib.Algebras.Signatures.html#2417" class="InductiveConstructor">·</a> <a id="2500" class="Symbol">→</a> <a id="2502" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2504" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Algebras](UALib.Algebras.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

