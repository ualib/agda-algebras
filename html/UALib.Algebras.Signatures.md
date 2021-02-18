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

<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="UALib.Relations.Quotients.html" class="Module">UALib.Relations.Quotients</a> <a id="500" class="Keyword">public</a>

<a id="508" class="Keyword">open</a> <a id="513" class="Keyword">import</a> <a id="520" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="548" class="Keyword">using</a> <a id="554" class="Symbol">(</a><a id="555" href="universes.html#613" class="Generalizable">𝓞</a><a id="556" class="Symbol">;</a> <a id="558" href="universes.html#617" class="Generalizable">𝓥</a><a id="559" class="Symbol">;</a> <a id="561" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="562" class="Symbol">;</a> <a id="564" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="565" class="Symbol">)</a> <a id="567" class="Keyword">public</a>

</pre>

-----------------------------------

#### <a id="operation-type">Operation type</a>

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="764" class="Keyword">module</a> <a id="771" href="UALib.Algebras.Signatures.html#771" class="Module">_</a> <a id="773" class="Symbol">{</a><a id="774" href="UALib.Algebras.Signatures.html#774" class="Bound">𝓤</a> <a id="776" class="Symbol">:</a> <a id="778" href="universes.html#551" class="Postulate">Universe</a><a id="786" class="Symbol">}</a> <a id="788" class="Keyword">where</a>

 <a id="796" class="Comment">--The type of operations</a>
 <a id="822" href="UALib.Algebras.Signatures.html#822" class="Function">Op</a> <a id="825" class="Symbol">:</a> <a id="827" href="universes.html#617" class="Generalizable">𝓥</a> <a id="829" href="universes.html#758" class="Function Operator">̇</a> <a id="831" class="Symbol">→</a> <a id="833" href="UALib.Algebras.Signatures.html#774" class="Bound">𝓤</a> <a id="835" href="universes.html#758" class="Function Operator">̇</a> <a id="837" class="Symbol">→</a> <a id="839" href="UALib.Algebras.Signatures.html#774" class="Bound">𝓤</a> <a id="841" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="843" href="universes.html#617" class="Generalizable">𝓥</a> <a id="845" href="universes.html#758" class="Function Operator">̇</a>
 <a id="848" href="UALib.Algebras.Signatures.html#822" class="Function">Op</a> <a id="851" href="UALib.Algebras.Signatures.html#851" class="Bound">I</a> <a id="853" href="UALib.Algebras.Signatures.html#853" class="Bound">A</a> <a id="855" class="Symbol">=</a> <a id="857" class="Symbol">(</a><a id="858" href="UALib.Algebras.Signatures.html#851" class="Bound">I</a> <a id="860" class="Symbol">→</a> <a id="862" href="UALib.Algebras.Signatures.html#853" class="Bound">A</a><a id="863" class="Symbol">)</a> <a id="865" class="Symbol">→</a> <a id="867" href="UALib.Algebras.Signatures.html#853" class="Bound">A</a>

 <a id="871" class="Comment">--Example. the projections</a>
 <a id="899" href="UALib.Algebras.Signatures.html#899" class="Function">π</a> <a id="901" class="Symbol">:</a> <a id="903" class="Symbol">{</a><a id="904" href="UALib.Algebras.Signatures.html#904" class="Bound">I</a> <a id="906" class="Symbol">:</a> <a id="908" href="universes.html#617" class="Generalizable">𝓥</a> <a id="910" href="universes.html#758" class="Function Operator">̇</a> <a id="912" class="Symbol">}</a> <a id="914" class="Symbol">{</a><a id="915" href="UALib.Algebras.Signatures.html#915" class="Bound">A</a> <a id="917" class="Symbol">:</a> <a id="919" href="UALib.Algebras.Signatures.html#774" class="Bound">𝓤</a> <a id="921" href="universes.html#758" class="Function Operator">̇</a> <a id="923" class="Symbol">}</a> <a id="925" class="Symbol">→</a> <a id="927" href="UALib.Algebras.Signatures.html#904" class="Bound">I</a> <a id="929" class="Symbol">→</a> <a id="931" href="UALib.Algebras.Signatures.html#822" class="Function">Op</a> <a id="934" href="UALib.Algebras.Signatures.html#904" class="Bound">I</a> <a id="936" href="UALib.Algebras.Signatures.html#915" class="Bound">A</a>
 <a id="939" href="UALib.Algebras.Signatures.html#899" class="Function">π</a> <a id="941" href="UALib.Algebras.Signatures.html#941" class="Bound">i</a> <a id="943" href="UALib.Algebras.Signatures.html#943" class="Bound">x</a> <a id="945" class="Symbol">=</a> <a id="947" href="UALib.Algebras.Signatures.html#943" class="Bound">x</a> <a id="949" href="UALib.Algebras.Signatures.html#941" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.

-----------------------------------

#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1454" href="UALib.Algebras.Signatures.html#1454" class="Function">Signature</a> <a id="1464" class="Symbol">:</a> <a id="1466" class="Symbol">(</a><a id="1467" href="UALib.Algebras.Signatures.html#1467" class="Bound">𝓞</a> <a id="1469" href="UALib.Algebras.Signatures.html#1469" class="Bound">𝓥</a> <a id="1471" class="Symbol">:</a> <a id="1473" href="universes.html#551" class="Postulate">Universe</a><a id="1481" class="Symbol">)</a> <a id="1483" class="Symbol">→</a> <a id="1485" class="Symbol">(</a><a id="1486" href="UALib.Algebras.Signatures.html#1467" class="Bound">𝓞</a> <a id="1488" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1490" href="UALib.Algebras.Signatures.html#1469" class="Bound">𝓥</a><a id="1491" class="Symbol">)</a> <a id="1493" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1495" href="universes.html#758" class="Function Operator">̇</a>
<a id="1497" href="UALib.Algebras.Signatures.html#1454" class="Function">Signature</a> <a id="1507" href="UALib.Algebras.Signatures.html#1507" class="Bound">𝓞</a> <a id="1509" href="UALib.Algebras.Signatures.html#1509" class="Bound">𝓥</a> <a id="1511" class="Symbol">=</a> <a id="1513" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1515" href="UALib.Algebras.Signatures.html#1515" class="Bound">F</a> <a id="1517" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1519" href="UALib.Algebras.Signatures.html#1507" class="Bound">𝓞</a> <a id="1521" href="universes.html#758" class="Function Operator">̇</a> <a id="1523" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1525" class="Symbol">(</a><a id="1526" href="UALib.Algebras.Signatures.html#1515" class="Bound">F</a> <a id="1528" class="Symbol">→</a> <a id="1530" href="UALib.Algebras.Signatures.html#1509" class="Bound">𝓥</a> <a id="1532" href="universes.html#758" class="Function Operator">̇</a><a id="1533" class="Symbol">)</a>

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

<a id="2342" class="Keyword">module</a> <a id="2349" href="UALib.Algebras.Signatures.html#2349" class="Module">_</a> <a id="2351" class="Symbol">{</a><a id="2352" href="UALib.Algebras.Signatures.html#2352" class="Bound">𝓞</a> <a id="2354" class="Symbol">:</a> <a id="2356" href="universes.html#551" class="Postulate">Universe</a><a id="2364" class="Symbol">}</a> <a id="2366" class="Keyword">where</a>

 <a id="2374" class="Keyword">data</a> <a id="2379" href="UALib.Algebras.Signatures.html#2379" class="Datatype">monoid-op</a> <a id="2389" class="Symbol">:</a> <a id="2391" href="UALib.Algebras.Signatures.html#2352" class="Bound">𝓞</a> <a id="2393" href="universes.html#758" class="Function Operator">̇</a> <a id="2395" class="Keyword">where</a>
  <a id="2403" href="UALib.Algebras.Signatures.html#2403" class="InductiveConstructor">e</a> <a id="2405" class="Symbol">:</a> <a id="2407" href="UALib.Algebras.Signatures.html#2379" class="Datatype">monoid-op</a>
  <a id="2419" href="UALib.Algebras.Signatures.html#2419" class="InductiveConstructor">·</a> <a id="2421" class="Symbol">:</a> <a id="2423" href="UALib.Algebras.Signatures.html#2379" class="Datatype">monoid-op</a>

 <a id="2435" href="UALib.Algebras.Signatures.html#2435" class="Function">monoid-sig</a> <a id="2446" class="Symbol">:</a> <a id="2448" href="UALib.Algebras.Signatures.html#1454" class="Function">Signature</a> <a id="2458" href="UALib.Algebras.Signatures.html#2352" class="Bound">𝓞</a> <a id="2460" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2464" href="UALib.Algebras.Signatures.html#2435" class="Function">monoid-sig</a> <a id="2475" class="Symbol">=</a> <a id="2477" href="UALib.Algebras.Signatures.html#2379" class="Datatype">monoid-op</a> <a id="2487" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="2489" class="Symbol">λ</a> <a id="2491" class="Symbol">{</a> <a id="2493" href="UALib.Algebras.Signatures.html#2403" class="InductiveConstructor">e</a> <a id="2495" class="Symbol">→</a> <a id="2497" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2498" class="Symbol">;</a> <a id="2500" href="UALib.Algebras.Signatures.html#2419" class="InductiveConstructor">·</a> <a id="2502" class="Symbol">→</a> <a id="2504" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2506" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Algebras](UALib.Algebras.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

