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

<a id="511" class="Keyword">open</a> <a id="516" class="Keyword">import</a> <a id="523" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="551" class="Keyword">using</a> <a id="557" class="Symbol">(</a><a id="558" href="universes.html#613" class="Generalizable">𝓞</a><a id="559" class="Symbol">;</a> <a id="561" href="universes.html#617" class="Generalizable">𝓥</a><a id="562" class="Symbol">;</a> <a id="564" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="565" class="Symbol">;</a> <a id="567" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="568" class="Symbol">)</a> <a id="570" class="Keyword">public</a>

</pre>

-----------------------------------

#### <a id="operation-type">Operation type</a>

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="767" class="Keyword">module</a> <a id="774" href="UALib.Algebras.Signatures.html#774" class="Module">_</a> <a id="776" class="Symbol">{</a><a id="777" href="UALib.Algebras.Signatures.html#777" class="Bound">𝓤</a> <a id="779" class="Symbol">:</a> <a id="781" href="universes.html#551" class="Postulate">Universe</a><a id="789" class="Symbol">}</a> <a id="791" class="Keyword">where</a>

 <a id="799" class="Comment">--The type of operations</a>
 <a id="825" href="UALib.Algebras.Signatures.html#825" class="Function">Op</a> <a id="828" class="Symbol">:</a> <a id="830" href="universes.html#617" class="Generalizable">𝓥</a> <a id="832" href="universes.html#758" class="Function Operator">̇</a> <a id="834" class="Symbol">→</a> <a id="836" href="UALib.Algebras.Signatures.html#777" class="Bound">𝓤</a> <a id="838" href="universes.html#758" class="Function Operator">̇</a> <a id="840" class="Symbol">→</a> <a id="842" href="UALib.Algebras.Signatures.html#777" class="Bound">𝓤</a> <a id="844" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="846" href="universes.html#617" class="Generalizable">𝓥</a> <a id="848" href="universes.html#758" class="Function Operator">̇</a>
 <a id="851" href="UALib.Algebras.Signatures.html#825" class="Function">Op</a> <a id="854" href="UALib.Algebras.Signatures.html#854" class="Bound">I</a> <a id="856" href="UALib.Algebras.Signatures.html#856" class="Bound">A</a> <a id="858" class="Symbol">=</a> <a id="860" class="Symbol">(</a><a id="861" href="UALib.Algebras.Signatures.html#854" class="Bound">I</a> <a id="863" class="Symbol">→</a> <a id="865" href="UALib.Algebras.Signatures.html#856" class="Bound">A</a><a id="866" class="Symbol">)</a> <a id="868" class="Symbol">→</a> <a id="870" href="UALib.Algebras.Signatures.html#856" class="Bound">A</a>

 <a id="874" class="Comment">--Example. the projections</a>
 <a id="902" href="UALib.Algebras.Signatures.html#902" class="Function">π</a> <a id="904" class="Symbol">:</a> <a id="906" class="Symbol">{</a><a id="907" href="UALib.Algebras.Signatures.html#907" class="Bound">I</a> <a id="909" class="Symbol">:</a> <a id="911" href="universes.html#617" class="Generalizable">𝓥</a> <a id="913" href="universes.html#758" class="Function Operator">̇</a> <a id="915" class="Symbol">}</a> <a id="917" class="Symbol">{</a><a id="918" href="UALib.Algebras.Signatures.html#918" class="Bound">A</a> <a id="920" class="Symbol">:</a> <a id="922" href="UALib.Algebras.Signatures.html#777" class="Bound">𝓤</a> <a id="924" href="universes.html#758" class="Function Operator">̇</a> <a id="926" class="Symbol">}</a> <a id="928" class="Symbol">→</a> <a id="930" href="UALib.Algebras.Signatures.html#907" class="Bound">I</a> <a id="932" class="Symbol">→</a> <a id="934" href="UALib.Algebras.Signatures.html#825" class="Function">Op</a> <a id="937" href="UALib.Algebras.Signatures.html#907" class="Bound">I</a> <a id="939" href="UALib.Algebras.Signatures.html#918" class="Bound">A</a>
 <a id="942" href="UALib.Algebras.Signatures.html#902" class="Function">π</a> <a id="944" href="UALib.Algebras.Signatures.html#944" class="Bound">i</a> <a id="946" href="UALib.Algebras.Signatures.html#946" class="Bound">x</a> <a id="948" class="Symbol">=</a> <a id="950" href="UALib.Algebras.Signatures.html#946" class="Bound">x</a> <a id="952" href="UALib.Algebras.Signatures.html#944" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.

-----------------------------------

#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1457" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="1467" class="Symbol">:</a> <a id="1469" class="Symbol">(</a><a id="1470" href="UALib.Algebras.Signatures.html#1470" class="Bound">𝓞</a> <a id="1472" href="UALib.Algebras.Signatures.html#1472" class="Bound">𝓥</a> <a id="1474" class="Symbol">:</a> <a id="1476" href="universes.html#551" class="Postulate">Universe</a><a id="1484" class="Symbol">)</a> <a id="1486" class="Symbol">→</a> <a id="1488" class="Symbol">(</a><a id="1489" href="UALib.Algebras.Signatures.html#1470" class="Bound">𝓞</a> <a id="1491" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1493" href="UALib.Algebras.Signatures.html#1472" class="Bound">𝓥</a><a id="1494" class="Symbol">)</a> <a id="1496" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1498" href="universes.html#758" class="Function Operator">̇</a>
<a id="1500" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="1510" href="UALib.Algebras.Signatures.html#1510" class="Bound">𝓞</a> <a id="1512" href="UALib.Algebras.Signatures.html#1512" class="Bound">𝓥</a> <a id="1514" class="Symbol">=</a> <a id="1516" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1518" href="UALib.Algebras.Signatures.html#1518" class="Bound">F</a> <a id="1520" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1522" href="UALib.Algebras.Signatures.html#1510" class="Bound">𝓞</a> <a id="1524" href="universes.html#758" class="Function Operator">̇</a> <a id="1526" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1528" class="Symbol">(</a><a id="1529" href="UALib.Algebras.Signatures.html#1518" class="Bound">F</a> <a id="1531" class="Symbol">→</a> <a id="1533" href="UALib.Algebras.Signatures.html#1512" class="Bound">𝓥</a> <a id="1535" href="universes.html#758" class="Function Operator">̇</a><a id="1536" class="Symbol">)</a>

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

<a id="2345" class="Keyword">module</a> <a id="2352" href="UALib.Algebras.Signatures.html#2352" class="Module">_</a> <a id="2354" class="Symbol">{</a><a id="2355" href="UALib.Algebras.Signatures.html#2355" class="Bound">𝓞</a> <a id="2357" class="Symbol">:</a> <a id="2359" href="universes.html#551" class="Postulate">Universe</a><a id="2367" class="Symbol">}</a> <a id="2369" class="Keyword">where</a>

 <a id="2377" class="Keyword">data</a> <a id="2382" href="UALib.Algebras.Signatures.html#2382" class="Datatype">monoid-op</a> <a id="2392" class="Symbol">:</a> <a id="2394" href="UALib.Algebras.Signatures.html#2355" class="Bound">𝓞</a> <a id="2396" href="universes.html#758" class="Function Operator">̇</a> <a id="2398" class="Keyword">where</a>
  <a id="2406" href="UALib.Algebras.Signatures.html#2406" class="InductiveConstructor">e</a> <a id="2408" class="Symbol">:</a> <a id="2410" href="UALib.Algebras.Signatures.html#2382" class="Datatype">monoid-op</a>
  <a id="2422" href="UALib.Algebras.Signatures.html#2422" class="InductiveConstructor">·</a> <a id="2424" class="Symbol">:</a> <a id="2426" href="UALib.Algebras.Signatures.html#2382" class="Datatype">monoid-op</a>

 <a id="2438" href="UALib.Algebras.Signatures.html#2438" class="Function">monoid-sig</a> <a id="2449" class="Symbol">:</a> <a id="2451" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="2461" href="UALib.Algebras.Signatures.html#2355" class="Bound">𝓞</a> <a id="2463" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2467" href="UALib.Algebras.Signatures.html#2438" class="Function">monoid-sig</a> <a id="2478" class="Symbol">=</a> <a id="2480" href="UALib.Algebras.Signatures.html#2382" class="Datatype">monoid-op</a> <a id="2490" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="2492" class="Symbol">λ</a> <a id="2494" class="Symbol">{</a> <a id="2496" href="UALib.Algebras.Signatures.html#2406" class="InductiveConstructor">e</a> <a id="2498" class="Symbol">→</a> <a id="2500" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2501" class="Symbol">;</a> <a id="2503" href="UALib.Algebras.Signatures.html#2422" class="InductiveConstructor">·</a> <a id="2505" class="Symbol">→</a> <a id="2507" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2509" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Algebras](UALib.Algebras.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

