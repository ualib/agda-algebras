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


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.

<pre class="Agda">

<a id="Signature"></a><a id="622" href="Algebras.Signatures.html#622" class="Function">Signature</a> <a id="632" class="Symbol">:</a> <a id="634" class="Symbol">(</a><a id="635" href="Algebras.Signatures.html#635" class="Bound">𝓞</a> <a id="637" href="Algebras.Signatures.html#637" class="Bound">𝓥</a> <a id="639" class="Symbol">:</a> <a id="641" href="Universes.html#205" class="Postulate">Universe</a><a id="649" class="Symbol">)</a> <a id="651" class="Symbol">→</a> <a id="653" class="Symbol">(</a><a id="654" href="Algebras.Signatures.html#635" class="Bound">𝓞</a> <a id="656" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="658" href="Algebras.Signatures.html#637" class="Bound">𝓥</a><a id="659" class="Symbol">)</a> <a id="661" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="663" href="Universes.html#403" class="Function Operator">̇</a>
<a id="665" href="Algebras.Signatures.html#622" class="Function">Signature</a> <a id="675" href="Algebras.Signatures.html#675" class="Bound">𝓞</a> <a id="677" href="Algebras.Signatures.html#677" class="Bound">𝓥</a> <a id="679" class="Symbol">=</a> <a id="681" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="683" href="Algebras.Signatures.html#683" class="Bound">F</a> <a id="685" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="687" href="Algebras.Signatures.html#675" class="Bound">𝓞</a> <a id="689" href="Universes.html#403" class="Function Operator">̇</a> <a id="691" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="693" class="Symbol">(</a><a id="694" href="Algebras.Signatures.html#683" class="Bound">F</a> <a id="696" class="Symbol">→</a> <a id="698" href="Algebras.Signatures.html#677" class="Bound">𝓥</a> <a id="700" href="Universes.html#403" class="Function Operator">̇</a><a id="701" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Discrete][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1369" class="Keyword">data</a> <a id="monoid-op"></a><a id="1374" href="Algebras.Signatures.html#1374" class="Datatype">monoid-op</a> <a id="1384" class="Symbol">{</a><a id="1385" href="Algebras.Signatures.html#1385" class="Bound">𝓞</a> <a id="1387" class="Symbol">:</a> <a id="1389" href="Universes.html#205" class="Postulate">Universe</a><a id="1397" class="Symbol">}</a> <a id="1399" class="Symbol">:</a> <a id="1401" href="Algebras.Signatures.html#1385" class="Bound">𝓞</a> <a id="1403" href="Universes.html#403" class="Function Operator">̇</a> <a id="1405" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="1412" href="Algebras.Signatures.html#1412" class="InductiveConstructor">e</a> <a id="1414" class="Symbol">:</a> <a id="1416" href="Algebras.Signatures.html#1374" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="1427" href="Algebras.Signatures.html#1427" class="InductiveConstructor">·</a> <a id="1429" class="Symbol">:</a> <a id="1431" href="Algebras.Signatures.html#1374" class="Datatype">monoid-op</a>

<a id="1442" class="Keyword">open</a> <a id="1447" class="Keyword">import</a> <a id="1454" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1463" class="Keyword">using</a> <a id="1469" class="Symbol">(</a><a id="1470" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1471" class="Symbol">;</a> <a id="1473" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="1474" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="1477" href="Algebras.Signatures.html#1477" class="Function">monoid-sig</a> <a id="1488" class="Symbol">:</a> <a id="1490" href="Algebras.Signatures.html#622" class="Function">Signature</a> <a id="1500" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="1502" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="1505" href="Algebras.Signatures.html#1477" class="Function">monoid-sig</a> <a id="1516" class="Symbol">=</a> <a id="1518" href="Algebras.Signatures.html#1374" class="Datatype">monoid-op</a> <a id="1528" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="1530" class="Symbol">λ</a> <a id="1532" class="Symbol">{</a> <a id="1534" href="Algebras.Signatures.html#1412" class="InductiveConstructor">e</a> <a id="1536" class="Symbol">→</a> <a id="1538" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1539" class="Symbol">;</a> <a id="1541" href="Algebras.Signatures.html#1427" class="InductiveConstructor">·</a> <a id="1543" class="Symbol">→</a> <a id="1545" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="1547" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

