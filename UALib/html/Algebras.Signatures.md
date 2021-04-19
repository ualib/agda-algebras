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

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Relations.RelExtensionality.html" class="Module">Relations.RelExtensionality</a> <a id="476" class="Keyword">public</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.

<pre class="Agda">

<a id="Signature"></a><a id="629" href="Algebras.Signatures.html#629" class="Function">Signature</a> <a id="639" class="Symbol">:</a> <a id="641" class="Symbol">(</a><a id="642" href="Algebras.Signatures.html#642" class="Bound">𝓞</a> <a id="644" href="Algebras.Signatures.html#644" class="Bound">𝓥</a> <a id="646" class="Symbol">:</a> <a id="648" href="Universes.html#205" class="Postulate">Universe</a><a id="656" class="Symbol">)</a> <a id="658" class="Symbol">→</a> <a id="660" class="Symbol">(</a><a id="661" href="Algebras.Signatures.html#642" class="Bound">𝓞</a> <a id="663" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="665" href="Algebras.Signatures.html#644" class="Bound">𝓥</a><a id="666" class="Symbol">)</a> <a id="668" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="670" href="Universes.html#403" class="Function Operator">̇</a>
<a id="672" href="Algebras.Signatures.html#629" class="Function">Signature</a> <a id="682" href="Algebras.Signatures.html#682" class="Bound">𝓞</a> <a id="684" href="Algebras.Signatures.html#684" class="Bound">𝓥</a> <a id="686" class="Symbol">=</a> <a id="688" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="690" href="Algebras.Signatures.html#690" class="Bound">F</a> <a id="692" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="694" href="Algebras.Signatures.html#682" class="Bound">𝓞</a> <a id="696" href="Universes.html#403" class="Function Operator">̇</a> <a id="698" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="700" class="Symbol">(</a><a id="701" href="Algebras.Signatures.html#690" class="Bound">F</a> <a id="703" class="Symbol">→</a> <a id="705" href="Algebras.Signatures.html#684" class="Bound">𝓥</a> <a id="707" href="Universes.html#403" class="Function Operator">̇</a><a id="708" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Discrete][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1376" class="Keyword">data</a> <a id="monoid-op"></a><a id="1381" href="Algebras.Signatures.html#1381" class="Datatype">monoid-op</a> <a id="1391" class="Symbol">{</a><a id="1392" href="Algebras.Signatures.html#1392" class="Bound">𝓞</a> <a id="1394" class="Symbol">:</a> <a id="1396" href="Universes.html#205" class="Postulate">Universe</a><a id="1404" class="Symbol">}</a> <a id="1406" class="Symbol">:</a> <a id="1408" href="Algebras.Signatures.html#1392" class="Bound">𝓞</a> <a id="1410" href="Universes.html#403" class="Function Operator">̇</a> <a id="1412" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="1419" href="Algebras.Signatures.html#1419" class="InductiveConstructor">e</a> <a id="1421" class="Symbol">:</a> <a id="1423" href="Algebras.Signatures.html#1381" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="1434" href="Algebras.Signatures.html#1434" class="InductiveConstructor">·</a> <a id="1436" class="Symbol">:</a> <a id="1438" href="Algebras.Signatures.html#1381" class="Datatype">monoid-op</a>

<a id="1449" class="Keyword">open</a> <a id="1454" class="Keyword">import</a> <a id="1461" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1470" class="Keyword">using</a> <a id="1476" class="Symbol">(</a><a id="1477" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1478" class="Symbol">;</a> <a id="1480" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="1481" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="1484" href="Algebras.Signatures.html#1484" class="Function">monoid-sig</a> <a id="1495" class="Symbol">:</a> <a id="1497" href="Algebras.Signatures.html#629" class="Function">Signature</a> <a id="1507" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="1509" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="1512" href="Algebras.Signatures.html#1484" class="Function">monoid-sig</a> <a id="1523" class="Symbol">=</a> <a id="1525" href="Algebras.Signatures.html#1381" class="Datatype">monoid-op</a> <a id="1535" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="1537" class="Symbol">λ</a> <a id="1539" class="Symbol">{</a> <a id="1541" href="Algebras.Signatures.html#1419" class="InductiveConstructor">e</a> <a id="1543" class="Symbol">→</a> <a id="1545" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1546" class="Symbol">;</a> <a id="1548" href="Algebras.Signatures.html#1434" class="InductiveConstructor">·</a> <a id="1550" class="Symbol">→</a> <a id="1552" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="1554" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

