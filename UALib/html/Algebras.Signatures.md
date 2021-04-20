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

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Relations.Extensionality.html" class="Module">Relations.Extensionality</a> <a id="473" class="Keyword">public</a>

</pre>


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.

<pre class="Agda">

<a id="Signature"></a><a id="626" href="Algebras.Signatures.html#626" class="Function">Signature</a> <a id="636" class="Symbol">:</a> <a id="638" class="Symbol">(</a><a id="639" href="Algebras.Signatures.html#639" class="Bound">𝓞</a> <a id="641" href="Algebras.Signatures.html#641" class="Bound">𝓥</a> <a id="643" class="Symbol">:</a> <a id="645" href="Universes.html#205" class="Postulate">Universe</a><a id="653" class="Symbol">)</a> <a id="655" class="Symbol">→</a> <a id="657" class="Symbol">(</a><a id="658" href="Algebras.Signatures.html#639" class="Bound">𝓞</a> <a id="660" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="662" href="Algebras.Signatures.html#641" class="Bound">𝓥</a><a id="663" class="Symbol">)</a> <a id="665" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="667" href="Universes.html#403" class="Function Operator">̇</a>
<a id="669" href="Algebras.Signatures.html#626" class="Function">Signature</a> <a id="679" href="Algebras.Signatures.html#679" class="Bound">𝓞</a> <a id="681" href="Algebras.Signatures.html#681" class="Bound">𝓥</a> <a id="683" class="Symbol">=</a> <a id="685" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="687" href="Algebras.Signatures.html#687" class="Bound">F</a> <a id="689" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="691" href="Algebras.Signatures.html#679" class="Bound">𝓞</a> <a id="693" href="Universes.html#403" class="Function Operator">̇</a> <a id="695" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="697" class="Symbol">(</a><a id="698" href="Algebras.Signatures.html#687" class="Bound">F</a> <a id="700" class="Symbol">→</a> <a id="702" href="Algebras.Signatures.html#681" class="Bound">𝓥</a> <a id="704" href="Universes.html#403" class="Function Operator">̇</a><a id="705" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Discrete][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="1373" class="Keyword">data</a> <a id="monoid-op"></a><a id="1378" href="Algebras.Signatures.html#1378" class="Datatype">monoid-op</a> <a id="1388" class="Symbol">{</a><a id="1389" href="Algebras.Signatures.html#1389" class="Bound">𝓞</a> <a id="1391" class="Symbol">:</a> <a id="1393" href="Universes.html#205" class="Postulate">Universe</a><a id="1401" class="Symbol">}</a> <a id="1403" class="Symbol">:</a> <a id="1405" href="Algebras.Signatures.html#1389" class="Bound">𝓞</a> <a id="1407" href="Universes.html#403" class="Function Operator">̇</a> <a id="1409" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="1416" href="Algebras.Signatures.html#1416" class="InductiveConstructor">e</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="Algebras.Signatures.html#1378" class="Datatype">monoid-op</a><a id="1429" class="Symbol">;</a> <a id="monoid-op.·"></a><a id="1431" href="Algebras.Signatures.html#1431" class="InductiveConstructor">·</a> <a id="1433" class="Symbol">:</a> <a id="1435" href="Algebras.Signatures.html#1378" class="Datatype">monoid-op</a>

<a id="1446" class="Keyword">open</a> <a id="1451" class="Keyword">import</a> <a id="1458" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1467" class="Keyword">using</a> <a id="1473" class="Symbol">(</a><a id="1474" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1475" class="Symbol">;</a> <a id="1477" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="1478" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="1481" href="Algebras.Signatures.html#1481" class="Function">monoid-sig</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="Algebras.Signatures.html#626" class="Function">Signature</a> <a id="1504" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="1506" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="1509" href="Algebras.Signatures.html#1481" class="Function">monoid-sig</a> <a id="1520" class="Symbol">=</a> <a id="1522" href="Algebras.Signatures.html#1378" class="Datatype">monoid-op</a> <a id="1532" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="1534" class="Symbol">λ</a> <a id="1536" class="Symbol">{</a> <a id="1538" href="Algebras.Signatures.html#1416" class="InductiveConstructor">e</a> <a id="1540" class="Symbol">→</a> <a id="1542" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="1543" class="Symbol">;</a> <a id="1545" href="Algebras.Signatures.html#1431" class="InductiveConstructor">·</a> <a id="1547" class="Symbol">→</a> <a id="1549" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="1551" class="Symbol">}</a>

</pre>

Thus, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

