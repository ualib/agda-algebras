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


In the [Relations.Continuous][] module we defined the type of *operations* on a domain of some type. Since nothing else (besides the operation type) is needed in other [UALib][] modules, we redefine the operation type here.  The semantics of this type is explained below.

<pre class="Agda">

<a id="777" class="Comment">--The type of operations</a>
<a id="Op"></a><a id="802" href="Algebras.Signatures.html#802" class="Function">Op</a> <a id="805" class="Symbol">:</a> <a id="807" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="809" href="Universes.html#403" class="Function Operator">̇</a> <a id="811" class="Symbol">→</a> <a id="813" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="815" href="Universes.html#403" class="Function Operator">̇</a> <a id="817" class="Symbol">→</a> <a id="819" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="821" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="823" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="825" href="Universes.html#403" class="Function Operator">̇</a>
<a id="827" href="Algebras.Signatures.html#802" class="Function">Op</a> <a id="830" href="Algebras.Signatures.html#830" class="Bound">I</a> <a id="832" href="Algebras.Signatures.html#832" class="Bound">A</a> <a id="834" class="Symbol">=</a> <a id="836" class="Symbol">(</a><a id="837" href="Algebras.Signatures.html#830" class="Bound">I</a> <a id="839" class="Symbol">→</a> <a id="841" href="Algebras.Signatures.html#832" class="Bound">A</a><a id="842" class="Symbol">)</a> <a id="844" class="Symbol">→</a> <a id="846" href="Algebras.Signatures.html#832" class="Bound">A</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.


#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1336" href="Algebras.Signatures.html#1336" class="Function">Signature</a> <a id="1346" class="Symbol">:</a> <a id="1348" class="Symbol">(</a><a id="1349" href="Algebras.Signatures.html#1349" class="Bound">𝓞</a> <a id="1351" href="Algebras.Signatures.html#1351" class="Bound">𝓥</a> <a id="1353" class="Symbol">:</a> <a id="1355" href="Universes.html#205" class="Postulate">Universe</a><a id="1363" class="Symbol">)</a> <a id="1365" class="Symbol">→</a> <a id="1367" class="Symbol">(</a><a id="1368" href="Algebras.Signatures.html#1349" class="Bound">𝓞</a> <a id="1370" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1372" href="Algebras.Signatures.html#1351" class="Bound">𝓥</a><a id="1373" class="Symbol">)</a> <a id="1375" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="1377" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1379" href="Algebras.Signatures.html#1336" class="Function">Signature</a> <a id="1389" href="Algebras.Signatures.html#1389" class="Bound">𝓞</a> <a id="1391" href="Algebras.Signatures.html#1391" class="Bound">𝓥</a> <a id="1393" class="Symbol">=</a> <a id="1395" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1397" href="Algebras.Signatures.html#1397" class="Bound">F</a> <a id="1399" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1401" href="Algebras.Signatures.html#1389" class="Bound">𝓞</a> <a id="1403" href="Universes.html#403" class="Function Operator">̇</a> <a id="1405" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1407" class="Symbol">(</a><a id="1408" href="Algebras.Signatures.html#1397" class="Bound">F</a> <a id="1410" class="Symbol">→</a> <a id="1412" href="Algebras.Signatures.html#1391" class="Bound">𝓥</a> <a id="1414" href="Universes.html#403" class="Function Operator">̇</a><a id="1415" class="Symbol">)</a>

</pre>

As mentioned in the [Relations.Continuous][] module, 𝓞 will always denote the universe of *operation symbol* types, while 𝓥 is the universe of *arity* types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



#### <a id="Example">Example</a>

Here is how we could define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2085" class="Keyword">data</a> <a id="monoid-op"></a><a id="2090" href="Algebras.Signatures.html#2090" class="Datatype">monoid-op</a> <a id="2100" class="Symbol">{</a><a id="2101" href="Algebras.Signatures.html#2101" class="Bound">𝓞</a> <a id="2103" class="Symbol">:</a> <a id="2105" href="Universes.html#205" class="Postulate">Universe</a><a id="2113" class="Symbol">}</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="Algebras.Signatures.html#2101" class="Bound">𝓞</a> <a id="2119" href="Universes.html#403" class="Function Operator">̇</a> <a id="2121" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="2128" href="Algebras.Signatures.html#2128" class="InductiveConstructor">e</a> <a id="2130" class="Symbol">:</a> <a id="2132" href="Algebras.Signatures.html#2090" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="2143" href="Algebras.Signatures.html#2143" class="InductiveConstructor">·</a> <a id="2145" class="Symbol">:</a> <a id="2147" href="Algebras.Signatures.html#2090" class="Datatype">monoid-op</a>

<a id="2158" class="Keyword">open</a> <a id="2163" class="Keyword">import</a> <a id="2170" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2179" class="Keyword">using</a> <a id="2185" class="Symbol">(</a><a id="2186" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2187" class="Symbol">;</a> <a id="2189" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2190" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="2193" href="Algebras.Signatures.html#2193" class="Function">monoid-sig</a> <a id="2204" class="Symbol">:</a> <a id="2206" href="Algebras.Signatures.html#1336" class="Function">Signature</a> <a id="2216" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="2218" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="2221" href="Algebras.Signatures.html#2193" class="Function">monoid-sig</a> <a id="2232" class="Symbol">=</a> <a id="2234" href="Algebras.Signatures.html#2090" class="Datatype">monoid-op</a> <a id="2244" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a> <a id="2246" class="Symbol">λ</a> <a id="2248" class="Symbol">{</a> <a id="2250" href="Algebras.Signatures.html#2128" class="InductiveConstructor">e</a> <a id="2252" class="Symbol">→</a> <a id="2254" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2255" class="Symbol">;</a> <a id="2257" href="Algebras.Signatures.html#2143" class="InductiveConstructor">·</a> <a id="2259" class="Symbol">→</a> <a id="2261" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2263" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[↑ Algebras](Algebras.html)
<span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

