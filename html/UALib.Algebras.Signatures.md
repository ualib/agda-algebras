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



#### <a id="operation-type">Operation type</a>

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="729" class="Keyword">module</a> <a id="736" href="UALib.Algebras.Signatures.html#736" class="Module">_</a> <a id="738" class="Symbol">{</a><a id="739" href="UALib.Algebras.Signatures.html#739" class="Bound">𝓤</a> <a id="741" class="Symbol">:</a> <a id="743" href="universes.html#551" class="Postulate">Universe</a><a id="751" class="Symbol">}</a> <a id="753" class="Keyword">where</a>

 <a id="761" class="Comment">--The type of operations</a>
 <a id="787" href="UALib.Algebras.Signatures.html#787" class="Function">Op</a> <a id="790" class="Symbol">:</a> <a id="792" href="universes.html#617" class="Generalizable">𝓥</a> <a id="794" href="universes.html#758" class="Function Operator">̇</a> <a id="796" class="Symbol">→</a> <a id="798" href="UALib.Algebras.Signatures.html#739" class="Bound">𝓤</a> <a id="800" href="universes.html#758" class="Function Operator">̇</a> <a id="802" class="Symbol">→</a> <a id="804" href="UALib.Algebras.Signatures.html#739" class="Bound">𝓤</a> <a id="806" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="808" href="universes.html#617" class="Generalizable">𝓥</a> <a id="810" href="universes.html#758" class="Function Operator">̇</a>
 <a id="813" href="UALib.Algebras.Signatures.html#787" class="Function">Op</a> <a id="816" href="UALib.Algebras.Signatures.html#816" class="Bound">I</a> <a id="818" href="UALib.Algebras.Signatures.html#818" class="Bound">A</a> <a id="820" class="Symbol">=</a> <a id="822" class="Symbol">(</a><a id="823" href="UALib.Algebras.Signatures.html#816" class="Bound">I</a> <a id="825" class="Symbol">→</a> <a id="827" href="UALib.Algebras.Signatures.html#818" class="Bound">A</a><a id="828" class="Symbol">)</a> <a id="830" class="Symbol">→</a> <a id="832" href="UALib.Algebras.Signatures.html#818" class="Bound">A</a>

 <a id="836" class="Comment">--Example. the projections</a>
 <a id="864" href="UALib.Algebras.Signatures.html#864" class="Function">π</a> <a id="866" class="Symbol">:</a> <a id="868" class="Symbol">{</a><a id="869" href="UALib.Algebras.Signatures.html#869" class="Bound">I</a> <a id="871" class="Symbol">:</a> <a id="873" href="universes.html#617" class="Generalizable">𝓥</a> <a id="875" href="universes.html#758" class="Function Operator">̇</a> <a id="877" class="Symbol">}</a> <a id="879" class="Symbol">{</a><a id="880" href="UALib.Algebras.Signatures.html#880" class="Bound">A</a> <a id="882" class="Symbol">:</a> <a id="884" href="UALib.Algebras.Signatures.html#739" class="Bound">𝓤</a> <a id="886" href="universes.html#758" class="Function Operator">̇</a> <a id="888" class="Symbol">}</a> <a id="890" class="Symbol">→</a> <a id="892" href="UALib.Algebras.Signatures.html#869" class="Bound">I</a> <a id="894" class="Symbol">→</a> <a id="896" href="UALib.Algebras.Signatures.html#787" class="Function">Op</a> <a id="899" href="UALib.Algebras.Signatures.html#869" class="Bound">I</a> <a id="901" href="UALib.Algebras.Signatures.html#880" class="Bound">A</a>
 <a id="904" href="UALib.Algebras.Signatures.html#864" class="Function">π</a> <a id="906" href="UALib.Algebras.Signatures.html#906" class="Bound">i</a> <a id="908" href="UALib.Algebras.Signatures.html#908" class="Bound">x</a> <a id="910" class="Symbol">=</a> <a id="912" href="UALib.Algebras.Signatures.html#908" class="Bound">x</a> <a id="914" href="UALib.Algebras.Signatures.html#906" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.




#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1385" href="UALib.Algebras.Signatures.html#1385" class="Function">Signature</a> <a id="1395" class="Symbol">:</a> <a id="1397" class="Symbol">(</a><a id="1398" href="UALib.Algebras.Signatures.html#1398" class="Bound">𝓞</a> <a id="1400" href="UALib.Algebras.Signatures.html#1400" class="Bound">𝓥</a> <a id="1402" class="Symbol">:</a> <a id="1404" href="universes.html#551" class="Postulate">Universe</a><a id="1412" class="Symbol">)</a> <a id="1414" class="Symbol">→</a> <a id="1416" class="Symbol">(</a><a id="1417" href="UALib.Algebras.Signatures.html#1398" class="Bound">𝓞</a> <a id="1419" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1421" href="UALib.Algebras.Signatures.html#1400" class="Bound">𝓥</a><a id="1422" class="Symbol">)</a> <a id="1424" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1426" href="universes.html#758" class="Function Operator">̇</a>
<a id="1428" href="UALib.Algebras.Signatures.html#1385" class="Function">Signature</a> <a id="1438" href="UALib.Algebras.Signatures.html#1438" class="Bound">𝓞</a> <a id="1440" href="UALib.Algebras.Signatures.html#1440" class="Bound">𝓥</a> <a id="1442" class="Symbol">=</a> <a id="1444" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1446" href="UALib.Algebras.Signatures.html#1446" class="Bound">F</a> <a id="1448" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1450" href="UALib.Algebras.Signatures.html#1438" class="Bound">𝓞</a> <a id="1452" href="universes.html#758" class="Function Operator">̇</a> <a id="1454" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1456" class="Symbol">(</a><a id="1457" href="UALib.Algebras.Signatures.html#1446" class="Bound">F</a> <a id="1459" class="Symbol">→</a> <a id="1461" href="UALib.Algebras.Signatures.html#1440" class="Bound">𝓥</a> <a id="1463" href="universes.html#758" class="Function Operator">̇</a><a id="1464" class="Symbol">)</a>

</pre>

Here 𝓞 is the universe level of operation symbol types, while 𝓥 is the universe level of arity types.

In the [UALib.Prelude][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.

For reference, we recall the definition of the Sigma type, `Σ`, which is

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```



#### <a id="Example">Example</a>

Here is how we might define the signature for monoids as a member of the type `Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="2237" class="Keyword">module</a> <a id="2244" href="UALib.Algebras.Signatures.html#2244" class="Module">_</a> <a id="2246" class="Symbol">{</a><a id="2247" href="UALib.Algebras.Signatures.html#2247" class="Bound">𝓞</a> <a id="2249" class="Symbol">:</a> <a id="2251" href="universes.html#551" class="Postulate">Universe</a><a id="2259" class="Symbol">}</a> <a id="2261" class="Keyword">where</a>

 <a id="2269" class="Keyword">data</a> <a id="2274" href="UALib.Algebras.Signatures.html#2274" class="Datatype">monoid-op</a> <a id="2284" class="Symbol">:</a> <a id="2286" href="UALib.Algebras.Signatures.html#2247" class="Bound">𝓞</a> <a id="2288" href="universes.html#758" class="Function Operator">̇</a> <a id="2290" class="Keyword">where</a>
  <a id="2298" href="UALib.Algebras.Signatures.html#2298" class="InductiveConstructor">e</a> <a id="2300" class="Symbol">:</a> <a id="2302" href="UALib.Algebras.Signatures.html#2274" class="Datatype">monoid-op</a>
  <a id="2314" href="UALib.Algebras.Signatures.html#2314" class="InductiveConstructor">·</a> <a id="2316" class="Symbol">:</a> <a id="2318" href="UALib.Algebras.Signatures.html#2274" class="Datatype">monoid-op</a>

 <a id="2330" href="UALib.Algebras.Signatures.html#2330" class="Function">monoid-sig</a> <a id="2341" class="Symbol">:</a> <a id="2343" href="UALib.Algebras.Signatures.html#1385" class="Function">Signature</a> <a id="2353" href="UALib.Algebras.Signatures.html#2247" class="Bound">𝓞</a> <a id="2355" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2359" href="UALib.Algebras.Signatures.html#2330" class="Function">monoid-sig</a> <a id="2370" class="Symbol">=</a> <a id="2372" href="UALib.Algebras.Signatures.html#2274" class="Datatype">monoid-op</a> <a id="2382" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="2384" class="Symbol">λ</a> <a id="2386" class="Symbol">{</a> <a id="2388" href="UALib.Algebras.Signatures.html#2298" class="InductiveConstructor">e</a> <a id="2390" class="Symbol">→</a> <a id="2392" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2393" class="Symbol">;</a> <a id="2395" href="UALib.Algebras.Signatures.html#2314" class="InductiveConstructor">·</a> <a id="2397" class="Symbol">→</a> <a id="2399" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2401" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Algebras](UALib.Algebras.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

