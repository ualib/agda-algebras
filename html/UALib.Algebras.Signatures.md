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

<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="universes.html" class="Module">universes</a> <a id="402" class="Keyword">using</a> <a id="408" class="Symbol">(</a><a id="409" href="universes.html#504" class="Primitive">𝓤₀</a><a id="411" class="Symbol">)</a>

<a id="414" class="Keyword">module</a> <a id="421" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="447" class="Keyword">where</a>

<a id="454" class="Keyword">open</a> <a id="459" class="Keyword">import</a> <a id="466" href="UALib.Relations.Quotients.html" class="Module">UALib.Relations.Quotients</a> <a id="492" class="Keyword">public</a>

<a id="500" class="Keyword">open</a> <a id="505" class="Keyword">import</a> <a id="512" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="540" class="Keyword">using</a> <a id="546" class="Symbol">(</a><a id="547" href="universes.html#613" class="Generalizable">𝓞</a><a id="548" class="Symbol">;</a> <a id="550" href="universes.html#617" class="Generalizable">𝓥</a><a id="551" class="Symbol">;</a> <a id="553" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="554" class="Symbol">;</a> <a id="556" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="557" class="Symbol">)</a> <a id="559" class="Keyword">public</a>

</pre>



#### <a id="operation-type">Operation type</a>

We define the type of **operations**, and give an example (the projections).

<pre class="Agda">

<a id="721" class="Keyword">module</a> <a id="728" href="UALib.Algebras.Signatures.html#728" class="Module">_</a> <a id="730" class="Symbol">{</a><a id="731" href="UALib.Algebras.Signatures.html#731" class="Bound">𝓤</a> <a id="733" class="Symbol">:</a> <a id="735" href="universes.html#551" class="Postulate">Universe</a><a id="743" class="Symbol">}</a> <a id="745" class="Keyword">where</a>

 <a id="753" class="Comment">--The type of operations</a>
 <a id="779" href="UALib.Algebras.Signatures.html#779" class="Function">Op</a> <a id="782" class="Symbol">:</a> <a id="784" href="universes.html#617" class="Generalizable">𝓥</a> <a id="786" href="universes.html#758" class="Function Operator">̇</a> <a id="788" class="Symbol">→</a> <a id="790" href="UALib.Algebras.Signatures.html#731" class="Bound">𝓤</a> <a id="792" href="universes.html#758" class="Function Operator">̇</a> <a id="794" class="Symbol">→</a> <a id="796" href="UALib.Algebras.Signatures.html#731" class="Bound">𝓤</a> <a id="798" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="800" href="universes.html#617" class="Generalizable">𝓥</a> <a id="802" href="universes.html#758" class="Function Operator">̇</a>
 <a id="805" href="UALib.Algebras.Signatures.html#779" class="Function">Op</a> <a id="808" href="UALib.Algebras.Signatures.html#808" class="Bound">I</a> <a id="810" href="UALib.Algebras.Signatures.html#810" class="Bound">A</a> <a id="812" class="Symbol">=</a> <a id="814" class="Symbol">(</a><a id="815" href="UALib.Algebras.Signatures.html#808" class="Bound">I</a> <a id="817" class="Symbol">→</a> <a id="819" href="UALib.Algebras.Signatures.html#810" class="Bound">A</a><a id="820" class="Symbol">)</a> <a id="822" class="Symbol">→</a> <a id="824" href="UALib.Algebras.Signatures.html#810" class="Bound">A</a>

 <a id="828" class="Comment">--Example. the projections</a>
 <a id="856" href="UALib.Algebras.Signatures.html#856" class="Function">π</a> <a id="858" class="Symbol">:</a> <a id="860" class="Symbol">{</a><a id="861" href="UALib.Algebras.Signatures.html#861" class="Bound">I</a> <a id="863" class="Symbol">:</a> <a id="865" href="universes.html#617" class="Generalizable">𝓥</a> <a id="867" href="universes.html#758" class="Function Operator">̇</a> <a id="869" class="Symbol">}</a> <a id="871" class="Symbol">{</a><a id="872" href="UALib.Algebras.Signatures.html#872" class="Bound">A</a> <a id="874" class="Symbol">:</a> <a id="876" href="UALib.Algebras.Signatures.html#731" class="Bound">𝓤</a> <a id="878" href="universes.html#758" class="Function Operator">̇</a> <a id="880" class="Symbol">}</a> <a id="882" class="Symbol">→</a> <a id="884" href="UALib.Algebras.Signatures.html#861" class="Bound">I</a> <a id="886" class="Symbol">→</a> <a id="888" href="UALib.Algebras.Signatures.html#779" class="Function">Op</a> <a id="891" href="UALib.Algebras.Signatures.html#861" class="Bound">I</a> <a id="893" href="UALib.Algebras.Signatures.html#872" class="Bound">A</a>
 <a id="896" href="UALib.Algebras.Signatures.html#856" class="Function">π</a> <a id="898" href="UALib.Algebras.Signatures.html#898" class="Bound">i</a> <a id="900" href="UALib.Algebras.Signatures.html#900" class="Bound">x</a> <a id="902" class="Symbol">=</a> <a id="904" href="UALib.Algebras.Signatures.html#900" class="Bound">x</a> <a id="906" href="UALib.Algebras.Signatures.html#898" class="Bound">i</a>

</pre>

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.




#### <a id="signature-type">Signature type</a>

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">

<a id="Signature"></a><a id="1377" href="UALib.Algebras.Signatures.html#1377" class="Function">Signature</a> <a id="1387" class="Symbol">:</a> <a id="1389" class="Symbol">(</a><a id="1390" href="UALib.Algebras.Signatures.html#1390" class="Bound">𝓞</a> <a id="1392" href="UALib.Algebras.Signatures.html#1392" class="Bound">𝓥</a> <a id="1394" class="Symbol">:</a> <a id="1396" href="universes.html#551" class="Postulate">Universe</a><a id="1404" class="Symbol">)</a> <a id="1406" class="Symbol">→</a> <a id="1408" class="Symbol">(</a><a id="1409" href="UALib.Algebras.Signatures.html#1390" class="Bound">𝓞</a> <a id="1411" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1413" href="UALib.Algebras.Signatures.html#1392" class="Bound">𝓥</a><a id="1414" class="Symbol">)</a> <a id="1416" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1418" href="universes.html#758" class="Function Operator">̇</a>
<a id="1420" href="UALib.Algebras.Signatures.html#1377" class="Function">Signature</a> <a id="1430" href="UALib.Algebras.Signatures.html#1430" class="Bound">𝓞</a> <a id="1432" href="UALib.Algebras.Signatures.html#1432" class="Bound">𝓥</a> <a id="1434" class="Symbol">=</a> <a id="1436" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1438" href="UALib.Algebras.Signatures.html#1438" class="Bound">F</a> <a id="1440" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1442" href="UALib.Algebras.Signatures.html#1430" class="Bound">𝓞</a> <a id="1444" href="universes.html#758" class="Function Operator">̇</a> <a id="1446" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1448" class="Symbol">(</a><a id="1449" href="UALib.Algebras.Signatures.html#1438" class="Bound">F</a> <a id="1451" class="Symbol">→</a> <a id="1453" href="UALib.Algebras.Signatures.html#1432" class="Bound">𝓥</a> <a id="1455" href="universes.html#758" class="Function Operator">̇</a><a id="1456" class="Symbol">)</a>

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

<a id="2229" class="Keyword">module</a> <a id="2236" href="UALib.Algebras.Signatures.html#2236" class="Module">_</a> <a id="2238" class="Symbol">{</a><a id="2239" href="UALib.Algebras.Signatures.html#2239" class="Bound">𝓞</a> <a id="2241" class="Symbol">:</a> <a id="2243" href="universes.html#551" class="Postulate">Universe</a><a id="2251" class="Symbol">}</a> <a id="2253" class="Keyword">where</a>

 <a id="2261" class="Keyword">data</a> <a id="2266" href="UALib.Algebras.Signatures.html#2266" class="Datatype">monoid-op</a> <a id="2276" class="Symbol">:</a> <a id="2278" href="UALib.Algebras.Signatures.html#2239" class="Bound">𝓞</a> <a id="2280" href="universes.html#758" class="Function Operator">̇</a> <a id="2282" class="Keyword">where</a>
  <a id="2290" href="UALib.Algebras.Signatures.html#2290" class="InductiveConstructor">e</a> <a id="2292" class="Symbol">:</a> <a id="2294" href="UALib.Algebras.Signatures.html#2266" class="Datatype">monoid-op</a>
  <a id="2306" href="UALib.Algebras.Signatures.html#2306" class="InductiveConstructor">·</a> <a id="2308" class="Symbol">:</a> <a id="2310" href="UALib.Algebras.Signatures.html#2266" class="Datatype">monoid-op</a>

 <a id="2322" href="UALib.Algebras.Signatures.html#2322" class="Function">monoid-sig</a> <a id="2333" class="Symbol">:</a> <a id="2335" href="UALib.Algebras.Signatures.html#1377" class="Function">Signature</a> <a id="2345" href="UALib.Algebras.Signatures.html#2239" class="Bound">𝓞</a> <a id="2347" href="universes.html#504" class="Primitive">𝓤₀</a>
 <a id="2351" href="UALib.Algebras.Signatures.html#2322" class="Function">monoid-sig</a> <a id="2362" class="Symbol">=</a> <a id="2364" href="UALib.Algebras.Signatures.html#2266" class="Datatype">monoid-op</a> <a id="2374" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="2376" class="Symbol">λ</a> <a id="2378" class="Symbol">{</a> <a id="2380" href="UALib.Algebras.Signatures.html#2290" class="InductiveConstructor">e</a> <a id="2382" class="Symbol">→</a> <a id="2384" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2385" class="Symbol">;</a> <a id="2387" href="UALib.Algebras.Signatures.html#2306" class="InductiveConstructor">·</a> <a id="2389" class="Symbol">→</a> <a id="2391" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="2393" class="Symbol">}</a>

</pre>

As expected, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).

-------------------------------------

[← UALib.Algebras](UALib.Algebras.html)
<span style="float:right;">[UALib.Algebras.Algebras →](UALib.Algebras.Algebras.html)</span>


{% include UALib.Links.md %}

