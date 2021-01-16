---
layout: default
title : UALib.Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="operation-and-signature-types">Operation and Signature Types</a>

This section presents the [UALib.Algebras.Signatures][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">
<a id="337" class="Symbol">{-#</a> <a id="341" class="Keyword">OPTIONS</a> <a id="349" class="Pragma">--without-K</a> <a id="361" class="Pragma">--exact-split</a> <a id="375" class="Pragma">--safe</a> <a id="382" class="Symbol">#-}</a>

<a id="387" class="Keyword">module</a> <a id="394" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="420" class="Keyword">where</a>

<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="UALib.Prelude.Extensionality.html" class="Module">UALib.Prelude.Extensionality</a> <a id="468" class="Keyword">public</a>

<a id="476" class="Keyword">module</a> <a id="483" href="UALib.Algebras.Signatures.html#483" class="Module">_</a> <a id="485" class="Symbol">{</a><a id="486" href="UALib.Algebras.Signatures.html#486" class="Bound">𝓤</a> <a id="488" href="UALib.Algebras.Signatures.html#488" class="Bound">𝓥</a> <a id="490" class="Symbol">:</a> <a id="492" href="universes.html#551" class="Postulate">Universe</a><a id="500" class="Symbol">}</a> <a id="502" class="Keyword">where</a>
 <a id="509" class="Comment">--The type of operations</a>
 <a id="535" href="UALib.Algebras.Signatures.html#535" class="Function">Op</a> <a id="538" class="Symbol">:</a> <a id="540" href="UALib.Algebras.Signatures.html#488" class="Bound">𝓥</a> <a id="542" href="universes.html#758" class="Function Operator">̇</a> <a id="544" class="Symbol">→</a> <a id="546" href="UALib.Algebras.Signatures.html#486" class="Bound">𝓤</a> <a id="548" href="universes.html#758" class="Function Operator">̇</a> <a id="550" class="Symbol">→</a> <a id="552" href="UALib.Algebras.Signatures.html#486" class="Bound">𝓤</a> <a id="554" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="556" href="UALib.Algebras.Signatures.html#488" class="Bound">𝓥</a> <a id="558" href="universes.html#758" class="Function Operator">̇</a>
 <a id="561" href="UALib.Algebras.Signatures.html#535" class="Function">Op</a> <a id="564" href="UALib.Algebras.Signatures.html#564" class="Bound">I</a> <a id="566" href="UALib.Algebras.Signatures.html#566" class="Bound">A</a> <a id="568" class="Symbol">=</a> <a id="570" class="Symbol">(</a><a id="571" href="UALib.Algebras.Signatures.html#564" class="Bound">I</a> <a id="573" class="Symbol">→</a> <a id="575" href="UALib.Algebras.Signatures.html#566" class="Bound">A</a><a id="576" class="Symbol">)</a> <a id="578" class="Symbol">→</a> <a id="580" href="UALib.Algebras.Signatures.html#566" class="Bound">A</a>

 <a id="584" class="Comment">--Example. the projections</a>
 <a id="612" href="UALib.Algebras.Signatures.html#612" class="Function">π</a> <a id="614" class="Symbol">:</a> <a id="616" class="Symbol">{</a><a id="617" href="UALib.Algebras.Signatures.html#617" class="Bound">I</a> <a id="619" class="Symbol">:</a> <a id="621" href="UALib.Algebras.Signatures.html#488" class="Bound">𝓥</a> <a id="623" href="universes.html#758" class="Function Operator">̇</a> <a id="625" class="Symbol">}</a> <a id="627" class="Symbol">{</a><a id="628" href="UALib.Algebras.Signatures.html#628" class="Bound">A</a> <a id="630" class="Symbol">:</a> <a id="632" href="UALib.Algebras.Signatures.html#486" class="Bound">𝓤</a> <a id="634" href="universes.html#758" class="Function Operator">̇</a> <a id="636" class="Symbol">}</a> <a id="638" class="Symbol">→</a> <a id="640" href="UALib.Algebras.Signatures.html#617" class="Bound">I</a> <a id="642" class="Symbol">→</a> <a id="644" href="UALib.Algebras.Signatures.html#535" class="Function">Op</a> <a id="647" href="UALib.Algebras.Signatures.html#617" class="Bound">I</a> <a id="649" href="UALib.Algebras.Signatures.html#628" class="Bound">A</a>
 <a id="652" href="UALib.Algebras.Signatures.html#612" class="Function">π</a> <a id="654" href="UALib.Algebras.Signatures.html#654" class="Bound">i</a> <a id="656" href="UALib.Algebras.Signatures.html#656" class="Bound">x</a> <a id="658" class="Symbol">=</a> <a id="660" href="UALib.Algebras.Signatures.html#656" class="Bound">x</a> <a id="662" href="UALib.Algebras.Signatures.html#654" class="Bound">i</a>

<a id="665" class="Comment">-- module _</a>
<a id="677" class="Comment">--  {𝓞  -- the universe in which operation symbols live</a>
<a id="733" class="Comment">--   𝓥 -- the universe in which arities live</a>
<a id="778" class="Comment">--   : Universe} where</a>

<a id="Signature"></a><a id="802" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="812" class="Symbol">:</a> <a id="814" class="Symbol">(</a><a id="815" href="UALib.Algebras.Signatures.html#815" class="Bound">𝓞</a> <a id="817" href="UALib.Algebras.Signatures.html#817" class="Bound">𝓥</a> <a id="819" class="Symbol">:</a> <a id="821" href="universes.html#551" class="Postulate">Universe</a><a id="829" class="Symbol">)</a> <a id="831" class="Symbol">→</a> <a id="833" class="Symbol">(</a><a id="834" href="UALib.Algebras.Signatures.html#815" class="Bound">𝓞</a> <a id="836" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="838" href="UALib.Algebras.Signatures.html#817" class="Bound">𝓥</a><a id="839" class="Symbol">)</a> <a id="841" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="843" href="universes.html#758" class="Function Operator">̇</a>
<a id="845" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="855" href="UALib.Algebras.Signatures.html#855" class="Bound">𝓞</a> <a id="857" href="UALib.Algebras.Signatures.html#857" class="Bound">𝓥</a> <a id="859" class="Symbol">=</a> <a id="861" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="863" href="UALib.Algebras.Signatures.html#863" class="Bound">F</a> <a id="865" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="867" href="UALib.Algebras.Signatures.html#855" class="Bound">𝓞</a> <a id="869" href="universes.html#758" class="Function Operator">̇</a> <a id="871" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="873" class="Symbol">(</a> <a id="875" href="UALib.Algebras.Signatures.html#863" class="Bound">F</a> <a id="877" class="Symbol">→</a> <a id="879" href="UALib.Algebras.Signatures.html#857" class="Bound">𝓥</a> <a id="881" href="universes.html#758" class="Function Operator">̇</a> <a id="883" class="Symbol">)</a>
</pre>

Recall, the definition of the type `Σ`.

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```

-------------------------------------

[Back to Table of Contents ↑](UALib.html#detailed-contents)

------------------------------------------------

{% include UALib.Links.md %}

