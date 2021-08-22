---
layout: default
title : ClosureSystems.Definitions module (The Agda Universal Algebra Library)
date : 2021-07-10
author: [agda-algebras development team][]
---

### Definitions for Closure Systems and Operators

<pre class="Agda">

<a id="231" class="Symbol">{-#</a> <a id="235" class="Keyword">OPTIONS</a> <a id="243" class="Pragma">--without-K</a> <a id="255" class="Pragma">--safe</a> <a id="262" class="Symbol">#-}</a>

<a id="267" class="Keyword">module</a> <a id="274" href="ClosureSystems.Definitions.html" class="Module">ClosureSystems.Definitions</a> <a id="301" class="Keyword">where</a>

<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>          <a id="344" class="Keyword">using</a>    <a id="353" class="Symbol">(</a> <a id="355" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="361" class="Symbol">)</a>
                                    <a id="399" class="Keyword">renaming</a> <a id="408" class="Symbol">(</a> <a id="410" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="414" class="Symbol">to</a> <a id="417" class="Primitive">Type</a> <a id="422" class="Symbol">)</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>    <a id="460" class="Keyword">using</a>    <a id="469" class="Symbol">(</a> <a id="471" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="475" class="Symbol">)</a>


<a id="479" class="Keyword">private</a> <a id="487" class="Keyword">variable</a>
 <a id="497" href="ClosureSystems.Definitions.html#497" class="Generalizable">a</a> <a id="499" href="ClosureSystems.Definitions.html#499" class="Generalizable">ℓ</a> <a id="501" class="Symbol">:</a> <a id="503" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="510" href="ClosureSystems.Definitions.html#510" class="Generalizable">A</a> <a id="512" class="Symbol">:</a> <a id="514" href="ClosureSystems.Definitions.html#417" class="Primitive">Type</a> <a id="519" href="ClosureSystems.Definitions.html#497" class="Generalizable">a</a>


<a id="Extensive"></a><a id="523" href="ClosureSystems.Definitions.html#523" class="Function">Extensive</a> <a id="533" class="Symbol">:</a> <a id="535" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="539" href="ClosureSystems.Definitions.html#510" class="Generalizable">A</a> <a id="541" href="ClosureSystems.Definitions.html#499" class="Generalizable">ℓ</a> <a id="543" class="Symbol">→</a> <a id="545" class="Symbol">(</a><a id="546" href="ClosureSystems.Definitions.html#510" class="Generalizable">A</a> <a id="548" class="Symbol">→</a> <a id="550" href="ClosureSystems.Definitions.html#510" class="Generalizable">A</a><a id="551" class="Symbol">)</a> <a id="553" class="Symbol">→</a> <a id="555" href="ClosureSystems.Definitions.html#417" class="Primitive">Type</a> <a id="560" class="Symbol">_</a>
<a id="562" href="ClosureSystems.Definitions.html#523" class="Function">Extensive</a> <a id="572" href="ClosureSystems.Definitions.html#572" class="Bound Operator">_≤_</a> <a id="576" href="ClosureSystems.Definitions.html#576" class="Bound">C</a> <a id="578" class="Symbol">=</a> <a id="580" class="Symbol">∀{</a><a id="582" href="ClosureSystems.Definitions.html#582" class="Bound">x</a><a id="583" class="Symbol">}</a> <a id="585" class="Symbol">→</a> <a id="587" href="ClosureSystems.Definitions.html#582" class="Bound">x</a> <a id="589" href="ClosureSystems.Definitions.html#572" class="Bound Operator">≤</a> <a id="591" href="ClosureSystems.Definitions.html#576" class="Bound">C</a> <a id="593" href="ClosureSystems.Definitions.html#582" class="Bound">x</a>
<a id="595" class="Comment">-- Try to replace Extensive by proposing a new stdlib equivalent: Relation.Binary.Core.Extensive</a>

<a id="693" class="Comment">-- (Deprecated) Replaced with stdlib equivalent: Relation.Binary.Core._Preserves_⟶_)</a>
<a id="778" class="Comment">-- OrderPreserving : Rel A ℓ → (A → A) → Type _</a>
<a id="826" class="Comment">-- OrderPreserving _≤_ C = ∀ {x y} → x ≤ y → C x ≤ C y</a>

<a id="882" class="Comment">-- (Deprecated) Replaced with stdlib equivalent: Algebra.Definitions(_≈_).IdempotentFun</a>
<a id="970" class="Comment">-- Idempotent : Rel A ℓ → (A → A) → Type _</a>
<a id="1013" class="Comment">-- Idempotent _≈_ C = ∀ {x} → C (C x) ≈ C x</a>

</pre>

--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

