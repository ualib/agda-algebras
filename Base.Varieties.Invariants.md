---
layout: default
title : "Base.Varieties.Invariants module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "the ualib/agda-algebras development team"
---

### Algebraic invariants

These are properties that are preserved under isomorphism.

<pre class="Agda">

<a id="273" class="Symbol">{-#</a> <a id="277" class="Keyword">OPTIONS</a> <a id="285" class="Pragma">--without-K</a> <a id="297" class="Pragma">--exact-split</a> <a id="311" class="Pragma">--safe</a> <a id="318" class="Symbol">#-}</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="355" class="Keyword">using</a> <a id="361" class="Symbol">(</a> <a id="363" href="Base.Algebras.Basic.html#1160" class="Generalizable">𝓞</a> <a id="365" class="Symbol">;</a> <a id="367" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓥</a> <a id="369" class="Symbol">;</a> <a id="371" href="Base.Algebras.Basic.html#3888" class="Function">Signature</a> <a id="381" class="Symbol">)</a>

<a id="384" class="Keyword">module</a> <a id="391" href="Base.Varieties.Invariants.html" class="Module">Base.Varieties.Invariants</a> <a id="417" class="Symbol">(</a><a id="418" href="Base.Varieties.Invariants.html#418" class="Bound">𝑆</a> <a id="420" class="Symbol">:</a> <a id="422" href="Base.Algebras.Basic.html#3888" class="Function">Signature</a> <a id="432" href="Base.Algebras.Basic.html#1160" class="Generalizable">𝓞</a> <a id="434" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓥</a><a id="435" class="Symbol">)</a> <a id="437" class="Keyword">where</a>

<a id="444" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="517" class="Keyword">open</a> <a id="522" class="Keyword">import</a> <a id="529" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="544" class="Keyword">using</a> <a id="550" class="Symbol">(</a> <a id="552" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="558" class="Symbol">)</a> <a id="560" class="Keyword">renaming</a> <a id="569" class="Symbol">(</a> <a id="571" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="575" class="Symbol">to</a> <a id="578" class="Primitive">Type</a> <a id="583" class="Symbol">)</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="612" class="Keyword">using</a> <a id="618" class="Symbol">(</a> <a id="620" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="625" class="Symbol">)</a>

<a id="628" class="Comment">-- Imports from the Agda Universal Algebra Library -------------------------------------------</a>
<a id="723" class="Keyword">open</a> <a id="728" class="Keyword">import</a> <a id="735" href="Base.Homomorphisms.Isomorphisms.html" class="Module">Base.Homomorphisms.Isomorphisms</a> <a id="767" class="Symbol">{</a><a id="768" class="Argument">𝑆</a> <a id="770" class="Symbol">=</a> <a id="772" href="Base.Varieties.Invariants.html#418" class="Bound">𝑆</a><a id="773" class="Symbol">}</a> <a id="775" class="Keyword">using</a> <a id="781" class="Symbol">(</a> <a id="783" href="Base.Homomorphisms.Isomorphisms.html#2378" class="Record Operator">_≅_</a> <a id="787" class="Symbol">)</a>
<a id="789" class="Keyword">open</a> <a id="794" class="Keyword">import</a> <a id="801" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>                     <a id="841" class="Keyword">using</a> <a id="847" class="Symbol">(</a> <a id="849" href="Base.Algebras.Basic.html#6257" class="Function">Algebra</a> <a id="857" class="Symbol">)</a>

<a id="860" class="Keyword">private</a> <a id="868" class="Keyword">variable</a> <a id="877" href="Base.Varieties.Invariants.html#877" class="Generalizable">α</a> <a id="879" href="Base.Varieties.Invariants.html#879" class="Generalizable">ℓ</a> <a id="881" class="Symbol">:</a> <a id="883" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="AlgebraicInvariant"></a><a id="890" href="Base.Varieties.Invariants.html#890" class="Function">AlgebraicInvariant</a> <a id="909" class="Symbol">:</a> <a id="911" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="916" class="Symbol">(</a><a id="917" href="Base.Algebras.Basic.html#6257" class="Function">Algebra</a> <a id="925" href="Base.Varieties.Invariants.html#877" class="Generalizable">α</a> <a id="927" href="Base.Varieties.Invariants.html#418" class="Bound">𝑆</a><a id="928" class="Symbol">)</a> <a id="930" href="Base.Varieties.Invariants.html#879" class="Generalizable">ℓ</a> <a id="932" class="Symbol">→</a> <a id="934" href="Base.Varieties.Invariants.html#578" class="Primitive">Type</a> <a id="939" class="Symbol">_</a>
<a id="941" href="Base.Varieties.Invariants.html#890" class="Function">AlgebraicInvariant</a> <a id="960" href="Base.Varieties.Invariants.html#960" class="Bound">P</a> <a id="962" class="Symbol">=</a> <a id="964" class="Symbol">∀</a> <a id="966" href="Base.Varieties.Invariants.html#966" class="Bound">𝑨</a> <a id="968" href="Base.Varieties.Invariants.html#968" class="Bound">𝑩</a> <a id="970" class="Symbol">→</a> <a id="972" href="Base.Varieties.Invariants.html#960" class="Bound">P</a> <a id="974" href="Base.Varieties.Invariants.html#966" class="Bound">𝑨</a> <a id="976" class="Symbol">→</a> <a id="978" href="Base.Varieties.Invariants.html#966" class="Bound">𝑨</a> <a id="980" href="Base.Homomorphisms.Isomorphisms.html#2378" class="Record Operator">≅</a> <a id="982" href="Base.Varieties.Invariants.html#968" class="Bound">𝑩</a> <a id="984" class="Symbol">→</a> <a id="986" href="Base.Varieties.Invariants.html#960" class="Bound">P</a> <a id="988" href="Base.Varieties.Invariants.html#968" class="Bound">𝑩</a>

</pre>

--------------------------------

{% include UALib.Links.md %}
