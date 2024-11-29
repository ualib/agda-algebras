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

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="Overture.html" class="Module">Overture</a> <a id="344" class="Keyword">using</a> <a id="350" class="Symbol">(</a> <a id="352" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="354" class="Symbol">;</a> <a id="356" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="358" class="Symbol">;</a> <a id="360" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="370" class="Symbol">)</a>

<a id="373" class="Keyword">module</a> <a id="380" href="Base.Varieties.Invariants.html" class="Module">Base.Varieties.Invariants</a> <a id="406" class="Symbol">(</a><a id="407" href="Base.Varieties.Invariants.html#407" class="Bound">𝑆</a> <a id="409" class="Symbol">:</a> <a id="411" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="421" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="423" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="424" class="Symbol">)</a> <a id="426" class="Keyword">where</a>

<a id="433" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="534" class="Keyword">using</a> <a id="540" class="Symbol">()</a> <a id="543" class="Keyword">renaming</a> <a id="552" class="Symbol">(</a> <a id="554" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="558" class="Symbol">to</a> <a id="561" class="Primitive">Type</a> <a id="566" class="Symbol">)</a>
<a id="568" class="Keyword">open</a> <a id="573" class="Keyword">import</a> <a id="580" href="Level.html" class="Module">Level</a>           <a id="596" class="Keyword">using</a> <a id="602" class="Symbol">(</a> <a id="604" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="610" class="Symbol">)</a>
<a id="612" class="Keyword">open</a> <a id="617" class="Keyword">import</a> <a id="624" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="640" class="Keyword">using</a> <a id="646" class="Symbol">(</a> <a id="648" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="653" class="Symbol">)</a>

<a id="656" class="Comment">-- Imports from the Agda Universal Algebra Library -------------------------------------------</a>
<a id="751" class="Keyword">open</a> <a id="756" class="Keyword">import</a> <a id="763" href="Base.Homomorphisms.html" class="Module">Base.Homomorphisms</a>   <a id="784" class="Symbol">{</a><a id="785" class="Argument">𝑆</a> <a id="787" class="Symbol">=</a> <a id="789" href="Base.Varieties.Invariants.html#407" class="Bound">𝑆</a><a id="790" class="Symbol">}</a> <a id="792" class="Keyword">using</a> <a id="798" class="Symbol">(</a> <a id="800" href="Base.Homomorphisms.Isomorphisms.html#2018" class="Record Operator">_≅_</a> <a id="804" class="Symbol">)</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a>  <a id="839" class="Symbol">{</a><a id="840" class="Argument">𝑆</a> <a id="842" class="Symbol">=</a> <a id="844" href="Base.Varieties.Invariants.html#407" class="Bound">𝑆</a><a id="845" class="Symbol">}</a> <a id="847" class="Keyword">using</a> <a id="853" class="Symbol">(</a> <a id="855" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="863" class="Symbol">)</a>

<a id="866" class="Keyword">private</a> <a id="874" class="Keyword">variable</a> <a id="883" href="Base.Varieties.Invariants.html#883" class="Generalizable">α</a> <a id="885" href="Base.Varieties.Invariants.html#885" class="Generalizable">ℓ</a> <a id="887" class="Symbol">:</a> <a id="889" href="Agda.Primitive.html#742" class="Postulate">Level</a>

<a id="AlgebraicInvariant"></a><a id="896" href="Base.Varieties.Invariants.html#896" class="Function">AlgebraicInvariant</a> <a id="915" class="Symbol">:</a> <a id="917" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="922" class="Symbol">(</a><a id="923" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="931" href="Base.Varieties.Invariants.html#883" class="Generalizable">α</a><a id="932" class="Symbol">)</a> <a id="934" href="Base.Varieties.Invariants.html#885" class="Generalizable">ℓ</a> <a id="936" class="Symbol">→</a> <a id="938" href="Base.Varieties.Invariants.html#561" class="Primitive">Type</a> <a id="943" class="Symbol">_</a>
<a id="945" href="Base.Varieties.Invariants.html#896" class="Function">AlgebraicInvariant</a> <a id="964" href="Base.Varieties.Invariants.html#964" class="Bound">P</a> <a id="966" class="Symbol">=</a> <a id="968" class="Symbol">∀</a> <a id="970" href="Base.Varieties.Invariants.html#970" class="Bound">𝑨</a> <a id="972" href="Base.Varieties.Invariants.html#972" class="Bound">𝑩</a> <a id="974" class="Symbol">→</a> <a id="976" href="Base.Varieties.Invariants.html#964" class="Bound">P</a> <a id="978" href="Base.Varieties.Invariants.html#970" class="Bound">𝑨</a> <a id="980" class="Symbol">→</a> <a id="982" href="Base.Varieties.Invariants.html#970" class="Bound">𝑨</a> <a id="984" href="Base.Homomorphisms.Isomorphisms.html#2018" class="Record Operator">≅</a> <a id="986" href="Base.Varieties.Invariants.html#972" class="Bound">𝑩</a> <a id="988" class="Symbol">→</a> <a id="990" href="Base.Varieties.Invariants.html#964" class="Bound">P</a> <a id="992" href="Base.Varieties.Invariants.html#972" class="Bound">𝑩</a>

</pre>

--------------------------------

{% include UALib.Links.md %}
