---
layout: default
title : Varieties.Invariants module (Agda Universal Algebra Library)
date : 2021-06-29
author: [the ualib/agda-algebras development team][]
---

### Algebraic invariants

These are properties that are preserved under isomorphism.

<pre class="Agda">

<a id="266" class="Symbol">{-#</a> <a id="270" class="Keyword">OPTIONS</a> <a id="278" class="Pragma">--without-K</a> <a id="290" class="Pragma">--exact-split</a> <a id="304" class="Pragma">--safe</a> <a id="311" class="Symbol">#-}</a>


<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="344" class="Keyword">using</a> <a id="350" class="Symbol">(</a> <a id="352" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="354" class="Symbol">;</a> <a id="356" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a> <a id="358" class="Symbol">;</a> <a id="360" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="370" class="Symbol">;</a> <a id="372" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="380" class="Symbol">)</a>

<a id="383" class="Keyword">module</a> <a id="390" href="Varieties.Invariants.html" class="Module">Varieties.Invariants</a> <a id="411" class="Symbol">(</a><a id="412" href="Varieties.Invariants.html#412" class="Bound">𝑆</a> <a id="414" class="Symbol">:</a> <a id="416" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="426" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="428" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a><a id="429" class="Symbol">)</a> <a id="431" class="Keyword">where</a>


<a id="439" class="Comment">-- Imports from Agda and the Agda Standard Library ---------------------</a>
<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="539" class="Keyword">using</a> <a id="545" class="Symbol">(</a> <a id="547" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="553" class="Symbol">)</a> <a id="555" class="Keyword">renaming</a> <a id="564" class="Symbol">(</a> <a id="566" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="570" class="Symbol">to</a> <a id="573" class="Primitive">Type</a> <a id="578" class="Symbol">)</a>
<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="607" class="Keyword">using</a> <a id="613" class="Symbol">(</a> <a id="615" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="620" class="Symbol">)</a>

<a id="623" class="Comment">-- Imports from the Agda Universal Algebra Library -------------------------------------------</a>
<a id="718" class="Keyword">open</a> <a id="723" class="Keyword">import</a> <a id="730" href="Homomorphisms.Isomorphisms.html" class="Module">Homomorphisms.Isomorphisms</a> <a id="757" class="Symbol">{</a><a id="758" class="Argument">𝑆</a> <a id="760" class="Symbol">=</a> <a id="762" href="Varieties.Invariants.html#412" class="Bound">𝑆</a><a id="763" class="Symbol">}</a> <a id="765" class="Keyword">using</a> <a id="771" class="Symbol">(</a> <a id="773" href="Homomorphisms.Isomorphisms.html#2291" class="Record Operator">_≅_</a> <a id="777" class="Symbol">)</a>

<a id="780" class="Keyword">private</a> <a id="788" class="Keyword">variable</a> <a id="797" href="Varieties.Invariants.html#797" class="Generalizable">α</a> <a id="799" href="Varieties.Invariants.html#799" class="Generalizable">ℓ</a> <a id="801" class="Symbol">:</a> <a id="803" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="AlgebraicInvariant"></a><a id="809" href="Varieties.Invariants.html#809" class="Function">AlgebraicInvariant</a> <a id="828" class="Symbol">:</a> <a id="830" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="835" class="Symbol">(</a><a id="836" href="Algebras.Basic.html#6023" class="Function">Algebra</a> <a id="844" href="Varieties.Invariants.html#797" class="Generalizable">α</a> <a id="846" href="Varieties.Invariants.html#412" class="Bound">𝑆</a><a id="847" class="Symbol">)</a> <a id="849" href="Varieties.Invariants.html#799" class="Generalizable">ℓ</a> <a id="851" class="Symbol">→</a> <a id="853" href="Varieties.Invariants.html#573" class="Primitive">Type</a> <a id="858" class="Symbol">_</a>
<a id="860" href="Varieties.Invariants.html#809" class="Function">AlgebraicInvariant</a> <a id="879" href="Varieties.Invariants.html#879" class="Bound">P</a> <a id="881" class="Symbol">=</a> <a id="883" class="Symbol">∀</a> <a id="885" href="Varieties.Invariants.html#885" class="Bound">𝑨</a> <a id="887" href="Varieties.Invariants.html#887" class="Bound">𝑩</a> <a id="889" class="Symbol">→</a> <a id="891" href="Varieties.Invariants.html#879" class="Bound">P</a> <a id="893" href="Varieties.Invariants.html#885" class="Bound">𝑨</a> <a id="895" class="Symbol">→</a> <a id="897" href="Varieties.Invariants.html#885" class="Bound">𝑨</a> <a id="899" href="Homomorphisms.Isomorphisms.html#2291" class="Record Operator">≅</a> <a id="901" href="Varieties.Invariants.html#887" class="Bound">𝑩</a> <a id="903" class="Symbol">→</a> <a id="905" href="Varieties.Invariants.html#879" class="Bound">P</a> <a id="907" href="Varieties.Invariants.html#887" class="Bound">𝑩</a>

</pre>
