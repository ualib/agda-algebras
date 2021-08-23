---
layout: default
title : ClosureSystems.Definitions module (The Agda Universal Algebra Library)
date : 2021-07-10
author: [agda-algebras development team][]
---

### <a id="definitions-for-closure-systems-and-operators">Definitions for Closure Systems and Operators</a>

<pre class="Agda">

<a id="289" class="Symbol">{-#</a> <a id="293" class="Keyword">OPTIONS</a> <a id="301" class="Pragma">--without-K</a> <a id="313" class="Pragma">--safe</a> <a id="320" class="Symbol">#-}</a>

<a id="325" class="Keyword">module</a> <a id="332" href="ClosureSystems.Definitions.html" class="Module">ClosureSystems.Definitions</a> <a id="359" class="Keyword">where</a>

<a id="366" class="Keyword">open</a> <a id="371" class="Keyword">import</a> <a id="378" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>          <a id="402" class="Keyword">using</a>    <a id="411" class="Symbol">(</a> <a id="413" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="419" class="Symbol">)</a>
                                    <a id="457" class="Keyword">renaming</a> <a id="466" class="Symbol">(</a> <a id="468" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="472" class="Symbol">to</a> <a id="475" class="Primitive">Type</a> <a id="480" class="Symbol">)</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="Relation.Binary.Core.html" class="Module">Relation.Binary.Core</a>    <a id="518" class="Keyword">using</a>    <a id="527" class="Symbol">(</a> <a id="529" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="533" class="Symbol">)</a>


<a id="537" class="Keyword">private</a> <a id="545" class="Keyword">variable</a>
 <a id="555" href="ClosureSystems.Definitions.html#555" class="Generalizable">a</a> <a id="557" href="ClosureSystems.Definitions.html#557" class="Generalizable">ℓ</a> <a id="559" class="Symbol">:</a> <a id="561" href="Agda.Primitive.html#597" class="Postulate">Level</a>
 <a id="568" href="ClosureSystems.Definitions.html#568" class="Generalizable">A</a> <a id="570" class="Symbol">:</a> <a id="572" href="ClosureSystems.Definitions.html#475" class="Primitive">Type</a> <a id="577" href="ClosureSystems.Definitions.html#555" class="Generalizable">a</a>


<a id="Extensive"></a><a id="581" href="ClosureSystems.Definitions.html#581" class="Function">Extensive</a> <a id="591" class="Symbol">:</a> <a id="593" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="597" href="ClosureSystems.Definitions.html#568" class="Generalizable">A</a> <a id="599" href="ClosureSystems.Definitions.html#557" class="Generalizable">ℓ</a> <a id="601" class="Symbol">→</a> <a id="603" class="Symbol">(</a><a id="604" href="ClosureSystems.Definitions.html#568" class="Generalizable">A</a> <a id="606" class="Symbol">→</a> <a id="608" href="ClosureSystems.Definitions.html#568" class="Generalizable">A</a><a id="609" class="Symbol">)</a> <a id="611" class="Symbol">→</a> <a id="613" href="ClosureSystems.Definitions.html#475" class="Primitive">Type</a> <a id="618" class="Symbol">_</a>
<a id="620" href="ClosureSystems.Definitions.html#581" class="Function">Extensive</a> <a id="630" href="ClosureSystems.Definitions.html#630" class="Bound Operator">_≤_</a> <a id="634" href="ClosureSystems.Definitions.html#634" class="Bound">C</a> <a id="636" class="Symbol">=</a> <a id="638" class="Symbol">∀{</a><a id="640" href="ClosureSystems.Definitions.html#640" class="Bound">x</a><a id="641" class="Symbol">}</a> <a id="643" class="Symbol">→</a> <a id="645" href="ClosureSystems.Definitions.html#640" class="Bound">x</a> <a id="647" href="ClosureSystems.Definitions.html#630" class="Bound Operator">≤</a> <a id="649" href="ClosureSystems.Definitions.html#634" class="Bound">C</a> <a id="651" href="ClosureSystems.Definitions.html#640" class="Bound">x</a>
<a id="653" class="Comment">-- Try to replace Extensive by proposing a new stdlib equivalent: Relation.Binary.Core.Extensive</a>

<a id="751" class="Comment">-- (Deprecated) Replaced with stdlib equivalent: Relation.Binary.Core._Preserves_⟶_)</a>
<a id="836" class="Comment">-- OrderPreserving : Rel A ℓ → (A → A) → Type _</a>
<a id="884" class="Comment">-- OrderPreserving _≤_ C = ∀ {x y} → x ≤ y → C x ≤ C y</a>

<a id="940" class="Comment">-- (Deprecated) Replaced with stdlib equivalent: Algebra.Definitions(_≈_).IdempotentFun</a>
<a id="1028" class="Comment">-- Idempotent : Rel A ℓ → (A → A) → Type _</a>
<a id="1071" class="Comment">-- Idempotent _≈_ C = ∀ {x} → C (C x) ≈ C x</a>

</pre>

--------------------------------------

<br>
<br>

[↑ ClosureSystems](ClosureSystems.html)
<span style="float:right;">[ClosureSystems.Basic →](ClosureSystems.Basic.html)</span>

{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

