---
layout: default
title : Overture.Preliminaries module
date : 2021-01-13
author: [agda-algebras development team][]
---

## <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [agda-algebras][] library.

### <a id="logical-foundations">Logical foundations</a>

(See also the Foundations module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [agda-algebras](https://github.com/ualib/agda-algebras) begins with the following line.

<pre class="Agda">

<a id="839" class="Symbol">{-#</a> <a id="843" class="Keyword">OPTIONS</a> <a id="851" class="Pragma">--without-K</a> <a id="863" class="Pragma">--exact-split</a> <a id="877" class="Pragma">--safe</a> <a id="884" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language).

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Martín Escardó](https://www.cs.bham.ac.uk/~mhe) explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference](https://agda.readthedocs.io/en/v2.6.1.3/language).

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [agda-algebras](https://github.com/ualib/agda-algebras) library.


### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line, and then a list of imports of things used in the module.

<pre class="Agda">
<a id="2930" class="Keyword">module</a> <a id="2937" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="2960" class="Keyword">where</a>

<a id="2967" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------------------------</a>
<a id="3066" class="Keyword">open</a> <a id="3071" class="Keyword">import</a> <a id="3078" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="3093" class="Keyword">using</a> <a id="3099" class="Symbol">(</a> <a id="3101" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3105" class="Symbol">;</a> <a id="3107" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3112" class="Symbol">)</a> <a id="3114" class="Keyword">renaming</a> <a id="3123" class="Symbol">(</a> <a id="3125" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3129" class="Symbol">to</a>  <a id="3133" class="Primitive">Type</a> <a id="3138" class="Symbol">;</a> <a id="3140" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="3146" class="Symbol">to</a>  <a id="3150" class="Primitive">ℓ₀</a> <a id="3153" class="Symbol">)</a>
<a id="3155" class="Keyword">open</a> <a id="3160" class="Keyword">import</a> <a id="3167" href="Data.Product.html" class="Module">Data.Product</a>   <a id="3182" class="Keyword">using</a> <a id="3188" class="Symbol">(</a> <a id="3190" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="3194" class="Symbol">;</a> <a id="3196" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="3205" class="Symbol">;</a> <a id="3207" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="3211" class="Symbol">)</a> <a id="3213" class="Keyword">renaming</a> <a id="3222" class="Symbol">(</a> <a id="3224" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="3230" class="Symbol">to</a> <a id="3233" class="Field">fst</a> <a id="3237" class="Symbol">;</a> <a id="3239" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="3245" class="Symbol">to</a> <a id="3248" class="Field">snd</a> <a id="3252" class="Symbol">)</a>
<a id="3254" class="Keyword">open</a> <a id="3259" class="Keyword">import</a> <a id="3266" href="Function.Base.html" class="Module">Function.Base</a>  <a id="3281" class="Keyword">using</a> <a id="3287" class="Symbol">(</a> <a id="3289" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3293" class="Symbol">;</a> <a id="3295" href="Function.Base.html#615" class="Function">id</a> <a id="3298" class="Symbol">)</a>
<a id="3300" class="Keyword">open</a> <a id="3305" class="Keyword">import</a> <a id="3312" href="Level.html" class="Module">Level</a>          <a id="3327" class="Keyword">using</a> <a id="3333" class="Symbol">(</a> <a id="3335" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3341" class="Symbol">;</a> <a id="3343" href="Level.html#400" class="Record">Lift</a> <a id="3348" class="Symbol">;</a> <a id="3350" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3355" class="Symbol">;</a> <a id="3357" href="Level.html#470" class="Field">lower</a> <a id="3363" class="Symbol">)</a>
<a id="3365" class="Keyword">open</a> <a id="3370" class="Keyword">import</a> <a id="3377" href="Relation.Binary.Structures.html" class="Module">Relation.Binary.Structures</a>
                           <a id="3431" class="Keyword">using</a> <a id="3437" class="Symbol">(</a> <a id="3439" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3453" class="Symbol">;</a> <a id="3455" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3470" class="Symbol">)</a>
<a id="3472" class="Keyword">open</a> <a id="3477" class="Keyword">import</a> <a id="3484" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                           <a id="3549" class="Keyword">using</a> <a id="3555" class="Symbol">(</a> <a id="3557" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3561" class="Symbol">;</a> <a id="3563" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3568" class="Symbol">;</a> <a id="3570" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3574" class="Symbol">;</a> <a id="3576" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3582" class="Symbol">)</a>

<a id="3585" class="Keyword">private</a> <a id="3593" class="Keyword">variable</a> <a id="3602" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="3604" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a> <a id="3606" class="Symbol">:</a> <a id="3608" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3615" href="Overture.Preliminaries.html#3615" class="Function">ℓ₁</a> <a id="3618" class="Symbol">:</a> <a id="3620" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3626" href="Overture.Preliminaries.html#3615" class="Function">ℓ₁</a> <a id="3629" class="Symbol">=</a> <a id="3631" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3636" href="Overture.Preliminaries.html#3150" class="Primitive">ℓ₀</a>

<a id="3640" class="Comment">-- The empty type</a>
<a id="3658" class="Keyword">data</a> <a id="𝟘"></a><a id="3663" href="Overture.Preliminaries.html#3663" class="Datatype">𝟘</a> <a id="3665" class="Symbol">:</a> <a id="3667" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="3672" href="Overture.Preliminaries.html#3150" class="Primitive">ℓ₀</a> <a id="3675" class="Keyword">where</a>  <a id="3682" class="Comment">-- maybe we should use ⊥ instead ...?</a>

<a id="3721" class="Comment">-- The one element type</a>
<a id="3745" class="Keyword">data</a> <a id="𝟙"></a><a id="3750" href="Overture.Preliminaries.html#3750" class="Datatype">𝟙</a> <a id="3752" class="Symbol">:</a> <a id="3754" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="3759" href="Overture.Preliminaries.html#3150" class="Primitive">ℓ₀</a> <a id="3762" class="Keyword">where</a>
 <a id="𝟙.𝟎"></a><a id="3769" href="Overture.Preliminaries.html#3769" class="InductiveConstructor">𝟎</a> <a id="3771" class="Symbol">:</a> <a id="3773" href="Overture.Preliminaries.html#3750" class="Datatype">𝟙</a>

<a id="3776" class="Comment">-- the two element type</a>
<a id="3800" class="Keyword">data</a> <a id="𝟚"></a><a id="3805" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="3807" class="Symbol">:</a> <a id="3809" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="3814" href="Overture.Preliminaries.html#3150" class="Primitive">ℓ₀</a> <a id="3817" class="Keyword">where</a>  <a id="3824" class="Comment">-- We could use Bool instead.</a>
 <a id="𝟚.𝟎"></a><a id="3855" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟎</a> <a id="3857" class="Symbol">:</a> <a id="3859" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a>                  <a id="3878" class="Comment">-- &quot;         &quot; false &quot;   &quot;</a>
 <a id="𝟚.𝟏"></a><a id="3906" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟏</a> <a id="3908" class="Symbol">:</a> <a id="3910" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a>                  <a id="3929" class="Comment">-- &quot;         &quot; true  &quot;   &quot;</a>

<a id="3957" class="Comment">-- the three element type</a>
<a id="3983" class="Keyword">data</a> <a id="𝟛"></a><a id="3988" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a> <a id="3990" class="Symbol">:</a> <a id="3992" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="3997" href="Overture.Preliminaries.html#3150" class="Primitive">ℓ₀</a> <a id="4000" class="Keyword">where</a>
 <a id="𝟛.𝟎"></a><a id="4007" href="Overture.Preliminaries.html#4007" class="InductiveConstructor">𝟎</a> <a id="4009" class="Symbol">:</a> <a id="4011" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a>
 <a id="𝟛.𝟏"></a><a id="4014" href="Overture.Preliminaries.html#4014" class="InductiveConstructor">𝟏</a> <a id="4016" class="Symbol">:</a> <a id="4018" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a>
 <a id="𝟛.𝟐"></a><a id="4021" href="Overture.Preliminaries.html#4021" class="InductiveConstructor">𝟐</a> <a id="4023" class="Symbol">:</a> <a id="4025" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a>

</pre>


### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second projections out of the product.  However, we prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥`, respectively. We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4477" class="Keyword">module</a> <a id="4484" href="Overture.Preliminaries.html#4484" class="Module">_</a> <a id="4486" class="Symbol">{</a><a id="4487" href="Overture.Preliminaries.html#4487" class="Bound">A</a> <a id="4489" class="Symbol">:</a> <a id="4491" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="4496" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="4498" class="Symbol">}{</a><a id="4500" href="Overture.Preliminaries.html#4500" class="Bound">B</a> <a id="4502" class="Symbol">:</a> <a id="4504" href="Overture.Preliminaries.html#4487" class="Bound">A</a> <a id="4506" class="Symbol">→</a> <a id="4508" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="4513" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="4514" class="Symbol">}</a> <a id="4516" class="Keyword">where</a>

 <a id="4524" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a> <a id="4528" class="Symbol">:</a> <a id="4530" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4533" href="Overture.Preliminaries.html#4533" class="Bound">x</a> <a id="4535" href="Data.Product.html#916" class="Function">∈</a> <a id="4537" href="Overture.Preliminaries.html#4487" class="Bound">A</a> <a id="4539" href="Data.Product.html#916" class="Function">]</a> <a id="4541" href="Overture.Preliminaries.html#4500" class="Bound">B</a> <a id="4543" href="Overture.Preliminaries.html#4533" class="Bound">x</a> <a id="4545" class="Symbol">→</a> <a id="4547" href="Overture.Preliminaries.html#4487" class="Bound">A</a>
 <a id="4550" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a> <a id="4554" class="Symbol">=</a> <a id="4556" href="Overture.Preliminaries.html#3233" class="Field">fst</a>

 <a id="4562" href="Overture.Preliminaries.html#4562" class="Function Operator">∥_∥</a> <a id="4566" class="Symbol">:</a> <a id="4568" class="Symbol">(</a><a id="4569" href="Overture.Preliminaries.html#4569" class="Bound">z</a> <a id="4571" class="Symbol">:</a> <a id="4573" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4576" href="Overture.Preliminaries.html#4576" class="Bound">a</a> <a id="4578" href="Data.Product.html#916" class="Function">∈</a> <a id="4580" href="Overture.Preliminaries.html#4487" class="Bound">A</a> <a id="4582" href="Data.Product.html#916" class="Function">]</a> <a id="4584" href="Overture.Preliminaries.html#4500" class="Bound">B</a> <a id="4586" href="Overture.Preliminaries.html#4576" class="Bound">a</a><a id="4587" class="Symbol">)</a> <a id="4589" class="Symbol">→</a> <a id="4591" href="Overture.Preliminaries.html#4500" class="Bound">B</a> <a id="4593" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a> <a id="4595" href="Overture.Preliminaries.html#4569" class="Bound">z</a> <a id="4597" href="Overture.Preliminaries.html#4524" class="Function Operator">∣</a>
 <a id="4600" href="Overture.Preliminaries.html#4562" class="Function Operator">∥_∥</a> <a id="4604" class="Symbol">=</a> <a id="4606" href="Overture.Preliminaries.html#3248" class="Field">snd</a>

 <a id="4612" class="Keyword">infix</a>  <a id="4619" class="Number">40</a> <a id="4622" href="Overture.Preliminaries.html#4524" class="Function Operator">∣_∣</a>
</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

Let's define some useful syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="5228" href="Overture.Preliminaries.html#5228" class="Function Operator">_⁻¹</a> <a id="5232" class="Symbol">:</a> <a id="5234" class="Symbol">{</a><a id="5235" href="Overture.Preliminaries.html#5235" class="Bound">A</a> <a id="5237" class="Symbol">:</a> <a id="5239" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="5244" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="5245" class="Symbol">}</a> <a id="5247" class="Symbol">{</a><a id="5248" href="Overture.Preliminaries.html#5248" class="Bound">x</a> <a id="5250" href="Overture.Preliminaries.html#5250" class="Bound">y</a> <a id="5252" class="Symbol">:</a> <a id="5254" href="Overture.Preliminaries.html#5235" class="Bound">A</a><a id="5255" class="Symbol">}</a> <a id="5257" class="Symbol">→</a> <a id="5259" href="Overture.Preliminaries.html#5248" class="Bound">x</a> <a id="5261" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5263" href="Overture.Preliminaries.html#5250" class="Bound">y</a> <a id="5265" class="Symbol">→</a> <a id="5267" href="Overture.Preliminaries.html#5250" class="Bound">y</a> <a id="5269" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5271" href="Overture.Preliminaries.html#5248" class="Bound">x</a>
<a id="5273" href="Overture.Preliminaries.html#5273" class="Bound">p</a> <a id="5275" href="Overture.Preliminaries.html#5228" class="Function Operator">⁻¹</a> <a id="5278" class="Symbol">=</a> <a id="5280" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="5284" href="Overture.Preliminaries.html#5273" class="Bound">p</a>

<a id="5287" class="Keyword">infix</a>  <a id="5294" class="Number">40</a> <a id="5297" href="Overture.Preliminaries.html#5228" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5554" href="Overture.Preliminaries.html#5554" class="Function Operator">_∙_</a> <a id="5558" class="Symbol">:</a> <a id="5560" class="Symbol">{</a><a id="5561" href="Overture.Preliminaries.html#5561" class="Bound">A</a> <a id="5563" class="Symbol">:</a> <a id="5565" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="5570" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="5571" class="Symbol">}{</a><a id="5573" href="Overture.Preliminaries.html#5573" class="Bound">x</a> <a id="5575" href="Overture.Preliminaries.html#5575" class="Bound">y</a> <a id="5577" href="Overture.Preliminaries.html#5577" class="Bound">z</a> <a id="5579" class="Symbol">:</a> <a id="5581" href="Overture.Preliminaries.html#5561" class="Bound">A</a><a id="5582" class="Symbol">}</a> <a id="5584" class="Symbol">→</a> <a id="5586" href="Overture.Preliminaries.html#5573" class="Bound">x</a> <a id="5588" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5590" href="Overture.Preliminaries.html#5575" class="Bound">y</a> <a id="5592" class="Symbol">→</a> <a id="5594" href="Overture.Preliminaries.html#5575" class="Bound">y</a> <a id="5596" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5598" href="Overture.Preliminaries.html#5577" class="Bound">z</a> <a id="5600" class="Symbol">→</a> <a id="5602" href="Overture.Preliminaries.html#5573" class="Bound">x</a> <a id="5604" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5606" href="Overture.Preliminaries.html#5577" class="Bound">z</a>
<a id="5608" href="Overture.Preliminaries.html#5608" class="Bound">p</a> <a id="5610" href="Overture.Preliminaries.html#5554" class="Function Operator">∙</a> <a id="5612" href="Overture.Preliminaries.html#5612" class="Bound">q</a> <a id="5614" class="Symbol">=</a> <a id="5616" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5622" href="Overture.Preliminaries.html#5608" class="Bound">p</a> <a id="5624" href="Overture.Preliminaries.html#5612" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5627" href="Overture.Preliminaries.html#5627" class="Function">𝑖𝑑</a> <a id="5630" class="Symbol">:</a> <a id="5632" class="Symbol">(</a><a id="5633" href="Overture.Preliminaries.html#5633" class="Bound">A</a> <a id="5635" class="Symbol">:</a> <a id="5637" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="5642" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="5644" class="Symbol">)</a> <a id="5646" class="Symbol">→</a> <a id="5648" href="Overture.Preliminaries.html#5633" class="Bound">A</a> <a id="5650" class="Symbol">→</a> <a id="5652" href="Overture.Preliminaries.html#5633" class="Bound">A</a>
<a id="5654" href="Overture.Preliminaries.html#5627" class="Function">𝑖𝑑</a> <a id="5657" href="Overture.Preliminaries.html#5657" class="Bound">A</a> <a id="5659" class="Symbol">=</a> <a id="5661" class="Symbol">λ</a> <a id="5663" href="Overture.Preliminaries.html#5663" class="Bound">x</a> <a id="5665" class="Symbol">→</a> <a id="5667" href="Overture.Preliminaries.html#5663" class="Bound">x</a>

<a id="5670" class="Keyword">infixl</a> <a id="5677" class="Number">30</a> <a id="5680" href="Overture.Preliminaries.html#5554" class="Function Operator">_∙_</a>
</pre>


### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with a Pi symbol typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes `(x : A) → B x` for the dependent function type, but may use syntax that is closer to the standard Π notation and made available in Agda as follows.

<pre class="Agda">

<a id="Π"></a><a id="6052" href="Overture.Preliminaries.html#6052" class="Function">Π</a> <a id="6054" class="Symbol">:</a> <a id="6056" class="Symbol">{</a><a id="6057" href="Overture.Preliminaries.html#6057" class="Bound">A</a> <a id="6059" class="Symbol">:</a> <a id="6061" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6066" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="6068" class="Symbol">}</a> <a id="6070" class="Symbol">(</a><a id="6071" href="Overture.Preliminaries.html#6071" class="Bound">B</a> <a id="6073" class="Symbol">:</a> <a id="6075" href="Overture.Preliminaries.html#6057" class="Bound">A</a> <a id="6077" class="Symbol">→</a> <a id="6079" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6084" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a> <a id="6086" class="Symbol">)</a> <a id="6088" class="Symbol">→</a> <a id="6090" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6095" class="Symbol">(</a><a id="6096" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="6098" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6100" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="6101" class="Symbol">)</a>
<a id="6103" href="Overture.Preliminaries.html#6052" class="Function">Π</a> <a id="6105" class="Symbol">{</a><a id="6106" class="Argument">A</a> <a id="6108" class="Symbol">=</a> <a id="6110" href="Overture.Preliminaries.html#6110" class="Bound">A</a><a id="6111" class="Symbol">}</a> <a id="6113" href="Overture.Preliminaries.html#6113" class="Bound">B</a> <a id="6115" class="Symbol">=</a> <a id="6117" class="Symbol">(</a><a id="6118" href="Overture.Preliminaries.html#6118" class="Bound">x</a> <a id="6120" class="Symbol">:</a> <a id="6122" href="Overture.Preliminaries.html#6110" class="Bound">A</a><a id="6123" class="Symbol">)</a> <a id="6125" class="Symbol">→</a> <a id="6127" href="Overture.Preliminaries.html#6113" class="Bound">B</a> <a id="6129" href="Overture.Preliminaries.html#6118" class="Bound">x</a>

<a id="Π-syntax"></a><a id="6132" href="Overture.Preliminaries.html#6132" class="Function">Π-syntax</a> <a id="6141" class="Symbol">:</a> <a id="6143" class="Symbol">(</a><a id="6144" href="Overture.Preliminaries.html#6144" class="Bound">A</a> <a id="6146" class="Symbol">:</a> <a id="6148" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6153" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="6154" class="Symbol">)(</a><a id="6156" href="Overture.Preliminaries.html#6156" class="Bound">B</a> <a id="6158" class="Symbol">:</a> <a id="6160" href="Overture.Preliminaries.html#6144" class="Bound">A</a> <a id="6162" class="Symbol">→</a> <a id="6164" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6169" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="6170" class="Symbol">)</a> <a id="6172" class="Symbol">→</a> <a id="6174" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="6179" class="Symbol">(</a><a id="6180" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="6182" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6184" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="6185" class="Symbol">)</a>
<a id="6187" href="Overture.Preliminaries.html#6132" class="Function">Π-syntax</a> <a id="6196" href="Overture.Preliminaries.html#6196" class="Bound">A</a> <a id="6198" href="Overture.Preliminaries.html#6198" class="Bound">B</a> <a id="6200" class="Symbol">=</a> <a id="6202" href="Overture.Preliminaries.html#6052" class="Function">Π</a> <a id="6204" href="Overture.Preliminaries.html#6198" class="Bound">B</a>

<a id="6207" class="Keyword">syntax</a> <a id="6214" href="Overture.Preliminaries.html#6132" class="Function">Π-syntax</a> <a id="6223" class="Bound">A</a> <a id="6225" class="Symbol">(λ</a> <a id="6228" class="Bound">x</a> <a id="6230" class="Symbol">→</a> <a id="6232" class="Bound">B</a><a id="6233" class="Symbol">)</a> <a id="6235" class="Symbol">=</a> <a id="6237" class="Function">Π[</a> <a id="6240" class="Bound">x</a> <a id="6242" class="Function">∈</a> <a id="6244" class="Bound">A</a> <a id="6246" class="Function">]</a> <a id="6248" class="Bound">B</a>
<a id="6250" class="Keyword">infix</a> <a id="6256" class="Number">6</a> <a id="6258" href="Overture.Preliminaries.html#6132" class="Function">Π-syntax</a>

</pre>

### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:

```agda
Type α : Type (lsuc α),   Type(lsuc α) : Type (lsuc (lsuc α)),  etc.
```

This means that the universe `Type α` has type `Type(lsuc α)`, and  `Type(lsuc α)` has type `Type(lsuc (lsuc α))`, and so on.  It is important to note, however, this does *not* imply that  `Type α : Type(lsuc(lsuc α))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Basic.html#lifts-of-algebras) of the [Algebras.Basic][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `lsuc α`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⊔ 𝓥 ⊔ lsuc α` instead.

The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].

```agda
 record Lift {𝓦 α : Level} (A : Type α) : Type (α ⊔ 𝓦) where
  constructor lift
  field lower : A
```

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="8852" href="Overture.Preliminaries.html#8852" class="Function">lift∼lower</a> <a id="8863" class="Symbol">:</a> <a id="8865" class="Symbol">{</a><a id="8866" href="Overture.Preliminaries.html#8866" class="Bound">A</a> <a id="8868" class="Symbol">:</a> <a id="8870" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="8875" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="8876" class="Symbol">}</a> <a id="8878" class="Symbol">→</a> <a id="8880" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8885" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8887" href="Level.html#470" class="Field">lower</a> <a id="8893" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8895" href="Overture.Preliminaries.html#5627" class="Function">𝑖𝑑</a> <a id="8898" class="Symbol">(</a><a id="8899" href="Level.html#400" class="Record">Lift</a> <a id="8904" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a> <a id="8906" href="Overture.Preliminaries.html#8866" class="Bound">A</a><a id="8907" class="Symbol">)</a>
<a id="8909" href="Overture.Preliminaries.html#8852" class="Function">lift∼lower</a> <a id="8920" class="Symbol">=</a> <a id="8922" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8928" href="Overture.Preliminaries.html#8928" class="Function">lower∼lift</a> <a id="8939" class="Symbol">:</a> <a id="8941" class="Symbol">{</a><a id="8942" href="Overture.Preliminaries.html#8942" class="Bound">A</a> <a id="8944" class="Symbol">:</a> <a id="8946" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="8951" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="8952" class="Symbol">}</a> <a id="8954" class="Symbol">→</a> <a id="8956" class="Symbol">(</a><a id="8957" href="Level.html#470" class="Field">lower</a> <a id="8963" class="Symbol">{</a><a id="8964" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="8965" class="Symbol">}{</a><a id="8967" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="8968" class="Symbol">})</a> <a id="8971" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8973" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8978" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8980" href="Overture.Preliminaries.html#5627" class="Function">𝑖𝑑</a> <a id="8983" href="Overture.Preliminaries.html#8942" class="Bound">A</a>
<a id="8985" href="Overture.Preliminaries.html#8928" class="Function">lower∼lift</a> <a id="8996" class="Symbol">=</a> <a id="8998" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Foundations.Extensionality][] module.)

<pre class="Agda">

<a id="9533" class="Keyword">module</a> <a id="9540" href="Overture.Preliminaries.html#9540" class="Module">_</a> <a id="9542" class="Symbol">{</a><a id="9543" href="Overture.Preliminaries.html#9543" class="Bound">α</a> <a id="9545" class="Symbol">:</a> <a id="9547" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9552" class="Symbol">}{</a><a id="9554" href="Overture.Preliminaries.html#9554" class="Bound">A</a> <a id="9556" class="Symbol">:</a> <a id="9558" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="9563" href="Overture.Preliminaries.html#9543" class="Bound">α</a><a id="9564" class="Symbol">}{</a><a id="9566" href="Overture.Preliminaries.html#9566" class="Bound">β</a> <a id="9568" class="Symbol">:</a> <a id="9570" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9575" class="Symbol">}{</a><a id="9577" href="Overture.Preliminaries.html#9577" class="Bound">B</a> <a id="9579" class="Symbol">:</a> <a id="9581" href="Overture.Preliminaries.html#9554" class="Bound">A</a> <a id="9583" class="Symbol">→</a> <a id="9585" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="9590" href="Overture.Preliminaries.html#9566" class="Bound">β</a> <a id="9592" class="Symbol">}</a> <a id="9594" class="Keyword">where</a>

 <a id="9602" href="Overture.Preliminaries.html#9602" class="Function Operator">_≈_</a> <a id="9606" class="Symbol">:</a>  <a id="9609" class="Symbol">(</a><a id="9610" href="Overture.Preliminaries.html#9610" class="Bound">f</a> <a id="9612" href="Overture.Preliminaries.html#9612" class="Bound">g</a> <a id="9614" class="Symbol">:</a> <a id="9616" class="Symbol">(</a><a id="9617" href="Overture.Preliminaries.html#9617" class="Bound">a</a> <a id="9619" class="Symbol">:</a> <a id="9621" href="Overture.Preliminaries.html#9554" class="Bound">A</a><a id="9622" class="Symbol">)</a> <a id="9624" class="Symbol">→</a> <a id="9626" href="Overture.Preliminaries.html#9577" class="Bound">B</a> <a id="9628" href="Overture.Preliminaries.html#9617" class="Bound">a</a><a id="9629" class="Symbol">)</a> <a id="9631" class="Symbol">→</a> <a id="9633" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="9638" class="Symbol">(</a><a id="9639" href="Overture.Preliminaries.html#9543" class="Bound">α</a> <a id="9641" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9643" href="Overture.Preliminaries.html#9566" class="Bound">β</a><a id="9644" class="Symbol">)</a>
 <a id="9647" href="Overture.Preliminaries.html#9647" class="Bound">f</a> <a id="9649" href="Overture.Preliminaries.html#9602" class="Function Operator">≈</a> <a id="9651" href="Overture.Preliminaries.html#9651" class="Bound">g</a> <a id="9653" class="Symbol">=</a> <a id="9655" class="Symbol">∀</a> <a id="9657" href="Overture.Preliminaries.html#9657" class="Bound">x</a> <a id="9659" class="Symbol">→</a> <a id="9661" href="Overture.Preliminaries.html#9647" class="Bound">f</a> <a id="9663" href="Overture.Preliminaries.html#9657" class="Bound">x</a> <a id="9665" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9667" href="Overture.Preliminaries.html#9651" class="Bound">g</a> <a id="9669" href="Overture.Preliminaries.html#9657" class="Bound">x</a>

 <a id="9673" class="Keyword">infix</a> <a id="9679" class="Number">8</a> <a id="9681" href="Overture.Preliminaries.html#9602" class="Function Operator">_≈_</a>

 <a id="9687" href="Overture.Preliminaries.html#9687" class="Function">≈IsEquivalence</a> <a id="9702" class="Symbol">:</a> <a id="9704" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9718" href="Overture.Preliminaries.html#9602" class="Function Operator">_≈_</a>
 <a id="9723" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a> <a id="9742" href="Overture.Preliminaries.html#9687" class="Function">≈IsEquivalence</a> <a id="9757" class="Symbol">=</a> <a id="9759" class="Symbol">λ</a> <a id="9761" href="Overture.Preliminaries.html#9761" class="Bound">_</a> <a id="9763" class="Symbol">→</a> <a id="9765" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9771" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a> <a id="9789" href="Overture.Preliminaries.html#9687" class="Function">≈IsEquivalence</a> <a id="9804" class="Symbol">{</a><a id="9805" href="Overture.Preliminaries.html#9805" class="Bound">f</a><a id="9806" class="Symbol">}{</a><a id="9808" href="Overture.Preliminaries.html#9808" class="Bound">g</a><a id="9809" class="Symbol">}</a> <a id="9811" href="Overture.Preliminaries.html#9811" class="Bound">f≈g</a> <a id="9815" class="Symbol">=</a> <a id="9817" class="Symbol">λ</a> <a id="9819" href="Overture.Preliminaries.html#9819" class="Bound">x</a> <a id="9821" class="Symbol">→</a> <a id="9823" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9827" class="Symbol">(</a><a id="9828" href="Overture.Preliminaries.html#9811" class="Bound">f≈g</a> <a id="9832" href="Overture.Preliminaries.html#9819" class="Bound">x</a><a id="9833" class="Symbol">)</a>
 <a id="9836" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a> <a id="9856" href="Overture.Preliminaries.html#9687" class="Function">≈IsEquivalence</a> <a id="9871" class="Symbol">{</a><a id="9872" href="Overture.Preliminaries.html#9872" class="Bound">f</a><a id="9873" class="Symbol">}{</a><a id="9875" href="Overture.Preliminaries.html#9875" class="Bound">g</a><a id="9876" class="Symbol">}{</a><a id="9878" href="Overture.Preliminaries.html#9878" class="Bound">h</a><a id="9879" class="Symbol">}</a> <a id="9881" href="Overture.Preliminaries.html#9881" class="Bound">f≈g</a> <a id="9885" href="Overture.Preliminaries.html#9885" class="Bound">g≈h</a> <a id="9889" class="Symbol">=</a> <a id="9891" class="Symbol">λ</a> <a id="9893" href="Overture.Preliminaries.html#9893" class="Bound">x</a> <a id="9895" class="Symbol">→</a> <a id="9897" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9903" class="Symbol">(</a><a id="9904" href="Overture.Preliminaries.html#9881" class="Bound">f≈g</a> <a id="9908" href="Overture.Preliminaries.html#9893" class="Bound">x</a><a id="9909" class="Symbol">)</a> <a id="9911" class="Symbol">(</a><a id="9912" href="Overture.Preliminaries.html#9885" class="Bound">g≈h</a> <a id="9916" href="Overture.Preliminaries.html#9893" class="Bound">x</a><a id="9917" class="Symbol">)</a>

</pre>

The following is convenient for proving two pairs of a product type are equal using the fact that their
respective components are equal.

<pre class="Agda">

<a id="≡-by-parts"></a><a id="10084" href="Overture.Preliminaries.html#10084" class="Function">≡-by-parts</a> <a id="10095" class="Symbol">:</a> <a id="10097" class="Symbol">{</a><a id="10098" href="Overture.Preliminaries.html#10098" class="Bound">A</a> <a id="10100" class="Symbol">:</a> <a id="10102" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="10107" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a><a id="10108" class="Symbol">}{</a><a id="10110" href="Overture.Preliminaries.html#10110" class="Bound">B</a> <a id="10112" class="Symbol">:</a> <a id="10114" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="10119" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="10120" class="Symbol">}{</a><a id="10122" href="Overture.Preliminaries.html#10122" class="Bound">u</a> <a id="10124" href="Overture.Preliminaries.html#10124" class="Bound">v</a> <a id="10126" class="Symbol">:</a> <a id="10128" href="Overture.Preliminaries.html#10098" class="Bound">A</a> <a id="10130" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="10132" href="Overture.Preliminaries.html#10110" class="Bound">B</a><a id="10133" class="Symbol">}</a> <a id="10135" class="Symbol">→</a> <a id="10137" href="Overture.Preliminaries.html#3233" class="Field">fst</a> <a id="10141" href="Overture.Preliminaries.html#10122" class="Bound">u</a> <a id="10143" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10145" href="Overture.Preliminaries.html#3233" class="Field">fst</a> <a id="10149" href="Overture.Preliminaries.html#10124" class="Bound">v</a> <a id="10151" class="Symbol">→</a> <a id="10153" href="Overture.Preliminaries.html#3248" class="Field">snd</a> <a id="10157" href="Overture.Preliminaries.html#10122" class="Bound">u</a> <a id="10159" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10161" href="Overture.Preliminaries.html#3248" class="Field">snd</a> <a id="10165" href="Overture.Preliminaries.html#10124" class="Bound">v</a> <a id="10167" class="Symbol">→</a> <a id="10169" href="Overture.Preliminaries.html#10122" class="Bound">u</a> <a id="10171" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10173" href="Overture.Preliminaries.html#10124" class="Bound">v</a>
<a id="10175" href="Overture.Preliminaries.html#10084" class="Function">≡-by-parts</a> <a id="10186" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10191" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10196" class="Symbol">=</a> <a id="10198" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

Lastly, we will use the following type (instead of `subst`) to transport equality proofs.

<pre class="Agda">

<a id="transport"></a><a id="10321" href="Overture.Preliminaries.html#10321" class="Function">transport</a> <a id="10331" class="Symbol">:</a> <a id="10333" class="Symbol">{</a><a id="10334" href="Overture.Preliminaries.html#10334" class="Bound">A</a> <a id="10336" class="Symbol">:</a> <a id="10338" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="10343" href="Overture.Preliminaries.html#3602" class="Generalizable">α</a> <a id="10345" class="Symbol">}</a> <a id="10347" class="Symbol">(</a><a id="10348" href="Overture.Preliminaries.html#10348" class="Bound">B</a> <a id="10350" class="Symbol">:</a> <a id="10352" href="Overture.Preliminaries.html#10334" class="Bound">A</a> <a id="10354" class="Symbol">→</a> <a id="10356" href="Overture.Preliminaries.html#3133" class="Primitive">Type</a> <a id="10361" href="Overture.Preliminaries.html#3604" class="Generalizable">β</a><a id="10362" class="Symbol">)</a> <a id="10364" class="Symbol">{</a><a id="10365" href="Overture.Preliminaries.html#10365" class="Bound">x</a> <a id="10367" href="Overture.Preliminaries.html#10367" class="Bound">y</a> <a id="10369" class="Symbol">:</a> <a id="10371" href="Overture.Preliminaries.html#10334" class="Bound">A</a><a id="10372" class="Symbol">}</a> <a id="10374" class="Symbol">→</a> <a id="10376" href="Overture.Preliminaries.html#10365" class="Bound">x</a> <a id="10378" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10380" href="Overture.Preliminaries.html#10367" class="Bound">y</a> <a id="10382" class="Symbol">→</a> <a id="10384" href="Overture.Preliminaries.html#10348" class="Bound">B</a> <a id="10386" href="Overture.Preliminaries.html#10365" class="Bound">x</a> <a id="10388" class="Symbol">→</a> <a id="10390" href="Overture.Preliminaries.html#10348" class="Bound">B</a> <a id="10392" href="Overture.Preliminaries.html#10367" class="Bound">y</a>
<a id="10394" href="Overture.Preliminaries.html#10321" class="Function">transport</a> <a id="10404" href="Overture.Preliminaries.html#10404" class="Bound">B</a> <a id="10406" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10411" class="Symbol">=</a> <a id="10413" href="Function.Base.html#615" class="Function">id</a>

</pre>


------------------------------

<span style="float:left;">[↑ Overture](Overture.html)</span>
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>


{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


