---
layout: default
title : Overture.Preliminaries module
date : 2021-01-13
author: [agda-algebras development team][]
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [agda-algebras][] library.

#### <a id="logical-foundations">Logical foundations</a>

(See also the Foundations module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [agda-algebras][] begins with the following line.

<pre class="Agda">

<a id="803" class="Symbol">{-#</a> <a id="807" class="Keyword">OPTIONS</a> <a id="815" class="Pragma">--without-K</a> <a id="827" class="Pragma">--exact-split</a> <a id="841" class="Pragma">--safe</a> <a id="848" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [agda-algebras][] library.


#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line, and then a list of imports of things used in the module.

<pre class="Agda">
<a id="2632" class="Keyword">module</a> <a id="2639" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="2662" class="Keyword">where</a>

<a id="2669" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library</a>
<a id="2734" class="Keyword">open</a> <a id="2739" class="Keyword">import</a> <a id="2746" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>              <a id="2774" class="Keyword">using</a> <a id="2780" class="Symbol">(</a> <a id="2782" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="2786" class="Symbol">;</a> <a id="2788" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2793" class="Symbol">)</a>           <a id="2805" class="Keyword">renaming</a> <a id="2814" class="Symbol">(</a> <a id="2816" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="2820" class="Symbol">to</a>  <a id="2824" class="Primitive">Type</a> <a id="2829" class="Symbol">;</a> <a id="2831" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="2837" class="Symbol">to</a>  <a id="2841" class="Primitive">ℓ₀</a> <a id="2844" class="Symbol">)</a>
<a id="2846" class="Keyword">open</a> <a id="2851" class="Keyword">import</a> <a id="2858" href="Data.Product.html" class="Module">Data.Product</a>                <a id="2886" class="Keyword">using</a> <a id="2892" class="Symbol">(</a> <a id="2894" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="2898" class="Symbol">;</a> <a id="2900" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="2909" class="Symbol">;</a> <a id="2911" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="2915" class="Symbol">)</a> <a id="2917" class="Keyword">renaming</a> <a id="2926" class="Symbol">(</a> <a id="2928" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="2934" class="Symbol">to</a> <a id="2937" class="Field">fst</a> <a id="2941" class="Symbol">;</a> <a id="2943" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="2949" class="Symbol">to</a> <a id="2952" class="Field">snd</a> <a id="2956" class="Symbol">)</a>
<a id="2958" class="Keyword">open</a> <a id="2963" class="Keyword">import</a> <a id="2970" href="Function.Base.html" class="Module">Function.Base</a>               <a id="2998" class="Keyword">using</a> <a id="3004" class="Symbol">(</a> <a id="3006" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3010" class="Symbol">;</a> <a id="3012" href="Function.Base.html#615" class="Function">id</a> <a id="3015" class="Symbol">)</a>
<a id="3017" class="Keyword">open</a> <a id="3022" class="Keyword">import</a> <a id="3029" href="Level.html" class="Module">Level</a>                       <a id="3057" class="Keyword">using</a> <a id="3063" class="Symbol">(</a> <a id="3065" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3071" class="Symbol">;</a> <a id="3073" href="Level.html#400" class="Record">Lift</a> <a id="3078" class="Symbol">;</a> <a id="3080" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3085" class="Symbol">;</a> <a id="3087" href="Level.html#470" class="Field">lower</a> <a id="3093" class="Symbol">)</a>
<a id="3095" class="Keyword">open</a> <a id="3100" class="Keyword">import</a> <a id="3107" href="Relation.Binary.Structures.html" class="Module">Relation.Binary.Structures</a>  <a id="3135" class="Keyword">using</a> <a id="3141" class="Symbol">(</a> <a id="3143" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3157" class="Symbol">;</a> <a id="3159" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3174" class="Symbol">)</a>
<a id="3176" class="Keyword">open</a> <a id="3181" class="Keyword">import</a> <a id="3188" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                                        <a id="3266" class="Keyword">using</a>    <a id="3275" class="Symbol">(</a> <a id="3277" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3281" class="Symbol">;</a> <a id="3283" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3288" class="Symbol">;</a> <a id="3290" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3294" class="Symbol">;</a> <a id="3296" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3302" class="Symbol">)</a>

<a id="3305" class="Keyword">private</a> <a id="3313" class="Keyword">variable</a> <a id="3322" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="3324" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a> <a id="3326" class="Symbol">:</a> <a id="3328" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3335" href="Overture.Preliminaries.html#3335" class="Function">ℓ₁</a> <a id="3338" class="Symbol">:</a> <a id="3340" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3346" href="Overture.Preliminaries.html#3335" class="Function">ℓ₁</a> <a id="3349" class="Symbol">=</a> <a id="3351" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3356" href="Overture.Preliminaries.html#2841" class="Primitive">ℓ₀</a>

<a id="3360" class="Comment">-- The empty type</a>
<a id="3378" class="Keyword">data</a> <a id="𝟘"></a><a id="3383" href="Overture.Preliminaries.html#3383" class="Datatype">𝟘</a> <a id="3385" class="Symbol">:</a> <a id="3387" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="3392" href="Overture.Preliminaries.html#2841" class="Primitive">ℓ₀</a> <a id="3395" class="Keyword">where</a>  <a id="3402" class="Comment">-- maybe we should use ⊥ instead ...?</a>

<a id="3441" class="Comment">-- The one element type</a>
<a id="3465" class="Keyword">data</a> <a id="𝟙"></a><a id="3470" href="Overture.Preliminaries.html#3470" class="Datatype">𝟙</a> <a id="3472" class="Symbol">:</a> <a id="3474" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="3479" href="Overture.Preliminaries.html#2841" class="Primitive">ℓ₀</a> <a id="3482" class="Keyword">where</a>
 <a id="𝟙.𝟎"></a><a id="3489" href="Overture.Preliminaries.html#3489" class="InductiveConstructor">𝟎</a> <a id="3491" class="Symbol">:</a> <a id="3493" href="Overture.Preliminaries.html#3470" class="Datatype">𝟙</a>

<a id="3496" class="Comment">-- the two element type</a>
<a id="3520" class="Keyword">data</a> <a id="𝟚"></a><a id="3525" href="Overture.Preliminaries.html#3525" class="Datatype">𝟚</a> <a id="3527" class="Symbol">:</a> <a id="3529" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="3534" href="Overture.Preliminaries.html#2841" class="Primitive">ℓ₀</a> <a id="3537" class="Keyword">where</a>  <a id="3544" class="Comment">-- We could use Bool instead.</a>
 <a id="𝟚.𝟎"></a><a id="3575" href="Overture.Preliminaries.html#3575" class="InductiveConstructor">𝟎</a> <a id="3577" class="Symbol">:</a> <a id="3579" href="Overture.Preliminaries.html#3525" class="Datatype">𝟚</a>                  <a id="3598" class="Comment">-- &quot;         &quot; false &quot;   &quot;</a>
 <a id="𝟚.𝟏"></a><a id="3626" href="Overture.Preliminaries.html#3626" class="InductiveConstructor">𝟏</a> <a id="3628" class="Symbol">:</a> <a id="3630" href="Overture.Preliminaries.html#3525" class="Datatype">𝟚</a>                  <a id="3649" class="Comment">-- &quot;         &quot; true  &quot;   &quot;</a>

<a id="3677" class="Comment">-- the three element type</a>
<a id="3703" class="Keyword">data</a> <a id="𝟛"></a><a id="3708" href="Overture.Preliminaries.html#3708" class="Datatype">𝟛</a> <a id="3710" class="Symbol">:</a> <a id="3712" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="3717" href="Overture.Preliminaries.html#2841" class="Primitive">ℓ₀</a> <a id="3720" class="Keyword">where</a>
 <a id="𝟛.𝟎"></a><a id="3727" href="Overture.Preliminaries.html#3727" class="InductiveConstructor">𝟎</a> <a id="3729" class="Symbol">:</a> <a id="3731" href="Overture.Preliminaries.html#3708" class="Datatype">𝟛</a>
 <a id="𝟛.𝟏"></a><a id="3734" href="Overture.Preliminaries.html#3734" class="InductiveConstructor">𝟏</a> <a id="3736" class="Symbol">:</a> <a id="3738" href="Overture.Preliminaries.html#3708" class="Datatype">𝟛</a>
 <a id="𝟛.𝟐"></a><a id="3741" href="Overture.Preliminaries.html#3741" class="InductiveConstructor">𝟐</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="Overture.Preliminaries.html#3708" class="Datatype">𝟛</a>

</pre>


#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second projections out of the product.  However, we prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥`, respectively. We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4198" class="Keyword">module</a> <a id="4205" href="Overture.Preliminaries.html#4205" class="Module">_</a> <a id="4207" class="Symbol">{</a><a id="4208" href="Overture.Preliminaries.html#4208" class="Bound">A</a> <a id="4210" class="Symbol">:</a> <a id="4212" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="4217" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="4219" class="Symbol">}{</a><a id="4221" href="Overture.Preliminaries.html#4221" class="Bound">B</a> <a id="4223" class="Symbol">:</a> <a id="4225" href="Overture.Preliminaries.html#4208" class="Bound">A</a> <a id="4227" class="Symbol">→</a> <a id="4229" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="4234" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="4235" class="Symbol">}</a> <a id="4237" class="Keyword">where</a>

 <a id="4245" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a> <a id="4249" class="Symbol">:</a> <a id="4251" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4254" href="Overture.Preliminaries.html#4254" class="Bound">x</a> <a id="4256" href="Data.Product.html#916" class="Function">∈</a> <a id="4258" href="Overture.Preliminaries.html#4208" class="Bound">A</a> <a id="4260" href="Data.Product.html#916" class="Function">]</a> <a id="4262" href="Overture.Preliminaries.html#4221" class="Bound">B</a> <a id="4264" href="Overture.Preliminaries.html#4254" class="Bound">x</a> <a id="4266" class="Symbol">→</a> <a id="4268" href="Overture.Preliminaries.html#4208" class="Bound">A</a>
 <a id="4271" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a> <a id="4275" class="Symbol">=</a> <a id="4277" href="Overture.Preliminaries.html#2937" class="Field">fst</a>

 <a id="4283" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a> <a id="4287" class="Symbol">:</a> <a id="4289" class="Symbol">(</a><a id="4290" href="Overture.Preliminaries.html#4290" class="Bound">z</a> <a id="4292" class="Symbol">:</a> <a id="4294" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4297" href="Overture.Preliminaries.html#4297" class="Bound">a</a> <a id="4299" href="Data.Product.html#916" class="Function">∈</a> <a id="4301" href="Overture.Preliminaries.html#4208" class="Bound">A</a> <a id="4303" href="Data.Product.html#916" class="Function">]</a> <a id="4305" href="Overture.Preliminaries.html#4221" class="Bound">B</a> <a id="4307" href="Overture.Preliminaries.html#4297" class="Bound">a</a><a id="4308" class="Symbol">)</a> <a id="4310" class="Symbol">→</a> <a id="4312" href="Overture.Preliminaries.html#4221" class="Bound">B</a> <a id="4314" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a> <a id="4316" href="Overture.Preliminaries.html#4290" class="Bound">z</a> <a id="4318" href="Overture.Preliminaries.html#4245" class="Function Operator">∣</a>
 <a id="4321" href="Overture.Preliminaries.html#4283" class="Function Operator">∥_∥</a> <a id="4325" class="Symbol">=</a> <a id="4327" href="Overture.Preliminaries.html#2952" class="Field">snd</a>

 <a id="4333" class="Keyword">infix</a>  <a id="4340" class="Number">40</a> <a id="4343" href="Overture.Preliminaries.html#4245" class="Function Operator">∣_∣</a>
</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

Let's define some useful syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4949" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a> <a id="4953" class="Symbol">:</a> <a id="4955" class="Symbol">{</a><a id="4956" href="Overture.Preliminaries.html#4956" class="Bound">A</a> <a id="4958" class="Symbol">:</a> <a id="4960" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="4965" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="4966" class="Symbol">}</a> <a id="4968" class="Symbol">{</a><a id="4969" href="Overture.Preliminaries.html#4969" class="Bound">x</a> <a id="4971" href="Overture.Preliminaries.html#4971" class="Bound">y</a> <a id="4973" class="Symbol">:</a> <a id="4975" href="Overture.Preliminaries.html#4956" class="Bound">A</a><a id="4976" class="Symbol">}</a> <a id="4978" class="Symbol">→</a> <a id="4980" href="Overture.Preliminaries.html#4969" class="Bound">x</a> <a id="4982" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4984" href="Overture.Preliminaries.html#4971" class="Bound">y</a> <a id="4986" class="Symbol">→</a> <a id="4988" href="Overture.Preliminaries.html#4971" class="Bound">y</a> <a id="4990" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4992" href="Overture.Preliminaries.html#4969" class="Bound">x</a>
<a id="4994" href="Overture.Preliminaries.html#4994" class="Bound">p</a> <a id="4996" href="Overture.Preliminaries.html#4949" class="Function Operator">⁻¹</a> <a id="4999" class="Symbol">=</a> <a id="5001" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="5005" href="Overture.Preliminaries.html#4994" class="Bound">p</a>

<a id="5008" class="Keyword">infix</a>  <a id="5015" class="Number">40</a> <a id="5018" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5275" href="Overture.Preliminaries.html#5275" class="Function Operator">_∙_</a> <a id="5279" class="Symbol">:</a> <a id="5281" class="Symbol">{</a><a id="5282" href="Overture.Preliminaries.html#5282" class="Bound">A</a> <a id="5284" class="Symbol">:</a> <a id="5286" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5291" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="5292" class="Symbol">}{</a><a id="5294" href="Overture.Preliminaries.html#5294" class="Bound">x</a> <a id="5296" href="Overture.Preliminaries.html#5296" class="Bound">y</a> <a id="5298" href="Overture.Preliminaries.html#5298" class="Bound">z</a> <a id="5300" class="Symbol">:</a> <a id="5302" href="Overture.Preliminaries.html#5282" class="Bound">A</a><a id="5303" class="Symbol">}</a> <a id="5305" class="Symbol">→</a> <a id="5307" href="Overture.Preliminaries.html#5294" class="Bound">x</a> <a id="5309" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5311" href="Overture.Preliminaries.html#5296" class="Bound">y</a> <a id="5313" class="Symbol">→</a> <a id="5315" href="Overture.Preliminaries.html#5296" class="Bound">y</a> <a id="5317" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5319" href="Overture.Preliminaries.html#5298" class="Bound">z</a> <a id="5321" class="Symbol">→</a> <a id="5323" href="Overture.Preliminaries.html#5294" class="Bound">x</a> <a id="5325" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5327" href="Overture.Preliminaries.html#5298" class="Bound">z</a>
<a id="5329" href="Overture.Preliminaries.html#5329" class="Bound">p</a> <a id="5331" href="Overture.Preliminaries.html#5275" class="Function Operator">∙</a> <a id="5333" href="Overture.Preliminaries.html#5333" class="Bound">q</a> <a id="5335" class="Symbol">=</a> <a id="5337" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5343" href="Overture.Preliminaries.html#5329" class="Bound">p</a> <a id="5345" href="Overture.Preliminaries.html#5333" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5348" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a> <a id="5351" class="Symbol">:</a> <a id="5353" class="Symbol">(</a><a id="5354" href="Overture.Preliminaries.html#5354" class="Bound">A</a> <a id="5356" class="Symbol">:</a> <a id="5358" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5363" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="5365" class="Symbol">)</a> <a id="5367" class="Symbol">→</a> <a id="5369" href="Overture.Preliminaries.html#5354" class="Bound">A</a> <a id="5371" class="Symbol">→</a> <a id="5373" href="Overture.Preliminaries.html#5354" class="Bound">A</a>
<a id="5375" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a> <a id="5378" href="Overture.Preliminaries.html#5378" class="Bound">A</a> <a id="5380" class="Symbol">=</a> <a id="5382" class="Symbol">λ</a> <a id="5384" href="Overture.Preliminaries.html#5384" class="Bound">x</a> <a id="5386" class="Symbol">→</a> <a id="5388" href="Overture.Preliminaries.html#5384" class="Bound">x</a>

<a id="5391" class="Keyword">infixl</a> <a id="5398" class="Number">30</a> <a id="5401" href="Overture.Preliminaries.html#5275" class="Function Operator">_∙_</a>
</pre>


#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with a Pi symbol typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes `(x : A) → B x` for the dependent function type, but may use syntax that is closer to the standard Π notation and made available in Agda as follows.

<pre class="Agda">

<a id="Π"></a><a id="5774" href="Overture.Preliminaries.html#5774" class="Function">Π</a> <a id="5776" class="Symbol">:</a> <a id="5778" class="Symbol">{</a><a id="5779" href="Overture.Preliminaries.html#5779" class="Bound">A</a> <a id="5781" class="Symbol">:</a> <a id="5783" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5788" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="5790" class="Symbol">}</a> <a id="5792" class="Symbol">(</a><a id="5793" href="Overture.Preliminaries.html#5793" class="Bound">B</a> <a id="5795" class="Symbol">:</a> <a id="5797" href="Overture.Preliminaries.html#5779" class="Bound">A</a> <a id="5799" class="Symbol">→</a> <a id="5801" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5806" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a> <a id="5808" class="Symbol">)</a> <a id="5810" class="Symbol">→</a> <a id="5812" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5817" class="Symbol">(</a><a id="5818" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="5820" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5822" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="5823" class="Symbol">)</a>
<a id="5825" href="Overture.Preliminaries.html#5774" class="Function">Π</a> <a id="5827" class="Symbol">{</a><a id="5828" class="Argument">A</a> <a id="5830" class="Symbol">=</a> <a id="5832" href="Overture.Preliminaries.html#5832" class="Bound">A</a><a id="5833" class="Symbol">}</a> <a id="5835" href="Overture.Preliminaries.html#5835" class="Bound">B</a> <a id="5837" class="Symbol">=</a> <a id="5839" class="Symbol">(</a><a id="5840" href="Overture.Preliminaries.html#5840" class="Bound">x</a> <a id="5842" class="Symbol">:</a> <a id="5844" href="Overture.Preliminaries.html#5832" class="Bound">A</a><a id="5845" class="Symbol">)</a> <a id="5847" class="Symbol">→</a> <a id="5849" href="Overture.Preliminaries.html#5835" class="Bound">B</a> <a id="5851" href="Overture.Preliminaries.html#5840" class="Bound">x</a>

<a id="Π-syntax"></a><a id="5854" href="Overture.Preliminaries.html#5854" class="Function">Π-syntax</a> <a id="5863" class="Symbol">:</a> <a id="5865" class="Symbol">(</a><a id="5866" href="Overture.Preliminaries.html#5866" class="Bound">A</a> <a id="5868" class="Symbol">:</a> <a id="5870" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5875" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="5876" class="Symbol">)(</a><a id="5878" href="Overture.Preliminaries.html#5878" class="Bound">B</a> <a id="5880" class="Symbol">:</a> <a id="5882" href="Overture.Preliminaries.html#5866" class="Bound">A</a> <a id="5884" class="Symbol">→</a> <a id="5886" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5891" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="5892" class="Symbol">)</a> <a id="5894" class="Symbol">→</a> <a id="5896" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="5901" class="Symbol">(</a><a id="5902" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="5904" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5906" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="5907" class="Symbol">)</a>
<a id="5909" href="Overture.Preliminaries.html#5854" class="Function">Π-syntax</a> <a id="5918" href="Overture.Preliminaries.html#5918" class="Bound">A</a> <a id="5920" href="Overture.Preliminaries.html#5920" class="Bound">B</a> <a id="5922" class="Symbol">=</a> <a id="5924" href="Overture.Preliminaries.html#5774" class="Function">Π</a> <a id="5926" href="Overture.Preliminaries.html#5920" class="Bound">B</a>

<a id="5929" class="Keyword">syntax</a> <a id="5936" href="Overture.Preliminaries.html#5854" class="Function">Π-syntax</a> <a id="5945" class="Bound">A</a> <a id="5947" class="Symbol">(λ</a> <a id="5950" class="Bound">x</a> <a id="5952" class="Symbol">→</a> <a id="5954" class="Bound">B</a><a id="5955" class="Symbol">)</a> <a id="5957" class="Symbol">=</a> <a id="5959" class="Function">Π[</a> <a id="5962" class="Bound">x</a> <a id="5964" class="Function">∈</a> <a id="5966" class="Bound">A</a> <a id="5968" class="Function">]</a> <a id="5970" class="Bound">B</a>
<a id="5972" class="Keyword">infix</a> <a id="5978" class="Number">6</a> <a id="5980" href="Overture.Preliminaries.html#5854" class="Function">Π-syntax</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
Type α : Type (lsuc α),   Type(lsuc α) : Type (lsuc (lsuc α)),  etc.
```

This means that the universe `Type α` has type `Type(lsuc α)`, and  `Type(lsuc α)` has type `Type(lsuc (lsuc α))`, and so on.  It is important to note, however, this does *not* imply that  `Type α : Type(lsuc(lsuc α))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

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

<a id="lift∼lower"></a><a id="8621" href="Overture.Preliminaries.html#8621" class="Function">lift∼lower</a> <a id="8632" class="Symbol">:</a> <a id="8634" class="Symbol">{</a><a id="8635" href="Overture.Preliminaries.html#8635" class="Bound">A</a> <a id="8637" class="Symbol">:</a> <a id="8639" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="8644" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="8645" class="Symbol">}</a> <a id="8647" class="Symbol">→</a> <a id="8649" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8654" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8656" href="Level.html#470" class="Field">lower</a> <a id="8662" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8664" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a> <a id="8667" class="Symbol">(</a><a id="8668" href="Level.html#400" class="Record">Lift</a> <a id="8673" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a> <a id="8675" href="Overture.Preliminaries.html#8635" class="Bound">A</a><a id="8676" class="Symbol">)</a>
<a id="8678" href="Overture.Preliminaries.html#8621" class="Function">lift∼lower</a> <a id="8689" class="Symbol">=</a> <a id="8691" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8697" href="Overture.Preliminaries.html#8697" class="Function">lower∼lift</a> <a id="8708" class="Symbol">:</a> <a id="8710" class="Symbol">{</a><a id="8711" href="Overture.Preliminaries.html#8711" class="Bound">A</a> <a id="8713" class="Symbol">:</a> <a id="8715" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="8720" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="8721" class="Symbol">}</a> <a id="8723" class="Symbol">→</a> <a id="8725" class="Symbol">(</a><a id="8726" href="Level.html#470" class="Field">lower</a> <a id="8732" class="Symbol">{</a><a id="8733" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="8734" class="Symbol">}{</a><a id="8736" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="8737" class="Symbol">})</a> <a id="8740" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8742" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8747" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8749" href="Overture.Preliminaries.html#5348" class="Function">𝑖𝑑</a> <a id="8752" href="Overture.Preliminaries.html#8711" class="Bound">A</a>
<a id="8754" href="Overture.Preliminaries.html#8697" class="Function">lower∼lift</a> <a id="8765" class="Symbol">=</a> <a id="8767" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Relations.Extensionality][] module.)

<pre class="Agda">

<a id="9301" class="Keyword">module</a> <a id="9308" href="Overture.Preliminaries.html#9308" class="Module">_</a> <a id="9310" class="Symbol">{</a><a id="9311" href="Overture.Preliminaries.html#9311" class="Bound">α</a> <a id="9313" class="Symbol">:</a> <a id="9315" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9320" class="Symbol">}{</a><a id="9322" href="Overture.Preliminaries.html#9322" class="Bound">A</a> <a id="9324" class="Symbol">:</a> <a id="9326" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="9331" href="Overture.Preliminaries.html#9311" class="Bound">α</a><a id="9332" class="Symbol">}{</a><a id="9334" href="Overture.Preliminaries.html#9334" class="Bound">β</a> <a id="9336" class="Symbol">:</a> <a id="9338" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9343" class="Symbol">}{</a><a id="9345" href="Overture.Preliminaries.html#9345" class="Bound">B</a> <a id="9347" class="Symbol">:</a> <a id="9349" href="Overture.Preliminaries.html#9322" class="Bound">A</a> <a id="9351" class="Symbol">→</a> <a id="9353" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="9358" href="Overture.Preliminaries.html#9334" class="Bound">β</a> <a id="9360" class="Symbol">}</a> <a id="9362" class="Keyword">where</a>

 <a id="9370" href="Overture.Preliminaries.html#9370" class="Function Operator">_≈_</a> <a id="9374" class="Symbol">:</a>  <a id="9377" class="Symbol">(</a><a id="9378" href="Overture.Preliminaries.html#9378" class="Bound">f</a> <a id="9380" href="Overture.Preliminaries.html#9380" class="Bound">g</a> <a id="9382" class="Symbol">:</a> <a id="9384" class="Symbol">(</a><a id="9385" href="Overture.Preliminaries.html#9385" class="Bound">a</a> <a id="9387" class="Symbol">:</a> <a id="9389" href="Overture.Preliminaries.html#9322" class="Bound">A</a><a id="9390" class="Symbol">)</a> <a id="9392" class="Symbol">→</a> <a id="9394" href="Overture.Preliminaries.html#9345" class="Bound">B</a> <a id="9396" href="Overture.Preliminaries.html#9385" class="Bound">a</a><a id="9397" class="Symbol">)</a> <a id="9399" class="Symbol">→</a> <a id="9401" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="9406" class="Symbol">(</a><a id="9407" href="Overture.Preliminaries.html#9311" class="Bound">α</a> <a id="9409" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9411" href="Overture.Preliminaries.html#9334" class="Bound">β</a><a id="9412" class="Symbol">)</a>
 <a id="9415" href="Overture.Preliminaries.html#9415" class="Bound">f</a> <a id="9417" href="Overture.Preliminaries.html#9370" class="Function Operator">≈</a> <a id="9419" href="Overture.Preliminaries.html#9419" class="Bound">g</a> <a id="9421" class="Symbol">=</a> <a id="9423" class="Symbol">∀</a> <a id="9425" href="Overture.Preliminaries.html#9425" class="Bound">x</a> <a id="9427" class="Symbol">→</a> <a id="9429" href="Overture.Preliminaries.html#9415" class="Bound">f</a> <a id="9431" href="Overture.Preliminaries.html#9425" class="Bound">x</a> <a id="9433" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9435" href="Overture.Preliminaries.html#9419" class="Bound">g</a> <a id="9437" href="Overture.Preliminaries.html#9425" class="Bound">x</a>

 <a id="9441" class="Keyword">infix</a> <a id="9447" class="Number">8</a> <a id="9449" href="Overture.Preliminaries.html#9370" class="Function Operator">_≈_</a>

 <a id="9455" href="Overture.Preliminaries.html#9455" class="Function">≈IsEquivalence</a> <a id="9470" class="Symbol">:</a> <a id="9472" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9486" href="Overture.Preliminaries.html#9370" class="Function Operator">_≈_</a>
 <a id="9491" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a> <a id="9510" href="Overture.Preliminaries.html#9455" class="Function">≈IsEquivalence</a> <a id="9525" class="Symbol">=</a> <a id="9527" class="Symbol">λ</a> <a id="9529" href="Overture.Preliminaries.html#9529" class="Bound">_</a> <a id="9531" class="Symbol">→</a> <a id="9533" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9539" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a> <a id="9557" href="Overture.Preliminaries.html#9455" class="Function">≈IsEquivalence</a> <a id="9572" class="Symbol">{</a><a id="9573" href="Overture.Preliminaries.html#9573" class="Bound">f</a><a id="9574" class="Symbol">}{</a><a id="9576" href="Overture.Preliminaries.html#9576" class="Bound">g</a><a id="9577" class="Symbol">}</a> <a id="9579" href="Overture.Preliminaries.html#9579" class="Bound">f≈g</a> <a id="9583" class="Symbol">=</a> <a id="9585" class="Symbol">λ</a> <a id="9587" href="Overture.Preliminaries.html#9587" class="Bound">x</a> <a id="9589" class="Symbol">→</a> <a id="9591" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9595" class="Symbol">(</a><a id="9596" href="Overture.Preliminaries.html#9579" class="Bound">f≈g</a> <a id="9600" href="Overture.Preliminaries.html#9587" class="Bound">x</a><a id="9601" class="Symbol">)</a>
 <a id="9604" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a> <a id="9624" href="Overture.Preliminaries.html#9455" class="Function">≈IsEquivalence</a> <a id="9639" class="Symbol">{</a><a id="9640" href="Overture.Preliminaries.html#9640" class="Bound">f</a><a id="9641" class="Symbol">}{</a><a id="9643" href="Overture.Preliminaries.html#9643" class="Bound">g</a><a id="9644" class="Symbol">}{</a><a id="9646" href="Overture.Preliminaries.html#9646" class="Bound">h</a><a id="9647" class="Symbol">}</a> <a id="9649" href="Overture.Preliminaries.html#9649" class="Bound">f≈g</a> <a id="9653" href="Overture.Preliminaries.html#9653" class="Bound">g≈h</a> <a id="9657" class="Symbol">=</a> <a id="9659" class="Symbol">λ</a> <a id="9661" href="Overture.Preliminaries.html#9661" class="Bound">x</a> <a id="9663" class="Symbol">→</a> <a id="9665" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9671" class="Symbol">(</a><a id="9672" href="Overture.Preliminaries.html#9649" class="Bound">f≈g</a> <a id="9676" href="Overture.Preliminaries.html#9661" class="Bound">x</a><a id="9677" class="Symbol">)</a> <a id="9679" class="Symbol">(</a><a id="9680" href="Overture.Preliminaries.html#9653" class="Bound">g≈h</a> <a id="9684" href="Overture.Preliminaries.html#9661" class="Bound">x</a><a id="9685" class="Symbol">)</a>

</pre>

The following is convenient for proving two pairs of a product type are equal using the fact that their
respective components are equal.

<pre class="Agda">

<a id="≡-by-parts"></a><a id="9852" href="Overture.Preliminaries.html#9852" class="Function">≡-by-parts</a> <a id="9863" class="Symbol">:</a> <a id="9865" class="Symbol">{</a><a id="9866" href="Overture.Preliminaries.html#9866" class="Bound">A</a> <a id="9868" class="Symbol">:</a> <a id="9870" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="9875" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a><a id="9876" class="Symbol">}{</a><a id="9878" href="Overture.Preliminaries.html#9878" class="Bound">B</a> <a id="9880" class="Symbol">:</a> <a id="9882" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="9887" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="9888" class="Symbol">}{</a><a id="9890" href="Overture.Preliminaries.html#9890" class="Bound">u</a> <a id="9892" href="Overture.Preliminaries.html#9892" class="Bound">v</a> <a id="9894" class="Symbol">:</a> <a id="9896" href="Overture.Preliminaries.html#9866" class="Bound">A</a> <a id="9898" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="9900" href="Overture.Preliminaries.html#9878" class="Bound">B</a><a id="9901" class="Symbol">}</a> <a id="9903" class="Symbol">→</a> <a id="9905" href="Overture.Preliminaries.html#2937" class="Field">fst</a> <a id="9909" href="Overture.Preliminaries.html#9890" class="Bound">u</a> <a id="9911" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9913" href="Overture.Preliminaries.html#2937" class="Field">fst</a> <a id="9917" href="Overture.Preliminaries.html#9892" class="Bound">v</a> <a id="9919" class="Symbol">→</a> <a id="9921" href="Overture.Preliminaries.html#2952" class="Field">snd</a> <a id="9925" href="Overture.Preliminaries.html#9890" class="Bound">u</a> <a id="9927" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9929" href="Overture.Preliminaries.html#2952" class="Field">snd</a> <a id="9933" href="Overture.Preliminaries.html#9892" class="Bound">v</a> <a id="9935" class="Symbol">→</a> <a id="9937" href="Overture.Preliminaries.html#9890" class="Bound">u</a> <a id="9939" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9941" href="Overture.Preliminaries.html#9892" class="Bound">v</a>
<a id="9943" href="Overture.Preliminaries.html#9852" class="Function">≡-by-parts</a> <a id="9954" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="9959" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="9964" class="Symbol">=</a> <a id="9966" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

Lastly, we will use the following type (instead of `subst`) to transport equality proofs.

<pre class="Agda">

<a id="transport"></a><a id="10089" href="Overture.Preliminaries.html#10089" class="Function">transport</a> <a id="10099" class="Symbol">:</a> <a id="10101" class="Symbol">{</a><a id="10102" href="Overture.Preliminaries.html#10102" class="Bound">A</a> <a id="10104" class="Symbol">:</a> <a id="10106" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="10111" href="Overture.Preliminaries.html#3322" class="Generalizable">α</a> <a id="10113" class="Symbol">}</a> <a id="10115" class="Symbol">(</a><a id="10116" href="Overture.Preliminaries.html#10116" class="Bound">B</a> <a id="10118" class="Symbol">:</a> <a id="10120" href="Overture.Preliminaries.html#10102" class="Bound">A</a> <a id="10122" class="Symbol">→</a> <a id="10124" href="Overture.Preliminaries.html#2824" class="Primitive">Type</a> <a id="10129" href="Overture.Preliminaries.html#3324" class="Generalizable">β</a><a id="10130" class="Symbol">)</a> <a id="10132" class="Symbol">{</a><a id="10133" href="Overture.Preliminaries.html#10133" class="Bound">x</a> <a id="10135" href="Overture.Preliminaries.html#10135" class="Bound">y</a> <a id="10137" class="Symbol">:</a> <a id="10139" href="Overture.Preliminaries.html#10102" class="Bound">A</a><a id="10140" class="Symbol">}</a> <a id="10142" class="Symbol">→</a> <a id="10144" href="Overture.Preliminaries.html#10133" class="Bound">x</a> <a id="10146" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10148" href="Overture.Preliminaries.html#10135" class="Bound">y</a> <a id="10150" class="Symbol">→</a> <a id="10152" href="Overture.Preliminaries.html#10116" class="Bound">B</a> <a id="10154" href="Overture.Preliminaries.html#10133" class="Bound">x</a> <a id="10156" class="Symbol">→</a> <a id="10158" href="Overture.Preliminaries.html#10116" class="Bound">B</a> <a id="10160" href="Overture.Preliminaries.html#10135" class="Bound">y</a>
<a id="10162" href="Overture.Preliminaries.html#10089" class="Function">transport</a> <a id="10172" href="Overture.Preliminaries.html#10172" class="Bound">B</a> <a id="10174" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10179" class="Symbol">=</a> <a id="10181" href="Function.Base.html#615" class="Function">id</a>

</pre>


------------------------------

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>



{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

[agda-algebras]: https://github.com/ualib/agda-algebras


