---
layout: default
title : Overture.Preliminaries module
date : 2021-01-13
author: [agda-algebras development team][]
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [agda-algebras][] library.

#### Logical foundations

(See also the Foundations module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [agda-algebras][] begins with the following line.

<pre class="Agda">

<a id="771" class="Symbol">{-#</a> <a id="775" class="Keyword">OPTIONS</a> <a id="783" class="Pragma">--without-K</a> <a id="795" class="Pragma">--exact-split</a> <a id="809" class="Pragma">--safe</a> <a id="816" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [agda-algebras][] library.

#### Agda Modules

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line, and then a list of imports of things used in the module.

<pre class="Agda">
<a id="2574" class="Keyword">module</a> <a id="2581" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="2604" class="Keyword">where</a>

<a id="2611" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library</a>
<a id="2676" class="Keyword">open</a> <a id="2681" class="Keyword">import</a> <a id="2688" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>              <a id="2716" class="Keyword">using</a> <a id="2722" class="Symbol">(</a> <a id="2724" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="2728" class="Symbol">;</a> <a id="2730" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2735" class="Symbol">)</a>           <a id="2747" class="Keyword">renaming</a> <a id="2756" class="Symbol">(</a> <a id="2758" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="2762" class="Symbol">to</a>  <a id="2766" class="Primitive">Type</a> <a id="2771" class="Symbol">;</a> <a id="2773" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="2779" class="Symbol">to</a>  <a id="2783" class="Primitive">ℓ₀</a> <a id="2786" class="Symbol">)</a>
<a id="2788" class="Keyword">open</a> <a id="2793" class="Keyword">import</a> <a id="2800" href="Data.Product.html" class="Module">Data.Product</a>                <a id="2828" class="Keyword">using</a> <a id="2834" class="Symbol">(</a> <a id="2836" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="2840" class="Symbol">;</a> <a id="2842" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="2851" class="Symbol">;</a> <a id="2853" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="2857" class="Symbol">)</a> <a id="2859" class="Keyword">renaming</a> <a id="2868" class="Symbol">(</a> <a id="2870" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="2876" class="Symbol">to</a> <a id="2879" class="Field">fst</a> <a id="2883" class="Symbol">;</a> <a id="2885" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="2891" class="Symbol">to</a> <a id="2894" class="Field">snd</a> <a id="2898" class="Symbol">)</a>
<a id="2900" class="Keyword">open</a> <a id="2905" class="Keyword">import</a> <a id="2912" href="Function.Base.html" class="Module">Function.Base</a>               <a id="2940" class="Keyword">using</a> <a id="2946" class="Symbol">(</a> <a id="2948" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="2952" class="Symbol">;</a> <a id="2954" href="Function.Base.html#615" class="Function">id</a> <a id="2957" class="Symbol">)</a>
<a id="2959" class="Keyword">open</a> <a id="2964" class="Keyword">import</a> <a id="2971" href="Level.html" class="Module">Level</a>                       <a id="2999" class="Keyword">using</a> <a id="3005" class="Symbol">(</a> <a id="3007" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3013" class="Symbol">;</a> <a id="3015" href="Level.html#400" class="Record">Lift</a> <a id="3020" class="Symbol">;</a> <a id="3022" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3027" class="Symbol">;</a> <a id="3029" href="Level.html#470" class="Field">lower</a> <a id="3035" class="Symbol">)</a>
<a id="3037" class="Keyword">open</a> <a id="3042" class="Keyword">import</a> <a id="3049" href="Relation.Binary.Structures.html" class="Module">Relation.Binary.Structures</a>  <a id="3077" class="Keyword">using</a> <a id="3083" class="Symbol">(</a> <a id="3085" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3099" class="Symbol">;</a> <a id="3101" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3116" class="Symbol">)</a>
<a id="3118" class="Keyword">open</a> <a id="3123" class="Keyword">import</a> <a id="3130" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                                        <a id="3208" class="Keyword">using</a>    <a id="3217" class="Symbol">(</a> <a id="3219" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3223" class="Symbol">;</a> <a id="3225" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3230" class="Symbol">;</a> <a id="3232" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3236" class="Symbol">;</a> <a id="3238" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3244" class="Symbol">)</a>

<a id="3247" class="Keyword">private</a> <a id="3255" class="Keyword">variable</a> <a id="3264" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="3266" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a> <a id="3268" class="Symbol">:</a> <a id="3270" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3277" href="Overture.Preliminaries.html#3277" class="Function">ℓ₁</a> <a id="3280" class="Symbol">:</a> <a id="3282" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3288" href="Overture.Preliminaries.html#3277" class="Function">ℓ₁</a> <a id="3291" class="Symbol">=</a> <a id="3293" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3298" href="Overture.Preliminaries.html#2783" class="Primitive">ℓ₀</a>

<a id="3302" class="Comment">-- The empty type</a>
<a id="3320" class="Keyword">data</a> <a id="𝟘"></a><a id="3325" href="Overture.Preliminaries.html#3325" class="Datatype">𝟘</a> <a id="3327" class="Symbol">:</a> <a id="3329" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="3334" href="Overture.Preliminaries.html#2783" class="Primitive">ℓ₀</a> <a id="3337" class="Keyword">where</a>  <a id="3344" class="Comment">-- maybe we should use ⊥ instead ...?</a>

<a id="3383" class="Comment">-- The one element type</a>
<a id="3407" class="Keyword">data</a> <a id="𝟙"></a><a id="3412" href="Overture.Preliminaries.html#3412" class="Datatype">𝟙</a> <a id="3414" class="Symbol">:</a> <a id="3416" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="3421" href="Overture.Preliminaries.html#2783" class="Primitive">ℓ₀</a> <a id="3424" class="Keyword">where</a>
 <a id="𝟙.𝟎"></a><a id="3431" href="Overture.Preliminaries.html#3431" class="InductiveConstructor">𝟎</a> <a id="3433" class="Symbol">:</a> <a id="3435" href="Overture.Preliminaries.html#3412" class="Datatype">𝟙</a>

<a id="3438" class="Comment">-- the two element type</a>
<a id="3462" class="Keyword">data</a> <a id="𝟚"></a><a id="3467" href="Overture.Preliminaries.html#3467" class="Datatype">𝟚</a> <a id="3469" class="Symbol">:</a> <a id="3471" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="3476" href="Overture.Preliminaries.html#2783" class="Primitive">ℓ₀</a> <a id="3479" class="Keyword">where</a>  <a id="3486" class="Comment">-- We could use Bool instead.</a>
 <a id="𝟚.𝟎"></a><a id="3517" href="Overture.Preliminaries.html#3517" class="InductiveConstructor">𝟎</a> <a id="3519" class="Symbol">:</a> <a id="3521" href="Overture.Preliminaries.html#3467" class="Datatype">𝟚</a>                  <a id="3540" class="Comment">-- &quot;         &quot; false &quot;   &quot;</a>
 <a id="𝟚.𝟏"></a><a id="3568" href="Overture.Preliminaries.html#3568" class="InductiveConstructor">𝟏</a> <a id="3570" class="Symbol">:</a> <a id="3572" href="Overture.Preliminaries.html#3467" class="Datatype">𝟚</a>                  <a id="3591" class="Comment">-- &quot;         &quot; true  &quot;   &quot;</a>

<a id="3619" class="Comment">-- the three element type</a>
<a id="3645" class="Keyword">data</a> <a id="𝟛"></a><a id="3650" href="Overture.Preliminaries.html#3650" class="Datatype">𝟛</a> <a id="3652" class="Symbol">:</a> <a id="3654" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="3659" href="Overture.Preliminaries.html#2783" class="Primitive">ℓ₀</a> <a id="3662" class="Keyword">where</a>
 <a id="𝟛.𝟎"></a><a id="3669" href="Overture.Preliminaries.html#3669" class="InductiveConstructor">𝟎</a> <a id="3671" class="Symbol">:</a> <a id="3673" href="Overture.Preliminaries.html#3650" class="Datatype">𝟛</a>
 <a id="𝟛.𝟏"></a><a id="3676" href="Overture.Preliminaries.html#3676" class="InductiveConstructor">𝟏</a> <a id="3678" class="Symbol">:</a> <a id="3680" href="Overture.Preliminaries.html#3650" class="Datatype">𝟛</a>
 <a id="𝟛.𝟐"></a><a id="3683" href="Overture.Preliminaries.html#3683" class="InductiveConstructor">𝟐</a> <a id="3685" class="Symbol">:</a> <a id="3687" href="Overture.Preliminaries.html#3650" class="Datatype">𝟛</a>

</pre>


#### Projection notation

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second projections out of the product.  However, we prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥`, respectively. We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4108" class="Keyword">module</a> <a id="4115" href="Overture.Preliminaries.html#4115" class="Module">_</a> <a id="4117" class="Symbol">{</a><a id="4118" href="Overture.Preliminaries.html#4118" class="Bound">A</a> <a id="4120" class="Symbol">:</a> <a id="4122" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="4127" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="4129" class="Symbol">}{</a><a id="4131" href="Overture.Preliminaries.html#4131" class="Bound">B</a> <a id="4133" class="Symbol">:</a> <a id="4135" href="Overture.Preliminaries.html#4118" class="Bound">A</a> <a id="4137" class="Symbol">→</a> <a id="4139" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="4144" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="4145" class="Symbol">}</a> <a id="4147" class="Keyword">where</a>

 <a id="4155" href="Overture.Preliminaries.html#4155" class="Function Operator">∣_∣</a> <a id="4159" class="Symbol">:</a> <a id="4161" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4164" href="Overture.Preliminaries.html#4164" class="Bound">x</a> <a id="4166" href="Data.Product.html#916" class="Function">∈</a> <a id="4168" href="Overture.Preliminaries.html#4118" class="Bound">A</a> <a id="4170" href="Data.Product.html#916" class="Function">]</a> <a id="4172" href="Overture.Preliminaries.html#4131" class="Bound">B</a> <a id="4174" href="Overture.Preliminaries.html#4164" class="Bound">x</a> <a id="4176" class="Symbol">→</a> <a id="4178" href="Overture.Preliminaries.html#4118" class="Bound">A</a>
 <a id="4181" href="Overture.Preliminaries.html#4155" class="Function Operator">∣_∣</a> <a id="4185" class="Symbol">=</a> <a id="4187" href="Overture.Preliminaries.html#2879" class="Field">fst</a>

 <a id="4193" href="Overture.Preliminaries.html#4193" class="Function Operator">∥_∥</a> <a id="4197" class="Symbol">:</a> <a id="4199" class="Symbol">(</a><a id="4200" href="Overture.Preliminaries.html#4200" class="Bound">z</a> <a id="4202" class="Symbol">:</a> <a id="4204" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4207" href="Overture.Preliminaries.html#4207" class="Bound">a</a> <a id="4209" href="Data.Product.html#916" class="Function">∈</a> <a id="4211" href="Overture.Preliminaries.html#4118" class="Bound">A</a> <a id="4213" href="Data.Product.html#916" class="Function">]</a> <a id="4215" href="Overture.Preliminaries.html#4131" class="Bound">B</a> <a id="4217" href="Overture.Preliminaries.html#4207" class="Bound">a</a><a id="4218" class="Symbol">)</a> <a id="4220" class="Symbol">→</a> <a id="4222" href="Overture.Preliminaries.html#4131" class="Bound">B</a> <a id="4224" href="Overture.Preliminaries.html#4155" class="Function Operator">∣</a> <a id="4226" href="Overture.Preliminaries.html#4200" class="Bound">z</a> <a id="4228" href="Overture.Preliminaries.html#4155" class="Function Operator">∣</a>
 <a id="4231" href="Overture.Preliminaries.html#4193" class="Function Operator">∥_∥</a> <a id="4235" class="Symbol">=</a> <a id="4237" href="Overture.Preliminaries.html#2894" class="Field">snd</a>

 <a id="4243" class="Keyword">infix</a>  <a id="4250" class="Number">40</a> <a id="4253" href="Overture.Preliminaries.html#4155" class="Function Operator">∣_∣</a>
</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

Let's define some useful syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4859" href="Overture.Preliminaries.html#4859" class="Function Operator">_⁻¹</a> <a id="4863" class="Symbol">:</a> <a id="4865" class="Symbol">{</a><a id="4866" href="Overture.Preliminaries.html#4866" class="Bound">A</a> <a id="4868" class="Symbol">:</a> <a id="4870" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="4875" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="4876" class="Symbol">}</a> <a id="4878" class="Symbol">{</a><a id="4879" href="Overture.Preliminaries.html#4879" class="Bound">x</a> <a id="4881" href="Overture.Preliminaries.html#4881" class="Bound">y</a> <a id="4883" class="Symbol">:</a> <a id="4885" href="Overture.Preliminaries.html#4866" class="Bound">A</a><a id="4886" class="Symbol">}</a> <a id="4888" class="Symbol">→</a> <a id="4890" href="Overture.Preliminaries.html#4879" class="Bound">x</a> <a id="4892" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4894" href="Overture.Preliminaries.html#4881" class="Bound">y</a> <a id="4896" class="Symbol">→</a> <a id="4898" href="Overture.Preliminaries.html#4881" class="Bound">y</a> <a id="4900" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4902" href="Overture.Preliminaries.html#4879" class="Bound">x</a>
<a id="4904" href="Overture.Preliminaries.html#4904" class="Bound">p</a> <a id="4906" href="Overture.Preliminaries.html#4859" class="Function Operator">⁻¹</a> <a id="4909" class="Symbol">=</a> <a id="4911" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="4915" href="Overture.Preliminaries.html#4904" class="Bound">p</a>

<a id="4918" class="Keyword">infix</a>  <a id="4925" class="Number">40</a> <a id="4928" href="Overture.Preliminaries.html#4859" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5185" href="Overture.Preliminaries.html#5185" class="Function Operator">_∙_</a> <a id="5189" class="Symbol">:</a> <a id="5191" class="Symbol">{</a><a id="5192" href="Overture.Preliminaries.html#5192" class="Bound">A</a> <a id="5194" class="Symbol">:</a> <a id="5196" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5201" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="5202" class="Symbol">}{</a><a id="5204" href="Overture.Preliminaries.html#5204" class="Bound">x</a> <a id="5206" href="Overture.Preliminaries.html#5206" class="Bound">y</a> <a id="5208" href="Overture.Preliminaries.html#5208" class="Bound">z</a> <a id="5210" class="Symbol">:</a> <a id="5212" href="Overture.Preliminaries.html#5192" class="Bound">A</a><a id="5213" class="Symbol">}</a> <a id="5215" class="Symbol">→</a> <a id="5217" href="Overture.Preliminaries.html#5204" class="Bound">x</a> <a id="5219" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5221" href="Overture.Preliminaries.html#5206" class="Bound">y</a> <a id="5223" class="Symbol">→</a> <a id="5225" href="Overture.Preliminaries.html#5206" class="Bound">y</a> <a id="5227" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5229" href="Overture.Preliminaries.html#5208" class="Bound">z</a> <a id="5231" class="Symbol">→</a> <a id="5233" href="Overture.Preliminaries.html#5204" class="Bound">x</a> <a id="5235" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5237" href="Overture.Preliminaries.html#5208" class="Bound">z</a>
<a id="5239" href="Overture.Preliminaries.html#5239" class="Bound">p</a> <a id="5241" href="Overture.Preliminaries.html#5185" class="Function Operator">∙</a> <a id="5243" href="Overture.Preliminaries.html#5243" class="Bound">q</a> <a id="5245" class="Symbol">=</a> <a id="5247" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5253" href="Overture.Preliminaries.html#5239" class="Bound">p</a> <a id="5255" href="Overture.Preliminaries.html#5243" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5258" href="Overture.Preliminaries.html#5258" class="Function">𝑖𝑑</a> <a id="5261" class="Symbol">:</a> <a id="5263" class="Symbol">(</a><a id="5264" href="Overture.Preliminaries.html#5264" class="Bound">A</a> <a id="5266" class="Symbol">:</a> <a id="5268" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5273" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="5275" class="Symbol">)</a> <a id="5277" class="Symbol">→</a> <a id="5279" href="Overture.Preliminaries.html#5264" class="Bound">A</a> <a id="5281" class="Symbol">→</a> <a id="5283" href="Overture.Preliminaries.html#5264" class="Bound">A</a>
<a id="5285" href="Overture.Preliminaries.html#5258" class="Function">𝑖𝑑</a> <a id="5288" href="Overture.Preliminaries.html#5288" class="Bound">A</a> <a id="5290" class="Symbol">=</a> <a id="5292" class="Symbol">λ</a> <a id="5294" href="Overture.Preliminaries.html#5294" class="Bound">x</a> <a id="5296" class="Symbol">→</a> <a id="5298" href="Overture.Preliminaries.html#5294" class="Bound">x</a>

<a id="5301" class="Keyword">infixl</a> <a id="5308" class="Number">30</a> <a id="5311" href="Overture.Preliminaries.html#5185" class="Function Operator">_∙_</a>
</pre>


#### Pi types

The dependent function type is traditionally denoted with a Pi symbol typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes `(x : A) → B x` for the dependent function type, but may use syntax that is closer to the standard Π notation and made available in Agda as follows.

<pre class="Agda">

<a id="Π"></a><a id="5663" href="Overture.Preliminaries.html#5663" class="Function">Π</a> <a id="5665" class="Symbol">:</a> <a id="5667" class="Symbol">{</a><a id="5668" href="Overture.Preliminaries.html#5668" class="Bound">A</a> <a id="5670" class="Symbol">:</a> <a id="5672" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5677" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="5679" class="Symbol">}</a> <a id="5681" class="Symbol">(</a><a id="5682" href="Overture.Preliminaries.html#5682" class="Bound">B</a> <a id="5684" class="Symbol">:</a> <a id="5686" href="Overture.Preliminaries.html#5668" class="Bound">A</a> <a id="5688" class="Symbol">→</a> <a id="5690" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5695" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a> <a id="5697" class="Symbol">)</a> <a id="5699" class="Symbol">→</a> <a id="5701" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5706" class="Symbol">(</a><a id="5707" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="5709" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5711" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="5712" class="Symbol">)</a>
<a id="5714" href="Overture.Preliminaries.html#5663" class="Function">Π</a> <a id="5716" class="Symbol">{</a><a id="5717" class="Argument">A</a> <a id="5719" class="Symbol">=</a> <a id="5721" href="Overture.Preliminaries.html#5721" class="Bound">A</a><a id="5722" class="Symbol">}</a> <a id="5724" href="Overture.Preliminaries.html#5724" class="Bound">B</a> <a id="5726" class="Symbol">=</a> <a id="5728" class="Symbol">(</a><a id="5729" href="Overture.Preliminaries.html#5729" class="Bound">x</a> <a id="5731" class="Symbol">:</a> <a id="5733" href="Overture.Preliminaries.html#5721" class="Bound">A</a><a id="5734" class="Symbol">)</a> <a id="5736" class="Symbol">→</a> <a id="5738" href="Overture.Preliminaries.html#5724" class="Bound">B</a> <a id="5740" href="Overture.Preliminaries.html#5729" class="Bound">x</a>

<a id="Π-syntax"></a><a id="5743" href="Overture.Preliminaries.html#5743" class="Function">Π-syntax</a> <a id="5752" class="Symbol">:</a> <a id="5754" class="Symbol">(</a><a id="5755" href="Overture.Preliminaries.html#5755" class="Bound">A</a> <a id="5757" class="Symbol">:</a> <a id="5759" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5764" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="5765" class="Symbol">)(</a><a id="5767" href="Overture.Preliminaries.html#5767" class="Bound">B</a> <a id="5769" class="Symbol">:</a> <a id="5771" href="Overture.Preliminaries.html#5755" class="Bound">A</a> <a id="5773" class="Symbol">→</a> <a id="5775" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5780" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="5781" class="Symbol">)</a> <a id="5783" class="Symbol">→</a> <a id="5785" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="5790" class="Symbol">(</a><a id="5791" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="5793" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5795" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="5796" class="Symbol">)</a>
<a id="5798" href="Overture.Preliminaries.html#5743" class="Function">Π-syntax</a> <a id="5807" href="Overture.Preliminaries.html#5807" class="Bound">A</a> <a id="5809" href="Overture.Preliminaries.html#5809" class="Bound">B</a> <a id="5811" class="Symbol">=</a> <a id="5813" href="Overture.Preliminaries.html#5663" class="Function">Π</a> <a id="5815" href="Overture.Preliminaries.html#5809" class="Bound">B</a>

<a id="5818" class="Keyword">syntax</a> <a id="5825" href="Overture.Preliminaries.html#5743" class="Function">Π-syntax</a> <a id="5834" class="Bound">A</a> <a id="5836" class="Symbol">(λ</a> <a id="5839" class="Bound">x</a> <a id="5841" class="Symbol">→</a> <a id="5843" class="Bound">B</a><a id="5844" class="Symbol">)</a> <a id="5846" class="Symbol">=</a> <a id="5848" class="Function">Π[</a> <a id="5851" class="Bound">x</a> <a id="5853" class="Function">∈</a> <a id="5855" class="Bound">A</a> <a id="5857" class="Function">]</a> <a id="5859" class="Bound">B</a>
<a id="5861" class="Keyword">infix</a> <a id="5867" class="Number">6</a> <a id="5869" href="Overture.Preliminaries.html#5743" class="Function">Π-syntax</a>

</pre>

#### Agda's universe hierarchy

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
Type α : Type (lsuc α),   Type(lsuc α) : Type (lsuc (lsuc α)),  etc.
```

This means that the universe `Type α` has type `Type(lsuc α)`, and  `Type(lsuc α)` has type `Type(lsuc (lsuc α))`, and so on.  It is important to note, however, this does *not* imply that  `Type α : Type(lsuc(lsuc α))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




#### Lifting and lowering

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

<a id="lift∼lower"></a><a id="8440" href="Overture.Preliminaries.html#8440" class="Function">lift∼lower</a> <a id="8451" class="Symbol">:</a> <a id="8453" class="Symbol">{</a><a id="8454" href="Overture.Preliminaries.html#8454" class="Bound">A</a> <a id="8456" class="Symbol">:</a> <a id="8458" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="8463" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="8464" class="Symbol">}</a> <a id="8466" class="Symbol">→</a> <a id="8468" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8473" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8475" href="Level.html#470" class="Field">lower</a> <a id="8481" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8483" href="Overture.Preliminaries.html#5258" class="Function">𝑖𝑑</a> <a id="8486" class="Symbol">(</a><a id="8487" href="Level.html#400" class="Record">Lift</a> <a id="8492" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a> <a id="8494" href="Overture.Preliminaries.html#8454" class="Bound">A</a><a id="8495" class="Symbol">)</a>
<a id="8497" href="Overture.Preliminaries.html#8440" class="Function">lift∼lower</a> <a id="8508" class="Symbol">=</a> <a id="8510" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8516" href="Overture.Preliminaries.html#8516" class="Function">lower∼lift</a> <a id="8527" class="Symbol">:</a> <a id="8529" class="Symbol">{</a><a id="8530" href="Overture.Preliminaries.html#8530" class="Bound">A</a> <a id="8532" class="Symbol">:</a> <a id="8534" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="8539" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="8540" class="Symbol">}</a> <a id="8542" class="Symbol">→</a> <a id="8544" class="Symbol">(</a><a id="8545" href="Level.html#470" class="Field">lower</a> <a id="8551" class="Symbol">{</a><a id="8552" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="8553" class="Symbol">}{</a><a id="8555" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="8556" class="Symbol">})</a> <a id="8559" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8561" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8566" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8568" href="Overture.Preliminaries.html#5258" class="Function">𝑖𝑑</a> <a id="8571" href="Overture.Preliminaries.html#8530" class="Bound">A</a>
<a id="8573" href="Overture.Preliminaries.html#8516" class="Function">lower∼lift</a> <a id="8584" class="Symbol">=</a> <a id="8586" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.

#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Relations.Extensionality][] module.)

<pre class="Agda">

<a id="9119" class="Comment">-- OLD notation</a>
<a id="9135" class="Comment">-- _∼_ : {A : Type α } {B : A → Type β } → (f g : (a : A) → B a) → Type (α ⊔ β)</a>
<a id="9215" class="Comment">-- f ∼ g = ∀ x → f x ≡ g x</a>

<a id="9243" class="Comment">-- NEW notation</a>
<a id="9259" class="Comment">-- (preferable since it coincides with the standard notation universally quantified equality)</a>
<a id="9353" class="Keyword">module</a> <a id="9360" href="Overture.Preliminaries.html#9360" class="Module">_</a> <a id="9362" class="Symbol">{</a><a id="9363" href="Overture.Preliminaries.html#9363" class="Bound">α</a> <a id="9365" class="Symbol">:</a> <a id="9367" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9372" class="Symbol">}{</a><a id="9374" href="Overture.Preliminaries.html#9374" class="Bound">A</a> <a id="9376" class="Symbol">:</a> <a id="9378" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="9383" href="Overture.Preliminaries.html#9363" class="Bound">α</a><a id="9384" class="Symbol">}{</a><a id="9386" href="Overture.Preliminaries.html#9386" class="Bound">β</a> <a id="9388" class="Symbol">:</a> <a id="9390" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9395" class="Symbol">}{</a><a id="9397" href="Overture.Preliminaries.html#9397" class="Bound">B</a> <a id="9399" class="Symbol">:</a> <a id="9401" href="Overture.Preliminaries.html#9374" class="Bound">A</a> <a id="9403" class="Symbol">→</a> <a id="9405" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="9410" href="Overture.Preliminaries.html#9386" class="Bound">β</a> <a id="9412" class="Symbol">}</a> <a id="9414" class="Keyword">where</a>

 <a id="9422" href="Overture.Preliminaries.html#9422" class="Function Operator">_≈_</a> <a id="9426" class="Symbol">:</a>  <a id="9429" class="Symbol">(</a><a id="9430" href="Overture.Preliminaries.html#9430" class="Bound">f</a> <a id="9432" href="Overture.Preliminaries.html#9432" class="Bound">g</a> <a id="9434" class="Symbol">:</a> <a id="9436" class="Symbol">(</a><a id="9437" href="Overture.Preliminaries.html#9437" class="Bound">a</a> <a id="9439" class="Symbol">:</a> <a id="9441" href="Overture.Preliminaries.html#9374" class="Bound">A</a><a id="9442" class="Symbol">)</a> <a id="9444" class="Symbol">→</a> <a id="9446" href="Overture.Preliminaries.html#9397" class="Bound">B</a> <a id="9448" href="Overture.Preliminaries.html#9437" class="Bound">a</a><a id="9449" class="Symbol">)</a> <a id="9451" class="Symbol">→</a> <a id="9453" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="9458" class="Symbol">(</a><a id="9459" href="Overture.Preliminaries.html#9363" class="Bound">α</a> <a id="9461" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9463" href="Overture.Preliminaries.html#9386" class="Bound">β</a><a id="9464" class="Symbol">)</a>
 <a id="9467" href="Overture.Preliminaries.html#9467" class="Bound">f</a> <a id="9469" href="Overture.Preliminaries.html#9422" class="Function Operator">≈</a> <a id="9471" href="Overture.Preliminaries.html#9471" class="Bound">g</a> <a id="9473" class="Symbol">=</a> <a id="9475" class="Symbol">∀</a> <a id="9477" href="Overture.Preliminaries.html#9477" class="Bound">x</a> <a id="9479" class="Symbol">→</a> <a id="9481" href="Overture.Preliminaries.html#9467" class="Bound">f</a> <a id="9483" href="Overture.Preliminaries.html#9477" class="Bound">x</a> <a id="9485" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9487" href="Overture.Preliminaries.html#9471" class="Bound">g</a> <a id="9489" href="Overture.Preliminaries.html#9477" class="Bound">x</a>

 <a id="9493" class="Keyword">infix</a> <a id="9499" class="Number">8</a> <a id="9501" href="Overture.Preliminaries.html#9422" class="Function Operator">_≈_</a>

 <a id="9507" href="Overture.Preliminaries.html#9507" class="Function">≈IsEquivalence</a> <a id="9522" class="Symbol">:</a> <a id="9524" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9538" href="Overture.Preliminaries.html#9422" class="Function Operator">_≈_</a>
 <a id="9543" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a> <a id="9562" href="Overture.Preliminaries.html#9507" class="Function">≈IsEquivalence</a> <a id="9577" class="Symbol">=</a> <a id="9579" class="Symbol">λ</a> <a id="9581" href="Overture.Preliminaries.html#9581" class="Bound">_</a> <a id="9583" class="Symbol">→</a> <a id="9585" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9591" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a> <a id="9609" href="Overture.Preliminaries.html#9507" class="Function">≈IsEquivalence</a> <a id="9624" class="Symbol">{</a><a id="9625" href="Overture.Preliminaries.html#9625" class="Bound">f</a><a id="9626" class="Symbol">}{</a><a id="9628" href="Overture.Preliminaries.html#9628" class="Bound">g</a><a id="9629" class="Symbol">}</a> <a id="9631" href="Overture.Preliminaries.html#9631" class="Bound">f≈g</a> <a id="9635" class="Symbol">=</a> <a id="9637" class="Symbol">λ</a> <a id="9639" href="Overture.Preliminaries.html#9639" class="Bound">x</a> <a id="9641" class="Symbol">→</a> <a id="9643" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9647" class="Symbol">(</a><a id="9648" href="Overture.Preliminaries.html#9631" class="Bound">f≈g</a> <a id="9652" href="Overture.Preliminaries.html#9639" class="Bound">x</a><a id="9653" class="Symbol">)</a>
 <a id="9656" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a> <a id="9676" href="Overture.Preliminaries.html#9507" class="Function">≈IsEquivalence</a> <a id="9691" class="Symbol">{</a><a id="9692" href="Overture.Preliminaries.html#9692" class="Bound">f</a><a id="9693" class="Symbol">}{</a><a id="9695" href="Overture.Preliminaries.html#9695" class="Bound">g</a><a id="9696" class="Symbol">}{</a><a id="9698" href="Overture.Preliminaries.html#9698" class="Bound">h</a><a id="9699" class="Symbol">}</a> <a id="9701" href="Overture.Preliminaries.html#9701" class="Bound">f≈g</a> <a id="9705" href="Overture.Preliminaries.html#9705" class="Bound">g≈h</a> <a id="9709" class="Symbol">=</a> <a id="9711" class="Symbol">λ</a> <a id="9713" href="Overture.Preliminaries.html#9713" class="Bound">x</a> <a id="9715" class="Symbol">→</a> <a id="9717" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9723" class="Symbol">(</a><a id="9724" href="Overture.Preliminaries.html#9701" class="Bound">f≈g</a> <a id="9728" href="Overture.Preliminaries.html#9713" class="Bound">x</a><a id="9729" class="Symbol">)</a> <a id="9731" class="Symbol">(</a><a id="9732" href="Overture.Preliminaries.html#9705" class="Bound">g≈h</a> <a id="9736" href="Overture.Preliminaries.html#9713" class="Bound">x</a><a id="9737" class="Symbol">)</a>

</pre>

The following is convenient for proving two pairs of a product type are equal using the fact that their
respective components are equal.

<pre class="Agda">

<a id="≡-by-parts"></a><a id="9904" href="Overture.Preliminaries.html#9904" class="Function">≡-by-parts</a> <a id="9915" class="Symbol">:</a> <a id="9917" class="Symbol">{</a><a id="9918" href="Overture.Preliminaries.html#9918" class="Bound">A</a> <a id="9920" class="Symbol">:</a> <a id="9922" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="9927" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a><a id="9928" class="Symbol">}{</a><a id="9930" href="Overture.Preliminaries.html#9930" class="Bound">B</a> <a id="9932" class="Symbol">:</a> <a id="9934" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="9939" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="9940" class="Symbol">}{</a><a id="9942" href="Overture.Preliminaries.html#9942" class="Bound">u</a> <a id="9944" href="Overture.Preliminaries.html#9944" class="Bound">v</a> <a id="9946" class="Symbol">:</a> <a id="9948" href="Overture.Preliminaries.html#9918" class="Bound">A</a> <a id="9950" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="9952" href="Overture.Preliminaries.html#9930" class="Bound">B</a><a id="9953" class="Symbol">}</a> <a id="9955" class="Symbol">→</a> <a id="9957" href="Overture.Preliminaries.html#2879" class="Field">fst</a> <a id="9961" href="Overture.Preliminaries.html#9942" class="Bound">u</a> <a id="9963" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9965" href="Overture.Preliminaries.html#2879" class="Field">fst</a> <a id="9969" href="Overture.Preliminaries.html#9944" class="Bound">v</a> <a id="9971" class="Symbol">→</a> <a id="9973" href="Overture.Preliminaries.html#2894" class="Field">snd</a> <a id="9977" href="Overture.Preliminaries.html#9942" class="Bound">u</a> <a id="9979" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9981" href="Overture.Preliminaries.html#2894" class="Field">snd</a> <a id="9985" href="Overture.Preliminaries.html#9944" class="Bound">v</a> <a id="9987" class="Symbol">→</a> <a id="9989" href="Overture.Preliminaries.html#9942" class="Bound">u</a> <a id="9991" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9993" href="Overture.Preliminaries.html#9944" class="Bound">v</a>
<a id="9995" href="Overture.Preliminaries.html#9904" class="Function">≡-by-parts</a> <a id="10006" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10011" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10016" class="Symbol">=</a> <a id="10018" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

Lastly, we will use the following type (instead of `subst`) to transport equality proofs.

<pre class="Agda">

<a id="transport"></a><a id="10141" href="Overture.Preliminaries.html#10141" class="Function">transport</a> <a id="10151" class="Symbol">:</a> <a id="10153" class="Symbol">{</a><a id="10154" href="Overture.Preliminaries.html#10154" class="Bound">A</a> <a id="10156" class="Symbol">:</a> <a id="10158" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="10163" href="Overture.Preliminaries.html#3264" class="Generalizable">α</a> <a id="10165" class="Symbol">}</a> <a id="10167" class="Symbol">(</a><a id="10168" href="Overture.Preliminaries.html#10168" class="Bound">B</a> <a id="10170" class="Symbol">:</a> <a id="10172" href="Overture.Preliminaries.html#10154" class="Bound">A</a> <a id="10174" class="Symbol">→</a> <a id="10176" href="Overture.Preliminaries.html#2766" class="Primitive">Type</a> <a id="10181" href="Overture.Preliminaries.html#3266" class="Generalizable">β</a><a id="10182" class="Symbol">)</a> <a id="10184" class="Symbol">{</a><a id="10185" href="Overture.Preliminaries.html#10185" class="Bound">x</a> <a id="10187" href="Overture.Preliminaries.html#10187" class="Bound">y</a> <a id="10189" class="Symbol">:</a> <a id="10191" href="Overture.Preliminaries.html#10154" class="Bound">A</a><a id="10192" class="Symbol">}</a> <a id="10194" class="Symbol">→</a> <a id="10196" href="Overture.Preliminaries.html#10185" class="Bound">x</a> <a id="10198" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10200" href="Overture.Preliminaries.html#10187" class="Bound">y</a> <a id="10202" class="Symbol">→</a> <a id="10204" href="Overture.Preliminaries.html#10168" class="Bound">B</a> <a id="10206" href="Overture.Preliminaries.html#10185" class="Bound">x</a> <a id="10208" class="Symbol">→</a> <a id="10210" href="Overture.Preliminaries.html#10168" class="Bound">B</a> <a id="10212" href="Overture.Preliminaries.html#10187" class="Bound">y</a>
<a id="10214" href="Overture.Preliminaries.html#10141" class="Function">transport</a> <a id="10224" href="Overture.Preliminaries.html#10224" class="Bound">B</a> <a id="10226" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10231" class="Symbol">=</a> <a id="10233" href="Function.Base.html#615" class="Function">id</a>

</pre>






------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

[agda-algebras]: https://github.com/ualib/agda-algebras


