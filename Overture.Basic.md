---
layout: default
title : "Overture.Basic module"
date : "2021-01-13"
author: "the agda-algebras development team"
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Basic][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

(See also the Equality module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types
from existing Agda libraries. Options are specified with the `OPTIONS` *pragma*
and control the way Agda behaves by, for example, specifying the logical axioms
and deduction rules we wish to assume when the program is type-checked to verify
its correctness. Every Agda program in [agda-algebras][] begins with the following line.

<pre class="Agda">

<a id="799" class="Symbol">{-#</a> <a id="803" class="Keyword">OPTIONS</a> <a id="811" class="Pragma">--without-K</a> <a id="823" class="Pragma">--exact-split</a> <a id="837" class="Pragma">--safe</a> <a id="844" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when
type-checking the program to verify its correctness.

*  `--without-K` disables 
   [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29);
   see also the
   [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html)
   in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language).

*  `--exact-split` makes Agda accept only those definitions that behave like so-called
   *judgmental* equalities.  [Martín Escardó](https://www.cs.bham.ac.uk/~mhe) explains
   this by saying it "makes sure that pattern matching corresponds to Martin-Löf
   eliminators;" see also the
   [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality)
   of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation.

*  `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be
   an explicit assumption (e.g., an argument to a function or module); see also
   [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe)
   of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation and the
   [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda)
   of the [Agda Language Reference](https://agda.readthedocs.io/en/v2.6.1.3/language).

Note that if we wish to type-check a file that imports another file that still 
has some unmet proof obligations, we must replace the `--safe` flag with 
`--allow-unsolved-metas`, but this is never done in (publicly released versions
 of) the [agda-algebras][].


#### <a id="agda-modules">Agda modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example,
the [Base.Functions.Basic][] module begins with the following line, and then a
list of imports of things used in the module.
<pre class="Agda">

<a id="2891" class="Keyword">module</a> <a id="2898" href="Overture.Basic.html" class="Module">Overture.Basic</a> <a id="2913" class="Keyword">where</a>

<a id="2920" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------------------------</a>
<a id="3019" class="Keyword">open</a> <a id="3024" class="Keyword">import</a> <a id="3031" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="3049" class="Keyword">using</a> <a id="3055" class="Symbol">()</a> <a id="3058" class="Keyword">renaming</a> <a id="3067" class="Symbol">(</a> <a id="3069" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3073" class="Symbol">to</a>  <a id="3077" class="Primitive">Type</a> <a id="3082" class="Symbol">;</a> <a id="3084" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="3090" class="Symbol">to</a>  <a id="3094" class="Primitive">ℓ₀</a> <a id="3097" class="Symbol">)</a>
<a id="3099" class="Keyword">open</a> <a id="3104" class="Keyword">import</a> <a id="3111" href="Data.Product.html" class="Module">Data.Product</a>      <a id="3129" class="Keyword">using</a> <a id="3135" class="Symbol">(</a> <a id="3137" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="3141" class="Symbol">;</a> <a id="3143" href="Data.Product.html#1369" class="Function">∃</a> <a id="3145" class="Symbol">;</a> <a id="3147" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="3156" class="Symbol">;</a> <a id="3158" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="3162" class="Symbol">)</a>
                              <a id="3194" class="Keyword">renaming</a> <a id="3203" class="Symbol">(</a> <a id="3205" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="3211" class="Symbol">to</a> <a id="3214" class="Field">fst</a> <a id="3218" class="Symbol">;</a> <a id="3220" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="3226" class="Symbol">to</a> <a id="3229" class="Field">snd</a> <a id="3233" class="Symbol">)</a>
<a id="3235" class="Keyword">open</a> <a id="3240" class="Keyword">import</a> <a id="3247" href="Function.Base.html" class="Module">Function.Base</a>     <a id="3265" class="Keyword">using</a> <a id="3271" class="Symbol">(</a> <a id="3273" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3277" class="Symbol">;</a> <a id="3279" href="Function.Base.html#615" class="Function">id</a> <a id="3282" class="Symbol">)</a>
<a id="3284" class="Keyword">open</a> <a id="3289" class="Keyword">import</a> <a id="3296" href="Level.html" class="Module">Level</a>             <a id="3314" class="Keyword">using</a> <a id="3320" class="Symbol">(</a> <a id="3322" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3328" class="Symbol">;</a> <a id="3330" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3334" class="Symbol">;</a> <a id="3336" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3340" class="Symbol">;</a> <a id="3342" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3347" class="Symbol">;</a> <a id="3349" href="Level.html#470" class="Field">lower</a> <a id="3355" class="Symbol">;</a> <a id="3357" href="Level.html#400" class="Record">Lift</a> <a id="3362" class="Symbol">)</a>
<a id="3364" class="Keyword">open</a> <a id="3369" class="Keyword">import</a> <a id="3376" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3394" class="Keyword">using</a> <a id="3400" class="Symbol">(</a> <a id="3402" href="Relation.Binary.Definitions.html#4687" class="Function">Decidable</a> <a id="3412" class="Symbol">)</a>
<a id="3414" class="Keyword">open</a> <a id="3419" class="Keyword">import</a> <a id="3426" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3444" class="Keyword">using</a> <a id="3450" class="Symbol">(</a> <a id="3452" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3466" class="Symbol">;</a> <a id="3468" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3483" class="Symbol">)</a>
<a id="3485" class="Keyword">open</a> <a id="3490" class="Keyword">import</a> <a id="3497" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>  <a id="3515" class="Keyword">using</a> <a id="3521" class="Symbol">(</a> <a id="3523" href="Relation.Nullary.html#1511" class="Record">Dec</a> <a id="3527" class="Symbol">;</a> <a id="3529" href="Relation.Nullary.html#1648" class="InductiveConstructor">yes</a> <a id="3533" class="Symbol">;</a> <a id="3535" href="Relation.Nullary.html#1685" class="InductiveConstructor">no</a> <a id="3538" class="Symbol">;</a> <a id="3540" href="Relation.Nullary.html#2040" class="Function">Irrelevant</a> <a id="3551" class="Symbol">)</a>

<a id="3554" class="Keyword">open</a> <a id="3559" class="Keyword">import</a> <a id="3566" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="3604" class="Keyword">using</a> <a id="3610" class="Symbol">(</a> <a id="3612" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3616" class="Symbol">;</a> <a id="3618" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3623" class="Symbol">;</a> <a id="3625" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3629" class="Symbol">;</a> <a id="3631" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3637" class="Symbol">)</a>

<a id="3640" class="Keyword">private</a> <a id="3648" class="Keyword">variable</a> <a id="3657" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="3659" href="Overture.Basic.html#3659" class="Generalizable">β</a> <a id="3661" class="Symbol">:</a> <a id="3663" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3670" href="Overture.Basic.html#3670" class="Function">ℓ₁</a> <a id="3673" class="Symbol">:</a> <a id="3675" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3681" href="Overture.Basic.html#3670" class="Function">ℓ₁</a> <a id="3684" class="Symbol">=</a> <a id="3686" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3690" href="Overture.Basic.html#3094" class="Primitive">ℓ₀</a>

<a id="3694" class="Comment">-- the two element type</a>
<a id="3718" class="Keyword">data</a> <a id="𝟚"></a><a id="3723" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="3725" class="Symbol">:</a> <a id="3727" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="3732" href="Overture.Basic.html#3094" class="Primitive">ℓ₀</a> <a id="3735" class="Keyword">where</a> <a id="𝟚.𝟎"></a><a id="3741" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟎</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="3747" class="Symbol">;</a>  <a id="𝟚.𝟏"></a><a id="3750" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟏</a> <a id="3752" class="Symbol">:</a> <a id="3754" href="Overture.Basic.html#3723" class="Datatype">𝟚</a>

<a id="3757" class="Comment">-- the three element type</a>
<a id="3783" class="Keyword">data</a> <a id="𝟛"></a><a id="3788" href="Overture.Basic.html#3788" class="Datatype">𝟛</a> <a id="3790" class="Symbol">:</a> <a id="3792" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="3797" href="Overture.Basic.html#3094" class="Primitive">ℓ₀</a> <a id="3800" class="Keyword">where</a> <a id="𝟛.𝟎"></a><a id="3806" href="Overture.Basic.html#3806" class="InductiveConstructor">𝟎</a> <a id="3808" class="Symbol">:</a> <a id="3810" href="Overture.Basic.html#3788" class="Datatype">𝟛</a> <a id="3812" class="Symbol">;</a>  <a id="𝟛.𝟏"></a><a id="3815" href="Overture.Basic.html#3815" class="InductiveConstructor">𝟏</a> <a id="3817" class="Symbol">:</a> <a id="3819" href="Overture.Basic.html#3788" class="Datatype">𝟛</a> <a id="3821" class="Symbol">;</a>  <a id="𝟛.𝟐"></a><a id="3824" href="Overture.Basic.html#3824" class="InductiveConstructor">𝟐</a> <a id="3826" class="Symbol">:</a> <a id="3828" href="Overture.Basic.html#3788" class="Datatype">𝟛</a>
</pre>

#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂`
representing the first and second projections out of the product.  However, we
prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these
projections by `∣_∣` and `∥_∥`, respectively. We define these alternative
notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4279" class="Keyword">module</a> <a id="4286" href="Overture.Basic.html#4286" class="Module">_</a> <a id="4288" class="Symbol">{</a><a id="4289" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4291" class="Symbol">:</a> <a id="4293" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4298" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="4300" class="Symbol">}{</a><a id="4302" href="Overture.Basic.html#4302" class="Bound">B</a> <a id="4304" class="Symbol">:</a> <a id="4306" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4308" class="Symbol">→</a> <a id="4310" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4315" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="4316" class="Symbol">}</a> <a id="4318" class="Keyword">where</a>

 <a id="4326" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a> <a id="4330" class="Symbol">:</a> <a id="4332" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4335" href="Overture.Basic.html#4335" class="Bound">x</a> <a id="4337" href="Data.Product.html#916" class="Function">∈</a> <a id="4339" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4341" href="Data.Product.html#916" class="Function">]</a> <a id="4343" href="Overture.Basic.html#4302" class="Bound">B</a> <a id="4345" href="Overture.Basic.html#4335" class="Bound">x</a> <a id="4347" class="Symbol">→</a> <a id="4349" href="Overture.Basic.html#4289" class="Bound">A</a>
 <a id="4352" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a> <a id="4356" class="Symbol">=</a> <a id="4358" href="Overture.Basic.html#3214" class="Field">fst</a>

 <a id="4364" href="Overture.Basic.html#4364" class="Function Operator">∥_∥</a> <a id="4368" class="Symbol">:</a> <a id="4370" class="Symbol">(</a><a id="4371" href="Overture.Basic.html#4371" class="Bound">z</a> <a id="4373" class="Symbol">:</a> <a id="4375" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4378" href="Overture.Basic.html#4378" class="Bound">a</a> <a id="4380" href="Data.Product.html#916" class="Function">∈</a> <a id="4382" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4384" href="Data.Product.html#916" class="Function">]</a> <a id="4386" href="Overture.Basic.html#4302" class="Bound">B</a> <a id="4388" href="Overture.Basic.html#4378" class="Bound">a</a><a id="4389" class="Symbol">)</a> <a id="4391" class="Symbol">→</a> <a id="4393" href="Overture.Basic.html#4302" class="Bound">B</a> <a id="4395" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="4397" href="Overture.Basic.html#4371" class="Bound">z</a> <a id="4399" href="Overture.Basic.html#4326" class="Function Operator">∣</a>
 <a id="4402" href="Overture.Basic.html#4364" class="Function Operator">∥_∥</a> <a id="4406" class="Symbol">=</a> <a id="4408" href="Overture.Basic.html#3229" class="Field">snd</a>

 <a id="4414" class="Keyword">infix</a>  <a id="4421" class="Number">40</a> <a id="4424" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the
 `module` keyword followed by an underscore (instead of a module name). The
purpose is simply to move the postulated typing judgments---the "parameters"
of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate
the definitions inside the module.

Let's define some useful syntactic sugar that will make it easier to apply
symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4920" href="Overture.Basic.html#4920" class="Function Operator">_⁻¹</a> <a id="4924" class="Symbol">:</a> <a id="4926" class="Symbol">{</a><a id="4927" href="Overture.Basic.html#4927" class="Bound">A</a> <a id="4929" class="Symbol">:</a> <a id="4931" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4936" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="4937" class="Symbol">}</a> <a id="4939" class="Symbol">{</a><a id="4940" href="Overture.Basic.html#4940" class="Bound">x</a> <a id="4942" href="Overture.Basic.html#4942" class="Bound">y</a> <a id="4944" class="Symbol">:</a> <a id="4946" href="Overture.Basic.html#4927" class="Bound">A</a><a id="4947" class="Symbol">}</a> <a id="4949" class="Symbol">→</a> <a id="4951" href="Overture.Basic.html#4940" class="Bound">x</a> <a id="4953" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4955" href="Overture.Basic.html#4942" class="Bound">y</a> <a id="4957" class="Symbol">→</a> <a id="4959" href="Overture.Basic.html#4942" class="Bound">y</a> <a id="4961" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4963" href="Overture.Basic.html#4940" class="Bound">x</a>
<a id="4965" href="Overture.Basic.html#4965" class="Bound">p</a> <a id="4967" href="Overture.Basic.html#4920" class="Function Operator">⁻¹</a> <a id="4970" class="Symbol">=</a> <a id="4972" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="4976" href="Overture.Basic.html#4965" class="Bound">p</a>

<a id="4979" class="Keyword">infix</a>  <a id="4986" class="Number">40</a> <a id="4989" href="Overture.Basic.html#4920" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of
`sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic
sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5246" href="Overture.Basic.html#5246" class="Function Operator">_∙_</a> <a id="5250" class="Symbol">:</a> <a id="5252" class="Symbol">{</a><a id="5253" href="Overture.Basic.html#5253" class="Bound">A</a> <a id="5255" class="Symbol">:</a> <a id="5257" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5262" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="5263" class="Symbol">}{</a><a id="5265" href="Overture.Basic.html#5265" class="Bound">x</a> <a id="5267" href="Overture.Basic.html#5267" class="Bound">y</a> <a id="5269" href="Overture.Basic.html#5269" class="Bound">z</a> <a id="5271" class="Symbol">:</a> <a id="5273" href="Overture.Basic.html#5253" class="Bound">A</a><a id="5274" class="Symbol">}</a> <a id="5276" class="Symbol">→</a> <a id="5278" href="Overture.Basic.html#5265" class="Bound">x</a> <a id="5280" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5282" href="Overture.Basic.html#5267" class="Bound">y</a> <a id="5284" class="Symbol">→</a> <a id="5286" href="Overture.Basic.html#5267" class="Bound">y</a> <a id="5288" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5290" href="Overture.Basic.html#5269" class="Bound">z</a> <a id="5292" class="Symbol">→</a> <a id="5294" href="Overture.Basic.html#5265" class="Bound">x</a> <a id="5296" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5298" href="Overture.Basic.html#5269" class="Bound">z</a>
<a id="5300" href="Overture.Basic.html#5300" class="Bound">p</a> <a id="5302" href="Overture.Basic.html#5246" class="Function Operator">∙</a> <a id="5304" href="Overture.Basic.html#5304" class="Bound">q</a> <a id="5306" class="Symbol">=</a> <a id="5308" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5314" href="Overture.Basic.html#5300" class="Bound">p</a> <a id="5316" href="Overture.Basic.html#5304" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5319" href="Overture.Basic.html#5319" class="Function">𝑖𝑑</a> <a id="5322" class="Symbol">:</a> <a id="5324" class="Symbol">(</a><a id="5325" href="Overture.Basic.html#5325" class="Bound">A</a> <a id="5327" class="Symbol">:</a> <a id="5329" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5334" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="5336" class="Symbol">)</a> <a id="5338" class="Symbol">→</a> <a id="5340" href="Overture.Basic.html#5325" class="Bound">A</a> <a id="5342" class="Symbol">→</a> <a id="5344" href="Overture.Basic.html#5325" class="Bound">A</a>
<a id="5346" href="Overture.Basic.html#5319" class="Function">𝑖𝑑</a> <a id="5349" href="Overture.Basic.html#5349" class="Bound">A</a> <a id="5351" class="Symbol">=</a> <a id="5353" class="Symbol">λ</a> <a id="5355" href="Overture.Basic.html#5355" class="Bound">x</a> <a id="5357" class="Symbol">→</a> <a id="5359" href="Overture.Basic.html#5355" class="Bound">x</a>

<a id="5362" class="Keyword">infixl</a> <a id="5369" class="Number">30</a> <a id="5372" href="Overture.Basic.html#5246" class="Function Operator">_∙_</a>
</pre>

#### <a id="sigma-types">Sigma types</a>

<pre class="Agda">

<a id="5444" class="Keyword">infix</a> <a id="5450" class="Number">2</a> <a id="5452" href="Overture.Basic.html#5462" class="Function">∃-syntax</a>

<a id="∃-syntax"></a><a id="5462" href="Overture.Basic.html#5462" class="Function">∃-syntax</a> <a id="5471" class="Symbol">:</a> <a id="5473" class="Symbol">∀</a> <a id="5475" class="Symbol">{</a><a id="5476" href="Overture.Basic.html#5476" class="Bound">A</a> <a id="5478" class="Symbol">:</a> <a id="5480" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5485" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="5486" class="Symbol">}</a> <a id="5488" class="Symbol">→</a> <a id="5490" class="Symbol">(</a><a id="5491" href="Overture.Basic.html#5476" class="Bound">A</a> <a id="5493" class="Symbol">→</a> <a id="5495" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5500" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="5501" class="Symbol">)</a> <a id="5503" class="Symbol">→</a> <a id="5505" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="5509" class="Symbol">(</a><a id="5510" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="5512" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5514" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="5515" class="Symbol">)</a>
<a id="5517" href="Overture.Basic.html#5462" class="Function">∃-syntax</a> <a id="5526" class="Symbol">=</a> <a id="5528" href="Data.Product.html#1369" class="Function">∃</a>

<a id="5531" class="Keyword">syntax</a> <a id="5538" href="Overture.Basic.html#5462" class="Function">∃-syntax</a> <a id="5547" class="Symbol">(λ</a> <a id="5550" class="Bound">x</a> <a id="5552" class="Symbol">→</a> <a id="5554" class="Bound">B</a><a id="5555" class="Symbol">)</a> <a id="5557" class="Symbol">=</a> <a id="5559" class="Function">∃[</a> <a id="5562" class="Bound">x</a> <a id="5564" class="Function">∈</a> <a id="5566" class="Function">A</a> <a id="5568" class="Function">]</a> <a id="5570" class="Bound">B</a>
</pre>

#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with an uppercase pi symbol
and typically expressed as `Π(x : A) B x`, or something similar.  In Agda syntax,
one writes `(x : A) → B x` for this dependent function type, but we can define
syntax that is closer to standard notation as follows.

<pre class="Agda">

<a id="Π"></a><a id="5932" href="Overture.Basic.html#5932" class="Function">Π</a> <a id="5934" class="Symbol">:</a> <a id="5936" class="Symbol">{</a><a id="5937" href="Overture.Basic.html#5937" class="Bound">A</a> <a id="5939" class="Symbol">:</a> <a id="5941" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5946" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="5948" class="Symbol">}</a> <a id="5950" class="Symbol">(</a><a id="5951" href="Overture.Basic.html#5951" class="Bound">B</a> <a id="5953" class="Symbol">:</a> <a id="5955" href="Overture.Basic.html#5937" class="Bound">A</a> <a id="5957" class="Symbol">→</a> <a id="5959" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5964" href="Overture.Basic.html#3659" class="Generalizable">β</a> <a id="5966" class="Symbol">)</a> <a id="5968" class="Symbol">→</a> <a id="5970" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5975" class="Symbol">(</a><a id="5976" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="5978" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5980" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="5981" class="Symbol">)</a>
<a id="5983" href="Overture.Basic.html#5932" class="Function">Π</a> <a id="5985" class="Symbol">{</a><a id="5986" class="Argument">A</a> <a id="5988" class="Symbol">=</a> <a id="5990" href="Overture.Basic.html#5990" class="Bound">A</a><a id="5991" class="Symbol">}</a> <a id="5993" href="Overture.Basic.html#5993" class="Bound">B</a> <a id="5995" class="Symbol">=</a> <a id="5997" class="Symbol">(</a><a id="5998" href="Overture.Basic.html#5998" class="Bound">x</a> <a id="6000" class="Symbol">:</a> <a id="6002" href="Overture.Basic.html#5990" class="Bound">A</a><a id="6003" class="Symbol">)</a> <a id="6005" class="Symbol">→</a> <a id="6007" href="Overture.Basic.html#5993" class="Bound">B</a> <a id="6009" href="Overture.Basic.html#5998" class="Bound">x</a>

<a id="Π-syntax"></a><a id="6012" href="Overture.Basic.html#6012" class="Function">Π-syntax</a> <a id="6021" class="Symbol">:</a> <a id="6023" class="Symbol">(</a><a id="6024" href="Overture.Basic.html#6024" class="Bound">A</a> <a id="6026" class="Symbol">:</a> <a id="6028" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6033" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="6034" class="Symbol">)(</a><a id="6036" href="Overture.Basic.html#6036" class="Bound">B</a> <a id="6038" class="Symbol">:</a> <a id="6040" href="Overture.Basic.html#6024" class="Bound">A</a> <a id="6042" class="Symbol">→</a> <a id="6044" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6049" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="6050" class="Symbol">)</a> <a id="6052" class="Symbol">→</a> <a id="6054" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6059" class="Symbol">(</a><a id="6060" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="6062" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6064" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="6065" class="Symbol">)</a>
<a id="6067" href="Overture.Basic.html#6012" class="Function">Π-syntax</a> <a id="6076" href="Overture.Basic.html#6076" class="Bound">A</a> <a id="6078" href="Overture.Basic.html#6078" class="Bound">B</a> <a id="6080" class="Symbol">=</a> <a id="6082" href="Overture.Basic.html#5932" class="Function">Π</a> <a id="6084" href="Overture.Basic.html#6078" class="Bound">B</a>

<a id="6087" class="Keyword">syntax</a> <a id="6094" href="Overture.Basic.html#6012" class="Function">Π-syntax</a> <a id="6103" class="Bound">A</a> <a id="6105" class="Symbol">(λ</a> <a id="6108" class="Bound">x</a> <a id="6110" class="Symbol">→</a> <a id="6112" class="Bound">B</a><a id="6113" class="Symbol">)</a> <a id="6115" class="Symbol">=</a> <a id="6117" class="Function">Π[</a> <a id="6120" class="Bound">x</a> <a id="6122" class="Function">∈</a> <a id="6124" class="Bound">A</a> <a id="6126" class="Function">]</a> <a id="6128" class="Bound">B</a>
<a id="6130" class="Keyword">infix</a> <a id="6136" class="Number">6</a> <a id="6138" href="Overture.Basic.html#6012" class="Function">Π-syntax</a>

</pre>
In the modules that follow, we will see many examples of this syntax in action.


#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:
```agda

Type α : Type (lsuc α) ,   Type (lsuc α) : Type (lsuc (lsuc α)) , etc.

```
and so on. This means that the universe `Type α` has type `Type(lsuc α)`, and
`Type(lsuc α)` has type `Type(lsuc (lsuc α))`, and so on.  It is important to
note, however, this does *not* imply that  `Type α : Type(lsuc(lsuc α))`. In other
words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to
treat universe levels more precisely, which is nice. On the other hand, a
non-cumulative hierarchy can sometimes make for a non-fun proof assistant.
Specifically, in certain situations, the non-cumulativity makes it unduly
difficult to convince Agda that a program or proof is correct.


#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue
described in the previous subsection.  In the [Lifts of algebras
section](Base.Algebras.Basic.html#lifts-of-algebras) of the
[Base.Algebras.Basic][] module we will define a couple domain-specific lifting
types which have certain properties that make them useful for resolving universe
level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical
example. Agda will often complain with errors like the following:
```
Birkhoff.lagda:498,20-23
α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that the expression... has type...
```
This error message means that Agda encountered the universe level `lsuc α`, on
line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type
at level `𝓞 ⊔ 𝓥 ⊔ lsuc α` instead. 

The general `Lift` record type that we now describe makes such problems easier to
deal with. It takes a type inhabiting some universe and embeds it into a higher
universe and, apart from syntax and notation, it is equivalent to the `Lift` type
one finds in the `Level` module of the [Agda Standard Library][].
```agda
record Lift {𝓦 α : Level} (A : Set α) : Set (α ⊔ 𝓦) where
```
```agda
    constructor lift
```
```agda
    field lower : A
```
The point of having a ramified hierarchy of universes is to avoid Russell's
paradox, and this would be subverted if we were to lower the universe of a type
that wasn't previously lifted.  However, we can prove that if an application of
`lower` is immediately followed by an application of `lift`, then the result is
the identity transformation. Similarly, `lift` followed by `lower` is the
identity.
<pre class="Agda">

<a id="lift∼lower"></a><a id="8841" href="Overture.Basic.html#8841" class="Function">lift∼lower</a> <a id="8852" class="Symbol">:</a> <a id="8854" class="Symbol">{</a><a id="8855" href="Overture.Basic.html#8855" class="Bound">A</a> <a id="8857" class="Symbol">:</a> <a id="8859" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="8864" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="8865" class="Symbol">}</a> <a id="8867" class="Symbol">→</a> <a id="8869" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8874" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8876" href="Level.html#470" class="Field">lower</a> <a id="8882" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8884" href="Overture.Basic.html#5319" class="Function">𝑖𝑑</a> <a id="8887" class="Symbol">(</a><a id="8888" href="Level.html#400" class="Record">Lift</a> <a id="8893" href="Overture.Basic.html#3659" class="Generalizable">β</a> <a id="8895" href="Overture.Basic.html#8855" class="Bound">A</a><a id="8896" class="Symbol">)</a>
<a id="8898" href="Overture.Basic.html#8841" class="Function">lift∼lower</a> <a id="8909" class="Symbol">=</a> <a id="8911" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8917" href="Overture.Basic.html#8917" class="Function">lower∼lift</a> <a id="8928" class="Symbol">:</a> <a id="8930" class="Symbol">{</a><a id="8931" href="Overture.Basic.html#8931" class="Bound">A</a> <a id="8933" class="Symbol">:</a> <a id="8935" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="8940" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="8941" class="Symbol">}</a> <a id="8943" class="Symbol">→</a> <a id="8945" class="Symbol">(</a><a id="8946" href="Level.html#470" class="Field">lower</a> <a id="8952" class="Symbol">{</a><a id="8953" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="8954" class="Symbol">}{</a><a id="8956" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="8957" class="Symbol">})</a> <a id="8960" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8962" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8967" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8969" href="Overture.Basic.html#5319" class="Function">𝑖𝑑</a> <a id="8972" href="Overture.Basic.html#8931" class="Bound">A</a>
<a id="8974" href="Overture.Basic.html#8917" class="Function">lower∼lift</a> <a id="8985" class="Symbol">=</a> <a id="8987" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>
The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion
that two functions are (extensionally) the same in the sense that they produce
the same output when given the same input.  (We will have more to say about
this notion of equality in the [Base.Equality.Extensionality][] module.)
<pre class="Agda">

<a id="9523" class="Keyword">module</a> <a id="9530" href="Overture.Basic.html#9530" class="Module">_</a> <a id="9532" class="Symbol">{</a><a id="9533" href="Overture.Basic.html#9533" class="Bound">α</a> <a id="9535" class="Symbol">:</a> <a id="9537" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9542" class="Symbol">}{</a><a id="9544" href="Overture.Basic.html#9544" class="Bound">A</a> <a id="9546" class="Symbol">:</a> <a id="9548" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9553" href="Overture.Basic.html#9533" class="Bound">α</a><a id="9554" class="Symbol">}{</a><a id="9556" href="Overture.Basic.html#9556" class="Bound">β</a> <a id="9558" class="Symbol">:</a> <a id="9560" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9565" class="Symbol">}{</a><a id="9567" href="Overture.Basic.html#9567" class="Bound">B</a> <a id="9569" class="Symbol">:</a> <a id="9571" href="Overture.Basic.html#9544" class="Bound">A</a> <a id="9573" class="Symbol">→</a> <a id="9575" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9580" href="Overture.Basic.html#9556" class="Bound">β</a> <a id="9582" class="Symbol">}</a> <a id="9584" class="Keyword">where</a>

 <a id="9592" href="Overture.Basic.html#9592" class="Function Operator">_≈_</a> <a id="9596" class="Symbol">:</a>  <a id="9599" class="Symbol">(</a><a id="9600" href="Overture.Basic.html#9600" class="Bound">f</a> <a id="9602" href="Overture.Basic.html#9602" class="Bound">g</a> <a id="9604" class="Symbol">:</a> <a id="9606" class="Symbol">(</a><a id="9607" href="Overture.Basic.html#9607" class="Bound">a</a> <a id="9609" class="Symbol">:</a> <a id="9611" href="Overture.Basic.html#9544" class="Bound">A</a><a id="9612" class="Symbol">)</a> <a id="9614" class="Symbol">→</a> <a id="9616" href="Overture.Basic.html#9567" class="Bound">B</a> <a id="9618" href="Overture.Basic.html#9607" class="Bound">a</a><a id="9619" class="Symbol">)</a> <a id="9621" class="Symbol">→</a> <a id="9623" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9628" class="Symbol">(</a><a id="9629" href="Overture.Basic.html#9533" class="Bound">α</a> <a id="9631" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9633" href="Overture.Basic.html#9556" class="Bound">β</a><a id="9634" class="Symbol">)</a>
 <a id="9637" href="Overture.Basic.html#9637" class="Bound">f</a> <a id="9639" href="Overture.Basic.html#9592" class="Function Operator">≈</a> <a id="9641" href="Overture.Basic.html#9641" class="Bound">g</a> <a id="9643" class="Symbol">=</a> <a id="9645" class="Symbol">∀</a> <a id="9647" href="Overture.Basic.html#9647" class="Bound">x</a> <a id="9649" class="Symbol">→</a> <a id="9651" href="Overture.Basic.html#9637" class="Bound">f</a> <a id="9653" href="Overture.Basic.html#9647" class="Bound">x</a> <a id="9655" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9657" href="Overture.Basic.html#9641" class="Bound">g</a> <a id="9659" href="Overture.Basic.html#9647" class="Bound">x</a>

 <a id="9663" class="Keyword">infix</a> <a id="9669" class="Number">8</a> <a id="9671" href="Overture.Basic.html#9592" class="Function Operator">_≈_</a>

 <a id="9677" href="Overture.Basic.html#9677" class="Function">≈IsEquivalence</a> <a id="9692" class="Symbol">:</a> <a id="9694" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9708" href="Overture.Basic.html#9592" class="Function Operator">_≈_</a>
 <a id="9713" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a>   <a id="9734" href="Overture.Basic.html#9677" class="Function">≈IsEquivalence</a>          <a id="9758" class="Symbol">=</a> <a id="9760" class="Symbol">λ</a> <a id="9762" href="Overture.Basic.html#9762" class="Bound">_</a> <a id="9764" class="Symbol">→</a> <a id="9766" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9772" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a>    <a id="9793" href="Overture.Basic.html#9677" class="Function">≈IsEquivalence</a> <a id="9808" href="Overture.Basic.html#9808" class="Bound">f≈g</a>      <a id="9817" class="Symbol">=</a> <a id="9819" class="Symbol">λ</a> <a id="9821" href="Overture.Basic.html#9821" class="Bound">x</a> <a id="9823" class="Symbol">→</a> <a id="9825" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9829" class="Symbol">(</a><a id="9830" href="Overture.Basic.html#9808" class="Bound">f≈g</a> <a id="9834" href="Overture.Basic.html#9821" class="Bound">x</a><a id="9835" class="Symbol">)</a>
 <a id="9838" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a>  <a id="9859" href="Overture.Basic.html#9677" class="Function">≈IsEquivalence</a> <a id="9874" href="Overture.Basic.html#9874" class="Bound">f≈g</a> <a id="9878" href="Overture.Basic.html#9878" class="Bound">g≈h</a>  <a id="9883" class="Symbol">=</a> <a id="9885" class="Symbol">λ</a> <a id="9887" href="Overture.Basic.html#9887" class="Bound">x</a> <a id="9889" class="Symbol">→</a> <a id="9891" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9897" class="Symbol">(</a><a id="9898" href="Overture.Basic.html#9874" class="Bound">f≈g</a> <a id="9902" href="Overture.Basic.html#9887" class="Bound">x</a><a id="9903" class="Symbol">)</a> <a id="9905" class="Symbol">(</a><a id="9906" href="Overture.Basic.html#9878" class="Bound">g≈h</a> <a id="9910" href="Overture.Basic.html#9887" class="Bound">x</a><a id="9911" class="Symbol">)</a>

</pre>
The following is convenient for proving two pairs of a product type are equal
using the fact that their respective components are equal.
<pre class="Agda">

<a id="≡-by-parts"></a><a id="10076" href="Overture.Basic.html#10076" class="Function">≡-by-parts</a> <a id="10087" class="Symbol">:</a>  <a id="10090" class="Symbol">{</a><a id="10091" href="Overture.Basic.html#10091" class="Bound">A</a> <a id="10093" class="Symbol">:</a> <a id="10095" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10100" href="Overture.Basic.html#3657" class="Generalizable">α</a><a id="10101" class="Symbol">}{</a><a id="10103" href="Overture.Basic.html#10103" class="Bound">B</a> <a id="10105" class="Symbol">:</a> <a id="10107" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10112" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="10113" class="Symbol">}{</a><a id="10115" href="Overture.Basic.html#10115" class="Bound">u</a> <a id="10117" href="Overture.Basic.html#10117" class="Bound">v</a> <a id="10119" class="Symbol">:</a> <a id="10121" href="Overture.Basic.html#10091" class="Bound">A</a> <a id="10123" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="10125" href="Overture.Basic.html#10103" class="Bound">B</a><a id="10126" class="Symbol">}</a>
 <a id="10129" class="Symbol">→</a>            <a id="10142" href="Overture.Basic.html#3214" class="Field">fst</a> <a id="10146" href="Overture.Basic.html#10115" class="Bound">u</a> <a id="10148" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10150" href="Overture.Basic.html#3214" class="Field">fst</a> <a id="10154" href="Overture.Basic.html#10117" class="Bound">v</a> <a id="10156" class="Symbol">→</a> <a id="10158" href="Overture.Basic.html#3229" class="Field">snd</a> <a id="10162" href="Overture.Basic.html#10115" class="Bound">u</a> <a id="10164" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10166" href="Overture.Basic.html#3229" class="Field">snd</a> <a id="10170" href="Overture.Basic.html#10117" class="Bound">v</a> <a id="10172" class="Symbol">→</a> <a id="10174" href="Overture.Basic.html#10115" class="Bound">u</a> <a id="10176" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10178" href="Overture.Basic.html#10117" class="Bound">v</a>

<a id="10181" href="Overture.Basic.html#10076" class="Function">≡-by-parts</a> <a id="10192" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10197" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10202" class="Symbol">=</a> <a id="10204" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>
Lastly, we will use the following type (instead of `subst`) to transport equality
proofs.

<pre class="Agda">

<a id="transport"></a><a id="10326" href="Overture.Basic.html#10326" class="Function">transport</a> <a id="10336" class="Symbol">:</a> <a id="10338" class="Symbol">{</a><a id="10339" href="Overture.Basic.html#10339" class="Bound">A</a> <a id="10341" class="Symbol">:</a> <a id="10343" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10348" href="Overture.Basic.html#3657" class="Generalizable">α</a> <a id="10350" class="Symbol">}</a> <a id="10352" class="Symbol">(</a><a id="10353" href="Overture.Basic.html#10353" class="Bound">B</a> <a id="10355" class="Symbol">:</a> <a id="10357" href="Overture.Basic.html#10339" class="Bound">A</a> <a id="10359" class="Symbol">→</a> <a id="10361" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10366" href="Overture.Basic.html#3659" class="Generalizable">β</a><a id="10367" class="Symbol">)</a> <a id="10369" class="Symbol">{</a><a id="10370" href="Overture.Basic.html#10370" class="Bound">x</a> <a id="10372" href="Overture.Basic.html#10372" class="Bound">y</a> <a id="10374" class="Symbol">:</a> <a id="10376" href="Overture.Basic.html#10339" class="Bound">A</a><a id="10377" class="Symbol">}</a> <a id="10379" class="Symbol">→</a> <a id="10381" href="Overture.Basic.html#10370" class="Bound">x</a> <a id="10383" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10385" href="Overture.Basic.html#10372" class="Bound">y</a> <a id="10387" class="Symbol">→</a> <a id="10389" href="Overture.Basic.html#10353" class="Bound">B</a> <a id="10391" href="Overture.Basic.html#10370" class="Bound">x</a> <a id="10393" class="Symbol">→</a> <a id="10395" href="Overture.Basic.html#10353" class="Bound">B</a> <a id="10397" href="Overture.Basic.html#10372" class="Bound">y</a>
<a id="10399" href="Overture.Basic.html#10326" class="Function">transport</a> <a id="10409" href="Overture.Basic.html#10409" class="Bound">B</a> <a id="10411" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10416" class="Symbol">=</a> <a id="10418" href="Function.Base.html#615" class="Function">id</a>
</pre>

------------------------------

<span style="float:left;">[← Overture.Preface](Overture.Preface.html)</span>
<span style="float:right;">[Overture.Signatures →](Overture.Signatures.html)</span>

{% include UALib.Links.md %}


