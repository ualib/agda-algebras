---
layout: default
title : "Base.Functions.Basic module"
date : "2021-01-13"
author: "the agda-algebras development team"
---

### <a id="preliminaries">Preliminaries</a>

This is the [Base.Functions.Basic][] module of the [agda-algebras][] library.

#### <a id="logical-foundations">Logical foundations</a>

(See also the Equality module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types
from existing Agda libraries. Options are specified with the `OPTIONS` *pragma*
and control the way Agda behaves by, for example, specifying the logical axioms
and deduction rules we wish to assume when the program is type-checked to verify
its correctness. Every Agda program in [agda-algebras][] line.

<pre class="Agda">

<a id="776" class="Symbol">{-#</a> <a id="780" class="Keyword">OPTIONS</a> <a id="788" class="Pragma">--without-K</a> <a id="800" class="Pragma">--exact-split</a> <a id="814" class="Pragma">--safe</a> <a id="821" class="Symbol">#-}</a>

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


#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example,
the [Base.Functions.Basic][] module begins with the following line, and then a
list of imports of things used in the module.
<pre class="Agda">

<a id="2868" class="Keyword">module</a> <a id="2875" href="Overture.Basic.html" class="Module">Overture.Basic</a> <a id="2890" class="Keyword">where</a>

<a id="2897" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------------------------</a>
<a id="2996" class="Keyword">open</a> <a id="3001" class="Keyword">import</a> <a id="3008" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="3026" class="Keyword">using</a> <a id="3032" class="Symbol">()</a> <a id="3035" class="Keyword">renaming</a> <a id="3044" class="Symbol">(</a> <a id="3046" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3050" class="Symbol">to</a>  <a id="3054" class="Primitive">Type</a> <a id="3059" class="Symbol">;</a> <a id="3061" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="3067" class="Symbol">to</a>  <a id="3071" class="Primitive">ℓ₀</a> <a id="3074" class="Symbol">)</a>
<a id="3076" class="Keyword">open</a> <a id="3081" class="Keyword">import</a> <a id="3088" href="Data.Product.html" class="Module">Data.Product</a>      <a id="3106" class="Keyword">using</a> <a id="3112" class="Symbol">(</a> <a id="3114" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="3118" class="Symbol">;</a> <a id="3120" href="Data.Product.html#1369" class="Function">∃</a> <a id="3122" class="Symbol">;</a> <a id="3124" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="3133" class="Symbol">;</a> <a id="3135" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="3139" class="Symbol">)</a>
                              <a id="3171" class="Keyword">renaming</a> <a id="3180" class="Symbol">(</a> <a id="3182" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="3188" class="Symbol">to</a> <a id="3191" class="Field">fst</a> <a id="3195" class="Symbol">;</a> <a id="3197" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="3203" class="Symbol">to</a> <a id="3206" class="Field">snd</a> <a id="3210" class="Symbol">)</a>
<a id="3212" class="Keyword">open</a> <a id="3217" class="Keyword">import</a> <a id="3224" href="Function.Base.html" class="Module">Function.Base</a>     <a id="3242" class="Keyword">using</a> <a id="3248" class="Symbol">(</a> <a id="3250" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3254" class="Symbol">;</a> <a id="3256" href="Function.Base.html#615" class="Function">id</a> <a id="3259" class="Symbol">)</a>
<a id="3261" class="Keyword">open</a> <a id="3266" class="Keyword">import</a> <a id="3273" href="Level.html" class="Module">Level</a>             <a id="3291" class="Keyword">using</a> <a id="3297" class="Symbol">(</a> <a id="3299" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3305" class="Symbol">;</a> <a id="3307" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3311" class="Symbol">;</a> <a id="3313" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3317" class="Symbol">;</a> <a id="3319" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3324" class="Symbol">;</a> <a id="3326" href="Level.html#470" class="Field">lower</a> <a id="3332" class="Symbol">;</a> <a id="3334" href="Level.html#400" class="Record">Lift</a> <a id="3339" class="Symbol">)</a>
<a id="3341" class="Keyword">open</a> <a id="3346" class="Keyword">import</a> <a id="3353" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3371" class="Keyword">using</a> <a id="3377" class="Symbol">(</a> <a id="3379" href="Relation.Binary.Definitions.html#4687" class="Function">Decidable</a> <a id="3389" class="Symbol">)</a>
<a id="3391" class="Keyword">open</a> <a id="3396" class="Keyword">import</a> <a id="3403" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3421" class="Keyword">using</a> <a id="3427" class="Symbol">(</a> <a id="3429" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3443" class="Symbol">;</a> <a id="3445" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3460" class="Symbol">)</a>
<a id="3462" class="Keyword">open</a> <a id="3467" class="Keyword">import</a> <a id="3474" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>  <a id="3492" class="Keyword">using</a> <a id="3498" class="Symbol">(</a> <a id="3500" href="Relation.Nullary.html#1511" class="Record">Dec</a> <a id="3504" class="Symbol">;</a> <a id="3506" href="Relation.Nullary.html#1648" class="InductiveConstructor">yes</a> <a id="3510" class="Symbol">;</a> <a id="3512" href="Relation.Nullary.html#1685" class="InductiveConstructor">no</a> <a id="3515" class="Symbol">;</a> <a id="3517" href="Relation.Nullary.html#2040" class="Function">Irrelevant</a> <a id="3528" class="Symbol">)</a>

<a id="3531" class="Keyword">open</a> <a id="3536" class="Keyword">import</a> <a id="3543" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="3581" class="Keyword">using</a> <a id="3587" class="Symbol">(</a> <a id="3589" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3593" class="Symbol">;</a> <a id="3595" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3600" class="Symbol">;</a> <a id="3602" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3606" class="Symbol">;</a> <a id="3608" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3614" class="Symbol">)</a>

<a id="3617" class="Keyword">private</a> <a id="3625" class="Keyword">variable</a> <a id="3634" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="3636" href="Overture.Basic.html#3636" class="Generalizable">β</a> <a id="3638" class="Symbol">:</a> <a id="3640" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3647" href="Overture.Basic.html#3647" class="Function">ℓ₁</a> <a id="3650" class="Symbol">:</a> <a id="3652" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3658" href="Overture.Basic.html#3647" class="Function">ℓ₁</a> <a id="3661" class="Symbol">=</a> <a id="3663" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="3667" href="Overture.Basic.html#3071" class="Primitive">ℓ₀</a>

<a id="3671" class="Comment">-- the two element type</a>
<a id="3695" class="Keyword">data</a> <a id="𝟚"></a><a id="3700" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="3702" class="Symbol">:</a> <a id="3704" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="3709" href="Overture.Basic.html#3071" class="Primitive">ℓ₀</a> <a id="3712" class="Keyword">where</a> <a id="𝟚.𝟎"></a><a id="3718" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟎</a> <a id="3720" class="Symbol">:</a> <a id="3722" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="3724" class="Symbol">;</a>  <a id="𝟚.𝟏"></a><a id="3727" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟏</a> <a id="3729" class="Symbol">:</a> <a id="3731" href="Overture.Basic.html#3700" class="Datatype">𝟚</a>

<a id="3734" class="Comment">-- the three element type</a>
<a id="3760" class="Keyword">data</a> <a id="𝟛"></a><a id="3765" href="Overture.Basic.html#3765" class="Datatype">𝟛</a> <a id="3767" class="Symbol">:</a> <a id="3769" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="3774" href="Overture.Basic.html#3071" class="Primitive">ℓ₀</a> <a id="3777" class="Keyword">where</a> <a id="𝟛.𝟎"></a><a id="3783" href="Overture.Basic.html#3783" class="InductiveConstructor">𝟎</a> <a id="3785" class="Symbol">:</a> <a id="3787" href="Overture.Basic.html#3765" class="Datatype">𝟛</a> <a id="3789" class="Symbol">;</a>  <a id="𝟛.𝟏"></a><a id="3792" href="Overture.Basic.html#3792" class="InductiveConstructor">𝟏</a> <a id="3794" class="Symbol">:</a> <a id="3796" href="Overture.Basic.html#3765" class="Datatype">𝟛</a> <a id="3798" class="Symbol">;</a>  <a id="𝟛.𝟐"></a><a id="3801" href="Overture.Basic.html#3801" class="InductiveConstructor">𝟐</a> <a id="3803" class="Symbol">:</a> <a id="3805" href="Overture.Basic.html#3765" class="Datatype">𝟛</a>
</pre>

#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂`
representing the first and second projections out of the product.  However, we
prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these
projections by `∣_∣` and `∥_∥`, respectively. We define these alternative
notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4256" class="Keyword">module</a> <a id="4263" href="Overture.Basic.html#4263" class="Module">_</a> <a id="4265" class="Symbol">{</a><a id="4266" href="Overture.Basic.html#4266" class="Bound">A</a> <a id="4268" class="Symbol">:</a> <a id="4270" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="4275" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="4277" class="Symbol">}{</a><a id="4279" href="Overture.Basic.html#4279" class="Bound">B</a> <a id="4281" class="Symbol">:</a> <a id="4283" href="Overture.Basic.html#4266" class="Bound">A</a> <a id="4285" class="Symbol">→</a> <a id="4287" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="4292" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="4293" class="Symbol">}</a> <a id="4295" class="Keyword">where</a>

 <a id="4303" href="Overture.Basic.html#4303" class="Function Operator">∣_∣</a> <a id="4307" class="Symbol">:</a> <a id="4309" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4312" href="Overture.Basic.html#4312" class="Bound">x</a> <a id="4314" href="Data.Product.html#916" class="Function">∈</a> <a id="4316" href="Overture.Basic.html#4266" class="Bound">A</a> <a id="4318" href="Data.Product.html#916" class="Function">]</a> <a id="4320" href="Overture.Basic.html#4279" class="Bound">B</a> <a id="4322" href="Overture.Basic.html#4312" class="Bound">x</a> <a id="4324" class="Symbol">→</a> <a id="4326" href="Overture.Basic.html#4266" class="Bound">A</a>
 <a id="4329" href="Overture.Basic.html#4303" class="Function Operator">∣_∣</a> <a id="4333" class="Symbol">=</a> <a id="4335" href="Overture.Basic.html#3191" class="Field">fst</a>

 <a id="4341" href="Overture.Basic.html#4341" class="Function Operator">∥_∥</a> <a id="4345" class="Symbol">:</a> <a id="4347" class="Symbol">(</a><a id="4348" href="Overture.Basic.html#4348" class="Bound">z</a> <a id="4350" class="Symbol">:</a> <a id="4352" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4355" href="Overture.Basic.html#4355" class="Bound">a</a> <a id="4357" href="Data.Product.html#916" class="Function">∈</a> <a id="4359" href="Overture.Basic.html#4266" class="Bound">A</a> <a id="4361" href="Data.Product.html#916" class="Function">]</a> <a id="4363" href="Overture.Basic.html#4279" class="Bound">B</a> <a id="4365" href="Overture.Basic.html#4355" class="Bound">a</a><a id="4366" class="Symbol">)</a> <a id="4368" class="Symbol">→</a> <a id="4370" href="Overture.Basic.html#4279" class="Bound">B</a> <a id="4372" href="Overture.Basic.html#4303" class="Function Operator">∣</a> <a id="4374" href="Overture.Basic.html#4348" class="Bound">z</a> <a id="4376" href="Overture.Basic.html#4303" class="Function Operator">∣</a>
 <a id="4379" href="Overture.Basic.html#4341" class="Function Operator">∥_∥</a> <a id="4383" class="Symbol">=</a> <a id="4385" href="Overture.Basic.html#3206" class="Field">snd</a>

 <a id="4391" class="Keyword">infix</a>  <a id="4398" class="Number">40</a> <a id="4401" href="Overture.Basic.html#4303" class="Function Operator">∣_∣</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the
 `module` keyword followed by an underscore (instead of a module name). The
purpose is simply to move the postulated typing judgments---the "parameters"
of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate
the definitions inside the module.

Let's define some useful syntactic sugar that will make it easier to apply
symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4897" href="Overture.Basic.html#4897" class="Function Operator">_⁻¹</a> <a id="4901" class="Symbol">:</a> <a id="4903" class="Symbol">{</a><a id="4904" href="Overture.Basic.html#4904" class="Bound">A</a> <a id="4906" class="Symbol">:</a> <a id="4908" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="4913" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="4914" class="Symbol">}</a> <a id="4916" class="Symbol">{</a><a id="4917" href="Overture.Basic.html#4917" class="Bound">x</a> <a id="4919" href="Overture.Basic.html#4919" class="Bound">y</a> <a id="4921" class="Symbol">:</a> <a id="4923" href="Overture.Basic.html#4904" class="Bound">A</a><a id="4924" class="Symbol">}</a> <a id="4926" class="Symbol">→</a> <a id="4928" href="Overture.Basic.html#4917" class="Bound">x</a> <a id="4930" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4932" href="Overture.Basic.html#4919" class="Bound">y</a> <a id="4934" class="Symbol">→</a> <a id="4936" href="Overture.Basic.html#4919" class="Bound">y</a> <a id="4938" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4940" href="Overture.Basic.html#4917" class="Bound">x</a>
<a id="4942" href="Overture.Basic.html#4942" class="Bound">p</a> <a id="4944" href="Overture.Basic.html#4897" class="Function Operator">⁻¹</a> <a id="4947" class="Symbol">=</a> <a id="4949" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="4953" href="Overture.Basic.html#4942" class="Bound">p</a>

<a id="4956" class="Keyword">infix</a>  <a id="4963" class="Number">40</a> <a id="4966" href="Overture.Basic.html#4897" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of
`sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic
sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5223" href="Overture.Basic.html#5223" class="Function Operator">_∙_</a> <a id="5227" class="Symbol">:</a> <a id="5229" class="Symbol">{</a><a id="5230" href="Overture.Basic.html#5230" class="Bound">A</a> <a id="5232" class="Symbol">:</a> <a id="5234" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5239" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="5240" class="Symbol">}{</a><a id="5242" href="Overture.Basic.html#5242" class="Bound">x</a> <a id="5244" href="Overture.Basic.html#5244" class="Bound">y</a> <a id="5246" href="Overture.Basic.html#5246" class="Bound">z</a> <a id="5248" class="Symbol">:</a> <a id="5250" href="Overture.Basic.html#5230" class="Bound">A</a><a id="5251" class="Symbol">}</a> <a id="5253" class="Symbol">→</a> <a id="5255" href="Overture.Basic.html#5242" class="Bound">x</a> <a id="5257" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5259" href="Overture.Basic.html#5244" class="Bound">y</a> <a id="5261" class="Symbol">→</a> <a id="5263" href="Overture.Basic.html#5244" class="Bound">y</a> <a id="5265" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5267" href="Overture.Basic.html#5246" class="Bound">z</a> <a id="5269" class="Symbol">→</a> <a id="5271" href="Overture.Basic.html#5242" class="Bound">x</a> <a id="5273" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5275" href="Overture.Basic.html#5246" class="Bound">z</a>
<a id="5277" href="Overture.Basic.html#5277" class="Bound">p</a> <a id="5279" href="Overture.Basic.html#5223" class="Function Operator">∙</a> <a id="5281" href="Overture.Basic.html#5281" class="Bound">q</a> <a id="5283" class="Symbol">=</a> <a id="5285" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5291" href="Overture.Basic.html#5277" class="Bound">p</a> <a id="5293" href="Overture.Basic.html#5281" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5296" href="Overture.Basic.html#5296" class="Function">𝑖𝑑</a> <a id="5299" class="Symbol">:</a> <a id="5301" class="Symbol">(</a><a id="5302" href="Overture.Basic.html#5302" class="Bound">A</a> <a id="5304" class="Symbol">:</a> <a id="5306" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5311" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="5313" class="Symbol">)</a> <a id="5315" class="Symbol">→</a> <a id="5317" href="Overture.Basic.html#5302" class="Bound">A</a> <a id="5319" class="Symbol">→</a> <a id="5321" href="Overture.Basic.html#5302" class="Bound">A</a>
<a id="5323" href="Overture.Basic.html#5296" class="Function">𝑖𝑑</a> <a id="5326" href="Overture.Basic.html#5326" class="Bound">A</a> <a id="5328" class="Symbol">=</a> <a id="5330" class="Symbol">λ</a> <a id="5332" href="Overture.Basic.html#5332" class="Bound">x</a> <a id="5334" class="Symbol">→</a> <a id="5336" href="Overture.Basic.html#5332" class="Bound">x</a>

<a id="5339" class="Keyword">infixl</a> <a id="5346" class="Number">30</a> <a id="5349" href="Overture.Basic.html#5223" class="Function Operator">_∙_</a>
</pre>

#### <a id="sigma-types">Sigma types</a>

<pre class="Agda">

<a id="5421" class="Keyword">infix</a> <a id="5427" class="Number">2</a> <a id="5429" href="Overture.Basic.html#5439" class="Function">∃-syntax</a>

<a id="∃-syntax"></a><a id="5439" href="Overture.Basic.html#5439" class="Function">∃-syntax</a> <a id="5448" class="Symbol">:</a> <a id="5450" class="Symbol">∀</a> <a id="5452" class="Symbol">{</a><a id="5453" href="Overture.Basic.html#5453" class="Bound">A</a> <a id="5455" class="Symbol">:</a> <a id="5457" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5462" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="5463" class="Symbol">}</a> <a id="5465" class="Symbol">→</a> <a id="5467" class="Symbol">(</a><a id="5468" href="Overture.Basic.html#5453" class="Bound">A</a> <a id="5470" class="Symbol">→</a> <a id="5472" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5477" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="5478" class="Symbol">)</a> <a id="5480" class="Symbol">→</a> <a id="5482" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="5486" class="Symbol">(</a><a id="5487" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="5489" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5491" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="5492" class="Symbol">)</a>
<a id="5494" href="Overture.Basic.html#5439" class="Function">∃-syntax</a> <a id="5503" class="Symbol">=</a> <a id="5505" href="Data.Product.html#1369" class="Function">∃</a>

<a id="5508" class="Keyword">syntax</a> <a id="5515" href="Overture.Basic.html#5439" class="Function">∃-syntax</a> <a id="5524" class="Symbol">(λ</a> <a id="5527" class="Bound">x</a> <a id="5529" class="Symbol">→</a> <a id="5531" class="Bound">B</a><a id="5532" class="Symbol">)</a> <a id="5534" class="Symbol">=</a> <a id="5536" class="Function">∃[</a> <a id="5539" class="Bound">x</a> <a id="5541" class="Function">∈</a> <a id="5543" class="Function">A</a> <a id="5545" class="Function">]</a> <a id="5547" class="Bound">B</a>
</pre>

#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with an uppercase pi symbol
and typically expressed as `Π(x : A) B x`, or something similar.  In Agda syntax,
one writes `(x : A) → B x` for this dependent function type, but we can define
syntax that is closer to standard notation as follows.

<pre class="Agda">

<a id="Π"></a><a id="5909" href="Overture.Basic.html#5909" class="Function">Π</a> <a id="5911" class="Symbol">:</a> <a id="5913" class="Symbol">{</a><a id="5914" href="Overture.Basic.html#5914" class="Bound">A</a> <a id="5916" class="Symbol">:</a> <a id="5918" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5923" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="5925" class="Symbol">}</a> <a id="5927" class="Symbol">(</a><a id="5928" href="Overture.Basic.html#5928" class="Bound">B</a> <a id="5930" class="Symbol">:</a> <a id="5932" href="Overture.Basic.html#5914" class="Bound">A</a> <a id="5934" class="Symbol">→</a> <a id="5936" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5941" href="Overture.Basic.html#3636" class="Generalizable">β</a> <a id="5943" class="Symbol">)</a> <a id="5945" class="Symbol">→</a> <a id="5947" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="5952" class="Symbol">(</a><a id="5953" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="5955" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5957" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="5958" class="Symbol">)</a>
<a id="5960" href="Overture.Basic.html#5909" class="Function">Π</a> <a id="5962" class="Symbol">{</a><a id="5963" class="Argument">A</a> <a id="5965" class="Symbol">=</a> <a id="5967" href="Overture.Basic.html#5967" class="Bound">A</a><a id="5968" class="Symbol">}</a> <a id="5970" href="Overture.Basic.html#5970" class="Bound">B</a> <a id="5972" class="Symbol">=</a> <a id="5974" class="Symbol">(</a><a id="5975" href="Overture.Basic.html#5975" class="Bound">x</a> <a id="5977" class="Symbol">:</a> <a id="5979" href="Overture.Basic.html#5967" class="Bound">A</a><a id="5980" class="Symbol">)</a> <a id="5982" class="Symbol">→</a> <a id="5984" href="Overture.Basic.html#5970" class="Bound">B</a> <a id="5986" href="Overture.Basic.html#5975" class="Bound">x</a>

<a id="Π-syntax"></a><a id="5989" href="Overture.Basic.html#5989" class="Function">Π-syntax</a> <a id="5998" class="Symbol">:</a> <a id="6000" class="Symbol">(</a><a id="6001" href="Overture.Basic.html#6001" class="Bound">A</a> <a id="6003" class="Symbol">:</a> <a id="6005" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="6010" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="6011" class="Symbol">)(</a><a id="6013" href="Overture.Basic.html#6013" class="Bound">B</a> <a id="6015" class="Symbol">:</a> <a id="6017" href="Overture.Basic.html#6001" class="Bound">A</a> <a id="6019" class="Symbol">→</a> <a id="6021" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="6026" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="6027" class="Symbol">)</a> <a id="6029" class="Symbol">→</a> <a id="6031" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="6036" class="Symbol">(</a><a id="6037" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="6039" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6041" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="6042" class="Symbol">)</a>
<a id="6044" href="Overture.Basic.html#5989" class="Function">Π-syntax</a> <a id="6053" href="Overture.Basic.html#6053" class="Bound">A</a> <a id="6055" href="Overture.Basic.html#6055" class="Bound">B</a> <a id="6057" class="Symbol">=</a> <a id="6059" href="Overture.Basic.html#5909" class="Function">Π</a> <a id="6061" href="Overture.Basic.html#6055" class="Bound">B</a>

<a id="6064" class="Keyword">syntax</a> <a id="6071" href="Overture.Basic.html#5989" class="Function">Π-syntax</a> <a id="6080" class="Bound">A</a> <a id="6082" class="Symbol">(λ</a> <a id="6085" class="Bound">x</a> <a id="6087" class="Symbol">→</a> <a id="6089" class="Bound">B</a><a id="6090" class="Symbol">)</a> <a id="6092" class="Symbol">=</a> <a id="6094" class="Function">Π[</a> <a id="6097" class="Bound">x</a> <a id="6099" class="Function">∈</a> <a id="6101" class="Bound">A</a> <a id="6103" class="Function">]</a> <a id="6105" class="Bound">B</a>
<a id="6107" class="Keyword">infix</a> <a id="6113" class="Number">6</a> <a id="6115" href="Overture.Basic.html#5989" class="Function">Π-syntax</a>

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

<a id="lift∼lower"></a><a id="8818" href="Overture.Basic.html#8818" class="Function">lift∼lower</a> <a id="8829" class="Symbol">:</a> <a id="8831" class="Symbol">{</a><a id="8832" href="Overture.Basic.html#8832" class="Bound">A</a> <a id="8834" class="Symbol">:</a> <a id="8836" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="8841" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="8842" class="Symbol">}</a> <a id="8844" class="Symbol">→</a> <a id="8846" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8851" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8853" href="Level.html#470" class="Field">lower</a> <a id="8859" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8861" href="Overture.Basic.html#5296" class="Function">𝑖𝑑</a> <a id="8864" class="Symbol">(</a><a id="8865" href="Level.html#400" class="Record">Lift</a> <a id="8870" href="Overture.Basic.html#3636" class="Generalizable">β</a> <a id="8872" href="Overture.Basic.html#8832" class="Bound">A</a><a id="8873" class="Symbol">)</a>
<a id="8875" href="Overture.Basic.html#8818" class="Function">lift∼lower</a> <a id="8886" class="Symbol">=</a> <a id="8888" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8894" href="Overture.Basic.html#8894" class="Function">lower∼lift</a> <a id="8905" class="Symbol">:</a> <a id="8907" class="Symbol">{</a><a id="8908" href="Overture.Basic.html#8908" class="Bound">A</a> <a id="8910" class="Symbol">:</a> <a id="8912" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="8917" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="8918" class="Symbol">}</a> <a id="8920" class="Symbol">→</a> <a id="8922" class="Symbol">(</a><a id="8923" href="Level.html#470" class="Field">lower</a> <a id="8929" class="Symbol">{</a><a id="8930" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="8931" class="Symbol">}{</a><a id="8933" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="8934" class="Symbol">})</a> <a id="8937" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8939" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8944" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8946" href="Overture.Basic.html#5296" class="Function">𝑖𝑑</a> <a id="8949" href="Overture.Basic.html#8908" class="Bound">A</a>
<a id="8951" href="Overture.Basic.html#8894" class="Function">lower∼lift</a> <a id="8962" class="Symbol">=</a> <a id="8964" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>
The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion
that two functions are (extensionally) the same in the sense that they produce
the same output when given the same input.  (We will have more to say about
this notion of equality in the [Base.Equality.Extensionality][] module.)
<pre class="Agda">

<a id="9500" class="Keyword">module</a> <a id="9507" href="Overture.Basic.html#9507" class="Module">_</a> <a id="9509" class="Symbol">{</a><a id="9510" href="Overture.Basic.html#9510" class="Bound">α</a> <a id="9512" class="Symbol">:</a> <a id="9514" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9519" class="Symbol">}{</a><a id="9521" href="Overture.Basic.html#9521" class="Bound">A</a> <a id="9523" class="Symbol">:</a> <a id="9525" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="9530" href="Overture.Basic.html#9510" class="Bound">α</a><a id="9531" class="Symbol">}{</a><a id="9533" href="Overture.Basic.html#9533" class="Bound">β</a> <a id="9535" class="Symbol">:</a> <a id="9537" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9542" class="Symbol">}{</a><a id="9544" href="Overture.Basic.html#9544" class="Bound">B</a> <a id="9546" class="Symbol">:</a> <a id="9548" href="Overture.Basic.html#9521" class="Bound">A</a> <a id="9550" class="Symbol">→</a> <a id="9552" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="9557" href="Overture.Basic.html#9533" class="Bound">β</a> <a id="9559" class="Symbol">}</a> <a id="9561" class="Keyword">where</a>

 <a id="9569" href="Overture.Basic.html#9569" class="Function Operator">_≈_</a> <a id="9573" class="Symbol">:</a>  <a id="9576" class="Symbol">(</a><a id="9577" href="Overture.Basic.html#9577" class="Bound">f</a> <a id="9579" href="Overture.Basic.html#9579" class="Bound">g</a> <a id="9581" class="Symbol">:</a> <a id="9583" class="Symbol">(</a><a id="9584" href="Overture.Basic.html#9584" class="Bound">a</a> <a id="9586" class="Symbol">:</a> <a id="9588" href="Overture.Basic.html#9521" class="Bound">A</a><a id="9589" class="Symbol">)</a> <a id="9591" class="Symbol">→</a> <a id="9593" href="Overture.Basic.html#9544" class="Bound">B</a> <a id="9595" href="Overture.Basic.html#9584" class="Bound">a</a><a id="9596" class="Symbol">)</a> <a id="9598" class="Symbol">→</a> <a id="9600" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="9605" class="Symbol">(</a><a id="9606" href="Overture.Basic.html#9510" class="Bound">α</a> <a id="9608" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9610" href="Overture.Basic.html#9533" class="Bound">β</a><a id="9611" class="Symbol">)</a>
 <a id="9614" href="Overture.Basic.html#9614" class="Bound">f</a> <a id="9616" href="Overture.Basic.html#9569" class="Function Operator">≈</a> <a id="9618" href="Overture.Basic.html#9618" class="Bound">g</a> <a id="9620" class="Symbol">=</a> <a id="9622" class="Symbol">∀</a> <a id="9624" href="Overture.Basic.html#9624" class="Bound">x</a> <a id="9626" class="Symbol">→</a> <a id="9628" href="Overture.Basic.html#9614" class="Bound">f</a> <a id="9630" href="Overture.Basic.html#9624" class="Bound">x</a> <a id="9632" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9634" href="Overture.Basic.html#9618" class="Bound">g</a> <a id="9636" href="Overture.Basic.html#9624" class="Bound">x</a>

 <a id="9640" class="Keyword">infix</a> <a id="9646" class="Number">8</a> <a id="9648" href="Overture.Basic.html#9569" class="Function Operator">_≈_</a>

 <a id="9654" href="Overture.Basic.html#9654" class="Function">≈IsEquivalence</a> <a id="9669" class="Symbol">:</a> <a id="9671" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9685" href="Overture.Basic.html#9569" class="Function Operator">_≈_</a>
 <a id="9690" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a>   <a id="9711" href="Overture.Basic.html#9654" class="Function">≈IsEquivalence</a>          <a id="9735" class="Symbol">=</a> <a id="9737" class="Symbol">λ</a> <a id="9739" href="Overture.Basic.html#9739" class="Bound">_</a> <a id="9741" class="Symbol">→</a> <a id="9743" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9749" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a>    <a id="9770" href="Overture.Basic.html#9654" class="Function">≈IsEquivalence</a> <a id="9785" href="Overture.Basic.html#9785" class="Bound">f≈g</a>      <a id="9794" class="Symbol">=</a> <a id="9796" class="Symbol">λ</a> <a id="9798" href="Overture.Basic.html#9798" class="Bound">x</a> <a id="9800" class="Symbol">→</a> <a id="9802" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9806" class="Symbol">(</a><a id="9807" href="Overture.Basic.html#9785" class="Bound">f≈g</a> <a id="9811" href="Overture.Basic.html#9798" class="Bound">x</a><a id="9812" class="Symbol">)</a>
 <a id="9815" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a>  <a id="9836" href="Overture.Basic.html#9654" class="Function">≈IsEquivalence</a> <a id="9851" href="Overture.Basic.html#9851" class="Bound">f≈g</a> <a id="9855" href="Overture.Basic.html#9855" class="Bound">g≈h</a>  <a id="9860" class="Symbol">=</a> <a id="9862" class="Symbol">λ</a> <a id="9864" href="Overture.Basic.html#9864" class="Bound">x</a> <a id="9866" class="Symbol">→</a> <a id="9868" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9874" class="Symbol">(</a><a id="9875" href="Overture.Basic.html#9851" class="Bound">f≈g</a> <a id="9879" href="Overture.Basic.html#9864" class="Bound">x</a><a id="9880" class="Symbol">)</a> <a id="9882" class="Symbol">(</a><a id="9883" href="Overture.Basic.html#9855" class="Bound">g≈h</a> <a id="9887" href="Overture.Basic.html#9864" class="Bound">x</a><a id="9888" class="Symbol">)</a>

</pre>
The following is convenient for proving two pairs of a product type are equal
using the fact that their respective components are equal.
<pre class="Agda">

<a id="≡-by-parts"></a><a id="10053" href="Overture.Basic.html#10053" class="Function">≡-by-parts</a> <a id="10064" class="Symbol">:</a>  <a id="10067" class="Symbol">{</a><a id="10068" href="Overture.Basic.html#10068" class="Bound">A</a> <a id="10070" class="Symbol">:</a> <a id="10072" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="10077" href="Overture.Basic.html#3634" class="Generalizable">α</a><a id="10078" class="Symbol">}{</a><a id="10080" href="Overture.Basic.html#10080" class="Bound">B</a> <a id="10082" class="Symbol">:</a> <a id="10084" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="10089" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="10090" class="Symbol">}{</a><a id="10092" href="Overture.Basic.html#10092" class="Bound">u</a> <a id="10094" href="Overture.Basic.html#10094" class="Bound">v</a> <a id="10096" class="Symbol">:</a> <a id="10098" href="Overture.Basic.html#10068" class="Bound">A</a> <a id="10100" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="10102" href="Overture.Basic.html#10080" class="Bound">B</a><a id="10103" class="Symbol">}</a>
 <a id="10106" class="Symbol">→</a>            <a id="10119" href="Overture.Basic.html#3191" class="Field">fst</a> <a id="10123" href="Overture.Basic.html#10092" class="Bound">u</a> <a id="10125" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10127" href="Overture.Basic.html#3191" class="Field">fst</a> <a id="10131" href="Overture.Basic.html#10094" class="Bound">v</a> <a id="10133" class="Symbol">→</a> <a id="10135" href="Overture.Basic.html#3206" class="Field">snd</a> <a id="10139" href="Overture.Basic.html#10092" class="Bound">u</a> <a id="10141" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10143" href="Overture.Basic.html#3206" class="Field">snd</a> <a id="10147" href="Overture.Basic.html#10094" class="Bound">v</a> <a id="10149" class="Symbol">→</a> <a id="10151" href="Overture.Basic.html#10092" class="Bound">u</a> <a id="10153" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10155" href="Overture.Basic.html#10094" class="Bound">v</a>

<a id="10158" href="Overture.Basic.html#10053" class="Function">≡-by-parts</a> <a id="10169" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10174" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10179" class="Symbol">=</a> <a id="10181" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>
Lastly, we will use the following type (instead of `subst`) to transport equality
proofs.

<pre class="Agda">

<a id="transport"></a><a id="10303" href="Overture.Basic.html#10303" class="Function">transport</a> <a id="10313" class="Symbol">:</a> <a id="10315" class="Symbol">{</a><a id="10316" href="Overture.Basic.html#10316" class="Bound">A</a> <a id="10318" class="Symbol">:</a> <a id="10320" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="10325" href="Overture.Basic.html#3634" class="Generalizable">α</a> <a id="10327" class="Symbol">}</a> <a id="10329" class="Symbol">(</a><a id="10330" href="Overture.Basic.html#10330" class="Bound">B</a> <a id="10332" class="Symbol">:</a> <a id="10334" href="Overture.Basic.html#10316" class="Bound">A</a> <a id="10336" class="Symbol">→</a> <a id="10338" href="Overture.Basic.html#3054" class="Primitive">Type</a> <a id="10343" href="Overture.Basic.html#3636" class="Generalizable">β</a><a id="10344" class="Symbol">)</a> <a id="10346" class="Symbol">{</a><a id="10347" href="Overture.Basic.html#10347" class="Bound">x</a> <a id="10349" href="Overture.Basic.html#10349" class="Bound">y</a> <a id="10351" class="Symbol">:</a> <a id="10353" href="Overture.Basic.html#10316" class="Bound">A</a><a id="10354" class="Symbol">}</a> <a id="10356" class="Symbol">→</a> <a id="10358" href="Overture.Basic.html#10347" class="Bound">x</a> <a id="10360" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10362" href="Overture.Basic.html#10349" class="Bound">y</a> <a id="10364" class="Symbol">→</a> <a id="10366" href="Overture.Basic.html#10330" class="Bound">B</a> <a id="10368" href="Overture.Basic.html#10347" class="Bound">x</a> <a id="10370" class="Symbol">→</a> <a id="10372" href="Overture.Basic.html#10330" class="Bound">B</a> <a id="10374" href="Overture.Basic.html#10349" class="Bound">y</a>
<a id="10376" href="Overture.Basic.html#10303" class="Function">transport</a> <a id="10386" href="Overture.Basic.html#10386" class="Bound">B</a> <a id="10388" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10393" class="Symbol">=</a> <a id="10395" href="Function.Base.html#615" class="Function">id</a>
</pre>

------------------------------

<span style="float:left;">[← Overture.Preface](Overture.Preface.html)</span>
<span style="float:right;">[Overture.Signatures →](Overture.Signatures.html)</span>

{% include UALib.Links.md %}


