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
<a id="3019" class="Keyword">open</a> <a id="3024" class="Keyword">import</a> <a id="3031" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>    <a id="3049" class="Keyword">using</a> <a id="3055" class="Symbol">()</a> <a id="3058" class="Keyword">renaming</a> <a id="3067" class="Symbol">(</a> <a id="3069" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3073" class="Symbol">to</a>  <a id="3077" class="Primitive">Type</a> <a id="3082" class="Symbol">;</a> <a id="3084" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="3090" class="Symbol">to</a>  <a id="3094" class="Primitive">ℓ₀</a> <a id="3097" class="Symbol">)</a>
<a id="3099" class="Keyword">open</a> <a id="3104" class="Keyword">import</a> <a id="3111" href="Data.Product.html" class="Module">Data.Product</a>      <a id="3129" class="Keyword">using</a> <a id="3135" class="Symbol">(</a> <a id="3137" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">_,_</a> <a id="3141" class="Symbol">;</a> <a id="3143" href="Data.Product.Base.html#852" class="Function">∃</a> <a id="3145" class="Symbol">;</a> <a id="3147" href="Data.Product.Base.html#1244" class="Function">Σ-syntax</a> <a id="3156" class="Symbol">;</a> <a id="3158" href="Data.Product.Base.html#1618" class="Function Operator">_×_</a> <a id="3162" class="Symbol">)</a>
                              <a id="3194" class="Keyword">renaming</a> <a id="3203" class="Symbol">(</a> <a id="3205" href="Data.Product.Base.html#636" class="Field">proj₁</a> <a id="3211" class="Symbol">to</a> <a id="3214" class="Field">fst</a> <a id="3218" class="Symbol">;</a> <a id="3220" href="Data.Product.Base.html#650" class="Field">proj₂</a> <a id="3226" class="Symbol">to</a> <a id="3229" class="Field">snd</a> <a id="3233" class="Symbol">)</a>
<a id="3235" class="Keyword">open</a> <a id="3240" class="Keyword">import</a> <a id="3247" href="Function.Base.html" class="Module">Function.Base</a>     <a id="3265" class="Keyword">using</a> <a id="3271" class="Symbol">(</a> <a id="3273" href="Function.Base.html#1115" class="Function Operator">_∘_</a> <a id="3277" class="Symbol">;</a> <a id="3279" href="Function.Base.html#704" class="Function">id</a> <a id="3282" class="Symbol">)</a>
<a id="3284" class="Keyword">open</a> <a id="3289" class="Keyword">import</a> <a id="3296" href="Level.html" class="Module">Level</a>             <a id="3314" class="Keyword">using</a> <a id="3320" class="Symbol">(</a> <a id="3322" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="3328" class="Symbol">;</a> <a id="3330" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="3334" class="Symbol">;</a> <a id="3336" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="3340" class="Symbol">;</a> <a id="3342" href="Level.html#466" class="InductiveConstructor">lift</a> <a id="3347" class="Symbol">;</a> <a id="3349" href="Level.html#479" class="Field">lower</a> <a id="3355" class="Symbol">;</a> <a id="3357" href="Level.html#409" class="Record">Lift</a> <a id="3362" class="Symbol">)</a>
<a id="3364" class="Keyword">open</a> <a id="3369" class="Keyword">import</a> <a id="3376" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3394" class="Keyword">using</a> <a id="3400" class="Symbol">(</a> <a id="3402" href="Relation.Binary.Definitions.html#6713" class="Function">Decidable</a> <a id="3412" class="Symbol">)</a>
<a id="3414" class="Keyword">open</a> <a id="3419" class="Keyword">import</a> <a id="3426" href="Relation.Binary.html" class="Module">Relation.Binary</a>   <a id="3444" class="Keyword">using</a> <a id="3450" class="Symbol">(</a> <a id="3452" href="Relation.Binary.Structures.html#1550" class="Record">IsEquivalence</a> <a id="3466" class="Symbol">;</a> <a id="3468" href="Relation.Binary.Structures.html#3522" class="Record">IsPartialOrder</a> <a id="3483" class="Symbol">)</a>
<a id="3485" class="Keyword">open</a> <a id="3490" class="Keyword">import</a> <a id="3497" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>  <a id="3515" class="Keyword">using</a> <a id="3521" class="Symbol">(</a> <a id="3523" href="Relation.Nullary.Decidable.Core.html#1861" class="Record">Dec</a> <a id="3527" class="Symbol">;</a> <a id="3529" href="Relation.Nullary.Decidable.Core.html#1994" class="InductiveConstructor">yes</a> <a id="3533" class="Symbol">;</a> <a id="3535" href="Relation.Nullary.Decidable.Core.html#2031" class="InductiveConstructor">no</a> <a id="3538" class="Symbol">;</a> <a id="3540" href="Relation.Nullary.html#1002" class="Function">Irrelevant</a> <a id="3551" class="Symbol">)</a>

<a id="3554" class="Keyword">open</a> <a id="3559" class="Keyword">import</a> <a id="3566" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="3604" class="Keyword">using</a> <a id="3610" class="Symbol">(</a> <a id="3612" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="3616" class="Symbol">;</a> <a id="3618" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="3623" class="Symbol">;</a> <a id="3625" href="Relation.Binary.PropositionalEquality.Core.html#1893" class="Function">sym</a> <a id="3629" class="Symbol">;</a> <a id="3631" href="Relation.Binary.PropositionalEquality.Core.html#1938" class="Function">trans</a> <a id="3637" class="Symbol">)</a>

<a id="3640" class="Keyword">private</a> <a id="3648" class="Keyword">variable</a> <a id="3657" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="3659" href="Overture.Basic.html#3659" class="Generalizable">b</a> <a id="3661" class="Symbol">:</a> <a id="3663" href="Agda.Primitive.html#742" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3670" href="Overture.Basic.html#3670" class="Function">ℓ₁</a> <a id="3673" class="Symbol">:</a> <a id="3675" href="Agda.Primitive.html#742" class="Postulate">Level</a>
<a id="3681" href="Overture.Basic.html#3670" class="Function">ℓ₁</a> <a id="3684" class="Symbol">=</a> <a id="3686" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="3690" href="Overture.Basic.html#3094" class="Primitive">ℓ₀</a>

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

<a id="4279" class="Keyword">module</a> <a id="4286" href="Overture.Basic.html#4286" class="Module">_</a> <a id="4288" class="Symbol">{</a><a id="4289" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4291" class="Symbol">:</a> <a id="4293" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4298" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="4299" class="Symbol">}{</a><a id="4301" href="Overture.Basic.html#4301" class="Bound">B</a> <a id="4303" class="Symbol">:</a> <a id="4305" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4307" class="Symbol">→</a> <a id="4309" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4314" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="4315" class="Symbol">}</a> <a id="4317" class="Keyword">where</a>

 <a id="4325" href="Overture.Basic.html#4325" class="Function Operator">∣_∣</a> <a id="4329" class="Symbol">:</a> <a id="4331" href="Data.Product.Base.html#1244" class="Function">Σ[</a> <a id="4334" href="Overture.Basic.html#4334" class="Bound">x</a> <a id="4336" href="Data.Product.Base.html#1244" class="Function">∈</a> <a id="4338" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4340" href="Data.Product.Base.html#1244" class="Function">]</a> <a id="4342" href="Overture.Basic.html#4301" class="Bound">B</a> <a id="4344" href="Overture.Basic.html#4334" class="Bound">x</a> <a id="4346" class="Symbol">→</a> <a id="4348" href="Overture.Basic.html#4289" class="Bound">A</a>
 <a id="4351" href="Overture.Basic.html#4325" class="Function Operator">∣_∣</a> <a id="4355" class="Symbol">=</a> <a id="4357" href="Overture.Basic.html#3214" class="Field">fst</a>

 <a id="4363" href="Overture.Basic.html#4363" class="Function Operator">∥_∥</a> <a id="4367" class="Symbol">:</a> <a id="4369" class="Symbol">(</a><a id="4370" href="Overture.Basic.html#4370" class="Bound">z</a> <a id="4372" class="Symbol">:</a> <a id="4374" href="Data.Product.Base.html#1244" class="Function">Σ[</a> <a id="4377" href="Overture.Basic.html#4377" class="Bound">a</a> <a id="4379" href="Data.Product.Base.html#1244" class="Function">∈</a> <a id="4381" href="Overture.Basic.html#4289" class="Bound">A</a> <a id="4383" href="Data.Product.Base.html#1244" class="Function">]</a> <a id="4385" href="Overture.Basic.html#4301" class="Bound">B</a> <a id="4387" href="Overture.Basic.html#4377" class="Bound">a</a><a id="4388" class="Symbol">)</a> <a id="4390" class="Symbol">→</a> <a id="4392" href="Overture.Basic.html#4301" class="Bound">B</a> <a id="4394" href="Overture.Basic.html#4325" class="Function Operator">∣</a> <a id="4396" href="Overture.Basic.html#4370" class="Bound">z</a> <a id="4398" href="Overture.Basic.html#4325" class="Function Operator">∣</a>
 <a id="4401" href="Overture.Basic.html#4363" class="Function Operator">∥_∥</a> <a id="4405" class="Symbol">=</a> <a id="4407" href="Overture.Basic.html#3229" class="Field">snd</a>

 <a id="4413" class="Keyword">infix</a>  <a id="4420" class="Number">40</a> <a id="4423" href="Overture.Basic.html#4325" class="Function Operator">∣_∣</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the
 `module` keyword followed by an underscore (instead of a module name). The
purpose is simply to move the postulated typing judgments---the "parameters"
of the module (e.g., `A : Type a`)---out of the way so they don't obfuscate
the definitions inside the module.

Let's define some useful syntactic sugar that will make it easier to apply
symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4919" href="Overture.Basic.html#4919" class="Function Operator">_⁻¹</a> <a id="4923" class="Symbol">:</a> <a id="4925" class="Symbol">{</a><a id="4926" href="Overture.Basic.html#4926" class="Bound">A</a> <a id="4928" class="Symbol">:</a> <a id="4930" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="4935" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="4936" class="Symbol">}</a> <a id="4938" class="Symbol">{</a><a id="4939" href="Overture.Basic.html#4939" class="Bound">x</a> <a id="4941" href="Overture.Basic.html#4941" class="Bound">y</a> <a id="4943" class="Symbol">:</a> <a id="4945" href="Overture.Basic.html#4926" class="Bound">A</a><a id="4946" class="Symbol">}</a> <a id="4948" class="Symbol">→</a> <a id="4950" href="Overture.Basic.html#4939" class="Bound">x</a> <a id="4952" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4954" href="Overture.Basic.html#4941" class="Bound">y</a> <a id="4956" class="Symbol">→</a> <a id="4958" href="Overture.Basic.html#4941" class="Bound">y</a> <a id="4960" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4962" href="Overture.Basic.html#4939" class="Bound">x</a>
<a id="4964" href="Overture.Basic.html#4964" class="Bound">p</a> <a id="4966" href="Overture.Basic.html#4919" class="Function Operator">⁻¹</a> <a id="4969" class="Symbol">=</a> <a id="4971" href="Relation.Binary.PropositionalEquality.Core.html#1893" class="Function">sym</a> <a id="4975" href="Overture.Basic.html#4964" class="Bound">p</a>

<a id="4978" class="Keyword">infix</a>  <a id="4985" class="Number">40</a> <a id="4988" href="Overture.Basic.html#4919" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of
`sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic
sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5245" href="Overture.Basic.html#5245" class="Function Operator">_∙_</a> <a id="5249" class="Symbol">:</a> <a id="5251" class="Symbol">{</a><a id="5252" href="Overture.Basic.html#5252" class="Bound">A</a> <a id="5254" class="Symbol">:</a> <a id="5256" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5261" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="5262" class="Symbol">}{</a><a id="5264" href="Overture.Basic.html#5264" class="Bound">x</a> <a id="5266" href="Overture.Basic.html#5266" class="Bound">y</a> <a id="5268" href="Overture.Basic.html#5268" class="Bound">z</a> <a id="5270" class="Symbol">:</a> <a id="5272" href="Overture.Basic.html#5252" class="Bound">A</a><a id="5273" class="Symbol">}</a> <a id="5275" class="Symbol">→</a> <a id="5277" href="Overture.Basic.html#5264" class="Bound">x</a> <a id="5279" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5281" href="Overture.Basic.html#5266" class="Bound">y</a> <a id="5283" class="Symbol">→</a> <a id="5285" href="Overture.Basic.html#5266" class="Bound">y</a> <a id="5287" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5289" href="Overture.Basic.html#5268" class="Bound">z</a> <a id="5291" class="Symbol">→</a> <a id="5293" href="Overture.Basic.html#5264" class="Bound">x</a> <a id="5295" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5297" href="Overture.Basic.html#5268" class="Bound">z</a>
<a id="5299" href="Overture.Basic.html#5299" class="Bound">p</a> <a id="5301" href="Overture.Basic.html#5245" class="Function Operator">∙</a> <a id="5303" href="Overture.Basic.html#5303" class="Bound">q</a> <a id="5305" class="Symbol">=</a> <a id="5307" href="Relation.Binary.PropositionalEquality.Core.html#1938" class="Function">trans</a> <a id="5313" href="Overture.Basic.html#5299" class="Bound">p</a> <a id="5315" href="Overture.Basic.html#5303" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5318" href="Overture.Basic.html#5318" class="Function">𝑖𝑑</a> <a id="5321" class="Symbol">:</a> <a id="5323" class="Symbol">(</a><a id="5324" href="Overture.Basic.html#5324" class="Bound">A</a> <a id="5326" class="Symbol">:</a> <a id="5328" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5333" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="5334" class="Symbol">)</a> <a id="5336" class="Symbol">→</a> <a id="5338" href="Overture.Basic.html#5324" class="Bound">A</a> <a id="5340" class="Symbol">→</a> <a id="5342" href="Overture.Basic.html#5324" class="Bound">A</a>
<a id="5344" href="Overture.Basic.html#5318" class="Function">𝑖𝑑</a> <a id="5347" href="Overture.Basic.html#5347" class="Bound">A</a> <a id="5349" class="Symbol">=</a> <a id="5351" class="Symbol">λ</a> <a id="5353" href="Overture.Basic.html#5353" class="Bound">x</a> <a id="5355" class="Symbol">→</a> <a id="5357" href="Overture.Basic.html#5353" class="Bound">x</a>

<a id="5360" class="Keyword">infixl</a> <a id="5367" class="Number">30</a> <a id="5370" href="Overture.Basic.html#5245" class="Function Operator">_∙_</a>
</pre>

#### <a id="sigma-types">Sigma types</a>

<pre class="Agda">

<a id="5442" class="Keyword">infix</a> <a id="5448" class="Number">2</a> <a id="5450" href="Overture.Basic.html#5460" class="Function">∃-syntax</a>

<a id="∃-syntax"></a><a id="5460" href="Overture.Basic.html#5460" class="Function">∃-syntax</a> <a id="5469" class="Symbol">:</a> <a id="5471" class="Symbol">∀</a> <a id="5473" class="Symbol">{</a><a id="5474" href="Overture.Basic.html#5474" class="Bound">A</a> <a id="5476" class="Symbol">:</a> <a id="5478" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5483" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="5484" class="Symbol">}</a> <a id="5486" class="Symbol">→</a> <a id="5488" class="Symbol">(</a><a id="5489" href="Overture.Basic.html#5474" class="Bound">A</a> <a id="5491" class="Symbol">→</a> <a id="5493" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5498" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="5499" class="Symbol">)</a> <a id="5501" class="Symbol">→</a> <a id="5503" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="5507" class="Symbol">(</a><a id="5508" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="5510" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5512" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="5513" class="Symbol">)</a>
<a id="5515" href="Overture.Basic.html#5460" class="Function">∃-syntax</a> <a id="5524" class="Symbol">=</a> <a id="5526" href="Data.Product.Base.html#852" class="Function">∃</a>

<a id="5529" class="Keyword">syntax</a> <a id="5536" href="Overture.Basic.html#5460" class="Function">∃-syntax</a> <a id="5545" class="Symbol">(λ</a> <a id="5548" class="Bound">x</a> <a id="5550" class="Symbol">→</a> <a id="5552" class="Bound">B</a><a id="5553" class="Symbol">)</a> <a id="5555" class="Symbol">=</a> <a id="5557" class="Function">∃[</a> <a id="5560" class="Bound">x</a> <a id="5562" class="Function">∈</a> <a id="5564" class="Function">A</a> <a id="5566" class="Function">]</a> <a id="5568" class="Bound">B</a>
</pre>

#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with an uppercase pi symbol
and typically expressed as `Π(x : A) B x`, or something similar.  In Agda syntax,
one writes `(x : A) → B x` for this dependent function type, but we can define
syntax that is closer to standard notation as follows.

<pre class="Agda">

<a id="Π"></a><a id="5930" href="Overture.Basic.html#5930" class="Function">Π</a> <a id="5932" class="Symbol">:</a> <a id="5934" class="Symbol">{</a><a id="5935" href="Overture.Basic.html#5935" class="Bound">A</a> <a id="5937" class="Symbol">:</a> <a id="5939" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5944" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="5946" class="Symbol">}</a> <a id="5948" class="Symbol">(</a><a id="5949" href="Overture.Basic.html#5949" class="Bound">B</a> <a id="5951" class="Symbol">:</a> <a id="5953" href="Overture.Basic.html#5935" class="Bound">A</a> <a id="5955" class="Symbol">→</a> <a id="5957" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5962" href="Overture.Basic.html#3659" class="Generalizable">b</a> <a id="5964" class="Symbol">)</a> <a id="5966" class="Symbol">→</a> <a id="5968" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="5973" class="Symbol">(</a><a id="5974" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="5976" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5978" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="5979" class="Symbol">)</a>
<a id="5981" href="Overture.Basic.html#5930" class="Function">Π</a> <a id="5983" class="Symbol">{</a><a id="5984" class="Argument">A</a> <a id="5986" class="Symbol">=</a> <a id="5988" href="Overture.Basic.html#5988" class="Bound">A</a><a id="5989" class="Symbol">}</a> <a id="5991" href="Overture.Basic.html#5991" class="Bound">B</a> <a id="5993" class="Symbol">=</a> <a id="5995" class="Symbol">(</a><a id="5996" href="Overture.Basic.html#5996" class="Bound">x</a> <a id="5998" class="Symbol">:</a> <a id="6000" href="Overture.Basic.html#5988" class="Bound">A</a><a id="6001" class="Symbol">)</a> <a id="6003" class="Symbol">→</a> <a id="6005" href="Overture.Basic.html#5991" class="Bound">B</a> <a id="6007" href="Overture.Basic.html#5996" class="Bound">x</a>

<a id="Π-syntax"></a><a id="6010" href="Overture.Basic.html#6010" class="Function">Π-syntax</a> <a id="6019" class="Symbol">:</a> <a id="6021" class="Symbol">(</a><a id="6022" href="Overture.Basic.html#6022" class="Bound">A</a> <a id="6024" class="Symbol">:</a> <a id="6026" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6031" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="6032" class="Symbol">)(</a><a id="6034" href="Overture.Basic.html#6034" class="Bound">B</a> <a id="6036" class="Symbol">:</a> <a id="6038" href="Overture.Basic.html#6022" class="Bound">A</a> <a id="6040" class="Symbol">→</a> <a id="6042" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6047" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="6048" class="Symbol">)</a> <a id="6050" class="Symbol">→</a> <a id="6052" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="6057" class="Symbol">(</a><a id="6058" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="6060" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6062" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="6063" class="Symbol">)</a>
<a id="6065" href="Overture.Basic.html#6010" class="Function">Π-syntax</a> <a id="6074" href="Overture.Basic.html#6074" class="Bound">A</a> <a id="6076" href="Overture.Basic.html#6076" class="Bound">B</a> <a id="6078" class="Symbol">=</a> <a id="6080" href="Overture.Basic.html#5930" class="Function">Π</a> <a id="6082" href="Overture.Basic.html#6076" class="Bound">B</a>

<a id="6085" class="Keyword">syntax</a> <a id="6092" href="Overture.Basic.html#6010" class="Function">Π-syntax</a> <a id="6101" class="Bound">A</a> <a id="6103" class="Symbol">(λ</a> <a id="6106" class="Bound">x</a> <a id="6108" class="Symbol">→</a> <a id="6110" class="Bound">B</a><a id="6111" class="Symbol">)</a> <a id="6113" class="Symbol">=</a> <a id="6115" class="Function">Π[</a> <a id="6118" class="Bound">x</a> <a id="6120" class="Function">∈</a> <a id="6122" class="Bound">A</a> <a id="6124" class="Function">]</a> <a id="6126" class="Bound">B</a>
<a id="6128" class="Keyword">infix</a> <a id="6134" class="Number">6</a> <a id="6136" href="Overture.Basic.html#6010" class="Function">Π-syntax</a>

</pre>
In the modules that follow, we will see many examples of this syntax in action.


#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:
```agda

Type a : Type (lsuc a) ,   Type (lsuc a) : Type (lsuc (lsuc a)) , etc.

```
and so on. This means that the universe `Type a` has type `Type(lsuc a)`, and
`Type(lsuc a)` has type `Type(lsuc (lsuc a))`, and so on.  It is important to
note, however, this does *not* imply that  `Type a : Type(lsuc(lsuc a))`. In other
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
a != 𝓞 ⊔ 𝓥 ⊔ (lsuc a) when checking that the expression... has type...
```
This error message means that Agda encountered the universe level `lsuc a`, on
line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type
at level `𝓞 ⊔ 𝓥 ⊔ lsuc a` instead.

The general `Lift` record type that we now describe makes such problems easier to
deal with. It takes a type inhabiting some universe and embeds it into a higher
universe and, apart from syntax and notation, it is equivalent to the `Lift` type
one finds in the `Level` module of the [Agda Standard Library][].
```agda
record Lift {𝓦 a : Level} (A : Set a) : Set (a ⊔ 𝓦) where
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

<a id="lift∼lower"></a><a id="8838" href="Overture.Basic.html#8838" class="Function">lift∼lower</a> <a id="8849" class="Symbol">:</a> <a id="8851" class="Symbol">{</a><a id="8852" href="Overture.Basic.html#8852" class="Bound">A</a> <a id="8854" class="Symbol">:</a> <a id="8856" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="8861" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="8862" class="Symbol">}</a> <a id="8864" class="Symbol">→</a> <a id="8866" href="Level.html#466" class="InductiveConstructor">lift</a> <a id="8871" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="8873" href="Level.html#479" class="Field">lower</a> <a id="8879" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8881" href="Overture.Basic.html#5318" class="Function">𝑖𝑑</a> <a id="8884" class="Symbol">(</a><a id="8885" href="Level.html#409" class="Record">Lift</a> <a id="8890" href="Overture.Basic.html#3659" class="Generalizable">b</a> <a id="8892" href="Overture.Basic.html#8852" class="Bound">A</a><a id="8893" class="Symbol">)</a>
<a id="8895" href="Overture.Basic.html#8838" class="Function">lift∼lower</a> <a id="8906" class="Symbol">=</a> <a id="8908" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8914" href="Overture.Basic.html#8914" class="Function">lower∼lift</a> <a id="8925" class="Symbol">:</a> <a id="8927" class="Symbol">{</a><a id="8928" href="Overture.Basic.html#8928" class="Bound">A</a> <a id="8930" class="Symbol">:</a> <a id="8932" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="8937" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="8938" class="Symbol">}</a> <a id="8940" class="Symbol">→</a> <a id="8942" class="Symbol">(</a><a id="8943" href="Level.html#479" class="Field">lower</a> <a id="8949" class="Symbol">{</a><a id="8950" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="8951" class="Symbol">}{</a><a id="8953" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="8954" class="Symbol">})</a> <a id="8957" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="8959" href="Level.html#466" class="InductiveConstructor">lift</a> <a id="8964" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8966" href="Overture.Basic.html#5318" class="Function">𝑖𝑑</a> <a id="8969" href="Overture.Basic.html#8928" class="Bound">A</a>
<a id="8971" href="Overture.Basic.html#8914" class="Function">lower∼lift</a> <a id="8982" class="Symbol">=</a> <a id="8984" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

</pre>
The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion
that two functions are (extensionally) the same in the sense that they produce
the same output when given the same input.  (We will have more to say about
this notion of equality in the [Base.Equality.Extensionality][] module.)
<pre class="Agda">

<a id="9520" class="Keyword">module</a> <a id="9527" href="Overture.Basic.html#9527" class="Module">_</a> <a id="9529" class="Symbol">{</a><a id="9530" href="Overture.Basic.html#9530" class="Bound">a</a> <a id="9532" class="Symbol">:</a> <a id="9534" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9539" class="Symbol">}{</a><a id="9541" href="Overture.Basic.html#9541" class="Bound">A</a> <a id="9543" class="Symbol">:</a> <a id="9545" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9550" href="Overture.Basic.html#9530" class="Bound">a</a><a id="9551" class="Symbol">}{</a><a id="9553" href="Overture.Basic.html#9553" class="Bound">b</a> <a id="9555" class="Symbol">:</a> <a id="9557" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9562" class="Symbol">}{</a><a id="9564" href="Overture.Basic.html#9564" class="Bound">B</a> <a id="9566" class="Symbol">:</a> <a id="9568" href="Overture.Basic.html#9541" class="Bound">A</a> <a id="9570" class="Symbol">→</a> <a id="9572" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9577" href="Overture.Basic.html#9553" class="Bound">b</a> <a id="9579" class="Symbol">}</a> <a id="9581" class="Keyword">where</a>

 <a id="9589" href="Overture.Basic.html#9589" class="Function Operator">_≈_</a> <a id="9593" class="Symbol">:</a>  <a id="9596" class="Symbol">(</a><a id="9597" href="Overture.Basic.html#9597" class="Bound">f</a> <a id="9599" href="Overture.Basic.html#9599" class="Bound">g</a> <a id="9601" class="Symbol">:</a> <a id="9603" class="Symbol">(</a><a id="9604" href="Overture.Basic.html#9604" class="Bound">a</a> <a id="9606" class="Symbol">:</a> <a id="9608" href="Overture.Basic.html#9541" class="Bound">A</a><a id="9609" class="Symbol">)</a> <a id="9611" class="Symbol">→</a> <a id="9613" href="Overture.Basic.html#9564" class="Bound">B</a> <a id="9615" href="Overture.Basic.html#9604" class="Bound">a</a><a id="9616" class="Symbol">)</a> <a id="9618" class="Symbol">→</a> <a id="9620" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="9625" class="Symbol">(</a><a id="9626" href="Overture.Basic.html#9530" class="Bound">a</a> <a id="9628" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="9630" href="Overture.Basic.html#9553" class="Bound">b</a><a id="9631" class="Symbol">)</a>
 <a id="9634" href="Overture.Basic.html#9634" class="Bound">f</a> <a id="9636" href="Overture.Basic.html#9589" class="Function Operator">≈</a> <a id="9638" href="Overture.Basic.html#9638" class="Bound">g</a> <a id="9640" class="Symbol">=</a> <a id="9642" class="Symbol">∀</a> <a id="9644" href="Overture.Basic.html#9644" class="Bound">x</a> <a id="9646" class="Symbol">→</a> <a id="9648" href="Overture.Basic.html#9634" class="Bound">f</a> <a id="9650" href="Overture.Basic.html#9644" class="Bound">x</a> <a id="9652" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9654" href="Overture.Basic.html#9638" class="Bound">g</a> <a id="9656" href="Overture.Basic.html#9644" class="Bound">x</a>

 <a id="9660" class="Keyword">infix</a> <a id="9666" class="Number">8</a> <a id="9668" href="Overture.Basic.html#9589" class="Function Operator">_≈_</a>

 <a id="9674" href="Overture.Basic.html#9674" class="Function">≈IsEquivalence</a> <a id="9689" class="Symbol">:</a> <a id="9691" href="Relation.Binary.Structures.html#1550" class="Record">IsEquivalence</a> <a id="9705" href="Overture.Basic.html#9589" class="Function Operator">_≈_</a>
 <a id="9710" href="Relation.Binary.Structures.html#1596" class="Field">IsEquivalence.refl</a>   <a id="9731" href="Overture.Basic.html#9674" class="Function">≈IsEquivalence</a>          <a id="9755" class="Symbol">=</a> <a id="9757" class="Symbol">λ</a> <a id="9759" href="Overture.Basic.html#9759" class="Bound">_</a> <a id="9761" class="Symbol">→</a> <a id="9763" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
 <a id="9769" href="Relation.Binary.Structures.html#1622" class="Field">IsEquivalence.sym</a>    <a id="9790" href="Overture.Basic.html#9674" class="Function">≈IsEquivalence</a> <a id="9805" href="Overture.Basic.html#9805" class="Bound">f≈g</a>      <a id="9814" class="Symbol">=</a> <a id="9816" class="Symbol">λ</a> <a id="9818" href="Overture.Basic.html#9818" class="Bound">x</a> <a id="9820" class="Symbol">→</a> <a id="9822" href="Relation.Binary.PropositionalEquality.Core.html#1893" class="Function">sym</a> <a id="9826" class="Symbol">(</a><a id="9827" href="Overture.Basic.html#9805" class="Bound">f≈g</a> <a id="9831" href="Overture.Basic.html#9818" class="Bound">x</a><a id="9832" class="Symbol">)</a>
 <a id="9835" href="Relation.Binary.Structures.html#1648" class="Field">IsEquivalence.trans</a>  <a id="9856" href="Overture.Basic.html#9674" class="Function">≈IsEquivalence</a> <a id="9871" href="Overture.Basic.html#9871" class="Bound">f≈g</a> <a id="9875" href="Overture.Basic.html#9875" class="Bound">g≈h</a>  <a id="9880" class="Symbol">=</a> <a id="9882" class="Symbol">λ</a> <a id="9884" href="Overture.Basic.html#9884" class="Bound">x</a> <a id="9886" class="Symbol">→</a> <a id="9888" href="Relation.Binary.PropositionalEquality.Core.html#1938" class="Function">trans</a> <a id="9894" class="Symbol">(</a><a id="9895" href="Overture.Basic.html#9871" class="Bound">f≈g</a> <a id="9899" href="Overture.Basic.html#9884" class="Bound">x</a><a id="9900" class="Symbol">)</a> <a id="9902" class="Symbol">(</a><a id="9903" href="Overture.Basic.html#9875" class="Bound">g≈h</a> <a id="9907" href="Overture.Basic.html#9884" class="Bound">x</a><a id="9908" class="Symbol">)</a>

</pre>
The following is convenient for proving two pairs of a product type are equal
using the fact that their respective components are equal.
<pre class="Agda">

<a id="≡-by-parts"></a><a id="10073" href="Overture.Basic.html#10073" class="Function">≡-by-parts</a> <a id="10084" class="Symbol">:</a>  <a id="10087" class="Symbol">{</a><a id="10088" href="Overture.Basic.html#10088" class="Bound">A</a> <a id="10090" class="Symbol">:</a> <a id="10092" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10097" href="Overture.Basic.html#3657" class="Generalizable">a</a><a id="10098" class="Symbol">}{</a><a id="10100" href="Overture.Basic.html#10100" class="Bound">B</a> <a id="10102" class="Symbol">:</a> <a id="10104" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10109" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="10110" class="Symbol">}{</a><a id="10112" href="Overture.Basic.html#10112" class="Bound">u</a> <a id="10114" href="Overture.Basic.html#10114" class="Bound">v</a> <a id="10116" class="Symbol">:</a> <a id="10118" href="Overture.Basic.html#10088" class="Bound">A</a> <a id="10120" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="10122" href="Overture.Basic.html#10100" class="Bound">B</a><a id="10123" class="Symbol">}</a>
 <a id="10126" class="Symbol">→</a>            <a id="10139" href="Overture.Basic.html#3214" class="Field">fst</a> <a id="10143" href="Overture.Basic.html#10112" class="Bound">u</a> <a id="10145" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10147" href="Overture.Basic.html#3214" class="Field">fst</a> <a id="10151" href="Overture.Basic.html#10114" class="Bound">v</a> <a id="10153" class="Symbol">→</a> <a id="10155" href="Overture.Basic.html#3229" class="Field">snd</a> <a id="10159" href="Overture.Basic.html#10112" class="Bound">u</a> <a id="10161" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10163" href="Overture.Basic.html#3229" class="Field">snd</a> <a id="10167" href="Overture.Basic.html#10114" class="Bound">v</a> <a id="10169" class="Symbol">→</a> <a id="10171" href="Overture.Basic.html#10112" class="Bound">u</a> <a id="10173" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10175" href="Overture.Basic.html#10114" class="Bound">v</a>

<a id="10178" href="Overture.Basic.html#10073" class="Function">≡-by-parts</a> <a id="10189" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="10194" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="10199" class="Symbol">=</a> <a id="10201" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

</pre>
Lastly, we will use the following type (instead of `subst`) to transport equality
proofs.

<pre class="Agda">

<a id="transport"></a><a id="10323" href="Overture.Basic.html#10323" class="Function">transport</a> <a id="10333" class="Symbol">:</a> <a id="10335" class="Symbol">{</a><a id="10336" href="Overture.Basic.html#10336" class="Bound">A</a> <a id="10338" class="Symbol">:</a> <a id="10340" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10345" href="Overture.Basic.html#3657" class="Generalizable">a</a> <a id="10347" class="Symbol">}</a> <a id="10349" class="Symbol">(</a><a id="10350" href="Overture.Basic.html#10350" class="Bound">B</a> <a id="10352" class="Symbol">:</a> <a id="10354" href="Overture.Basic.html#10336" class="Bound">A</a> <a id="10356" class="Symbol">→</a> <a id="10358" href="Overture.Basic.html#3077" class="Primitive">Type</a> <a id="10363" href="Overture.Basic.html#3659" class="Generalizable">b</a><a id="10364" class="Symbol">)</a> <a id="10366" class="Symbol">{</a><a id="10367" href="Overture.Basic.html#10367" class="Bound">x</a> <a id="10369" href="Overture.Basic.html#10369" class="Bound">y</a> <a id="10371" class="Symbol">:</a> <a id="10373" href="Overture.Basic.html#10336" class="Bound">A</a><a id="10374" class="Symbol">}</a> <a id="10376" class="Symbol">→</a> <a id="10378" href="Overture.Basic.html#10367" class="Bound">x</a> <a id="10380" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10382" href="Overture.Basic.html#10369" class="Bound">y</a> <a id="10384" class="Symbol">→</a> <a id="10386" href="Overture.Basic.html#10350" class="Bound">B</a> <a id="10388" href="Overture.Basic.html#10367" class="Bound">x</a> <a id="10390" class="Symbol">→</a> <a id="10392" href="Overture.Basic.html#10350" class="Bound">B</a> <a id="10394" href="Overture.Basic.html#10369" class="Bound">y</a>
<a id="10396" href="Overture.Basic.html#10323" class="Function">transport</a> <a id="10406" href="Overture.Basic.html#10406" class="Bound">B</a> <a id="10408" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="10413" class="Symbol">=</a> <a id="10415" href="Function.Base.html#704" class="Function">id</a>
</pre>

------------------------------

<span style="float:left;">[← Overture.Preface](Overture.Preface.html)</span>
<span style="float:right;">[Overture.Signatures →](Overture.Signatures.html)</span>

{% include UALib.Links.md %}


