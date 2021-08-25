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

<a id="2669" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------------------------</a>
<a id="2768" class="Keyword">open</a> <a id="2773" class="Keyword">import</a> <a id="2780" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="2795" class="Keyword">using</a> <a id="2801" class="Symbol">(</a> <a id="2803" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="2807" class="Symbol">;</a> <a id="2809" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="2814" class="Symbol">)</a> <a id="2816" class="Keyword">renaming</a> <a id="2825" class="Symbol">(</a> <a id="2827" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="2831" class="Symbol">to</a>  <a id="2835" class="Primitive">Type</a> <a id="2840" class="Symbol">;</a> <a id="2842" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="2848" class="Symbol">to</a>  <a id="2852" class="Primitive">ℓ₀</a> <a id="2855" class="Symbol">)</a>
<a id="2857" class="Keyword">open</a> <a id="2862" class="Keyword">import</a> <a id="2869" href="Data.Product.html" class="Module">Data.Product</a>   <a id="2884" class="Keyword">using</a> <a id="2890" class="Symbol">(</a> <a id="2892" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="2896" class="Symbol">;</a> <a id="2898" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="2907" class="Symbol">;</a> <a id="2909" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="2913" class="Symbol">)</a> <a id="2915" class="Keyword">renaming</a> <a id="2924" class="Symbol">(</a> <a id="2926" href="Agda.Builtin.Sigma.html#252" class="Field">proj₁</a> <a id="2932" class="Symbol">to</a> <a id="2935" class="Field">fst</a> <a id="2939" class="Symbol">;</a> <a id="2941" href="Agda.Builtin.Sigma.html#264" class="Field">proj₂</a> <a id="2947" class="Symbol">to</a> <a id="2950" class="Field">snd</a> <a id="2954" class="Symbol">)</a>
<a id="2956" class="Keyword">open</a> <a id="2961" class="Keyword">import</a> <a id="2968" href="Function.Base.html" class="Module">Function.Base</a>  <a id="2983" class="Keyword">using</a> <a id="2989" class="Symbol">(</a> <a id="2991" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="2995" class="Symbol">;</a> <a id="2997" href="Function.Base.html#615" class="Function">id</a> <a id="3000" class="Symbol">)</a>
<a id="3002" class="Keyword">open</a> <a id="3007" class="Keyword">import</a> <a id="3014" href="Level.html" class="Module">Level</a>          <a id="3029" class="Keyword">using</a> <a id="3035" class="Symbol">(</a> <a id="3037" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="3043" class="Symbol">;</a> <a id="3045" href="Level.html#400" class="Record">Lift</a> <a id="3050" class="Symbol">;</a> <a id="3052" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="3057" class="Symbol">;</a> <a id="3059" href="Level.html#470" class="Field">lower</a> <a id="3065" class="Symbol">)</a>
<a id="3067" class="Keyword">open</a> <a id="3072" class="Keyword">import</a> <a id="3079" href="Relation.Binary.Structures.html" class="Module">Relation.Binary.Structures</a>
                           <a id="3133" class="Keyword">using</a> <a id="3139" class="Symbol">(</a> <a id="3141" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3155" class="Symbol">;</a> <a id="3157" href="Relation.Binary.Structures.html#3174" class="Record">IsPartialOrder</a> <a id="3172" class="Symbol">)</a>
<a id="3174" class="Keyword">open</a> <a id="3179" class="Keyword">import</a> <a id="3186" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                           <a id="3251" class="Keyword">using</a> <a id="3257" class="Symbol">(</a> <a id="3259" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="3263" class="Symbol">;</a> <a id="3265" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="3270" class="Symbol">;</a> <a id="3272" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="3276" class="Symbol">;</a> <a id="3278" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="3284" class="Symbol">)</a>

<a id="3287" class="Keyword">private</a> <a id="3295" class="Keyword">variable</a> <a id="3304" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="3306" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a> <a id="3308" class="Symbol">:</a> <a id="3310" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="ℓ₁"></a><a id="3317" href="Overture.Preliminaries.html#3317" class="Function">ℓ₁</a> <a id="3320" class="Symbol">:</a> <a id="3322" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="3328" href="Overture.Preliminaries.html#3317" class="Function">ℓ₁</a> <a id="3331" class="Symbol">=</a> <a id="3333" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3338" href="Overture.Preliminaries.html#2852" class="Primitive">ℓ₀</a>

<a id="3342" class="Comment">-- The empty type</a>
<a id="3360" class="Keyword">data</a> <a id="𝟘"></a><a id="3365" href="Overture.Preliminaries.html#3365" class="Datatype">𝟘</a> <a id="3367" class="Symbol">:</a> <a id="3369" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="3374" href="Overture.Preliminaries.html#2852" class="Primitive">ℓ₀</a> <a id="3377" class="Keyword">where</a>  <a id="3384" class="Comment">-- maybe we should use ⊥ instead ...?</a>

<a id="3423" class="Comment">-- The one element type</a>
<a id="3447" class="Keyword">data</a> <a id="𝟙"></a><a id="3452" href="Overture.Preliminaries.html#3452" class="Datatype">𝟙</a> <a id="3454" class="Symbol">:</a> <a id="3456" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="3461" href="Overture.Preliminaries.html#2852" class="Primitive">ℓ₀</a> <a id="3464" class="Keyword">where</a>
 <a id="𝟙.𝟎"></a><a id="3471" href="Overture.Preliminaries.html#3471" class="InductiveConstructor">𝟎</a> <a id="3473" class="Symbol">:</a> <a id="3475" href="Overture.Preliminaries.html#3452" class="Datatype">𝟙</a>

<a id="3478" class="Comment">-- the two element type</a>
<a id="3502" class="Keyword">data</a> <a id="𝟚"></a><a id="3507" href="Overture.Preliminaries.html#3507" class="Datatype">𝟚</a> <a id="3509" class="Symbol">:</a> <a id="3511" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="3516" href="Overture.Preliminaries.html#2852" class="Primitive">ℓ₀</a> <a id="3519" class="Keyword">where</a>  <a id="3526" class="Comment">-- We could use Bool instead.</a>
 <a id="𝟚.𝟎"></a><a id="3557" href="Overture.Preliminaries.html#3557" class="InductiveConstructor">𝟎</a> <a id="3559" class="Symbol">:</a> <a id="3561" href="Overture.Preliminaries.html#3507" class="Datatype">𝟚</a>                  <a id="3580" class="Comment">-- &quot;         &quot; false &quot;   &quot;</a>
 <a id="𝟚.𝟏"></a><a id="3608" href="Overture.Preliminaries.html#3608" class="InductiveConstructor">𝟏</a> <a id="3610" class="Symbol">:</a> <a id="3612" href="Overture.Preliminaries.html#3507" class="Datatype">𝟚</a>                  <a id="3631" class="Comment">-- &quot;         &quot; true  &quot;   &quot;</a>

<a id="3659" class="Comment">-- the three element type</a>
<a id="3685" class="Keyword">data</a> <a id="𝟛"></a><a id="3690" href="Overture.Preliminaries.html#3690" class="Datatype">𝟛</a> <a id="3692" class="Symbol">:</a> <a id="3694" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="3699" href="Overture.Preliminaries.html#2852" class="Primitive">ℓ₀</a> <a id="3702" class="Keyword">where</a>
 <a id="𝟛.𝟎"></a><a id="3709" href="Overture.Preliminaries.html#3709" class="InductiveConstructor">𝟎</a> <a id="3711" class="Symbol">:</a> <a id="3713" href="Overture.Preliminaries.html#3690" class="Datatype">𝟛</a>
 <a id="𝟛.𝟏"></a><a id="3716" href="Overture.Preliminaries.html#3716" class="InductiveConstructor">𝟏</a> <a id="3718" class="Symbol">:</a> <a id="3720" href="Overture.Preliminaries.html#3690" class="Datatype">𝟛</a>
 <a id="𝟛.𝟐"></a><a id="3723" href="Overture.Preliminaries.html#3723" class="InductiveConstructor">𝟐</a> <a id="3725" class="Symbol">:</a> <a id="3727" href="Overture.Preliminaries.html#3690" class="Datatype">𝟛</a>

</pre>


#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second projections out of the product.  However, we prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥`, respectively. We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="4180" class="Keyword">module</a> <a id="4187" href="Overture.Preliminaries.html#4187" class="Module">_</a> <a id="4189" class="Symbol">{</a><a id="4190" href="Overture.Preliminaries.html#4190" class="Bound">A</a> <a id="4192" class="Symbol">:</a> <a id="4194" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="4199" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="4201" class="Symbol">}{</a><a id="4203" href="Overture.Preliminaries.html#4203" class="Bound">B</a> <a id="4205" class="Symbol">:</a> <a id="4207" href="Overture.Preliminaries.html#4190" class="Bound">A</a> <a id="4209" class="Symbol">→</a> <a id="4211" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="4216" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="4217" class="Symbol">}</a> <a id="4219" class="Keyword">where</a>

 <a id="4227" href="Overture.Preliminaries.html#4227" class="Function Operator">∣_∣</a> <a id="4231" class="Symbol">:</a> <a id="4233" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4236" href="Overture.Preliminaries.html#4236" class="Bound">x</a> <a id="4238" href="Data.Product.html#916" class="Function">∈</a> <a id="4240" href="Overture.Preliminaries.html#4190" class="Bound">A</a> <a id="4242" href="Data.Product.html#916" class="Function">]</a> <a id="4244" href="Overture.Preliminaries.html#4203" class="Bound">B</a> <a id="4246" href="Overture.Preliminaries.html#4236" class="Bound">x</a> <a id="4248" class="Symbol">→</a> <a id="4250" href="Overture.Preliminaries.html#4190" class="Bound">A</a>
 <a id="4253" href="Overture.Preliminaries.html#4227" class="Function Operator">∣_∣</a> <a id="4257" class="Symbol">=</a> <a id="4259" href="Overture.Preliminaries.html#2935" class="Field">fst</a>

 <a id="4265" href="Overture.Preliminaries.html#4265" class="Function Operator">∥_∥</a> <a id="4269" class="Symbol">:</a> <a id="4271" class="Symbol">(</a><a id="4272" href="Overture.Preliminaries.html#4272" class="Bound">z</a> <a id="4274" class="Symbol">:</a> <a id="4276" href="Data.Product.html#916" class="Function">Σ[</a> <a id="4279" href="Overture.Preliminaries.html#4279" class="Bound">a</a> <a id="4281" href="Data.Product.html#916" class="Function">∈</a> <a id="4283" href="Overture.Preliminaries.html#4190" class="Bound">A</a> <a id="4285" href="Data.Product.html#916" class="Function">]</a> <a id="4287" href="Overture.Preliminaries.html#4203" class="Bound">B</a> <a id="4289" href="Overture.Preliminaries.html#4279" class="Bound">a</a><a id="4290" class="Symbol">)</a> <a id="4292" class="Symbol">→</a> <a id="4294" href="Overture.Preliminaries.html#4203" class="Bound">B</a> <a id="4296" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a> <a id="4298" href="Overture.Preliminaries.html#4272" class="Bound">z</a> <a id="4300" href="Overture.Preliminaries.html#4227" class="Function Operator">∣</a>
 <a id="4303" href="Overture.Preliminaries.html#4265" class="Function Operator">∥_∥</a> <a id="4307" class="Symbol">=</a> <a id="4309" href="Overture.Preliminaries.html#2950" class="Field">snd</a>

 <a id="4315" class="Keyword">infix</a>  <a id="4322" class="Number">40</a> <a id="4325" href="Overture.Preliminaries.html#4227" class="Function Operator">∣_∣</a>
</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

Let's define some useful syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.

<pre class="Agda">

<a id="_⁻¹"></a><a id="4931" href="Overture.Preliminaries.html#4931" class="Function Operator">_⁻¹</a> <a id="4935" class="Symbol">:</a> <a id="4937" class="Symbol">{</a><a id="4938" href="Overture.Preliminaries.html#4938" class="Bound">A</a> <a id="4940" class="Symbol">:</a> <a id="4942" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="4947" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="4948" class="Symbol">}</a> <a id="4950" class="Symbol">{</a><a id="4951" href="Overture.Preliminaries.html#4951" class="Bound">x</a> <a id="4953" href="Overture.Preliminaries.html#4953" class="Bound">y</a> <a id="4955" class="Symbol">:</a> <a id="4957" href="Overture.Preliminaries.html#4938" class="Bound">A</a><a id="4958" class="Symbol">}</a> <a id="4960" class="Symbol">→</a> <a id="4962" href="Overture.Preliminaries.html#4951" class="Bound">x</a> <a id="4964" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4966" href="Overture.Preliminaries.html#4953" class="Bound">y</a> <a id="4968" class="Symbol">→</a> <a id="4970" href="Overture.Preliminaries.html#4953" class="Bound">y</a> <a id="4972" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="4974" href="Overture.Preliminaries.html#4951" class="Bound">x</a>
<a id="4976" href="Overture.Preliminaries.html#4976" class="Bound">p</a> <a id="4978" href="Overture.Preliminaries.html#4931" class="Function Operator">⁻¹</a> <a id="4981" class="Symbol">=</a> <a id="4983" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="4987" href="Overture.Preliminaries.html#4976" class="Bound">p</a>

<a id="4990" class="Keyword">infix</a>  <a id="4997" class="Number">40</a> <a id="5000" href="Overture.Preliminaries.html#4931" class="Function Operator">_⁻¹</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

<a id="_∙_"></a><a id="5257" href="Overture.Preliminaries.html#5257" class="Function Operator">_∙_</a> <a id="5261" class="Symbol">:</a> <a id="5263" class="Symbol">{</a><a id="5264" href="Overture.Preliminaries.html#5264" class="Bound">A</a> <a id="5266" class="Symbol">:</a> <a id="5268" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5273" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="5274" class="Symbol">}{</a><a id="5276" href="Overture.Preliminaries.html#5276" class="Bound">x</a> <a id="5278" href="Overture.Preliminaries.html#5278" class="Bound">y</a> <a id="5280" href="Overture.Preliminaries.html#5280" class="Bound">z</a> <a id="5282" class="Symbol">:</a> <a id="5284" href="Overture.Preliminaries.html#5264" class="Bound">A</a><a id="5285" class="Symbol">}</a> <a id="5287" class="Symbol">→</a> <a id="5289" href="Overture.Preliminaries.html#5276" class="Bound">x</a> <a id="5291" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5293" href="Overture.Preliminaries.html#5278" class="Bound">y</a> <a id="5295" class="Symbol">→</a> <a id="5297" href="Overture.Preliminaries.html#5278" class="Bound">y</a> <a id="5299" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5301" href="Overture.Preliminaries.html#5280" class="Bound">z</a> <a id="5303" class="Symbol">→</a> <a id="5305" href="Overture.Preliminaries.html#5276" class="Bound">x</a> <a id="5307" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5309" href="Overture.Preliminaries.html#5280" class="Bound">z</a>
<a id="5311" href="Overture.Preliminaries.html#5311" class="Bound">p</a> <a id="5313" href="Overture.Preliminaries.html#5257" class="Function Operator">∙</a> <a id="5315" href="Overture.Preliminaries.html#5315" class="Bound">q</a> <a id="5317" class="Symbol">=</a> <a id="5319" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="5325" href="Overture.Preliminaries.html#5311" class="Bound">p</a> <a id="5327" href="Overture.Preliminaries.html#5315" class="Bound">q</a>

<a id="𝑖𝑑"></a><a id="5330" href="Overture.Preliminaries.html#5330" class="Function">𝑖𝑑</a> <a id="5333" class="Symbol">:</a> <a id="5335" class="Symbol">(</a><a id="5336" href="Overture.Preliminaries.html#5336" class="Bound">A</a> <a id="5338" class="Symbol">:</a> <a id="5340" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5345" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="5347" class="Symbol">)</a> <a id="5349" class="Symbol">→</a> <a id="5351" href="Overture.Preliminaries.html#5336" class="Bound">A</a> <a id="5353" class="Symbol">→</a> <a id="5355" href="Overture.Preliminaries.html#5336" class="Bound">A</a>
<a id="5357" href="Overture.Preliminaries.html#5330" class="Function">𝑖𝑑</a> <a id="5360" href="Overture.Preliminaries.html#5360" class="Bound">A</a> <a id="5362" class="Symbol">=</a> <a id="5364" class="Symbol">λ</a> <a id="5366" href="Overture.Preliminaries.html#5366" class="Bound">x</a> <a id="5368" class="Symbol">→</a> <a id="5370" href="Overture.Preliminaries.html#5366" class="Bound">x</a>

<a id="5373" class="Keyword">infixl</a> <a id="5380" class="Number">30</a> <a id="5383" href="Overture.Preliminaries.html#5257" class="Function Operator">_∙_</a>
</pre>


#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with a Pi symbol typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes `(x : A) → B x` for the dependent function type, but may use syntax that is closer to the standard Π notation and made available in Agda as follows.

<pre class="Agda">

<a id="Π"></a><a id="5756" href="Overture.Preliminaries.html#5756" class="Function">Π</a> <a id="5758" class="Symbol">:</a> <a id="5760" class="Symbol">{</a><a id="5761" href="Overture.Preliminaries.html#5761" class="Bound">A</a> <a id="5763" class="Symbol">:</a> <a id="5765" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5770" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="5772" class="Symbol">}</a> <a id="5774" class="Symbol">(</a><a id="5775" href="Overture.Preliminaries.html#5775" class="Bound">B</a> <a id="5777" class="Symbol">:</a> <a id="5779" href="Overture.Preliminaries.html#5761" class="Bound">A</a> <a id="5781" class="Symbol">→</a> <a id="5783" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5788" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a> <a id="5790" class="Symbol">)</a> <a id="5792" class="Symbol">→</a> <a id="5794" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5799" class="Symbol">(</a><a id="5800" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="5802" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5804" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="5805" class="Symbol">)</a>
<a id="5807" href="Overture.Preliminaries.html#5756" class="Function">Π</a> <a id="5809" class="Symbol">{</a><a id="5810" class="Argument">A</a> <a id="5812" class="Symbol">=</a> <a id="5814" href="Overture.Preliminaries.html#5814" class="Bound">A</a><a id="5815" class="Symbol">}</a> <a id="5817" href="Overture.Preliminaries.html#5817" class="Bound">B</a> <a id="5819" class="Symbol">=</a> <a id="5821" class="Symbol">(</a><a id="5822" href="Overture.Preliminaries.html#5822" class="Bound">x</a> <a id="5824" class="Symbol">:</a> <a id="5826" href="Overture.Preliminaries.html#5814" class="Bound">A</a><a id="5827" class="Symbol">)</a> <a id="5829" class="Symbol">→</a> <a id="5831" href="Overture.Preliminaries.html#5817" class="Bound">B</a> <a id="5833" href="Overture.Preliminaries.html#5822" class="Bound">x</a>

<a id="Π-syntax"></a><a id="5836" href="Overture.Preliminaries.html#5836" class="Function">Π-syntax</a> <a id="5845" class="Symbol">:</a> <a id="5847" class="Symbol">(</a><a id="5848" href="Overture.Preliminaries.html#5848" class="Bound">A</a> <a id="5850" class="Symbol">:</a> <a id="5852" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5857" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="5858" class="Symbol">)(</a><a id="5860" href="Overture.Preliminaries.html#5860" class="Bound">B</a> <a id="5862" class="Symbol">:</a> <a id="5864" href="Overture.Preliminaries.html#5848" class="Bound">A</a> <a id="5866" class="Symbol">→</a> <a id="5868" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5873" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="5874" class="Symbol">)</a> <a id="5876" class="Symbol">→</a> <a id="5878" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="5883" class="Symbol">(</a><a id="5884" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="5886" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5888" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="5889" class="Symbol">)</a>
<a id="5891" href="Overture.Preliminaries.html#5836" class="Function">Π-syntax</a> <a id="5900" href="Overture.Preliminaries.html#5900" class="Bound">A</a> <a id="5902" href="Overture.Preliminaries.html#5902" class="Bound">B</a> <a id="5904" class="Symbol">=</a> <a id="5906" href="Overture.Preliminaries.html#5756" class="Function">Π</a> <a id="5908" href="Overture.Preliminaries.html#5902" class="Bound">B</a>

<a id="5911" class="Keyword">syntax</a> <a id="5918" href="Overture.Preliminaries.html#5836" class="Function">Π-syntax</a> <a id="5927" class="Bound">A</a> <a id="5929" class="Symbol">(λ</a> <a id="5932" class="Bound">x</a> <a id="5934" class="Symbol">→</a> <a id="5936" class="Bound">B</a><a id="5937" class="Symbol">)</a> <a id="5939" class="Symbol">=</a> <a id="5941" class="Function">Π[</a> <a id="5944" class="Bound">x</a> <a id="5946" class="Function">∈</a> <a id="5948" class="Bound">A</a> <a id="5950" class="Function">]</a> <a id="5952" class="Bound">B</a>
<a id="5954" class="Keyword">infix</a> <a id="5960" class="Number">6</a> <a id="5962" href="Overture.Preliminaries.html#5836" class="Function">Π-syntax</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:

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

<a id="lift∼lower"></a><a id="8564" href="Overture.Preliminaries.html#8564" class="Function">lift∼lower</a> <a id="8575" class="Symbol">:</a> <a id="8577" class="Symbol">{</a><a id="8578" href="Overture.Preliminaries.html#8578" class="Bound">A</a> <a id="8580" class="Symbol">:</a> <a id="8582" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="8587" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="8588" class="Symbol">}</a> <a id="8590" class="Symbol">→</a> <a id="8592" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8597" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8599" href="Level.html#470" class="Field">lower</a> <a id="8605" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8607" href="Overture.Preliminaries.html#5330" class="Function">𝑖𝑑</a> <a id="8610" class="Symbol">(</a><a id="8611" href="Level.html#400" class="Record">Lift</a> <a id="8616" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a> <a id="8618" href="Overture.Preliminaries.html#8578" class="Bound">A</a><a id="8619" class="Symbol">)</a>
<a id="8621" href="Overture.Preliminaries.html#8564" class="Function">lift∼lower</a> <a id="8632" class="Symbol">=</a> <a id="8634" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="8640" href="Overture.Preliminaries.html#8640" class="Function">lower∼lift</a> <a id="8651" class="Symbol">:</a> <a id="8653" class="Symbol">{</a><a id="8654" href="Overture.Preliminaries.html#8654" class="Bound">A</a> <a id="8656" class="Symbol">:</a> <a id="8658" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="8663" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="8664" class="Symbol">}</a> <a id="8666" class="Symbol">→</a> <a id="8668" class="Symbol">(</a><a id="8669" href="Level.html#470" class="Field">lower</a> <a id="8675" class="Symbol">{</a><a id="8676" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="8677" class="Symbol">}{</a><a id="8679" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="8680" class="Symbol">})</a> <a id="8683" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="8685" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="8690" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8692" href="Overture.Preliminaries.html#5330" class="Function">𝑖𝑑</a> <a id="8695" href="Overture.Preliminaries.html#8654" class="Bound">A</a>
<a id="8697" href="Overture.Preliminaries.html#8640" class="Function">lower∼lift</a> <a id="8708" class="Symbol">=</a> <a id="8710" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Foundations.Extensionality][] module.)

<pre class="Agda">

<a id="9246" class="Keyword">module</a> <a id="9253" href="Overture.Preliminaries.html#9253" class="Module">_</a> <a id="9255" class="Symbol">{</a><a id="9256" href="Overture.Preliminaries.html#9256" class="Bound">α</a> <a id="9258" class="Symbol">:</a> <a id="9260" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9265" class="Symbol">}{</a><a id="9267" href="Overture.Preliminaries.html#9267" class="Bound">A</a> <a id="9269" class="Symbol">:</a> <a id="9271" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="9276" href="Overture.Preliminaries.html#9256" class="Bound">α</a><a id="9277" class="Symbol">}{</a><a id="9279" href="Overture.Preliminaries.html#9279" class="Bound">β</a> <a id="9281" class="Symbol">:</a> <a id="9283" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="9288" class="Symbol">}{</a><a id="9290" href="Overture.Preliminaries.html#9290" class="Bound">B</a> <a id="9292" class="Symbol">:</a> <a id="9294" href="Overture.Preliminaries.html#9267" class="Bound">A</a> <a id="9296" class="Symbol">→</a> <a id="9298" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="9303" href="Overture.Preliminaries.html#9279" class="Bound">β</a> <a id="9305" class="Symbol">}</a> <a id="9307" class="Keyword">where</a>

 <a id="9315" href="Overture.Preliminaries.html#9315" class="Function Operator">_≈_</a> <a id="9319" class="Symbol">:</a>  <a id="9322" class="Symbol">(</a><a id="9323" href="Overture.Preliminaries.html#9323" class="Bound">f</a> <a id="9325" href="Overture.Preliminaries.html#9325" class="Bound">g</a> <a id="9327" class="Symbol">:</a> <a id="9329" class="Symbol">(</a><a id="9330" href="Overture.Preliminaries.html#9330" class="Bound">a</a> <a id="9332" class="Symbol">:</a> <a id="9334" href="Overture.Preliminaries.html#9267" class="Bound">A</a><a id="9335" class="Symbol">)</a> <a id="9337" class="Symbol">→</a> <a id="9339" href="Overture.Preliminaries.html#9290" class="Bound">B</a> <a id="9341" href="Overture.Preliminaries.html#9330" class="Bound">a</a><a id="9342" class="Symbol">)</a> <a id="9344" class="Symbol">→</a> <a id="9346" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="9351" class="Symbol">(</a><a id="9352" href="Overture.Preliminaries.html#9256" class="Bound">α</a> <a id="9354" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9356" href="Overture.Preliminaries.html#9279" class="Bound">β</a><a id="9357" class="Symbol">)</a>
 <a id="9360" href="Overture.Preliminaries.html#9360" class="Bound">f</a> <a id="9362" href="Overture.Preliminaries.html#9315" class="Function Operator">≈</a> <a id="9364" href="Overture.Preliminaries.html#9364" class="Bound">g</a> <a id="9366" class="Symbol">=</a> <a id="9368" class="Symbol">∀</a> <a id="9370" href="Overture.Preliminaries.html#9370" class="Bound">x</a> <a id="9372" class="Symbol">→</a> <a id="9374" href="Overture.Preliminaries.html#9360" class="Bound">f</a> <a id="9376" href="Overture.Preliminaries.html#9370" class="Bound">x</a> <a id="9378" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9380" href="Overture.Preliminaries.html#9364" class="Bound">g</a> <a id="9382" href="Overture.Preliminaries.html#9370" class="Bound">x</a>

 <a id="9386" class="Keyword">infix</a> <a id="9392" class="Number">8</a> <a id="9394" href="Overture.Preliminaries.html#9315" class="Function Operator">_≈_</a>

 <a id="9400" href="Overture.Preliminaries.html#9400" class="Function">≈IsEquivalence</a> <a id="9415" class="Symbol">:</a> <a id="9417" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="9431" href="Overture.Preliminaries.html#9315" class="Function Operator">_≈_</a>
 <a id="9436" href="Relation.Binary.Structures.html#1568" class="Field">IsEquivalence.refl</a> <a id="9455" href="Overture.Preliminaries.html#9400" class="Function">≈IsEquivalence</a> <a id="9470" class="Symbol">=</a> <a id="9472" class="Symbol">λ</a> <a id="9474" href="Overture.Preliminaries.html#9474" class="Bound">_</a> <a id="9476" class="Symbol">→</a> <a id="9478" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>
 <a id="9484" href="Relation.Binary.Structures.html#1594" class="Field">IsEquivalence.sym</a> <a id="9502" href="Overture.Preliminaries.html#9400" class="Function">≈IsEquivalence</a> <a id="9517" class="Symbol">{</a><a id="9518" href="Overture.Preliminaries.html#9518" class="Bound">f</a><a id="9519" class="Symbol">}{</a><a id="9521" href="Overture.Preliminaries.html#9521" class="Bound">g</a><a id="9522" class="Symbol">}</a> <a id="9524" href="Overture.Preliminaries.html#9524" class="Bound">f≈g</a> <a id="9528" class="Symbol">=</a> <a id="9530" class="Symbol">λ</a> <a id="9532" href="Overture.Preliminaries.html#9532" class="Bound">x</a> <a id="9534" class="Symbol">→</a> <a id="9536" href="Relation.Binary.PropositionalEquality.Core.html#1684" class="Function">sym</a> <a id="9540" class="Symbol">(</a><a id="9541" href="Overture.Preliminaries.html#9524" class="Bound">f≈g</a> <a id="9545" href="Overture.Preliminaries.html#9532" class="Bound">x</a><a id="9546" class="Symbol">)</a>
 <a id="9549" href="Relation.Binary.Structures.html#1620" class="Field">IsEquivalence.trans</a> <a id="9569" href="Overture.Preliminaries.html#9400" class="Function">≈IsEquivalence</a> <a id="9584" class="Symbol">{</a><a id="9585" href="Overture.Preliminaries.html#9585" class="Bound">f</a><a id="9586" class="Symbol">}{</a><a id="9588" href="Overture.Preliminaries.html#9588" class="Bound">g</a><a id="9589" class="Symbol">}{</a><a id="9591" href="Overture.Preliminaries.html#9591" class="Bound">h</a><a id="9592" class="Symbol">}</a> <a id="9594" href="Overture.Preliminaries.html#9594" class="Bound">f≈g</a> <a id="9598" href="Overture.Preliminaries.html#9598" class="Bound">g≈h</a> <a id="9602" class="Symbol">=</a> <a id="9604" class="Symbol">λ</a> <a id="9606" href="Overture.Preliminaries.html#9606" class="Bound">x</a> <a id="9608" class="Symbol">→</a> <a id="9610" href="Relation.Binary.PropositionalEquality.Core.html#1729" class="Function">trans</a> <a id="9616" class="Symbol">(</a><a id="9617" href="Overture.Preliminaries.html#9594" class="Bound">f≈g</a> <a id="9621" href="Overture.Preliminaries.html#9606" class="Bound">x</a><a id="9622" class="Symbol">)</a> <a id="9624" class="Symbol">(</a><a id="9625" href="Overture.Preliminaries.html#9598" class="Bound">g≈h</a> <a id="9629" href="Overture.Preliminaries.html#9606" class="Bound">x</a><a id="9630" class="Symbol">)</a>

</pre>

The following is convenient for proving two pairs of a product type are equal using the fact that their
respective components are equal.

<pre class="Agda">

<a id="≡-by-parts"></a><a id="9797" href="Overture.Preliminaries.html#9797" class="Function">≡-by-parts</a> <a id="9808" class="Symbol">:</a> <a id="9810" class="Symbol">{</a><a id="9811" href="Overture.Preliminaries.html#9811" class="Bound">A</a> <a id="9813" class="Symbol">:</a> <a id="9815" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="9820" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a><a id="9821" class="Symbol">}{</a><a id="9823" href="Overture.Preliminaries.html#9823" class="Bound">B</a> <a id="9825" class="Symbol">:</a> <a id="9827" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="9832" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="9833" class="Symbol">}{</a><a id="9835" href="Overture.Preliminaries.html#9835" class="Bound">u</a> <a id="9837" href="Overture.Preliminaries.html#9837" class="Bound">v</a> <a id="9839" class="Symbol">:</a> <a id="9841" href="Overture.Preliminaries.html#9811" class="Bound">A</a> <a id="9843" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="9845" href="Overture.Preliminaries.html#9823" class="Bound">B</a><a id="9846" class="Symbol">}</a> <a id="9848" class="Symbol">→</a> <a id="9850" href="Overture.Preliminaries.html#2935" class="Field">fst</a> <a id="9854" href="Overture.Preliminaries.html#9835" class="Bound">u</a> <a id="9856" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9858" href="Overture.Preliminaries.html#2935" class="Field">fst</a> <a id="9862" href="Overture.Preliminaries.html#9837" class="Bound">v</a> <a id="9864" class="Symbol">→</a> <a id="9866" href="Overture.Preliminaries.html#2950" class="Field">snd</a> <a id="9870" href="Overture.Preliminaries.html#9835" class="Bound">u</a> <a id="9872" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9874" href="Overture.Preliminaries.html#2950" class="Field">snd</a> <a id="9878" href="Overture.Preliminaries.html#9837" class="Bound">v</a> <a id="9880" class="Symbol">→</a> <a id="9882" href="Overture.Preliminaries.html#9835" class="Bound">u</a> <a id="9884" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9886" href="Overture.Preliminaries.html#9837" class="Bound">v</a>
<a id="9888" href="Overture.Preliminaries.html#9797" class="Function">≡-by-parts</a> <a id="9899" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="9904" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="9909" class="Symbol">=</a> <a id="9911" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a>

</pre>

Lastly, we will use the following type (instead of `subst`) to transport equality proofs.

<pre class="Agda">

<a id="transport"></a><a id="10034" href="Overture.Preliminaries.html#10034" class="Function">transport</a> <a id="10044" class="Symbol">:</a> <a id="10046" class="Symbol">{</a><a id="10047" href="Overture.Preliminaries.html#10047" class="Bound">A</a> <a id="10049" class="Symbol">:</a> <a id="10051" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="10056" href="Overture.Preliminaries.html#3304" class="Generalizable">α</a> <a id="10058" class="Symbol">}</a> <a id="10060" class="Symbol">(</a><a id="10061" href="Overture.Preliminaries.html#10061" class="Bound">B</a> <a id="10063" class="Symbol">:</a> <a id="10065" href="Overture.Preliminaries.html#10047" class="Bound">A</a> <a id="10067" class="Symbol">→</a> <a id="10069" href="Overture.Preliminaries.html#2835" class="Primitive">Type</a> <a id="10074" href="Overture.Preliminaries.html#3306" class="Generalizable">β</a><a id="10075" class="Symbol">)</a> <a id="10077" class="Symbol">{</a><a id="10078" href="Overture.Preliminaries.html#10078" class="Bound">x</a> <a id="10080" href="Overture.Preliminaries.html#10080" class="Bound">y</a> <a id="10082" class="Symbol">:</a> <a id="10084" href="Overture.Preliminaries.html#10047" class="Bound">A</a><a id="10085" class="Symbol">}</a> <a id="10087" class="Symbol">→</a> <a id="10089" href="Overture.Preliminaries.html#10078" class="Bound">x</a> <a id="10091" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10093" href="Overture.Preliminaries.html#10080" class="Bound">y</a> <a id="10095" class="Symbol">→</a> <a id="10097" href="Overture.Preliminaries.html#10061" class="Bound">B</a> <a id="10099" href="Overture.Preliminaries.html#10078" class="Bound">x</a> <a id="10101" class="Symbol">→</a> <a id="10103" href="Overture.Preliminaries.html#10061" class="Bound">B</a> <a id="10105" href="Overture.Preliminaries.html#10080" class="Bound">y</a>
<a id="10107" href="Overture.Preliminaries.html#10034" class="Function">transport</a> <a id="10117" href="Overture.Preliminaries.html#10117" class="Bound">B</a> <a id="10119" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="10124" class="Symbol">=</a> <a id="10126" href="Function.Base.html#615" class="Function">id</a>

</pre>


------------------------------

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>


{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


