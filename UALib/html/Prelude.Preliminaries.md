---
layout: default
title : Prelude.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

<!--
FILE: Preliminaries.lagda
AUTHOR: William DeMeo
DATE: 14 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martín Hötzel Escardó.
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
-->

### <a id="preliminaries">Preliminaries</a>

This is the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

For the benefit of readers who are not proficient in Agda or type theory, we briefly describe some of the type theoretic foundations of the [Agda UALib][], as well as the most important basic types and features that are used throughout the library.

The [UALib][] is based on a minimal version of [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) (MLTT) which is the same or very close to the type theory on which Martin Escardo's [Type Topology][] Agda library is based.  We won't go into great detail here because there are already other very nice resources available, such as the section on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda) of the lecture notes by Escardó just mentioned, the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), and the [HoTT Book][].

We begin by noting that only a very small collection of objects is assumed at the jumping-off point for MLTT. We have the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type), and an infinite collection of *type universes* (types of types) and universe variables to denote them.
Like Escardó's, our universe variables are typically upper-case caligraphic letters from the latter half of the English alphabet (e.g., `𝓤`, `𝓥`, `𝓦`, etc.).


##### Specifying logical foundations in Agda

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2592" class="Symbol">{-#</a> <a id="2596" class="Keyword">OPTIONS</a> <a id="2604" class="Pragma">--without-K</a> <a id="2616" class="Pragma">--exact-split</a> <a id="2630" class="Pragma">--safe</a> <a id="2637" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



##### <a id="agda-modules">Agda Modules</a>
The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4349" class="Keyword">module</a> <a id="4356" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="4378" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




##### <a id="agda-universes">Agda's universes hierarchy</a>

-- Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import now.<sup>[2](Prelude.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="5892" class="Keyword">open</a> <a id="5897" class="Keyword">import</a> <a id="5904" href="Universes.html" class="Module">Universes</a> <a id="5914" class="Keyword">public</a>

</pre>

Since we used the `public` directive, the `Universes` module will be available to all modules that import [Prelude.Preliminaries][].

The `Universes` module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="6310" class="Keyword">variable</a>
 <a id="6320" href="Prelude.Preliminaries.html#6320" class="Generalizable">𝓞</a> <a id="6322" class="Symbol">:</a> <a id="6324" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

The `Universes` module also provides an elegant notation for type universes, and we adopt this notation throughout the Agda UALib.

Following [Escardó][], we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module [Escardó][] defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.

Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and [Escardó][]) denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and Type Topology/UALib notation.

```agda
Agda              Type Topology/UALib
====              ===================
Level             Universe
lzero             𝓤₀
𝓤 : Level         𝓤 : Universe
Set lzero         𝓤₀ ̇
Set 𝓤             𝓤 ̇
lsuc lzero        𝓤₀ ⁺
lsuc 𝓤            𝓤 ⁺
Set (lsuc lzero)  𝓤₀ ⁺ ̇
Set (lsuc 𝓤)      𝓤 ⁺ ̇
Setω              𝓤ω
```

To justify the introduction of this somewhat nonstandard notation for universe levels, [Escardó][] points out that the Agda library uses `Level` for universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for precisely this purpose.


#### <a id="dependent-types">Dependent types</a>



#### <a id="dependent-pair-type">Sigma types (dependent pairs)</a>

Given universes 𝓤 and 𝓥, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the **Sigma type** (or **dependent pair type**), denoted by `Σ(x ꞉ X), Y x`, generalizes the Cartesian product `X × Y` by allowing the type `Y x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ(x ꞉ X), Y x` is a pair `(x , y)` such that `x : X` and `y : Y x`.

The [Type Topology][] library contains a standard definition of the dependent product.
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Prelude.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="9106" class="Keyword">module</a> <a id="hide-sigma"></a><a id="9113" href="Prelude.Preliminaries.html#9113" class="Module">hide-sigma</a> <a id="9124" class="Keyword">where</a>

 <a id="9132" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="9139" href="Prelude.Preliminaries.html#9139" class="Record">Σ</a> <a id="9141" class="Symbol">{</a><a id="9142" href="Prelude.Preliminaries.html#9142" class="Bound">𝓤</a> <a id="9144" href="Prelude.Preliminaries.html#9144" class="Bound">𝓥</a><a id="9145" class="Symbol">}</a> <a id="9147" class="Symbol">{</a><a id="9148" href="Prelude.Preliminaries.html#9148" class="Bound">X</a> <a id="9150" class="Symbol">:</a> <a id="9152" href="Prelude.Preliminaries.html#9142" class="Bound">𝓤</a> <a id="9154" href="Universes.html#403" class="Function Operator">̇</a> <a id="9156" class="Symbol">}</a> <a id="9158" class="Symbol">(</a><a id="9159" href="Prelude.Preliminaries.html#9159" class="Bound">Y</a> <a id="9161" class="Symbol">:</a> <a id="9163" href="Prelude.Preliminaries.html#9148" class="Bound">X</a> <a id="9165" class="Symbol">→</a> <a id="9167" href="Prelude.Preliminaries.html#9144" class="Bound">𝓥</a> <a id="9169" href="Universes.html#403" class="Function Operator">̇</a> <a id="9171" class="Symbol">)</a> <a id="9173" class="Symbol">:</a> <a id="9175" href="Prelude.Preliminaries.html#9142" class="Bound">𝓤</a> <a id="9177" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9179" href="Prelude.Preliminaries.html#9144" class="Bound">𝓥</a> <a id="9181" href="Universes.html#403" class="Function Operator">̇</a>  <a id="9184" class="Keyword">where</a>
  <a id="9192" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="9204" href="Prelude.Preliminaries.html#9204" class="InductiveConstructor Operator">_,_</a>
  <a id="9210" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="9219" href="Prelude.Preliminaries.html#9219" class="Field">pr₁</a> <a id="9223" class="Symbol">:</a> <a id="9225" href="Prelude.Preliminaries.html#9148" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="9230" href="Prelude.Preliminaries.html#9230" class="Field">pr₂</a> <a id="9234" class="Symbol">:</a> <a id="9236" href="Prelude.Preliminaries.html#9159" class="Bound">Y</a> <a id="9238" href="Prelude.Preliminaries.html#9219" class="Field">pr₁</a>

 <a id="9244" class="Keyword">infixr</a> <a id="9251" class="Number">50</a> <a id="9254" href="Prelude.Preliminaries.html#9204" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="9575" href="Prelude.Preliminaries.html#9575" class="Function">-Σ</a> <a id="9578" class="Symbol">:</a> <a id="9580" class="Symbol">{</a><a id="9581" href="Prelude.Preliminaries.html#9581" class="Bound">𝓤</a> <a id="9583" href="Prelude.Preliminaries.html#9583" class="Bound">𝓥</a> <a id="9585" class="Symbol">:</a> <a id="9587" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9595" class="Symbol">}</a> <a id="9597" class="Symbol">(</a><a id="9598" href="Prelude.Preliminaries.html#9598" class="Bound">X</a> <a id="9600" class="Symbol">:</a> <a id="9602" href="Prelude.Preliminaries.html#9581" class="Bound">𝓤</a> <a id="9604" href="Universes.html#403" class="Function Operator">̇</a> <a id="9606" class="Symbol">)</a> <a id="9608" class="Symbol">(</a><a id="9609" href="Prelude.Preliminaries.html#9609" class="Bound">Y</a> <a id="9611" class="Symbol">:</a> <a id="9613" href="Prelude.Preliminaries.html#9598" class="Bound">X</a> <a id="9615" class="Symbol">→</a> <a id="9617" href="Prelude.Preliminaries.html#9583" class="Bound">𝓥</a> <a id="9619" href="Universes.html#403" class="Function Operator">̇</a> <a id="9621" class="Symbol">)</a> <a id="9623" class="Symbol">→</a> <a id="9625" href="Prelude.Preliminaries.html#9581" class="Bound">𝓤</a> <a id="9627" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9629" href="Prelude.Preliminaries.html#9583" class="Bound">𝓥</a> <a id="9631" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9634" href="Prelude.Preliminaries.html#9575" class="Function">-Σ</a> <a id="9637" href="Prelude.Preliminaries.html#9637" class="Bound">X</a> <a id="9639" href="Prelude.Preliminaries.html#9639" class="Bound">Y</a> <a id="9641" class="Symbol">=</a> <a id="9643" href="Prelude.Preliminaries.html#9139" class="Record">Σ</a> <a id="9645" href="Prelude.Preliminaries.html#9639" class="Bound">Y</a>

 <a id="9649" class="Keyword">syntax</a> <a id="9656" href="Prelude.Preliminaries.html#9575" class="Function">-Σ</a> <a id="9659" class="Bound">X</a> <a id="9661" class="Symbol">(λ</a> <a id="9664" class="Bound">x</a> <a id="9666" class="Symbol">→</a> <a id="9668" class="Bound">Y</a><a id="9669" class="Symbol">)</a> <a id="9671" class="Symbol">=</a> <a id="9673" class="Function">Σ</a> <a id="9675" class="Bound">x</a> <a id="9677" class="Function">꞉</a> <a id="9679" class="Bound">X</a> <a id="9681" class="Function">,</a> <a id="9683" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="10056" href="Prelude.Preliminaries.html#10056" class="Function Operator">_×_</a> <a id="10060" class="Symbol">:</a> <a id="10062" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10064" href="Universes.html#403" class="Function Operator">̇</a> <a id="10066" class="Symbol">→</a> <a id="10068" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10070" href="Universes.html#403" class="Function Operator">̇</a> <a id="10072" class="Symbol">→</a> <a id="10074" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10076" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10078" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10080" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10083" href="Prelude.Preliminaries.html#10083" class="Bound">X</a> <a id="10085" href="Prelude.Preliminaries.html#10056" class="Function Operator">×</a> <a id="10087" href="Prelude.Preliminaries.html#10087" class="Bound">Y</a> <a id="10089" class="Symbol">=</a> <a id="10091" href="Prelude.Preliminaries.html#9575" class="Function">Σ</a> <a id="10093" href="Prelude.Preliminaries.html#10093" class="Bound">x</a> <a id="10095" href="Prelude.Preliminaries.html#9575" class="Function">꞉</a> <a id="10097" href="Prelude.Preliminaries.html#10083" class="Bound">X</a> <a id="10099" href="Prelude.Preliminaries.html#9575" class="Function">,</a> <a id="10101" href="Prelude.Preliminaries.html#10087" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="10311" class="Keyword">open</a> <a id="10316" class="Keyword">import</a> <a id="10323" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="10334" class="Keyword">renaming</a> <a id="10343" class="Symbol">(</a><a id="10344" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="10348" class="Symbol">to</a> <a id="10351" class="Keyword">infixr</a> <a id="10358" class="Number">50</a> <a id="_,_"></a><a id="10361" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">_,_</a><a id="10364" class="Symbol">)</a>
<a id="10366" class="Keyword">open</a> <a id="10371" class="Keyword">import</a> <a id="10378" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="10387" class="Keyword">using</a> <a id="10393" class="Symbol">(</a><a id="10394" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="10397" class="Symbol">;</a> <a id="10399" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="10402" class="Symbol">;</a> <a id="10404" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="10407" class="Symbol">;</a> <a id="10409" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="10411" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, for emphasis or readability we alternate between these and the standard alternatives `fst` and `snd`.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="10824" class="Keyword">module</a> <a id="10831" href="Prelude.Preliminaries.html#10831" class="Module">_</a> <a id="10833" class="Symbol">{</a><a id="10834" href="Prelude.Preliminaries.html#10834" class="Bound">𝓤</a> <a id="10836" class="Symbol">:</a> <a id="10838" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10846" class="Symbol">}</a> <a id="10848" class="Keyword">where</a>

 <a id="10856" href="Prelude.Preliminaries.html#10856" class="Function Operator">∣_∣</a> <a id="10860" href="Prelude.Preliminaries.html#10860" class="Function">fst</a> <a id="10864" class="Symbol">:</a> <a id="10866" class="Symbol">{</a><a id="10867" href="Prelude.Preliminaries.html#10867" class="Bound">X</a> <a id="10869" class="Symbol">:</a> <a id="10871" href="Prelude.Preliminaries.html#10834" class="Bound">𝓤</a> <a id="10873" href="Universes.html#403" class="Function Operator">̇</a> <a id="10875" class="Symbol">}{</a><a id="10877" href="Prelude.Preliminaries.html#10877" class="Bound">Y</a> <a id="10879" class="Symbol">:</a> <a id="10881" href="Prelude.Preliminaries.html#10867" class="Bound">X</a> <a id="10883" class="Symbol">→</a> <a id="10885" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10887" href="Universes.html#403" class="Function Operator">̇</a><a id="10888" class="Symbol">}</a> <a id="10890" class="Symbol">→</a> <a id="10892" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10894" href="Prelude.Preliminaries.html#10877" class="Bound">Y</a> <a id="10896" class="Symbol">→</a> <a id="10898" href="Prelude.Preliminaries.html#10867" class="Bound">X</a>
 <a id="10901" href="Prelude.Preliminaries.html#10856" class="Function Operator">∣</a> <a id="10903" href="Prelude.Preliminaries.html#10903" class="Bound">x</a> <a id="10905" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="10907" href="Prelude.Preliminaries.html#10907" class="Bound">y</a> <a id="10909" href="Prelude.Preliminaries.html#10856" class="Function Operator">∣</a> <a id="10911" class="Symbol">=</a> <a id="10913" href="Prelude.Preliminaries.html#10903" class="Bound">x</a>
 <a id="10916" href="Prelude.Preliminaries.html#10860" class="Function">fst</a> <a id="10920" class="Symbol">(</a><a id="10921" href="Prelude.Preliminaries.html#10921" class="Bound">x</a> <a id="10923" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="10925" href="Prelude.Preliminaries.html#10925" class="Bound">y</a><a id="10926" class="Symbol">)</a> <a id="10928" class="Symbol">=</a> <a id="10930" href="Prelude.Preliminaries.html#10921" class="Bound">x</a>

 <a id="10934" href="Prelude.Preliminaries.html#10934" class="Function Operator">∥_∥</a> <a id="10938" href="Prelude.Preliminaries.html#10938" class="Function">snd</a> <a id="10942" class="Symbol">:</a> <a id="10944" class="Symbol">{</a><a id="10945" href="Prelude.Preliminaries.html#10945" class="Bound">X</a> <a id="10947" class="Symbol">:</a> <a id="10949" href="Prelude.Preliminaries.html#10834" class="Bound">𝓤</a> <a id="10951" href="Universes.html#403" class="Function Operator">̇</a> <a id="10953" class="Symbol">}{</a><a id="10955" href="Prelude.Preliminaries.html#10955" class="Bound">Y</a> <a id="10957" class="Symbol">:</a> <a id="10959" href="Prelude.Preliminaries.html#10945" class="Bound">X</a> <a id="10961" class="Symbol">→</a> <a id="10963" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10965" href="Universes.html#403" class="Function Operator">̇</a> <a id="10967" class="Symbol">}</a> <a id="10969" class="Symbol">→</a> <a id="10971" class="Symbol">(</a><a id="10972" href="Prelude.Preliminaries.html#10972" class="Bound">z</a> <a id="10974" class="Symbol">:</a> <a id="10976" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10978" href="Prelude.Preliminaries.html#10955" class="Bound">Y</a><a id="10979" class="Symbol">)</a> <a id="10981" class="Symbol">→</a> <a id="10983" href="Prelude.Preliminaries.html#10955" class="Bound">Y</a> <a id="10985" class="Symbol">(</a><a id="10986" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="10990" href="Prelude.Preliminaries.html#10972" class="Bound">z</a><a id="10991" class="Symbol">)</a>
 <a id="10994" href="Prelude.Preliminaries.html#10934" class="Function Operator">∥</a> <a id="10996" href="Prelude.Preliminaries.html#10996" class="Bound">x</a> <a id="10998" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="11000" href="Prelude.Preliminaries.html#11000" class="Bound">y</a> <a id="11002" href="Prelude.Preliminaries.html#10934" class="Function Operator">∥</a> <a id="11004" class="Symbol">=</a> <a id="11006" href="Prelude.Preliminaries.html#11000" class="Bound">y</a>
 <a id="11009" href="Prelude.Preliminaries.html#10938" class="Function">snd</a> <a id="11013" class="Symbol">(</a><a id="11014" href="Prelude.Preliminaries.html#11014" class="Bound">x</a> <a id="11016" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="11018" href="Prelude.Preliminaries.html#11018" class="Bound">y</a><a id="11019" class="Symbol">)</a> <a id="11021" class="Symbol">=</a> <a id="11023" href="Prelude.Preliminaries.html#11018" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.



#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Prelude.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="11971" class="Keyword">module</a> <a id="hide-pi"></a><a id="11978" href="Prelude.Preliminaries.html#11978" class="Module">hide-pi</a> <a id="11986" class="Symbol">{</a><a id="11987" href="Prelude.Preliminaries.html#11987" class="Bound">𝓤</a> <a id="11989" href="Prelude.Preliminaries.html#11989" class="Bound">𝓦</a> <a id="11991" class="Symbol">:</a> <a id="11993" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12001" class="Symbol">}</a> <a id="12003" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="12011" href="Prelude.Preliminaries.html#12011" class="Function">Π</a> <a id="12013" class="Symbol">:</a> <a id="12015" class="Symbol">{</a><a id="12016" href="Prelude.Preliminaries.html#12016" class="Bound">X</a> <a id="12018" class="Symbol">:</a> <a id="12020" href="Prelude.Preliminaries.html#11987" class="Bound">𝓤</a> <a id="12022" href="Universes.html#403" class="Function Operator">̇</a> <a id="12024" class="Symbol">}</a> <a id="12026" class="Symbol">(</a><a id="12027" href="Prelude.Preliminaries.html#12027" class="Bound">A</a> <a id="12029" class="Symbol">:</a> <a id="12031" href="Prelude.Preliminaries.html#12016" class="Bound">X</a> <a id="12033" class="Symbol">→</a> <a id="12035" href="Prelude.Preliminaries.html#11989" class="Bound">𝓦</a> <a id="12037" href="Universes.html#403" class="Function Operator">̇</a> <a id="12039" class="Symbol">)</a> <a id="12041" class="Symbol">→</a> <a id="12043" href="Prelude.Preliminaries.html#11987" class="Bound">𝓤</a> <a id="12045" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12047" href="Prelude.Preliminaries.html#11989" class="Bound">𝓦</a> <a id="12049" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12052" href="Prelude.Preliminaries.html#12011" class="Function">Π</a> <a id="12054" class="Symbol">{</a><a id="12055" href="Prelude.Preliminaries.html#12055" class="Bound">X</a><a id="12056" class="Symbol">}</a> <a id="12058" href="Prelude.Preliminaries.html#12058" class="Bound">A</a> <a id="12060" class="Symbol">=</a> <a id="12062" class="Symbol">(</a><a id="12063" href="Prelude.Preliminaries.html#12063" class="Bound">x</a> <a id="12065" class="Symbol">:</a> <a id="12067" href="Prelude.Preliminaries.html#12055" class="Bound">X</a><a id="12068" class="Symbol">)</a> <a id="12070" class="Symbol">→</a> <a id="12072" href="Prelude.Preliminaries.html#12058" class="Bound">A</a> <a id="12074" href="Prelude.Preliminaries.html#12063" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="12078" href="Prelude.Preliminaries.html#12078" class="Function">-Π</a> <a id="12081" class="Symbol">:</a> <a id="12083" class="Symbol">(</a><a id="12084" href="Prelude.Preliminaries.html#12084" class="Bound">X</a> <a id="12086" class="Symbol">:</a> <a id="12088" href="Prelude.Preliminaries.html#11987" class="Bound">𝓤</a> <a id="12090" href="Universes.html#403" class="Function Operator">̇</a> <a id="12092" class="Symbol">)(</a><a id="12094" href="Prelude.Preliminaries.html#12094" class="Bound">Y</a> <a id="12096" class="Symbol">:</a> <a id="12098" href="Prelude.Preliminaries.html#12084" class="Bound">X</a> <a id="12100" class="Symbol">→</a> <a id="12102" href="Prelude.Preliminaries.html#11989" class="Bound">𝓦</a> <a id="12104" href="Universes.html#403" class="Function Operator">̇</a> <a id="12106" class="Symbol">)</a> <a id="12108" class="Symbol">→</a> <a id="12110" href="Prelude.Preliminaries.html#11987" class="Bound">𝓤</a> <a id="12112" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12114" href="Prelude.Preliminaries.html#11989" class="Bound">𝓦</a> <a id="12116" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12119" href="Prelude.Preliminaries.html#12078" class="Function">-Π</a> <a id="12122" href="Prelude.Preliminaries.html#12122" class="Bound">X</a> <a id="12124" href="Prelude.Preliminaries.html#12124" class="Bound">Y</a> <a id="12126" class="Symbol">=</a> <a id="12128" href="Prelude.Preliminaries.html#12011" class="Function">Π</a> <a id="12130" href="Prelude.Preliminaries.html#12124" class="Bound">Y</a>

 <a id="12134" class="Keyword">infixr</a> <a id="12141" class="Number">-1</a> <a id="12144" href="Prelude.Preliminaries.html#12078" class="Function">-Π</a>
 <a id="12148" class="Keyword">syntax</a> <a id="12155" href="Prelude.Preliminaries.html#12078" class="Function">-Π</a> <a id="12158" class="Bound">A</a> <a id="12160" class="Symbol">(λ</a> <a id="12163" class="Bound">x</a> <a id="12165" class="Symbol">→</a> <a id="12167" class="Bound">b</a><a id="12168" class="Symbol">)</a> <a id="12170" class="Symbol">=</a> <a id="12172" class="Function">Π</a> <a id="12174" class="Bound">x</a> <a id="12176" class="Function">꞉</a> <a id="12178" class="Bound">A</a> <a id="12180" class="Function">,</a> <a id="12182" class="Bound">b</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="12463" class="Keyword">open</a> <a id="12468" class="Keyword">import</a> <a id="12475" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12486" class="Keyword">renaming</a> <a id="12495" class="Symbol">(</a><a id="12496" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="12500" class="Symbol">to</a> <a id="12503" class="Keyword">infixr</a> <a id="12510" class="Number">50</a> <a id="_,_"></a><a id="12513" href="Prelude.Preliminaries.html#12513" class="InductiveConstructor Operator">_,_</a><a id="12516" class="Symbol">)</a> <a id="12518" class="Keyword">public</a>
<a id="12525" class="Keyword">open</a> <a id="12530" class="Keyword">import</a> <a id="12537" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="12546" class="Keyword">using</a> <a id="12552" class="Symbol">(</a><a id="12553" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="12556" class="Symbol">;</a> <a id="12558" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="12561" class="Symbol">;</a> <a id="12563" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="12566" class="Symbol">;</a> <a id="12568" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="12570" class="Symbol">;</a> <a id="12572" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="12573" class="Symbol">)</a> <a id="12575" class="Keyword">public</a>


<a id="12584" class="Keyword">module</a> <a id="12591" href="Prelude.Preliminaries.html#12591" class="Module">_</a> <a id="12593" class="Symbol">{</a><a id="12594" href="Prelude.Preliminaries.html#12594" class="Bound">𝓨</a> <a id="12596" href="Prelude.Preliminaries.html#12596" class="Bound">𝓩</a> <a id="12598" class="Symbol">:</a> <a id="12600" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12608" class="Symbol">}{</a><a id="12610" href="Prelude.Preliminaries.html#12610" class="Bound">I</a> <a id="12612" class="Symbol">:</a> <a id="12614" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12616" href="Universes.html#403" class="Function Operator">̇</a><a id="12617" class="Symbol">}{</a><a id="12619" href="Prelude.Preliminaries.html#12619" class="Bound">B</a> <a id="12621" class="Symbol">:</a> <a id="12623" href="Prelude.Preliminaries.html#12610" class="Bound">I</a> <a id="12625" class="Symbol">→</a> <a id="12627" href="Prelude.Preliminaries.html#12594" class="Bound">𝓨</a> <a id="12629" href="Universes.html#403" class="Function Operator">̇</a><a id="12630" class="Symbol">}{</a><a id="12632" href="Prelude.Preliminaries.html#12632" class="Bound">C</a> <a id="12634" class="Symbol">:</a> <a id="12636" href="Prelude.Preliminaries.html#12610" class="Bound">I</a> <a id="12638" class="Symbol">→</a> <a id="12640" href="Prelude.Preliminaries.html#12596" class="Bound">𝓩</a> <a id="12642" href="Universes.html#403" class="Function Operator">̇</a><a id="12643" class="Symbol">}</a> <a id="12645" class="Keyword">where</a>
 <a id="12652" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="12675" href="Prelude.Preliminaries.html#12675" class="Function">zip</a> <a id="12679" class="Symbol">:</a> <a id="12681" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="12683" href="Prelude.Preliminaries.html#12619" class="Bound">B</a> <a id="12685" class="Symbol">→</a> <a id="12687" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="12689" href="Prelude.Preliminaries.html#12632" class="Bound">C</a> <a id="12691" class="Symbol">→</a> <a id="12693" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="12695" class="Symbol">(λ</a> <a id="12698" href="Prelude.Preliminaries.html#12698" class="Bound">i</a> <a id="12700" class="Symbol">→</a> <a id="12702" class="Symbol">(</a><a id="12703" href="Prelude.Preliminaries.html#12619" class="Bound">B</a> <a id="12705" href="Prelude.Preliminaries.html#12698" class="Bound">i</a><a id="12706" class="Symbol">)</a> <a id="12708" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="12710" class="Symbol">(</a><a id="12711" href="Prelude.Preliminaries.html#12632" class="Bound">C</a> <a id="12713" href="Prelude.Preliminaries.html#12698" class="Bound">i</a><a id="12714" class="Symbol">))</a>
 <a id="12718" href="Prelude.Preliminaries.html#12675" class="Function">zip</a> <a id="12722" href="Prelude.Preliminaries.html#12722" class="Bound">f</a> <a id="12724" href="Prelude.Preliminaries.html#12724" class="Bound">a</a> <a id="12726" class="Symbol">=</a> <a id="12728" class="Symbol">λ</a> <a id="12730" href="Prelude.Preliminaries.html#12730" class="Bound">i</a> <a id="12732" class="Symbol">→</a> <a id="12734" class="Symbol">(</a><a id="12735" href="Prelude.Preliminaries.html#12722" class="Bound">f</a> <a id="12737" href="Prelude.Preliminaries.html#12730" class="Bound">i</a> <a id="12739" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="12741" href="Prelude.Preliminaries.html#12724" class="Bound">a</a> <a id="12743" href="Prelude.Preliminaries.html#12730" class="Bound">i</a><a id="12744" class="Symbol">)</a>

 <a id="12748" href="Prelude.Preliminaries.html#12748" class="Function">eval</a> <a id="12753" class="Symbol">:</a> <a id="12755" class="Symbol">{</a><a id="12756" href="Prelude.Preliminaries.html#12756" class="Bound">Y</a> <a id="12758" class="Symbol">:</a> <a id="12760" href="Prelude.Preliminaries.html#12594" class="Bound">𝓨</a> <a id="12762" href="Universes.html#403" class="Function Operator">̇</a><a id="12763" class="Symbol">}{</a><a id="12765" href="Prelude.Preliminaries.html#12765" class="Bound">Z</a> <a id="12767" class="Symbol">:</a> <a id="12769" href="Prelude.Preliminaries.html#12596" class="Bound">𝓩</a> <a id="12771" href="Universes.html#403" class="Function Operator">̇</a><a id="12772" class="Symbol">}</a> <a id="12774" class="Symbol">→</a> <a id="12776" class="Symbol">((</a><a id="12778" href="Prelude.Preliminaries.html#12756" class="Bound">Y</a> <a id="12780" class="Symbol">→</a> <a id="12782" href="Prelude.Preliminaries.html#12765" class="Bound">Z</a><a id="12783" class="Symbol">)</a> <a id="12785" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="12787" href="Prelude.Preliminaries.html#12756" class="Bound">Y</a><a id="12788" class="Symbol">)</a> <a id="12790" class="Symbol">→</a> <a id="12792" href="Prelude.Preliminaries.html#12765" class="Bound">Z</a>
 <a id="12795" href="Prelude.Preliminaries.html#12748" class="Function">eval</a> <a id="12800" class="Symbol">(</a><a id="12801" href="Prelude.Preliminaries.html#12801" class="Bound">f</a> <a id="12803" href="Prelude.Preliminaries.html#10361" class="InductiveConstructor Operator">,</a> <a id="12805" href="Prelude.Preliminaries.html#12805" class="Bound">a</a><a id="12806" class="Symbol">)</a> <a id="12808" class="Symbol">=</a> <a id="12810" href="Prelude.Preliminaries.html#12801" class="Bound">f</a> <a id="12812" href="Prelude.Preliminaries.html#12805" class="Bound">a</a>

<a id="12815" class="Keyword">module</a> <a id="12822" href="Prelude.Preliminaries.html#12822" class="Module">_</a> <a id="12824" class="Symbol">{</a><a id="12825" href="Prelude.Preliminaries.html#12825" class="Bound">𝓨</a> <a id="12827" class="Symbol">:</a> <a id="12829" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12837" class="Symbol">}{</a><a id="12839" href="Prelude.Preliminaries.html#12839" class="Bound">I</a> <a id="12841" href="Prelude.Preliminaries.html#12841" class="Bound">J</a> <a id="12843" class="Symbol">:</a> <a id="12845" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12847" href="Universes.html#403" class="Function Operator">̇</a><a id="12848" class="Symbol">}{</a><a id="12850" href="Prelude.Preliminaries.html#12850" class="Bound">B</a> <a id="12852" class="Symbol">:</a> <a id="12854" href="Prelude.Preliminaries.html#12839" class="Bound">I</a> <a id="12856" class="Symbol">→</a> <a id="12858" href="Prelude.Preliminaries.html#12825" class="Bound">𝓨</a> <a id="12860" href="Universes.html#403" class="Function Operator">̇</a><a id="12861" class="Symbol">}</a> <a id="12863" class="Keyword">where</a>

 <a id="12871" href="Prelude.Preliminaries.html#12871" class="Function">dapp</a> <a id="12876" class="Symbol">:</a> <a id="12878" class="Symbol">(∀</a> <a id="12881" href="Prelude.Preliminaries.html#12881" class="Bound">i</a> <a id="12883" class="Symbol">→</a> <a id="12885" class="Symbol">(</a><a id="12886" href="Prelude.Preliminaries.html#12841" class="Bound">J</a> <a id="12888" class="Symbol">→</a> <a id="12890" class="Symbol">(</a><a id="12891" href="Prelude.Preliminaries.html#12850" class="Bound">B</a> <a id="12893" href="Prelude.Preliminaries.html#12881" class="Bound">i</a><a id="12894" class="Symbol">))</a> <a id="12897" class="Symbol">→</a> <a id="12899" class="Symbol">(</a><a id="12900" href="Prelude.Preliminaries.html#12850" class="Bound">B</a> <a id="12902" href="Prelude.Preliminaries.html#12881" class="Bound">i</a><a id="12903" class="Symbol">))</a> <a id="12906" class="Symbol">→</a> <a id="12908" class="Symbol">(∀</a> <a id="12911" href="Prelude.Preliminaries.html#12911" class="Bound">i</a> <a id="12913" class="Symbol">→</a> <a id="12915" class="Symbol">(</a><a id="12916" href="Prelude.Preliminaries.html#12841" class="Bound">J</a> <a id="12918" class="Symbol">→</a> <a id="12920" class="Symbol">(</a><a id="12921" href="Prelude.Preliminaries.html#12850" class="Bound">B</a> <a id="12923" href="Prelude.Preliminaries.html#12911" class="Bound">i</a><a id="12924" class="Symbol">)))</a> <a id="12928" class="Symbol">→</a> <a id="12930" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="12932" href="Prelude.Preliminaries.html#12850" class="Bound">B</a>
 <a id="12935" href="Prelude.Preliminaries.html#12871" class="Function">dapp</a> <a id="12940" href="Prelude.Preliminaries.html#12940" class="Bound">f</a> <a id="12942" href="Prelude.Preliminaries.html#12942" class="Bound">a</a> <a id="12944" class="Symbol">=</a> <a id="12946" class="Symbol">λ</a> <a id="12948" href="Prelude.Preliminaries.html#12948" class="Bound">i</a> <a id="12950" class="Symbol">→</a> <a id="12952" class="Symbol">(</a><a id="12953" href="Prelude.Preliminaries.html#12940" class="Bound">f</a> <a id="12955" href="Prelude.Preliminaries.html#12948" class="Bound">i</a><a id="12956" class="Symbol">)</a> <a id="12958" class="Symbol">(</a><a id="12959" href="Prelude.Preliminaries.html#12942" class="Bound">a</a> <a id="12961" href="Prelude.Preliminaries.html#12948" class="Bound">i</a><a id="12962" class="Symbol">)</a>

</pre>

----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}, which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library, even though we import the latter right after repeating their definitions.  As long as we don't invoke `open hide-refl`, the code inside the `hide-refl` module remains essentially hidden (though Agda *will* type-check this code). It may seem odd to both define things in the hidden module only to immediately import the definition that we actually use, but we do this in an attempt to exhibit all of the types on which the [UALib][] depends, in a clear and self-contained way, while also ensuring that this cannot be misinterpreted as a claim to originality.</span>

<sup>4</sup><span class="footnote" id="fn4">**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].</sup>


<br>
<br>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

<!--

<sup>3</sup><span class="footnote" id="fn3">We have made a concerted effort to avoid duplicating types that are already provided elsewhere, such as the [Type Topology][] library.  We occasionally repeat the definitions of such types for pedagogical purposes, but we almost always import and work with the original definitions in order to make the sources known and to credit the original authors.</span>



The main module of a file must have the same name as the file (without the trailing `.agda` or `.lagda`, of course).  The code inside the main module is not indented. Modules may be declared inside the main module and code inside these submodules must be indented to the same column.  As long as the code is indented, Agda considers it part of the submodule.  To exit the submodule, we return to nonindented code.  So, the general pattern is as follows:

```agda
module main where

a-function-in-the-main-module : {𝓤 : Universe}{A B : 𝓤 ̇} → A → B
a-function-in-the-main-module = λ a → a

module _ {𝓤 : Universe} where

 a-function-inside-an-anonymous-submodule : {A B : 𝓤 ̇} → A → B
 a-function-inside-an-anonymous-submodule = λ a → a

a-function-outside-the-submodule : {A B : 𝓤 ̇} → A → B
a-function-outside-the-submodule a = a
```

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. We tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.
-->
