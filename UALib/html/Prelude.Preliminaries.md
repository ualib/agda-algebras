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


#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2634" class="Symbol">{-#</a> <a id="2638" class="Keyword">OPTIONS</a> <a id="2646" class="Pragma">--without-K</a> <a id="2658" class="Pragma">--exact-split</a> <a id="2672" class="Pragma">--safe</a> <a id="2679" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4391" class="Keyword">module</a> <a id="4398" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="4420" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Prelude.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="6228" class="Keyword">open</a> <a id="6233" class="Keyword">import</a> <a id="6240" href="Universes.html" class="Module">Universes</a> <a id="6250" class="Keyword">public</a>

</pre>

Since we use the `public` directive, the `Universes` module will be available to all modules that import the present module ([Prelude.Preliminaries][]).

The `Universes` module includes a number of symbols used to denote *universes* in Agda.
In particular, Following [Escardó][], we refer to universes using capitalized script letters from near the end of the alphabet, e.g., `𝓤`, `𝓥`, `𝓦`, `𝓧`, `𝓨`, `𝓩`, etc. To this list we add one more that we use later to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="6847" class="Keyword">variable</a> <a id="6856" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="6858" class="Symbol">:</a> <a id="6860" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

The `Universes` module also provides elegant notation for the few primitive operations on universes that Agda supports. Specifically, the ` ̇` operator maps a universe level `𝓤` to the type `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The primitive Agda level `lzero` is renamed `𝓤₀`, so `𝓤₀ ̇` is an alias for `Set lzero`. Thus, `𝓤 ̇` is simply an alias for `Set 𝓤`, and we have the typing judgment `Set 𝓤 : Set (lsuc 𝓤)`. Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and [Escardó][]) denote by `𝓤₀ ⁺ ̇`.

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

To justify the introduction of this somewhat nonstandard notation for universe levels, [Escardó][] points out that the Agda library uses `Level` for universes (so what we write as `𝓤 ̇` is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in `𝓤 ̇` need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, `𝓤 ̇` and `𝓥 ̇` . The universe `𝓤 ⊔ 𝓥 ̇` denotes this least upper bound. Here `𝓤 ⊔ 𝓥̇ ` is used to denote the universe level corresponding to the least upper bound of the levels `𝓤` and `𝓥`, where the `_⊔_` is an Agda primitive designed for precisely this purpose.


#### <a id="dependent-pair-type">Sigma types (dependent pairs)</a>

Given universes 𝓤 and 𝓥, a type `A : 𝓤 ̇`, and a type family `B : A → 𝓥 ̇`, the *Sigma type* (or *dependent pair type*), denoted by `Σ(x ꞉ A), B x`, generalizes the Cartesian product `A × B` by allowing the type `B x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ(x ꞉ A), B x` is a pair `(x , y)` such that `x : A` and `y : B x`.

The [Type Topology][] library contains a standard definition of the dependent product.
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Prelude.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="9361" class="Keyword">module</a> <a id="hide-sigma"></a><a id="9368" href="Prelude.Preliminaries.html#9368" class="Module">hide-sigma</a> <a id="9379" class="Keyword">where</a>

 <a id="9387" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="9394" href="Prelude.Preliminaries.html#9394" class="Record">Σ</a> <a id="9396" class="Symbol">{</a><a id="9397" href="Prelude.Preliminaries.html#9397" class="Bound">𝓤</a> <a id="9399" href="Prelude.Preliminaries.html#9399" class="Bound">𝓥</a><a id="9400" class="Symbol">}</a> <a id="9402" class="Symbol">{</a><a id="9403" href="Prelude.Preliminaries.html#9403" class="Bound">A</a> <a id="9405" class="Symbol">:</a> <a id="9407" href="Prelude.Preliminaries.html#9397" class="Bound">𝓤</a> <a id="9409" href="Universes.html#403" class="Function Operator">̇</a> <a id="9411" class="Symbol">}</a> <a id="9413" class="Symbol">(</a><a id="9414" href="Prelude.Preliminaries.html#9414" class="Bound">B</a> <a id="9416" class="Symbol">:</a> <a id="9418" href="Prelude.Preliminaries.html#9403" class="Bound">A</a> <a id="9420" class="Symbol">→</a> <a id="9422" href="Prelude.Preliminaries.html#9399" class="Bound">𝓥</a> <a id="9424" href="Universes.html#403" class="Function Operator">̇</a> <a id="9426" class="Symbol">)</a> <a id="9428" class="Symbol">:</a> <a id="9430" href="Prelude.Preliminaries.html#9397" class="Bound">𝓤</a> <a id="9432" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9434" href="Prelude.Preliminaries.html#9399" class="Bound">𝓥</a> <a id="9436" href="Universes.html#403" class="Function Operator">̇</a>  <a id="9439" class="Keyword">where</a>
  <a id="9447" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="9459" href="Prelude.Preliminaries.html#9459" class="InductiveConstructor Operator">_,_</a>
  <a id="9465" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="9474" href="Prelude.Preliminaries.html#9474" class="Field">pr₁</a> <a id="9478" class="Symbol">:</a> <a id="9480" href="Prelude.Preliminaries.html#9403" class="Bound">A</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="9485" href="Prelude.Preliminaries.html#9485" class="Field">pr₂</a> <a id="9489" class="Symbol">:</a> <a id="9491" href="Prelude.Preliminaries.html#9414" class="Bound">B</a> <a id="9493" href="Prelude.Preliminaries.html#9474" class="Field">pr₁</a>

 <a id="9499" class="Keyword">infixr</a> <a id="9506" class="Number">50</a> <a id="9509" href="Prelude.Preliminaries.html#9459" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ A , B`, which is more pleasing and more standard than Agda's default syntax, `Σ A (λ x → B)`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="9829" href="Prelude.Preliminaries.html#9829" class="Function">-Σ</a> <a id="9832" class="Symbol">:</a> <a id="9834" class="Symbol">{</a><a id="9835" href="Prelude.Preliminaries.html#9835" class="Bound">𝓤</a> <a id="9837" href="Prelude.Preliminaries.html#9837" class="Bound">𝓥</a> <a id="9839" class="Symbol">:</a> <a id="9841" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9849" class="Symbol">}</a> <a id="9851" class="Symbol">(</a><a id="9852" href="Prelude.Preliminaries.html#9852" class="Bound">A</a> <a id="9854" class="Symbol">:</a> <a id="9856" href="Prelude.Preliminaries.html#9835" class="Bound">𝓤</a> <a id="9858" href="Universes.html#403" class="Function Operator">̇</a> <a id="9860" class="Symbol">)</a> <a id="9862" class="Symbol">(</a><a id="9863" href="Prelude.Preliminaries.html#9863" class="Bound">B</a> <a id="9865" class="Symbol">:</a> <a id="9867" href="Prelude.Preliminaries.html#9852" class="Bound">A</a> <a id="9869" class="Symbol">→</a> <a id="9871" href="Prelude.Preliminaries.html#9837" class="Bound">𝓥</a> <a id="9873" href="Universes.html#403" class="Function Operator">̇</a> <a id="9875" class="Symbol">)</a> <a id="9877" class="Symbol">→</a> <a id="9879" href="Prelude.Preliminaries.html#9835" class="Bound">𝓤</a> <a id="9881" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9883" href="Prelude.Preliminaries.html#9837" class="Bound">𝓥</a> <a id="9885" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9888" href="Prelude.Preliminaries.html#9829" class="Function">-Σ</a> <a id="9891" href="Prelude.Preliminaries.html#9891" class="Bound">A</a> <a id="9893" href="Prelude.Preliminaries.html#9893" class="Bound">B</a> <a id="9895" class="Symbol">=</a> <a id="9897" href="Prelude.Preliminaries.html#9394" class="Record">Σ</a> <a id="9899" href="Prelude.Preliminaries.html#9893" class="Bound">B</a>

 <a id="9903" class="Keyword">syntax</a> <a id="9910" href="Prelude.Preliminaries.html#9829" class="Function">-Σ</a> <a id="9913" class="Bound">A</a> <a id="9915" class="Symbol">(λ</a> <a id="9918" class="Bound">x</a> <a id="9920" class="Symbol">→</a> <a id="9922" class="Bound">B</a><a id="9923" class="Symbol">)</a> <a id="9925" class="Symbol">=</a> <a id="9927" class="Function">Σ</a> <a id="9929" class="Bound">x</a> <a id="9931" class="Function">꞉</a> <a id="9933" class="Bound">A</a> <a id="9935" class="Function">,</a> <a id="9937" class="Bound">B</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="10310" href="Prelude.Preliminaries.html#10310" class="Function Operator">_×_</a> <a id="10314" class="Symbol">:</a> <a id="10316" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10318" href="Universes.html#403" class="Function Operator">̇</a> <a id="10320" class="Symbol">→</a> <a id="10322" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10324" href="Universes.html#403" class="Function Operator">̇</a> <a id="10326" class="Symbol">→</a> <a id="10328" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10330" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10332" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10334" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10337" href="Prelude.Preliminaries.html#10337" class="Bound">A</a> <a id="10339" href="Prelude.Preliminaries.html#10310" class="Function Operator">×</a> <a id="10341" href="Prelude.Preliminaries.html#10341" class="Bound">B</a> <a id="10343" class="Symbol">=</a> <a id="10345" href="Prelude.Preliminaries.html#9829" class="Function">Σ</a> <a id="10347" href="Prelude.Preliminaries.html#10347" class="Bound">x</a> <a id="10349" href="Prelude.Preliminaries.html#9829" class="Function">꞉</a> <a id="10351" href="Prelude.Preliminaries.html#10337" class="Bound">A</a> <a id="10353" href="Prelude.Preliminaries.html#9829" class="Function">,</a> <a id="10355" href="Prelude.Preliminaries.html#10341" class="Bound">B</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Prelude.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="10956" class="Keyword">module</a> <a id="hide-pi"></a><a id="10963" href="Prelude.Preliminaries.html#10963" class="Module">hide-pi</a> <a id="10971" class="Symbol">{</a><a id="10972" href="Prelude.Preliminaries.html#10972" class="Bound">𝓤</a> <a id="10974" href="Prelude.Preliminaries.html#10974" class="Bound">𝓦</a> <a id="10976" class="Symbol">:</a> <a id="10978" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10986" class="Symbol">}</a> <a id="10988" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="10996" href="Prelude.Preliminaries.html#10996" class="Function">Π</a> <a id="10998" class="Symbol">:</a> <a id="11000" class="Symbol">{</a><a id="11001" href="Prelude.Preliminaries.html#11001" class="Bound">A</a> <a id="11003" class="Symbol">:</a> <a id="11005" href="Prelude.Preliminaries.html#10972" class="Bound">𝓤</a> <a id="11007" href="Universes.html#403" class="Function Operator">̇</a> <a id="11009" class="Symbol">}</a> <a id="11011" class="Symbol">(</a><a id="11012" href="Prelude.Preliminaries.html#11012" class="Bound">B</a> <a id="11014" class="Symbol">:</a> <a id="11016" href="Prelude.Preliminaries.html#11001" class="Bound">A</a> <a id="11018" class="Symbol">→</a> <a id="11020" href="Prelude.Preliminaries.html#10974" class="Bound">𝓦</a> <a id="11022" href="Universes.html#403" class="Function Operator">̇</a> <a id="11024" class="Symbol">)</a> <a id="11026" class="Symbol">→</a> <a id="11028" href="Prelude.Preliminaries.html#10972" class="Bound">𝓤</a> <a id="11030" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11032" href="Prelude.Preliminaries.html#10974" class="Bound">𝓦</a> <a id="11034" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11037" href="Prelude.Preliminaries.html#10996" class="Function">Π</a> <a id="11039" class="Symbol">{</a><a id="11040" href="Prelude.Preliminaries.html#11040" class="Bound">A</a><a id="11041" class="Symbol">}</a> <a id="11043" href="Prelude.Preliminaries.html#11043" class="Bound">B</a> <a id="11045" class="Symbol">=</a> <a id="11047" class="Symbol">(</a><a id="11048" href="Prelude.Preliminaries.html#11048" class="Bound">x</a> <a id="11050" class="Symbol">:</a> <a id="11052" href="Prelude.Preliminaries.html#11040" class="Bound">A</a><a id="11053" class="Symbol">)</a> <a id="11055" class="Symbol">→</a> <a id="11057" href="Prelude.Preliminaries.html#11043" class="Bound">B</a> <a id="11059" href="Prelude.Preliminaries.html#11048" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="11063" href="Prelude.Preliminaries.html#11063" class="Function">-Π</a> <a id="11066" class="Symbol">:</a> <a id="11068" class="Symbol">(</a><a id="11069" href="Prelude.Preliminaries.html#11069" class="Bound">A</a> <a id="11071" class="Symbol">:</a> <a id="11073" href="Prelude.Preliminaries.html#10972" class="Bound">𝓤</a> <a id="11075" href="Universes.html#403" class="Function Operator">̇</a> <a id="11077" class="Symbol">)(</a><a id="11079" href="Prelude.Preliminaries.html#11079" class="Bound">B</a> <a id="11081" class="Symbol">:</a> <a id="11083" href="Prelude.Preliminaries.html#11069" class="Bound">A</a> <a id="11085" class="Symbol">→</a> <a id="11087" href="Prelude.Preliminaries.html#10974" class="Bound">𝓦</a> <a id="11089" href="Universes.html#403" class="Function Operator">̇</a> <a id="11091" class="Symbol">)</a> <a id="11093" class="Symbol">→</a> <a id="11095" href="Prelude.Preliminaries.html#10972" class="Bound">𝓤</a> <a id="11097" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11099" href="Prelude.Preliminaries.html#10974" class="Bound">𝓦</a> <a id="11101" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11104" href="Prelude.Preliminaries.html#11063" class="Function">-Π</a> <a id="11107" href="Prelude.Preliminaries.html#11107" class="Bound">A</a> <a id="11109" href="Prelude.Preliminaries.html#11109" class="Bound">B</a> <a id="11111" class="Symbol">=</a> <a id="11113" href="Prelude.Preliminaries.html#10996" class="Function">Π</a> <a id="11115" href="Prelude.Preliminaries.html#11109" class="Bound">B</a>

 <a id="11119" class="Keyword">infixr</a> <a id="11126" class="Number">-1</a> <a id="11129" href="Prelude.Preliminaries.html#11063" class="Function">-Π</a>
 <a id="11133" class="Keyword">syntax</a> <a id="11140" href="Prelude.Preliminaries.html#11063" class="Function">-Π</a> <a id="11143" class="Bound">A</a> <a id="11145" class="Symbol">(λ</a> <a id="11148" class="Bound">x</a> <a id="11150" class="Symbol">→</a> <a id="11152" class="Bound">B</a><a id="11153" class="Symbol">)</a> <a id="11155" class="Symbol">=</a> <a id="11157" class="Function">Π</a> <a id="11159" class="Bound">x</a> <a id="11161" class="Function">꞉</a> <a id="11163" class="Bound">A</a> <a id="11165" class="Function">,</a> <a id="11167" class="Bound">B</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Prelude.Preliminaries][].

<pre class="Agda">

<a id="11657" class="Keyword">open</a> <a id="11662" class="Keyword">import</a> <a id="11669" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="11680" class="Keyword">renaming</a> <a id="11689" class="Symbol">(</a><a id="11690" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="11694" class="Symbol">to</a> <a id="11697" class="Keyword">infixr</a> <a id="11704" class="Number">50</a> <a id="_,_"></a><a id="11707" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">_,_</a><a id="11710" class="Symbol">)</a> <a id="11712" class="Keyword">public</a>
<a id="11719" class="Keyword">open</a> <a id="11724" class="Keyword">import</a> <a id="11731" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="11740" class="Keyword">using</a> <a id="11746" class="Symbol">(</a><a id="11747" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="11750" class="Symbol">;</a> <a id="11752" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="11755" class="Symbol">;</a> <a id="11757" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="11760" class="Symbol">;</a> <a id="11762" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="11764" class="Symbol">;</a> <a id="11766" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="11767" class="Symbol">;</a> <a id="11769" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="11771" class="Symbol">)</a> <a id="11773" class="Keyword">public</a>

</pre>

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="12347" class="Keyword">module</a> <a id="12354" href="Prelude.Preliminaries.html#12354" class="Module">_</a> <a id="12356" class="Symbol">{</a><a id="12357" href="Prelude.Preliminaries.html#12357" class="Bound">𝓤</a> <a id="12359" class="Symbol">:</a> <a id="12361" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12369" class="Symbol">}</a> <a id="12371" class="Keyword">where</a>

 <a id="12379" href="Prelude.Preliminaries.html#12379" class="Function Operator">∣_∣</a> <a id="12383" href="Prelude.Preliminaries.html#12383" class="Function">fst</a> <a id="12387" class="Symbol">:</a> <a id="12389" class="Symbol">{</a><a id="12390" href="Prelude.Preliminaries.html#12390" class="Bound">A</a> <a id="12392" class="Symbol">:</a> <a id="12394" href="Prelude.Preliminaries.html#12357" class="Bound">𝓤</a> <a id="12396" href="Universes.html#403" class="Function Operator">̇</a> <a id="12398" class="Symbol">}{</a><a id="12400" href="Prelude.Preliminaries.html#12400" class="Bound">B</a> <a id="12402" class="Symbol">:</a> <a id="12404" href="Prelude.Preliminaries.html#12390" class="Bound">A</a> <a id="12406" class="Symbol">→</a> <a id="12408" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12410" href="Universes.html#403" class="Function Operator">̇</a><a id="12411" class="Symbol">}</a> <a id="12413" class="Symbol">→</a> <a id="12415" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12417" href="Prelude.Preliminaries.html#12400" class="Bound">B</a> <a id="12419" class="Symbol">→</a> <a id="12421" href="Prelude.Preliminaries.html#12390" class="Bound">A</a>
 <a id="12424" href="Prelude.Preliminaries.html#12379" class="Function Operator">∣</a> <a id="12426" href="Prelude.Preliminaries.html#12426" class="Bound">x</a> <a id="12428" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="12430" href="Prelude.Preliminaries.html#12430" class="Bound">y</a> <a id="12432" href="Prelude.Preliminaries.html#12379" class="Function Operator">∣</a> <a id="12434" class="Symbol">=</a> <a id="12436" href="Prelude.Preliminaries.html#12426" class="Bound">x</a>
 <a id="12439" href="Prelude.Preliminaries.html#12383" class="Function">fst</a> <a id="12443" class="Symbol">(</a><a id="12444" href="Prelude.Preliminaries.html#12444" class="Bound">x</a> <a id="12446" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="12448" href="Prelude.Preliminaries.html#12448" class="Bound">y</a><a id="12449" class="Symbol">)</a> <a id="12451" class="Symbol">=</a> <a id="12453" href="Prelude.Preliminaries.html#12444" class="Bound">x</a>

 <a id="12457" href="Prelude.Preliminaries.html#12457" class="Function Operator">∥_∥</a> <a id="12461" href="Prelude.Preliminaries.html#12461" class="Function">snd</a> <a id="12465" class="Symbol">:</a> <a id="12467" class="Symbol">{</a><a id="12468" href="Prelude.Preliminaries.html#12468" class="Bound">A</a> <a id="12470" class="Symbol">:</a> <a id="12472" href="Prelude.Preliminaries.html#12357" class="Bound">𝓤</a> <a id="12474" href="Universes.html#403" class="Function Operator">̇</a> <a id="12476" class="Symbol">}{</a><a id="12478" href="Prelude.Preliminaries.html#12478" class="Bound">B</a> <a id="12480" class="Symbol">:</a> <a id="12482" href="Prelude.Preliminaries.html#12468" class="Bound">A</a> <a id="12484" class="Symbol">→</a> <a id="12486" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12488" href="Universes.html#403" class="Function Operator">̇</a> <a id="12490" class="Symbol">}</a> <a id="12492" class="Symbol">→</a> <a id="12494" class="Symbol">(</a><a id="12495" href="Prelude.Preliminaries.html#12495" class="Bound">z</a> <a id="12497" class="Symbol">:</a> <a id="12499" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12501" href="Prelude.Preliminaries.html#12478" class="Bound">B</a><a id="12502" class="Symbol">)</a> <a id="12504" class="Symbol">→</a> <a id="12506" href="Prelude.Preliminaries.html#12478" class="Bound">B</a> <a id="12508" class="Symbol">(</a><a id="12509" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12513" href="Prelude.Preliminaries.html#12495" class="Bound">z</a><a id="12514" class="Symbol">)</a>
 <a id="12517" href="Prelude.Preliminaries.html#12457" class="Function Operator">∥</a> <a id="12519" href="Prelude.Preliminaries.html#12519" class="Bound">x</a> <a id="12521" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="12523" href="Prelude.Preliminaries.html#12523" class="Bound">y</a> <a id="12525" href="Prelude.Preliminaries.html#12457" class="Function Operator">∥</a> <a id="12527" class="Symbol">=</a> <a id="12529" href="Prelude.Preliminaries.html#12523" class="Bound">y</a>
 <a id="12532" href="Prelude.Preliminaries.html#12461" class="Function">snd</a> <a id="12536" class="Symbol">(</a><a id="12537" href="Prelude.Preliminaries.html#12537" class="Bound">x</a> <a id="12539" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="12541" href="Prelude.Preliminaries.html#12541" class="Bound">y</a><a id="12542" class="Symbol">)</a> <a id="12544" class="Symbol">=</a> <a id="12546" href="Prelude.Preliminaries.html#12541" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.


----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}, which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this is not misinterpreted as a claim to originality.</span>

<sup>4</sup><span class="footnote" id="fn4">**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].</sup>


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
