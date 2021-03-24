---
layout: default
title : Overture.Preliminaries module (The Agda Universal Algebra Library)
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

This is the [Overture.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

For the benefit of readers who are not proficient in Agda or type theory, we briefly describe some of the type theoretic foundations of the [Agda UALib][], as well as the most important basic types and features that are used throughout the library.

The [UALib][] is based on a minimal version of [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) (MLTT) which is the same or very close to the type theory on which Martin Escardo's [Type Topology][] Agda library is based.  We won't go into great detail here because there are already other very nice resources available, such as the section on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda) of the lecture notes by Escardó just mentioned, the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), and the [HoTT Book][].

We begin by noting that only a very small collection of objects is assumed at the jumping-off point for MLTT. We have the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type), and an infinite collection of *type universes* (types of types) and universe variables to denote them.
Like Escardó's, our universe variables are typically upper-case caligraphic letters from the latter half of the English alphabet (e.g., `𝓤`, `𝓥`, `𝓦`, etc.).


#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2636" class="Symbol">{-#</a> <a id="2640" class="Keyword">OPTIONS</a> <a id="2648" class="Pragma">--without-K</a> <a id="2660" class="Pragma">--exact-split</a> <a id="2674" class="Pragma">--safe</a> <a id="2681" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4394" class="Keyword">module</a> <a id="4401" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="4424" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Overture.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Overture.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="6234" class="Keyword">open</a> <a id="6239" class="Keyword">import</a> <a id="6246" href="Universes.html" class="Module">Universes</a> <a id="6256" class="Keyword">public</a>

</pre>

Since we use the `public` directive, the `Universes` module will be available to all modules that import the present module ([Overture.Preliminaries][]).

The `Universes` module includes a number of symbols that we use to denote *universes* in Agda. Following [Escardó][], we denote universes by capital script letters from the latter half of the English alphabet, e.g., `𝓝`, `𝓞`, …, `𝓧`, `𝓨`, `𝓩`, etc. Some of these are already defined in the [Type Topology][] library, but for those that are not, we use deine them with a line like the following.

<pre class="Agda">

<a id="6841" class="Keyword">variable</a> <a id="6850" href="Overture.Preliminaries.html#6850" class="Generalizable">𝓞</a> <a id="6852" class="Symbol">:</a> <a id="6854" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

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
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Overture.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="9356" class="Keyword">module</a> <a id="hide-sigma"></a><a id="9363" href="Overture.Preliminaries.html#9363" class="Module">hide-sigma</a> <a id="9374" class="Keyword">where</a>

 <a id="9382" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="9389" href="Overture.Preliminaries.html#9389" class="Record">Σ</a> <a id="9391" class="Symbol">{</a><a id="9392" href="Overture.Preliminaries.html#9392" class="Bound">𝓤</a> <a id="9394" href="Overture.Preliminaries.html#9394" class="Bound">𝓥</a><a id="9395" class="Symbol">}</a> <a id="9397" class="Symbol">{</a><a id="9398" href="Overture.Preliminaries.html#9398" class="Bound">A</a> <a id="9400" class="Symbol">:</a> <a id="9402" href="Overture.Preliminaries.html#9392" class="Bound">𝓤</a> <a id="9404" href="Universes.html#403" class="Function Operator">̇</a> <a id="9406" class="Symbol">}</a> <a id="9408" class="Symbol">(</a><a id="9409" href="Overture.Preliminaries.html#9409" class="Bound">B</a> <a id="9411" class="Symbol">:</a> <a id="9413" href="Overture.Preliminaries.html#9398" class="Bound">A</a> <a id="9415" class="Symbol">→</a> <a id="9417" href="Overture.Preliminaries.html#9394" class="Bound">𝓥</a> <a id="9419" href="Universes.html#403" class="Function Operator">̇</a> <a id="9421" class="Symbol">)</a> <a id="9423" class="Symbol">:</a> <a id="9425" href="Overture.Preliminaries.html#9392" class="Bound">𝓤</a> <a id="9427" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9429" href="Overture.Preliminaries.html#9394" class="Bound">𝓥</a> <a id="9431" href="Universes.html#403" class="Function Operator">̇</a>  <a id="9434" class="Keyword">where</a>
  <a id="9442" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="9454" href="Overture.Preliminaries.html#9454" class="InductiveConstructor Operator">_,_</a>
  <a id="9460" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="9469" href="Overture.Preliminaries.html#9469" class="Field">pr₁</a> <a id="9473" class="Symbol">:</a> <a id="9475" href="Overture.Preliminaries.html#9398" class="Bound">A</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="9480" href="Overture.Preliminaries.html#9480" class="Field">pr₂</a> <a id="9484" class="Symbol">:</a> <a id="9486" href="Overture.Preliminaries.html#9409" class="Bound">B</a> <a id="9488" href="Overture.Preliminaries.html#9469" class="Field">pr₁</a>

 <a id="9494" class="Keyword">infixr</a> <a id="9501" class="Number">50</a> <a id="9504" href="Overture.Preliminaries.html#9454" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ A , B`, which is more pleasing and more standard than Agda's default syntax, `Σ A (λ x → B)`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="9824" href="Overture.Preliminaries.html#9824" class="Function">-Σ</a> <a id="9827" class="Symbol">:</a> <a id="9829" class="Symbol">{</a><a id="9830" href="Overture.Preliminaries.html#9830" class="Bound">𝓤</a> <a id="9832" href="Overture.Preliminaries.html#9832" class="Bound">𝓥</a> <a id="9834" class="Symbol">:</a> <a id="9836" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9844" class="Symbol">}</a> <a id="9846" class="Symbol">(</a><a id="9847" href="Overture.Preliminaries.html#9847" class="Bound">A</a> <a id="9849" class="Symbol">:</a> <a id="9851" href="Overture.Preliminaries.html#9830" class="Bound">𝓤</a> <a id="9853" href="Universes.html#403" class="Function Operator">̇</a> <a id="9855" class="Symbol">)</a> <a id="9857" class="Symbol">(</a><a id="9858" href="Overture.Preliminaries.html#9858" class="Bound">B</a> <a id="9860" class="Symbol">:</a> <a id="9862" href="Overture.Preliminaries.html#9847" class="Bound">A</a> <a id="9864" class="Symbol">→</a> <a id="9866" href="Overture.Preliminaries.html#9832" class="Bound">𝓥</a> <a id="9868" href="Universes.html#403" class="Function Operator">̇</a> <a id="9870" class="Symbol">)</a> <a id="9872" class="Symbol">→</a> <a id="9874" href="Overture.Preliminaries.html#9830" class="Bound">𝓤</a> <a id="9876" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9878" href="Overture.Preliminaries.html#9832" class="Bound">𝓥</a> <a id="9880" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9883" href="Overture.Preliminaries.html#9824" class="Function">-Σ</a> <a id="9886" href="Overture.Preliminaries.html#9886" class="Bound">A</a> <a id="9888" href="Overture.Preliminaries.html#9888" class="Bound">B</a> <a id="9890" class="Symbol">=</a> <a id="9892" href="Overture.Preliminaries.html#9389" class="Record">Σ</a> <a id="9894" href="Overture.Preliminaries.html#9888" class="Bound">B</a>

 <a id="9898" class="Keyword">syntax</a> <a id="9905" href="Overture.Preliminaries.html#9824" class="Function">-Σ</a> <a id="9908" class="Bound">A</a> <a id="9910" class="Symbol">(λ</a> <a id="9913" class="Bound">x</a> <a id="9915" class="Symbol">→</a> <a id="9917" class="Bound">B</a><a id="9918" class="Symbol">)</a> <a id="9920" class="Symbol">=</a> <a id="9922" class="Function">Σ</a> <a id="9924" class="Bound">x</a> <a id="9926" class="Function">꞉</a> <a id="9928" class="Bound">A</a> <a id="9930" class="Function">,</a> <a id="9932" class="Bound">B</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="10305" href="Overture.Preliminaries.html#10305" class="Function Operator">_×_</a> <a id="10309" class="Symbol">:</a> <a id="10311" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10313" href="Universes.html#403" class="Function Operator">̇</a> <a id="10315" class="Symbol">→</a> <a id="10317" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10319" href="Universes.html#403" class="Function Operator">̇</a> <a id="10321" class="Symbol">→</a> <a id="10323" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10325" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10327" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10329" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10332" href="Overture.Preliminaries.html#10332" class="Bound">A</a> <a id="10334" href="Overture.Preliminaries.html#10305" class="Function Operator">×</a> <a id="10336" href="Overture.Preliminaries.html#10336" class="Bound">B</a> <a id="10338" class="Symbol">=</a> <a id="10340" href="Overture.Preliminaries.html#9824" class="Function">Σ</a> <a id="10342" href="Overture.Preliminaries.html#10342" class="Bound">x</a> <a id="10344" href="Overture.Preliminaries.html#9824" class="Function">꞉</a> <a id="10346" href="Overture.Preliminaries.html#10332" class="Bound">A</a> <a id="10348" href="Overture.Preliminaries.html#9824" class="Function">,</a> <a id="10350" href="Overture.Preliminaries.html#10336" class="Bound">B</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Overture.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="10952" class="Keyword">module</a> <a id="hide-pi"></a><a id="10959" href="Overture.Preliminaries.html#10959" class="Module">hide-pi</a> <a id="10967" class="Symbol">{</a><a id="10968" href="Overture.Preliminaries.html#10968" class="Bound">𝓤</a> <a id="10970" href="Overture.Preliminaries.html#10970" class="Bound">𝓦</a> <a id="10972" class="Symbol">:</a> <a id="10974" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10982" class="Symbol">}</a> <a id="10984" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="10992" href="Overture.Preliminaries.html#10992" class="Function">Π</a> <a id="10994" class="Symbol">:</a> <a id="10996" class="Symbol">{</a><a id="10997" href="Overture.Preliminaries.html#10997" class="Bound">A</a> <a id="10999" class="Symbol">:</a> <a id="11001" href="Overture.Preliminaries.html#10968" class="Bound">𝓤</a> <a id="11003" href="Universes.html#403" class="Function Operator">̇</a> <a id="11005" class="Symbol">}</a> <a id="11007" class="Symbol">(</a><a id="11008" href="Overture.Preliminaries.html#11008" class="Bound">B</a> <a id="11010" class="Symbol">:</a> <a id="11012" href="Overture.Preliminaries.html#10997" class="Bound">A</a> <a id="11014" class="Symbol">→</a> <a id="11016" href="Overture.Preliminaries.html#10970" class="Bound">𝓦</a> <a id="11018" href="Universes.html#403" class="Function Operator">̇</a> <a id="11020" class="Symbol">)</a> <a id="11022" class="Symbol">→</a> <a id="11024" href="Overture.Preliminaries.html#10968" class="Bound">𝓤</a> <a id="11026" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11028" href="Overture.Preliminaries.html#10970" class="Bound">𝓦</a> <a id="11030" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11033" href="Overture.Preliminaries.html#10992" class="Function">Π</a> <a id="11035" class="Symbol">{</a><a id="11036" href="Overture.Preliminaries.html#11036" class="Bound">A</a><a id="11037" class="Symbol">}</a> <a id="11039" href="Overture.Preliminaries.html#11039" class="Bound">B</a> <a id="11041" class="Symbol">=</a> <a id="11043" class="Symbol">(</a><a id="11044" href="Overture.Preliminaries.html#11044" class="Bound">x</a> <a id="11046" class="Symbol">:</a> <a id="11048" href="Overture.Preliminaries.html#11036" class="Bound">A</a><a id="11049" class="Symbol">)</a> <a id="11051" class="Symbol">→</a> <a id="11053" href="Overture.Preliminaries.html#11039" class="Bound">B</a> <a id="11055" href="Overture.Preliminaries.html#11044" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="11059" href="Overture.Preliminaries.html#11059" class="Function">-Π</a> <a id="11062" class="Symbol">:</a> <a id="11064" class="Symbol">(</a><a id="11065" href="Overture.Preliminaries.html#11065" class="Bound">A</a> <a id="11067" class="Symbol">:</a> <a id="11069" href="Overture.Preliminaries.html#10968" class="Bound">𝓤</a> <a id="11071" href="Universes.html#403" class="Function Operator">̇</a> <a id="11073" class="Symbol">)(</a><a id="11075" href="Overture.Preliminaries.html#11075" class="Bound">B</a> <a id="11077" class="Symbol">:</a> <a id="11079" href="Overture.Preliminaries.html#11065" class="Bound">A</a> <a id="11081" class="Symbol">→</a> <a id="11083" href="Overture.Preliminaries.html#10970" class="Bound">𝓦</a> <a id="11085" href="Universes.html#403" class="Function Operator">̇</a> <a id="11087" class="Symbol">)</a> <a id="11089" class="Symbol">→</a> <a id="11091" href="Overture.Preliminaries.html#10968" class="Bound">𝓤</a> <a id="11093" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11095" href="Overture.Preliminaries.html#10970" class="Bound">𝓦</a> <a id="11097" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11100" href="Overture.Preliminaries.html#11059" class="Function">-Π</a> <a id="11103" href="Overture.Preliminaries.html#11103" class="Bound">A</a> <a id="11105" href="Overture.Preliminaries.html#11105" class="Bound">B</a> <a id="11107" class="Symbol">=</a> <a id="11109" href="Overture.Preliminaries.html#10992" class="Function">Π</a> <a id="11111" href="Overture.Preliminaries.html#11105" class="Bound">B</a>

 <a id="11115" class="Keyword">infixr</a> <a id="11122" class="Number">-1</a> <a id="11125" href="Overture.Preliminaries.html#11059" class="Function">-Π</a>
 <a id="11129" class="Keyword">syntax</a> <a id="11136" href="Overture.Preliminaries.html#11059" class="Function">-Π</a> <a id="11139" class="Bound">A</a> <a id="11141" class="Symbol">(λ</a> <a id="11144" class="Bound">x</a> <a id="11146" class="Symbol">→</a> <a id="11148" class="Bound">B</a><a id="11149" class="Symbol">)</a> <a id="11151" class="Symbol">=</a> <a id="11153" class="Function">Π</a> <a id="11155" class="Bound">x</a> <a id="11157" class="Function">꞉</a> <a id="11159" class="Bound">A</a> <a id="11161" class="Function">,</a> <a id="11163" class="Bound">B</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Overture.Preliminaries][].

<pre class="Agda">

<a id="11654" class="Keyword">open</a> <a id="11659" class="Keyword">import</a> <a id="11666" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="11677" class="Keyword">renaming</a> <a id="11686" class="Symbol">(</a><a id="11687" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="11691" class="Symbol">to</a> <a id="11694" class="Keyword">infixr</a> <a id="11701" class="Number">50</a> <a id="_,_"></a><a id="11704" href="Overture.Preliminaries.html#11704" class="InductiveConstructor Operator">_,_</a><a id="11707" class="Symbol">)</a> <a id="11709" class="Keyword">public</a>
<a id="11716" class="Keyword">open</a> <a id="11721" class="Keyword">import</a> <a id="11728" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="11737" class="Keyword">using</a> <a id="11743" class="Symbol">(</a><a id="11744" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="11747" class="Symbol">;</a> <a id="11749" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="11752" class="Symbol">;</a> <a id="11754" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="11757" class="Symbol">;</a> <a id="11759" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="11761" class="Symbol">;</a> <a id="11763" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="11764" class="Symbol">;</a> <a id="11766" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="11768" class="Symbol">)</a> <a id="11770" class="Keyword">public</a>

</pre>

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.


<pre class="Agda">

<a id="12345" class="Keyword">module</a> <a id="12352" href="Overture.Preliminaries.html#12352" class="Module">_</a> <a id="12354" class="Symbol">{</a><a id="12355" href="Overture.Preliminaries.html#12355" class="Bound">𝓤</a> <a id="12357" class="Symbol">:</a> <a id="12359" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12367" class="Symbol">}{</a><a id="12369" href="Overture.Preliminaries.html#12369" class="Bound">A</a> <a id="12371" class="Symbol">:</a> <a id="12373" href="Overture.Preliminaries.html#12355" class="Bound">𝓤</a> <a id="12375" href="Universes.html#403" class="Function Operator">̇</a> <a id="12377" class="Symbol">}{</a><a id="12379" href="Overture.Preliminaries.html#12379" class="Bound">B</a> <a id="12381" class="Symbol">:</a> <a id="12383" href="Overture.Preliminaries.html#12369" class="Bound">A</a> <a id="12385" class="Symbol">→</a> <a id="12387" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12389" href="Universes.html#403" class="Function Operator">̇</a><a id="12390" class="Symbol">}</a> <a id="12392" class="Keyword">where</a>

 <a id="12400" href="Overture.Preliminaries.html#12400" class="Function Operator">∣_∣</a> <a id="12404" href="Overture.Preliminaries.html#12404" class="Function">fst</a> <a id="12408" class="Symbol">:</a> <a id="12410" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12412" href="Overture.Preliminaries.html#12379" class="Bound">B</a> <a id="12414" class="Symbol">→</a> <a id="12416" href="Overture.Preliminaries.html#12369" class="Bound">A</a>
 <a id="12419" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a> <a id="12421" href="Overture.Preliminaries.html#12421" class="Bound">x</a> <a id="12423" href="Overture.Preliminaries.html#11704" class="InductiveConstructor Operator">,</a> <a id="12425" href="Overture.Preliminaries.html#12425" class="Bound">y</a> <a id="12427" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a> <a id="12429" class="Symbol">=</a> <a id="12431" href="Overture.Preliminaries.html#12421" class="Bound">x</a>
 <a id="12434" href="Overture.Preliminaries.html#12404" class="Function">fst</a> <a id="12438" class="Symbol">(</a><a id="12439" href="Overture.Preliminaries.html#12439" class="Bound">x</a> <a id="12441" href="Overture.Preliminaries.html#11704" class="InductiveConstructor Operator">,</a> <a id="12443" href="Overture.Preliminaries.html#12443" class="Bound">y</a><a id="12444" class="Symbol">)</a> <a id="12446" class="Symbol">=</a> <a id="12448" href="Overture.Preliminaries.html#12439" class="Bound">x</a>

 <a id="12452" href="Overture.Preliminaries.html#12452" class="Function Operator">∥_∥</a> <a id="12456" href="Overture.Preliminaries.html#12456" class="Function">snd</a> <a id="12460" class="Symbol">:</a> <a id="12462" class="Symbol">(</a><a id="12463" href="Overture.Preliminaries.html#12463" class="Bound">z</a> <a id="12465" class="Symbol">:</a> <a id="12467" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12469" href="Overture.Preliminaries.html#12379" class="Bound">B</a><a id="12470" class="Symbol">)</a> <a id="12472" class="Symbol">→</a> <a id="12474" href="Overture.Preliminaries.html#12379" class="Bound">B</a> <a id="12476" class="Symbol">(</a><a id="12477" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12481" href="Overture.Preliminaries.html#12463" class="Bound">z</a><a id="12482" class="Symbol">)</a>
 <a id="12485" href="Overture.Preliminaries.html#12452" class="Function Operator">∥</a> <a id="12487" href="Overture.Preliminaries.html#12487" class="Bound">x</a> <a id="12489" href="Overture.Preliminaries.html#11704" class="InductiveConstructor Operator">,</a> <a id="12491" href="Overture.Preliminaries.html#12491" class="Bound">y</a> <a id="12493" href="Overture.Preliminaries.html#12452" class="Function Operator">∥</a> <a id="12495" class="Symbol">=</a> <a id="12497" href="Overture.Preliminaries.html#12491" class="Bound">y</a>
 <a id="12500" href="Overture.Preliminaries.html#12456" class="Function">snd</a> <a id="12504" class="Symbol">(</a><a id="12505" href="Overture.Preliminaries.html#12505" class="Bound">x</a> <a id="12507" href="Overture.Preliminaries.html#11704" class="InductiveConstructor Operator">,</a> <a id="12509" href="Overture.Preliminaries.html#12509" class="Bound">y</a><a id="12510" class="Symbol">)</a> <a id="12512" class="Symbol">=</a> <a id="12514" href="Overture.Preliminaries.html#12509" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., \AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and \AgdaFunction{fst}) may be declared on the same line.

----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}, which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this is not misinterpreted as a claim to originality.</span>

<sup>4</sup><span class="footnote" id="fn4">**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].</sup>

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Equality →](Overture.Equality.html)</span>


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
