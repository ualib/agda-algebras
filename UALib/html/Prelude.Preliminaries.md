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


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Prelude.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="10702" class="Keyword">module</a> <a id="hide-pi"></a><a id="10709" href="Prelude.Preliminaries.html#10709" class="Module">hide-pi</a> <a id="10717" class="Symbol">{</a><a id="10718" href="Prelude.Preliminaries.html#10718" class="Bound">𝓤</a> <a id="10720" href="Prelude.Preliminaries.html#10720" class="Bound">𝓦</a> <a id="10722" class="Symbol">:</a> <a id="10724" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10732" class="Symbol">}</a> <a id="10734" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="10742" href="Prelude.Preliminaries.html#10742" class="Function">Π</a> <a id="10744" class="Symbol">:</a> <a id="10746" class="Symbol">{</a><a id="10747" href="Prelude.Preliminaries.html#10747" class="Bound">X</a> <a id="10749" class="Symbol">:</a> <a id="10751" href="Prelude.Preliminaries.html#10718" class="Bound">𝓤</a> <a id="10753" href="Universes.html#403" class="Function Operator">̇</a> <a id="10755" class="Symbol">}</a> <a id="10757" class="Symbol">(</a><a id="10758" href="Prelude.Preliminaries.html#10758" class="Bound">A</a> <a id="10760" class="Symbol">:</a> <a id="10762" href="Prelude.Preliminaries.html#10747" class="Bound">X</a> <a id="10764" class="Symbol">→</a> <a id="10766" href="Prelude.Preliminaries.html#10720" class="Bound">𝓦</a> <a id="10768" href="Universes.html#403" class="Function Operator">̇</a> <a id="10770" class="Symbol">)</a> <a id="10772" class="Symbol">→</a> <a id="10774" href="Prelude.Preliminaries.html#10718" class="Bound">𝓤</a> <a id="10776" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10778" href="Prelude.Preliminaries.html#10720" class="Bound">𝓦</a> <a id="10780" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10783" href="Prelude.Preliminaries.html#10742" class="Function">Π</a> <a id="10785" class="Symbol">{</a><a id="10786" href="Prelude.Preliminaries.html#10786" class="Bound">X</a><a id="10787" class="Symbol">}</a> <a id="10789" href="Prelude.Preliminaries.html#10789" class="Bound">A</a> <a id="10791" class="Symbol">=</a> <a id="10793" class="Symbol">(</a><a id="10794" href="Prelude.Preliminaries.html#10794" class="Bound">x</a> <a id="10796" class="Symbol">:</a> <a id="10798" href="Prelude.Preliminaries.html#10786" class="Bound">X</a><a id="10799" class="Symbol">)</a> <a id="10801" class="Symbol">→</a> <a id="10803" href="Prelude.Preliminaries.html#10789" class="Bound">A</a> <a id="10805" href="Prelude.Preliminaries.html#10794" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="10809" href="Prelude.Preliminaries.html#10809" class="Function">-Π</a> <a id="10812" class="Symbol">:</a> <a id="10814" class="Symbol">(</a><a id="10815" href="Prelude.Preliminaries.html#10815" class="Bound">X</a> <a id="10817" class="Symbol">:</a> <a id="10819" href="Prelude.Preliminaries.html#10718" class="Bound">𝓤</a> <a id="10821" href="Universes.html#403" class="Function Operator">̇</a> <a id="10823" class="Symbol">)(</a><a id="10825" href="Prelude.Preliminaries.html#10825" class="Bound">Y</a> <a id="10827" class="Symbol">:</a> <a id="10829" href="Prelude.Preliminaries.html#10815" class="Bound">X</a> <a id="10831" class="Symbol">→</a> <a id="10833" href="Prelude.Preliminaries.html#10720" class="Bound">𝓦</a> <a id="10835" href="Universes.html#403" class="Function Operator">̇</a> <a id="10837" class="Symbol">)</a> <a id="10839" class="Symbol">→</a> <a id="10841" href="Prelude.Preliminaries.html#10718" class="Bound">𝓤</a> <a id="10843" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10845" href="Prelude.Preliminaries.html#10720" class="Bound">𝓦</a> <a id="10847" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10850" href="Prelude.Preliminaries.html#10809" class="Function">-Π</a> <a id="10853" href="Prelude.Preliminaries.html#10853" class="Bound">X</a> <a id="10855" href="Prelude.Preliminaries.html#10855" class="Bound">Y</a> <a id="10857" class="Symbol">=</a> <a id="10859" href="Prelude.Preliminaries.html#10742" class="Function">Π</a> <a id="10861" href="Prelude.Preliminaries.html#10855" class="Bound">Y</a>

 <a id="10865" class="Keyword">infixr</a> <a id="10872" class="Number">-1</a> <a id="10875" href="Prelude.Preliminaries.html#10809" class="Function">-Π</a>
 <a id="10879" class="Keyword">syntax</a> <a id="10886" href="Prelude.Preliminaries.html#10809" class="Function">-Π</a> <a id="10889" class="Bound">A</a> <a id="10891" class="Symbol">(λ</a> <a id="10894" class="Bound">x</a> <a id="10896" class="Symbol">→</a> <a id="10898" class="Bound">b</a><a id="10899" class="Symbol">)</a> <a id="10901" class="Symbol">=</a> <a id="10903" class="Function">Π</a> <a id="10905" class="Bound">x</a> <a id="10907" class="Function">꞉</a> <a id="10909" class="Bound">A</a> <a id="10911" class="Function">,</a> <a id="10913" class="Bound">b</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Prelude.Preliminaries][].

<pre class="Agda">

<a id="11403" class="Keyword">open</a> <a id="11408" class="Keyword">import</a> <a id="11415" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="11426" class="Keyword">renaming</a> <a id="11435" class="Symbol">(</a><a id="11436" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="11440" class="Symbol">to</a> <a id="11443" class="Keyword">infixr</a> <a id="11450" class="Number">50</a> <a id="_,_"></a><a id="11453" href="Prelude.Preliminaries.html#11453" class="InductiveConstructor Operator">_,_</a><a id="11456" class="Symbol">)</a> <a id="11458" class="Keyword">public</a>
<a id="11465" class="Keyword">open</a> <a id="11470" class="Keyword">import</a> <a id="11477" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="11486" class="Keyword">using</a> <a id="11492" class="Symbol">(</a><a id="11493" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="11496" class="Symbol">;</a> <a id="11498" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="11501" class="Symbol">;</a> <a id="11503" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="11506" class="Symbol">;</a> <a id="11508" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="11510" class="Symbol">;</a> <a id="11512" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="11513" class="Symbol">;</a> <a id="11515" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="11517" class="Symbol">)</a> <a id="11519" class="Keyword">public</a>

</pre>

##### Notation for the first and second projections

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣\_∣` and `∥\_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="12090" class="Keyword">module</a> <a id="12097" href="Prelude.Preliminaries.html#12097" class="Module">_</a> <a id="12099" class="Symbol">{</a><a id="12100" href="Prelude.Preliminaries.html#12100" class="Bound">𝓤</a> <a id="12102" class="Symbol">:</a> <a id="12104" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12112" class="Symbol">}</a> <a id="12114" class="Keyword">where</a>

 <a id="12122" href="Prelude.Preliminaries.html#12122" class="Function Operator">∣_∣</a> <a id="12126" href="Prelude.Preliminaries.html#12126" class="Function">fst</a> <a id="12130" class="Symbol">:</a> <a id="12132" class="Symbol">{</a><a id="12133" href="Prelude.Preliminaries.html#12133" class="Bound">X</a> <a id="12135" class="Symbol">:</a> <a id="12137" href="Prelude.Preliminaries.html#12100" class="Bound">𝓤</a> <a id="12139" href="Universes.html#403" class="Function Operator">̇</a> <a id="12141" class="Symbol">}{</a><a id="12143" href="Prelude.Preliminaries.html#12143" class="Bound">Y</a> <a id="12145" class="Symbol">:</a> <a id="12147" href="Prelude.Preliminaries.html#12133" class="Bound">X</a> <a id="12149" class="Symbol">→</a> <a id="12151" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12153" href="Universes.html#403" class="Function Operator">̇</a><a id="12154" class="Symbol">}</a> <a id="12156" class="Symbol">→</a> <a id="12158" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12160" href="Prelude.Preliminaries.html#12143" class="Bound">Y</a> <a id="12162" class="Symbol">→</a> <a id="12164" href="Prelude.Preliminaries.html#12133" class="Bound">X</a>
 <a id="12167" href="Prelude.Preliminaries.html#12122" class="Function Operator">∣</a> <a id="12169" href="Prelude.Preliminaries.html#12169" class="Bound">x</a> <a id="12171" href="Prelude.Preliminaries.html#11453" class="InductiveConstructor Operator">,</a> <a id="12173" href="Prelude.Preliminaries.html#12173" class="Bound">y</a> <a id="12175" href="Prelude.Preliminaries.html#12122" class="Function Operator">∣</a> <a id="12177" class="Symbol">=</a> <a id="12179" href="Prelude.Preliminaries.html#12169" class="Bound">x</a>
 <a id="12182" href="Prelude.Preliminaries.html#12126" class="Function">fst</a> <a id="12186" class="Symbol">(</a><a id="12187" href="Prelude.Preliminaries.html#12187" class="Bound">x</a> <a id="12189" href="Prelude.Preliminaries.html#11453" class="InductiveConstructor Operator">,</a> <a id="12191" href="Prelude.Preliminaries.html#12191" class="Bound">y</a><a id="12192" class="Symbol">)</a> <a id="12194" class="Symbol">=</a> <a id="12196" href="Prelude.Preliminaries.html#12187" class="Bound">x</a>

 <a id="12200" href="Prelude.Preliminaries.html#12200" class="Function Operator">∥_∥</a> <a id="12204" href="Prelude.Preliminaries.html#12204" class="Function">snd</a> <a id="12208" class="Symbol">:</a> <a id="12210" class="Symbol">{</a><a id="12211" href="Prelude.Preliminaries.html#12211" class="Bound">X</a> <a id="12213" class="Symbol">:</a> <a id="12215" href="Prelude.Preliminaries.html#12100" class="Bound">𝓤</a> <a id="12217" href="Universes.html#403" class="Function Operator">̇</a> <a id="12219" class="Symbol">}{</a><a id="12221" href="Prelude.Preliminaries.html#12221" class="Bound">Y</a> <a id="12223" class="Symbol">:</a> <a id="12225" href="Prelude.Preliminaries.html#12211" class="Bound">X</a> <a id="12227" class="Symbol">→</a> <a id="12229" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12231" href="Universes.html#403" class="Function Operator">̇</a> <a id="12233" class="Symbol">}</a> <a id="12235" class="Symbol">→</a> <a id="12237" class="Symbol">(</a><a id="12238" href="Prelude.Preliminaries.html#12238" class="Bound">z</a> <a id="12240" class="Symbol">:</a> <a id="12242" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12244" href="Prelude.Preliminaries.html#12221" class="Bound">Y</a><a id="12245" class="Symbol">)</a> <a id="12247" class="Symbol">→</a> <a id="12249" href="Prelude.Preliminaries.html#12221" class="Bound">Y</a> <a id="12251" class="Symbol">(</a><a id="12252" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12256" href="Prelude.Preliminaries.html#12238" class="Bound">z</a><a id="12257" class="Symbol">)</a>
 <a id="12260" href="Prelude.Preliminaries.html#12200" class="Function Operator">∥</a> <a id="12262" href="Prelude.Preliminaries.html#12262" class="Bound">x</a> <a id="12264" href="Prelude.Preliminaries.html#11453" class="InductiveConstructor Operator">,</a> <a id="12266" href="Prelude.Preliminaries.html#12266" class="Bound">y</a> <a id="12268" href="Prelude.Preliminaries.html#12200" class="Function Operator">∥</a> <a id="12270" class="Symbol">=</a> <a id="12272" href="Prelude.Preliminaries.html#12266" class="Bound">y</a>
 <a id="12275" href="Prelude.Preliminaries.html#12204" class="Function">snd</a> <a id="12279" class="Symbol">(</a><a id="12280" href="Prelude.Preliminaries.html#12280" class="Bound">x</a> <a id="12282" href="Prelude.Preliminaries.html#11453" class="InductiveConstructor Operator">,</a> <a id="12284" href="Prelude.Preliminaries.html#12284" class="Bound">y</a><a id="12285" class="Symbol">)</a> <a id="12287" class="Symbol">=</a> <a id="12289" href="Prelude.Preliminaries.html#12284" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.


----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}, which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this is not misinterpreted as a claim to originality.</span>

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
