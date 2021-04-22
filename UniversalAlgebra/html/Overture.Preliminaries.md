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

The [Agda UALib][] is based on a type theory that is the same or very close to the one on which on which Martín Escardó's [Type Topology][] Agda library is based. We don't discuss [MLTT][] in great detail here because there are already nice and freely available resources covering the theory. (See, for example, the section of [Escardó's notes][] on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda), the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), or the [HoTT Book][].)

The objects and assumptions that form the foundation of [MLTT][] are few.  There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of *type universes* (types of types) and *universe variables* to denote them. Following Escardó, use denote universes in the [UALib][] by upper-case calligraphic letters from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[0](Overture.Preliminaries.html#fn0)</sup>

That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundation of [MLTT][] that we take as the starting point of the [Agda UALib][].  The logical semantics come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and predicates are represented by types and the inhabitants of these types are the proofs of the propositions and predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed as we progress.  However, classical axioms such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed anywhere in the library.  In this sense, all theorems and proofs in the [UALib][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such cases, the theory is not [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="4064" class="Symbol">{-#</a> <a id="4068" class="Keyword">OPTIONS</a> <a id="4076" class="Pragma">--without-K</a> <a id="4088" class="Pragma">--exact-split</a> <a id="4102" class="Pragma">--safe</a> <a id="4109" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="5822" class="Keyword">module</a> <a id="5829" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="5852" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Overture.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Overture.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="7662" class="Keyword">open</a> <a id="7667" class="Keyword">import</a> <a id="7674" href="Universes.html" class="Module">Universes</a> <a id="7684" class="Keyword">public</a>

</pre>

Since we use the `public` directive, the `Universes` module will be available to all modules that import the present module ([Overture.Preliminaries][]). This module declares symbols used to denote universes.  As mentioned, we adopt Escardó's convention of denoting universes by capital calligraphic letters, and most of the ones we use are already declared in the `Universes` module; those that are not are declared as follows.

<pre class="Agda">

<a id="8148" class="Keyword">variable</a> <a id="8157" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="8159" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="8161" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="8163" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="8165" class="Symbol">:</a> <a id="8167" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

The `Universes` module also provides alternative syntax for the primitive operations on universes that Agda supports.  The ` ̇` operator maps a universe level `𝓤` to the type `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`. The primitive Agda level `lzero` is renamed `𝓤₀`, so `𝓤₀ ̇` is an alias for `Set lzero`. Thus, `𝓤 ̇` is simply an alias for `Set 𝓤`, and we have the typing judgment `Set 𝓤 : Set (lsuc 𝓤)`. Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and [Escardó][]) denote by `𝓤₀ ⁺ ̇`.

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

The dependent product type is defined in the [Type Topology][] library. For pedagogical purposes we repeat this definition here (inside a "hidden module" so that it doesn't conflict with the [Type Topology][] definition that we import and use.)<sup>[3](Overture.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="10650" class="Keyword">module</a> <a id="hide-sigma"></a><a id="10657" href="Overture.Preliminaries.html#10657" class="Module">hide-sigma</a> <a id="10668" class="Keyword">where</a>

 <a id="10676" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="10683" href="Overture.Preliminaries.html#10683" class="Record">Σ</a> <a id="10685" class="Symbol">{</a><a id="10686" href="Overture.Preliminaries.html#10686" class="Bound">𝓤</a> <a id="10688" href="Overture.Preliminaries.html#10688" class="Bound">𝓥</a><a id="10689" class="Symbol">}</a> <a id="10691" class="Symbol">{</a><a id="10692" href="Overture.Preliminaries.html#10692" class="Bound">A</a> <a id="10694" class="Symbol">:</a> <a id="10696" href="Overture.Preliminaries.html#10686" class="Bound">𝓤</a> <a id="10698" href="Universes.html#403" class="Function Operator">̇</a> <a id="10700" class="Symbol">}</a> <a id="10702" class="Symbol">(</a><a id="10703" href="Overture.Preliminaries.html#10703" class="Bound">B</a> <a id="10705" class="Symbol">:</a> <a id="10707" href="Overture.Preliminaries.html#10692" class="Bound">A</a> <a id="10709" class="Symbol">→</a> <a id="10711" href="Overture.Preliminaries.html#10688" class="Bound">𝓥</a> <a id="10713" href="Universes.html#403" class="Function Operator">̇</a> <a id="10715" class="Symbol">)</a> <a id="10717" class="Symbol">:</a> <a id="10719" href="Overture.Preliminaries.html#10686" class="Bound">𝓤</a> <a id="10721" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10723" href="Overture.Preliminaries.html#10688" class="Bound">𝓥</a> <a id="10725" href="Universes.html#403" class="Function Operator">̇</a>  <a id="10728" class="Keyword">where</a>
  <a id="10736" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="10748" href="Overture.Preliminaries.html#10748" class="InductiveConstructor Operator">_,_</a>
  <a id="10754" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="10763" href="Overture.Preliminaries.html#10763" class="Field">pr₁</a> <a id="10767" class="Symbol">:</a> <a id="10769" href="Overture.Preliminaries.html#10692" class="Bound">A</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="10774" href="Overture.Preliminaries.html#10774" class="Field">pr₂</a> <a id="10778" class="Symbol">:</a> <a id="10780" href="Overture.Preliminaries.html#10703" class="Bound">B</a> <a id="10782" href="Overture.Preliminaries.html#10763" class="Field">pr₁</a>

 <a id="10788" class="Keyword">infixr</a> <a id="10795" class="Number">50</a> <a id="10798" href="Overture.Preliminaries.html#10748" class="InductiveConstructor Operator">_,_</a>

</pre>

Agda's default syntax for this type is `Σ A (λ x → B)`, but we prefer the notation `Σ x ꞉ A , B`, which is closer to the syntax in the preceding paragraph and the notation used in the HoTT book~\cite{HoTT}, for example. Fortunately, the [Type Topology][] library makes the preferred notation available with the following type definition and `syntax` declaration.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="11194" href="Overture.Preliminaries.html#11194" class="Function">-Σ</a> <a id="11197" class="Symbol">:</a> <a id="11199" class="Symbol">{</a><a id="11200" href="Overture.Preliminaries.html#11200" class="Bound">𝓤</a> <a id="11202" href="Overture.Preliminaries.html#11202" class="Bound">𝓥</a> <a id="11204" class="Symbol">:</a> <a id="11206" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="11214" class="Symbol">}</a> <a id="11216" class="Symbol">(</a><a id="11217" href="Overture.Preliminaries.html#11217" class="Bound">A</a> <a id="11219" class="Symbol">:</a> <a id="11221" href="Overture.Preliminaries.html#11200" class="Bound">𝓤</a> <a id="11223" href="Universes.html#403" class="Function Operator">̇</a> <a id="11225" class="Symbol">)</a> <a id="11227" class="Symbol">(</a><a id="11228" href="Overture.Preliminaries.html#11228" class="Bound">B</a> <a id="11230" class="Symbol">:</a> <a id="11232" href="Overture.Preliminaries.html#11217" class="Bound">A</a> <a id="11234" class="Symbol">→</a> <a id="11236" href="Overture.Preliminaries.html#11202" class="Bound">𝓥</a> <a id="11238" href="Universes.html#403" class="Function Operator">̇</a> <a id="11240" class="Symbol">)</a> <a id="11242" class="Symbol">→</a> <a id="11244" href="Overture.Preliminaries.html#11200" class="Bound">𝓤</a> <a id="11246" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11248" href="Overture.Preliminaries.html#11202" class="Bound">𝓥</a> <a id="11250" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11253" href="Overture.Preliminaries.html#11194" class="Function">-Σ</a> <a id="11256" href="Overture.Preliminaries.html#11256" class="Bound">A</a> <a id="11258" href="Overture.Preliminaries.html#11258" class="Bound">B</a> <a id="11260" class="Symbol">=</a> <a id="11262" href="Overture.Preliminaries.html#10683" class="Record">Σ</a> <a id="11264" href="Overture.Preliminaries.html#11258" class="Bound">B</a>

 <a id="11268" class="Keyword">syntax</a> <a id="11275" href="Overture.Preliminaries.html#11194" class="Function">-Σ</a> <a id="11278" class="Bound">A</a> <a id="11280" class="Symbol">(λ</a> <a id="11283" class="Bound">x</a> <a id="11285" class="Symbol">→</a> <a id="11287" class="Bound">B</a><a id="11288" class="Symbol">)</a> <a id="11290" class="Symbol">=</a> <a id="11292" class="Function">Σ</a> <a id="11294" class="Bound">x</a> <a id="11296" class="Function">꞉</a> <a id="11298" class="Bound">A</a> <a id="11300" class="Function">,</a> <a id="11302" class="Bound">B</a>

</pre>

**Warning!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="11675" href="Overture.Preliminaries.html#11675" class="Function Operator">_×_</a> <a id="11679" class="Symbol">:</a> <a id="11681" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11683" href="Universes.html#403" class="Function Operator">̇</a> <a id="11685" class="Symbol">→</a> <a id="11687" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11689" href="Universes.html#403" class="Function Operator">̇</a> <a id="11691" class="Symbol">→</a> <a id="11693" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11695" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11697" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11699" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11702" href="Overture.Preliminaries.html#11702" class="Bound">A</a> <a id="11704" href="Overture.Preliminaries.html#11675" class="Function Operator">×</a> <a id="11706" href="Overture.Preliminaries.html#11706" class="Bound">B</a> <a id="11708" class="Symbol">=</a> <a id="11710" href="Overture.Preliminaries.html#11194" class="Function">Σ</a> <a id="11712" href="Overture.Preliminaries.html#11712" class="Bound">x</a> <a id="11714" href="Overture.Preliminaries.html#11194" class="Function">꞉</a> <a id="11716" href="Overture.Preliminaries.html#11702" class="Bound">A</a> <a id="11718" href="Overture.Preliminaries.html#11194" class="Function">,</a> <a id="11720" href="Overture.Preliminaries.html#11706" class="Bound">B</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).

<pre class="Agda">

<a id="12275" class="Keyword">module</a> <a id="hide-pi"></a><a id="12282" href="Overture.Preliminaries.html#12282" class="Module">hide-pi</a> <a id="12290" class="Symbol">{</a><a id="12291" href="Overture.Preliminaries.html#12291" class="Bound">𝓤</a> <a id="12293" href="Overture.Preliminaries.html#12293" class="Bound">𝓦</a> <a id="12295" class="Symbol">:</a> <a id="12297" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12305" class="Symbol">}</a> <a id="12307" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="12315" href="Overture.Preliminaries.html#12315" class="Function">Π</a> <a id="12317" class="Symbol">:</a> <a id="12319" class="Symbol">{</a><a id="12320" href="Overture.Preliminaries.html#12320" class="Bound">A</a> <a id="12322" class="Symbol">:</a> <a id="12324" href="Overture.Preliminaries.html#12291" class="Bound">𝓤</a> <a id="12326" href="Universes.html#403" class="Function Operator">̇</a> <a id="12328" class="Symbol">}</a> <a id="12330" class="Symbol">(</a><a id="12331" href="Overture.Preliminaries.html#12331" class="Bound">B</a> <a id="12333" class="Symbol">:</a> <a id="12335" href="Overture.Preliminaries.html#12320" class="Bound">A</a> <a id="12337" class="Symbol">→</a> <a id="12339" href="Overture.Preliminaries.html#12293" class="Bound">𝓦</a> <a id="12341" href="Universes.html#403" class="Function Operator">̇</a> <a id="12343" class="Symbol">)</a> <a id="12345" class="Symbol">→</a> <a id="12347" href="Overture.Preliminaries.html#12291" class="Bound">𝓤</a> <a id="12349" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12351" href="Overture.Preliminaries.html#12293" class="Bound">𝓦</a> <a id="12353" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12356" href="Overture.Preliminaries.html#12315" class="Function">Π</a> <a id="12358" class="Symbol">{</a><a id="12359" href="Overture.Preliminaries.html#12359" class="Bound">A</a><a id="12360" class="Symbol">}</a> <a id="12362" href="Overture.Preliminaries.html#12362" class="Bound">B</a> <a id="12364" class="Symbol">=</a> <a id="12366" class="Symbol">(</a><a id="12367" href="Overture.Preliminaries.html#12367" class="Bound">x</a> <a id="12369" class="Symbol">:</a> <a id="12371" href="Overture.Preliminaries.html#12359" class="Bound">A</a><a id="12372" class="Symbol">)</a> <a id="12374" class="Symbol">→</a> <a id="12376" href="Overture.Preliminaries.html#12362" class="Bound">B</a> <a id="12378" href="Overture.Preliminaries.html#12367" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="12382" href="Overture.Preliminaries.html#12382" class="Function">-Π</a> <a id="12385" class="Symbol">:</a> <a id="12387" class="Symbol">(</a><a id="12388" href="Overture.Preliminaries.html#12388" class="Bound">A</a> <a id="12390" class="Symbol">:</a> <a id="12392" href="Overture.Preliminaries.html#12291" class="Bound">𝓤</a> <a id="12394" href="Universes.html#403" class="Function Operator">̇</a> <a id="12396" class="Symbol">)(</a><a id="12398" href="Overture.Preliminaries.html#12398" class="Bound">B</a> <a id="12400" class="Symbol">:</a> <a id="12402" href="Overture.Preliminaries.html#12388" class="Bound">A</a> <a id="12404" class="Symbol">→</a> <a id="12406" href="Overture.Preliminaries.html#12293" class="Bound">𝓦</a> <a id="12408" href="Universes.html#403" class="Function Operator">̇</a> <a id="12410" class="Symbol">)</a> <a id="12412" class="Symbol">→</a> <a id="12414" href="Overture.Preliminaries.html#12291" class="Bound">𝓤</a> <a id="12416" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12418" href="Overture.Preliminaries.html#12293" class="Bound">𝓦</a> <a id="12420" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12423" href="Overture.Preliminaries.html#12382" class="Function">-Π</a> <a id="12426" href="Overture.Preliminaries.html#12426" class="Bound">A</a> <a id="12428" href="Overture.Preliminaries.html#12428" class="Bound">B</a> <a id="12430" class="Symbol">=</a> <a id="12432" href="Overture.Preliminaries.html#12315" class="Function">Π</a> <a id="12434" href="Overture.Preliminaries.html#12428" class="Bound">B</a>

 <a id="12438" class="Keyword">infixr</a> <a id="12445" class="Number">-1</a> <a id="12448" href="Overture.Preliminaries.html#12382" class="Function">-Π</a>
 <a id="12452" class="Keyword">syntax</a> <a id="12459" href="Overture.Preliminaries.html#12382" class="Function">-Π</a> <a id="12462" class="Bound">A</a> <a id="12464" class="Symbol">(λ</a> <a id="12467" class="Bound">x</a> <a id="12469" class="Symbol">→</a> <a id="12471" class="Bound">B</a><a id="12472" class="Symbol">)</a> <a id="12474" class="Symbol">=</a> <a id="12476" class="Function">Π</a> <a id="12478" class="Bound">x</a> <a id="12480" class="Function">꞉</a> <a id="12482" class="Bound">A</a> <a id="12484" class="Function">,</a> <a id="12486" class="Bound">B</a>

</pre>

**Warning!** The symbol ꞉ is not the same as :. Type the colon in `Π x ꞉ A , B` as `\:4` in [agda2-mode][].

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Overture.Preliminaries][].

<pre class="Agda">

<a id="13086" class="Keyword">open</a> <a id="13091" class="Keyword">import</a> <a id="13098" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13109" class="Keyword">renaming</a> <a id="13118" class="Symbol">(</a><a id="13119" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13123" class="Symbol">to</a> <a id="13126" class="Keyword">infixr</a> <a id="13133" class="Number">50</a> <a id="_,_"></a><a id="13136" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">_,_</a><a id="13139" class="Symbol">)</a> <a id="13141" class="Keyword">public</a>
<a id="13148" class="Keyword">open</a> <a id="13153" class="Keyword">import</a> <a id="13160" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13169" class="Keyword">using</a> <a id="13175" class="Symbol">(</a><a id="13176" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13179" class="Symbol">;</a> <a id="13181" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13184" class="Symbol">;</a> <a id="13186" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13189" class="Symbol">;</a> <a id="13191" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13193" class="Symbol">;</a> <a id="13195" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="13196" class="Symbol">;</a> <a id="13198" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="13200" class="Symbol">)</a> <a id="13202" class="Keyword">public</a>

</pre>

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.


<pre class="Agda">

<a id="13777" class="Keyword">module</a> <a id="13784" href="Overture.Preliminaries.html#13784" class="Module">_</a> <a id="13786" class="Symbol">{</a><a id="13787" href="Overture.Preliminaries.html#13787" class="Bound">𝓤</a> <a id="13789" class="Symbol">:</a> <a id="13791" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13799" class="Symbol">}{</a><a id="13801" href="Overture.Preliminaries.html#13801" class="Bound">A</a> <a id="13803" class="Symbol">:</a> <a id="13805" href="Overture.Preliminaries.html#13787" class="Bound">𝓤</a> <a id="13807" href="Universes.html#403" class="Function Operator">̇</a> <a id="13809" class="Symbol">}{</a><a id="13811" href="Overture.Preliminaries.html#13811" class="Bound">B</a> <a id="13813" class="Symbol">:</a> <a id="13815" href="Overture.Preliminaries.html#13801" class="Bound">A</a> <a id="13817" class="Symbol">→</a> <a id="13819" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13821" href="Universes.html#403" class="Function Operator">̇</a><a id="13822" class="Symbol">}</a> <a id="13824" class="Keyword">where</a>

 <a id="13832" href="Overture.Preliminaries.html#13832" class="Function Operator">∣_∣</a> <a id="13836" href="Overture.Preliminaries.html#13836" class="Function">fst</a> <a id="13840" class="Symbol">:</a> <a id="13842" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13844" href="Overture.Preliminaries.html#13811" class="Bound">B</a> <a id="13846" class="Symbol">→</a> <a id="13848" href="Overture.Preliminaries.html#13801" class="Bound">A</a>
 <a id="13851" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="13853" href="Overture.Preliminaries.html#13853" class="Bound">x</a> <a id="13855" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a> <a id="13857" href="Overture.Preliminaries.html#13857" class="Bound">y</a> <a id="13859" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="13861" class="Symbol">=</a> <a id="13863" href="Overture.Preliminaries.html#13853" class="Bound">x</a>
 <a id="13866" href="Overture.Preliminaries.html#13836" class="Function">fst</a> <a id="13870" class="Symbol">(</a><a id="13871" href="Overture.Preliminaries.html#13871" class="Bound">x</a> <a id="13873" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a> <a id="13875" href="Overture.Preliminaries.html#13875" class="Bound">y</a><a id="13876" class="Symbol">)</a> <a id="13878" class="Symbol">=</a> <a id="13880" href="Overture.Preliminaries.html#13871" class="Bound">x</a>

 <a id="13884" href="Overture.Preliminaries.html#13884" class="Function Operator">∥_∥</a> <a id="13888" href="Overture.Preliminaries.html#13888" class="Function">snd</a> <a id="13892" class="Symbol">:</a> <a id="13894" class="Symbol">(</a><a id="13895" href="Overture.Preliminaries.html#13895" class="Bound">z</a> <a id="13897" class="Symbol">:</a> <a id="13899" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13901" href="Overture.Preliminaries.html#13811" class="Bound">B</a><a id="13902" class="Symbol">)</a> <a id="13904" class="Symbol">→</a> <a id="13906" href="Overture.Preliminaries.html#13811" class="Bound">B</a> <a id="13908" class="Symbol">(</a><a id="13909" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13913" href="Overture.Preliminaries.html#13895" class="Bound">z</a><a id="13914" class="Symbol">)</a>
 <a id="13917" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="13919" href="Overture.Preliminaries.html#13919" class="Bound">x</a> <a id="13921" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a> <a id="13923" href="Overture.Preliminaries.html#13923" class="Bound">y</a> <a id="13925" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="13927" class="Symbol">=</a> <a id="13929" href="Overture.Preliminaries.html#13923" class="Bound">y</a>
 <a id="13932" href="Overture.Preliminaries.html#13888" class="Function">snd</a> <a id="13936" class="Symbol">(</a><a id="13937" href="Overture.Preliminaries.html#13937" class="Bound">x</a> <a id="13939" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a> <a id="13941" href="Overture.Preliminaries.html#13941" class="Bound">y</a><a id="13942" class="Symbol">)</a> <a id="13944" class="Symbol">=</a> <a id="13946" href="Overture.Preliminaries.html#13941" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

----------------------------------------

<sup>0</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe variable because in the [Type Topology][] library `𝓟` denotes a powerset type.</span>

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes entitled [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html) which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3"> To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this cannot be misinterpreted as a claim to originality.</span>

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
