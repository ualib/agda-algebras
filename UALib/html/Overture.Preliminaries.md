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

The [Agda UALib][] is based on a type theory that is the same or very close to the one on which on which Martín Escardó's [Type Topology][] Agda library is based. We don't discuss [MLTT][] in great detail here because there are already nice and freely available resources covering the theory. (See, for example, the section of [Escardó's notes][] on [A spartan Martin-Löf type theory](\href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda), the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), or the [HoTT Book][].)

The objects and assumptions that form the foundation of [MLTT][] are few.  There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of *type universes* (types of types) and *universe variables* to denote them. Following Escardó, use denote universes in the [UALib][] by upper-case calligraphic letters from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[0](Overture.Preliminaries.html#fn0)</sup>

That's all!  That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundation of [MLTT][] that we take as the starting point of the [Agda UALib][].  The logical semantics come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and predicates are represented by types and the inhabitants of these types are the proofs of the propositions and predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed as we progress.  However, classical axioms such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed anywhere in the library.  In this sense, all theorems and proofs in the [UALib][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such cases, the theory is not [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="4083" class="Symbol">{-#</a> <a id="4087" class="Keyword">OPTIONS</a> <a id="4095" class="Pragma">--without-K</a> <a id="4107" class="Pragma">--exact-split</a> <a id="4121" class="Pragma">--safe</a> <a id="4128" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="5841" class="Keyword">module</a> <a id="5848" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="5871" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Overture.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Overture.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="7681" class="Keyword">open</a> <a id="7686" class="Keyword">import</a> <a id="7693" href="Universes.html" class="Module">Universes</a> <a id="7703" class="Keyword">public</a>

</pre>

Since we use the `public` directive, the `Universes` module will be available to all modules that import the present module ([Overture.Preliminaries][]). This module declares symbols used to denote universes.  As mentioned, we adopt Escardó's convention of denoting universes by capital calligraphic letters, and most of the ones we use are already declared in the `Universes` module; those that are not are declared as follows.

<pre class="Agda">

<a id="8167" class="Keyword">variable</a> <a id="8176" href="Overture.Preliminaries.html#8176" class="Generalizable">𝓞</a> <a id="8178" href="Overture.Preliminaries.html#8178" class="Generalizable">𝓧</a> <a id="8180" href="Overture.Preliminaries.html#8180" class="Generalizable">𝓨</a> <a id="8182" href="Overture.Preliminaries.html#8182" class="Generalizable">𝓩</a> <a id="8184" class="Symbol">:</a> <a id="8186" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

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

The [Type Topology][] library contains a standard definition of the dependent product.
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Overture.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="10672" class="Keyword">module</a> <a id="hide-sigma"></a><a id="10679" href="Overture.Preliminaries.html#10679" class="Module">hide-sigma</a> <a id="10690" class="Keyword">where</a>

 <a id="10698" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="10705" href="Overture.Preliminaries.html#10705" class="Record">Σ</a> <a id="10707" class="Symbol">{</a><a id="10708" href="Overture.Preliminaries.html#10708" class="Bound">𝓤</a> <a id="10710" href="Overture.Preliminaries.html#10710" class="Bound">𝓥</a><a id="10711" class="Symbol">}</a> <a id="10713" class="Symbol">{</a><a id="10714" href="Overture.Preliminaries.html#10714" class="Bound">A</a> <a id="10716" class="Symbol">:</a> <a id="10718" href="Overture.Preliminaries.html#10708" class="Bound">𝓤</a> <a id="10720" href="Universes.html#403" class="Function Operator">̇</a> <a id="10722" class="Symbol">}</a> <a id="10724" class="Symbol">(</a><a id="10725" href="Overture.Preliminaries.html#10725" class="Bound">B</a> <a id="10727" class="Symbol">:</a> <a id="10729" href="Overture.Preliminaries.html#10714" class="Bound">A</a> <a id="10731" class="Symbol">→</a> <a id="10733" href="Overture.Preliminaries.html#10710" class="Bound">𝓥</a> <a id="10735" href="Universes.html#403" class="Function Operator">̇</a> <a id="10737" class="Symbol">)</a> <a id="10739" class="Symbol">:</a> <a id="10741" href="Overture.Preliminaries.html#10708" class="Bound">𝓤</a> <a id="10743" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10745" href="Overture.Preliminaries.html#10710" class="Bound">𝓥</a> <a id="10747" href="Universes.html#403" class="Function Operator">̇</a>  <a id="10750" class="Keyword">where</a>
  <a id="10758" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="10770" href="Overture.Preliminaries.html#10770" class="InductiveConstructor Operator">_,_</a>
  <a id="10776" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="10785" href="Overture.Preliminaries.html#10785" class="Field">pr₁</a> <a id="10789" class="Symbol">:</a> <a id="10791" href="Overture.Preliminaries.html#10714" class="Bound">A</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="10796" href="Overture.Preliminaries.html#10796" class="Field">pr₂</a> <a id="10800" class="Symbol">:</a> <a id="10802" href="Overture.Preliminaries.html#10725" class="Bound">B</a> <a id="10804" href="Overture.Preliminaries.html#10785" class="Field">pr₁</a>

 <a id="10810" class="Keyword">infixr</a> <a id="10817" class="Number">50</a> <a id="10820" href="Overture.Preliminaries.html#10770" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ A , B`, which is more pleasing and more standard than Agda's default syntax, `Σ A (λ x → B)`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="11140" href="Overture.Preliminaries.html#11140" class="Function">-Σ</a> <a id="11143" class="Symbol">:</a> <a id="11145" class="Symbol">{</a><a id="11146" href="Overture.Preliminaries.html#11146" class="Bound">𝓤</a> <a id="11148" href="Overture.Preliminaries.html#11148" class="Bound">𝓥</a> <a id="11150" class="Symbol">:</a> <a id="11152" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="11160" class="Symbol">}</a> <a id="11162" class="Symbol">(</a><a id="11163" href="Overture.Preliminaries.html#11163" class="Bound">A</a> <a id="11165" class="Symbol">:</a> <a id="11167" href="Overture.Preliminaries.html#11146" class="Bound">𝓤</a> <a id="11169" href="Universes.html#403" class="Function Operator">̇</a> <a id="11171" class="Symbol">)</a> <a id="11173" class="Symbol">(</a><a id="11174" href="Overture.Preliminaries.html#11174" class="Bound">B</a> <a id="11176" class="Symbol">:</a> <a id="11178" href="Overture.Preliminaries.html#11163" class="Bound">A</a> <a id="11180" class="Symbol">→</a> <a id="11182" href="Overture.Preliminaries.html#11148" class="Bound">𝓥</a> <a id="11184" href="Universes.html#403" class="Function Operator">̇</a> <a id="11186" class="Symbol">)</a> <a id="11188" class="Symbol">→</a> <a id="11190" href="Overture.Preliminaries.html#11146" class="Bound">𝓤</a> <a id="11192" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11194" href="Overture.Preliminaries.html#11148" class="Bound">𝓥</a> <a id="11196" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11199" href="Overture.Preliminaries.html#11140" class="Function">-Σ</a> <a id="11202" href="Overture.Preliminaries.html#11202" class="Bound">A</a> <a id="11204" href="Overture.Preliminaries.html#11204" class="Bound">B</a> <a id="11206" class="Symbol">=</a> <a id="11208" href="Overture.Preliminaries.html#10705" class="Record">Σ</a> <a id="11210" href="Overture.Preliminaries.html#11204" class="Bound">B</a>

 <a id="11214" class="Keyword">syntax</a> <a id="11221" href="Overture.Preliminaries.html#11140" class="Function">-Σ</a> <a id="11224" class="Bound">A</a> <a id="11226" class="Symbol">(λ</a> <a id="11229" class="Bound">x</a> <a id="11231" class="Symbol">→</a> <a id="11233" class="Bound">B</a><a id="11234" class="Symbol">)</a> <a id="11236" class="Symbol">=</a> <a id="11238" class="Function">Σ</a> <a id="11240" class="Bound">x</a> <a id="11242" class="Function">꞉</a> <a id="11244" class="Bound">A</a> <a id="11246" class="Function">,</a> <a id="11248" class="Bound">B</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="11621" href="Overture.Preliminaries.html#11621" class="Function Operator">_×_</a> <a id="11625" class="Symbol">:</a> <a id="11627" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11629" href="Universes.html#403" class="Function Operator">̇</a> <a id="11631" class="Symbol">→</a> <a id="11633" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11635" href="Universes.html#403" class="Function Operator">̇</a> <a id="11637" class="Symbol">→</a> <a id="11639" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11641" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11643" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11645" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11648" href="Overture.Preliminaries.html#11648" class="Bound">A</a> <a id="11650" href="Overture.Preliminaries.html#11621" class="Function Operator">×</a> <a id="11652" href="Overture.Preliminaries.html#11652" class="Bound">B</a> <a id="11654" class="Symbol">=</a> <a id="11656" href="Overture.Preliminaries.html#11140" class="Function">Σ</a> <a id="11658" href="Overture.Preliminaries.html#11658" class="Bound">x</a> <a id="11660" href="Overture.Preliminaries.html#11140" class="Function">꞉</a> <a id="11662" href="Overture.Preliminaries.html#11648" class="Bound">A</a> <a id="11664" href="Overture.Preliminaries.html#11140" class="Function">,</a> <a id="11666" href="Overture.Preliminaries.html#11652" class="Bound">B</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Overture.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="12268" class="Keyword">module</a> <a id="hide-pi"></a><a id="12275" href="Overture.Preliminaries.html#12275" class="Module">hide-pi</a> <a id="12283" class="Symbol">{</a><a id="12284" href="Overture.Preliminaries.html#12284" class="Bound">𝓤</a> <a id="12286" href="Overture.Preliminaries.html#12286" class="Bound">𝓦</a> <a id="12288" class="Symbol">:</a> <a id="12290" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12298" class="Symbol">}</a> <a id="12300" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="12308" href="Overture.Preliminaries.html#12308" class="Function">Π</a> <a id="12310" class="Symbol">:</a> <a id="12312" class="Symbol">{</a><a id="12313" href="Overture.Preliminaries.html#12313" class="Bound">A</a> <a id="12315" class="Symbol">:</a> <a id="12317" href="Overture.Preliminaries.html#12284" class="Bound">𝓤</a> <a id="12319" href="Universes.html#403" class="Function Operator">̇</a> <a id="12321" class="Symbol">}</a> <a id="12323" class="Symbol">(</a><a id="12324" href="Overture.Preliminaries.html#12324" class="Bound">B</a> <a id="12326" class="Symbol">:</a> <a id="12328" href="Overture.Preliminaries.html#12313" class="Bound">A</a> <a id="12330" class="Symbol">→</a> <a id="12332" href="Overture.Preliminaries.html#12286" class="Bound">𝓦</a> <a id="12334" href="Universes.html#403" class="Function Operator">̇</a> <a id="12336" class="Symbol">)</a> <a id="12338" class="Symbol">→</a> <a id="12340" href="Overture.Preliminaries.html#12284" class="Bound">𝓤</a> <a id="12342" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12344" href="Overture.Preliminaries.html#12286" class="Bound">𝓦</a> <a id="12346" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12349" href="Overture.Preliminaries.html#12308" class="Function">Π</a> <a id="12351" class="Symbol">{</a><a id="12352" href="Overture.Preliminaries.html#12352" class="Bound">A</a><a id="12353" class="Symbol">}</a> <a id="12355" href="Overture.Preliminaries.html#12355" class="Bound">B</a> <a id="12357" class="Symbol">=</a> <a id="12359" class="Symbol">(</a><a id="12360" href="Overture.Preliminaries.html#12360" class="Bound">x</a> <a id="12362" class="Symbol">:</a> <a id="12364" href="Overture.Preliminaries.html#12352" class="Bound">A</a><a id="12365" class="Symbol">)</a> <a id="12367" class="Symbol">→</a> <a id="12369" href="Overture.Preliminaries.html#12355" class="Bound">B</a> <a id="12371" href="Overture.Preliminaries.html#12360" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="12375" href="Overture.Preliminaries.html#12375" class="Function">-Π</a> <a id="12378" class="Symbol">:</a> <a id="12380" class="Symbol">(</a><a id="12381" href="Overture.Preliminaries.html#12381" class="Bound">A</a> <a id="12383" class="Symbol">:</a> <a id="12385" href="Overture.Preliminaries.html#12284" class="Bound">𝓤</a> <a id="12387" href="Universes.html#403" class="Function Operator">̇</a> <a id="12389" class="Symbol">)(</a><a id="12391" href="Overture.Preliminaries.html#12391" class="Bound">B</a> <a id="12393" class="Symbol">:</a> <a id="12395" href="Overture.Preliminaries.html#12381" class="Bound">A</a> <a id="12397" class="Symbol">→</a> <a id="12399" href="Overture.Preliminaries.html#12286" class="Bound">𝓦</a> <a id="12401" href="Universes.html#403" class="Function Operator">̇</a> <a id="12403" class="Symbol">)</a> <a id="12405" class="Symbol">→</a> <a id="12407" href="Overture.Preliminaries.html#12284" class="Bound">𝓤</a> <a id="12409" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12411" href="Overture.Preliminaries.html#12286" class="Bound">𝓦</a> <a id="12413" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12416" href="Overture.Preliminaries.html#12375" class="Function">-Π</a> <a id="12419" href="Overture.Preliminaries.html#12419" class="Bound">A</a> <a id="12421" href="Overture.Preliminaries.html#12421" class="Bound">B</a> <a id="12423" class="Symbol">=</a> <a id="12425" href="Overture.Preliminaries.html#12308" class="Function">Π</a> <a id="12427" href="Overture.Preliminaries.html#12421" class="Bound">B</a>

 <a id="12431" class="Keyword">infixr</a> <a id="12438" class="Number">-1</a> <a id="12441" href="Overture.Preliminaries.html#12375" class="Function">-Π</a>
 <a id="12445" class="Keyword">syntax</a> <a id="12452" href="Overture.Preliminaries.html#12375" class="Function">-Π</a> <a id="12455" class="Bound">A</a> <a id="12457" class="Symbol">(λ</a> <a id="12460" class="Bound">x</a> <a id="12462" class="Symbol">→</a> <a id="12464" class="Bound">B</a><a id="12465" class="Symbol">)</a> <a id="12467" class="Symbol">=</a> <a id="12469" class="Function">Π</a> <a id="12471" class="Bound">x</a> <a id="12473" class="Function">꞉</a> <a id="12475" class="Bound">A</a> <a id="12477" class="Function">,</a> <a id="12479" class="Bound">B</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Overture.Preliminaries][].

<pre class="Agda">

<a id="12970" class="Keyword">open</a> <a id="12975" class="Keyword">import</a> <a id="12982" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12993" class="Keyword">renaming</a> <a id="13002" class="Symbol">(</a><a id="13003" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13007" class="Symbol">to</a> <a id="13010" class="Keyword">infixr</a> <a id="13017" class="Number">50</a> <a id="_,_"></a><a id="13020" href="Overture.Preliminaries.html#13020" class="InductiveConstructor Operator">_,_</a><a id="13023" class="Symbol">)</a> <a id="13025" class="Keyword">public</a>
<a id="13032" class="Keyword">open</a> <a id="13037" class="Keyword">import</a> <a id="13044" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13053" class="Keyword">using</a> <a id="13059" class="Symbol">(</a><a id="13060" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13063" class="Symbol">;</a> <a id="13065" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13068" class="Symbol">;</a> <a id="13070" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13073" class="Symbol">;</a> <a id="13075" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13077" class="Symbol">;</a> <a id="13079" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="13080" class="Symbol">;</a> <a id="13082" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="13084" class="Symbol">)</a> <a id="13086" class="Keyword">public</a>

</pre>

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.


<pre class="Agda">

<a id="13661" class="Keyword">module</a> <a id="13668" href="Overture.Preliminaries.html#13668" class="Module">_</a> <a id="13670" class="Symbol">{</a><a id="13671" href="Overture.Preliminaries.html#13671" class="Bound">𝓤</a> <a id="13673" class="Symbol">:</a> <a id="13675" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13683" class="Symbol">}{</a><a id="13685" href="Overture.Preliminaries.html#13685" class="Bound">A</a> <a id="13687" class="Symbol">:</a> <a id="13689" href="Overture.Preliminaries.html#13671" class="Bound">𝓤</a> <a id="13691" href="Universes.html#403" class="Function Operator">̇</a> <a id="13693" class="Symbol">}{</a><a id="13695" href="Overture.Preliminaries.html#13695" class="Bound">B</a> <a id="13697" class="Symbol">:</a> <a id="13699" href="Overture.Preliminaries.html#13685" class="Bound">A</a> <a id="13701" class="Symbol">→</a> <a id="13703" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13705" href="Universes.html#403" class="Function Operator">̇</a><a id="13706" class="Symbol">}</a> <a id="13708" class="Keyword">where</a>

 <a id="13716" href="Overture.Preliminaries.html#13716" class="Function Operator">∣_∣</a> <a id="13720" href="Overture.Preliminaries.html#13720" class="Function">fst</a> <a id="13724" class="Symbol">:</a> <a id="13726" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13728" href="Overture.Preliminaries.html#13695" class="Bound">B</a> <a id="13730" class="Symbol">→</a> <a id="13732" href="Overture.Preliminaries.html#13685" class="Bound">A</a>
 <a id="13735" href="Overture.Preliminaries.html#13716" class="Function Operator">∣</a> <a id="13737" href="Overture.Preliminaries.html#13737" class="Bound">x</a> <a id="13739" href="Overture.Preliminaries.html#13020" class="InductiveConstructor Operator">,</a> <a id="13741" href="Overture.Preliminaries.html#13741" class="Bound">y</a> <a id="13743" href="Overture.Preliminaries.html#13716" class="Function Operator">∣</a> <a id="13745" class="Symbol">=</a> <a id="13747" href="Overture.Preliminaries.html#13737" class="Bound">x</a>
 <a id="13750" href="Overture.Preliminaries.html#13720" class="Function">fst</a> <a id="13754" class="Symbol">(</a><a id="13755" href="Overture.Preliminaries.html#13755" class="Bound">x</a> <a id="13757" href="Overture.Preliminaries.html#13020" class="InductiveConstructor Operator">,</a> <a id="13759" href="Overture.Preliminaries.html#13759" class="Bound">y</a><a id="13760" class="Symbol">)</a> <a id="13762" class="Symbol">=</a> <a id="13764" href="Overture.Preliminaries.html#13755" class="Bound">x</a>

 <a id="13768" href="Overture.Preliminaries.html#13768" class="Function Operator">∥_∥</a> <a id="13772" href="Overture.Preliminaries.html#13772" class="Function">snd</a> <a id="13776" class="Symbol">:</a> <a id="13778" class="Symbol">(</a><a id="13779" href="Overture.Preliminaries.html#13779" class="Bound">z</a> <a id="13781" class="Symbol">:</a> <a id="13783" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13785" href="Overture.Preliminaries.html#13695" class="Bound">B</a><a id="13786" class="Symbol">)</a> <a id="13788" class="Symbol">→</a> <a id="13790" href="Overture.Preliminaries.html#13695" class="Bound">B</a> <a id="13792" class="Symbol">(</a><a id="13793" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13797" href="Overture.Preliminaries.html#13779" class="Bound">z</a><a id="13798" class="Symbol">)</a>
 <a id="13801" href="Overture.Preliminaries.html#13768" class="Function Operator">∥</a> <a id="13803" href="Overture.Preliminaries.html#13803" class="Bound">x</a> <a id="13805" href="Overture.Preliminaries.html#13020" class="InductiveConstructor Operator">,</a> <a id="13807" href="Overture.Preliminaries.html#13807" class="Bound">y</a> <a id="13809" href="Overture.Preliminaries.html#13768" class="Function Operator">∥</a> <a id="13811" class="Symbol">=</a> <a id="13813" href="Overture.Preliminaries.html#13807" class="Bound">y</a>
 <a id="13816" href="Overture.Preliminaries.html#13772" class="Function">snd</a> <a id="13820" class="Symbol">(</a><a id="13821" href="Overture.Preliminaries.html#13821" class="Bound">x</a> <a id="13823" href="Overture.Preliminaries.html#13020" class="InductiveConstructor Operator">,</a> <a id="13825" href="Overture.Preliminaries.html#13825" class="Bound">y</a><a id="13826" class="Symbol">)</a> <a id="13828" class="Symbol">=</a> <a id="13830" href="Overture.Preliminaries.html#13825" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣\_∣` and `fst`) may be declared on the same line.

----------------------------------------

<sup>0</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe variable because in the [Type Topology][] library `𝓟` denotes a powerset type.</span>

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
