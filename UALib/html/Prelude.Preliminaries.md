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

This is the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

### <a id="logical-foundations">Logical foundations</a>

For the benefit of readers who are not proficient in Agda or type theory, we briefly describe some of the type theoretic foundations of the [Agda UALib][], as well as the most important basic types and features that are used throughout the library.

The [UALib][] is based on a minimal version of [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) (MLTT) which is the same or very close to the type theory on which \MartinEscardo's \TypeTopology Agda library is based.  We won't go into great detail here because there are already other very nice resources available, such as the section on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda) of the lecture notes by Escardó just mentioned, the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), and the [HoTT Book][].

We begin by recalling the handful of objects that are assumed at the jumping-off point for MLTT: "primitive" types (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type), and an infinite collection of *universes* (types of types) and universe variables to denote them (for which we will use upper-case caligraphic letters like `𝓤`, `𝓥`, `𝓦`, etc., typically from the latter half of the English alphabet, following Escardó's convention).

#### <a id="options">Options</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2505" class="Symbol">{-#</a> <a id="2509" class="Keyword">OPTIONS</a> <a id="2517" class="Pragma">--without-K</a> <a id="2529" class="Pragma">--exact-split</a> <a id="2543" class="Pragma">--safe</a> <a id="2550" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`; we would use the following `OPTIONS` line in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

but this is never done in publicly released versions of the UALib.





#### <a id="modules">Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4383" class="Keyword">module</a> <a id="4390" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="4412" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

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


#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.


<pre class="Agda">

<a id="6623" class="Keyword">open</a> <a id="6628" class="Keyword">import</a> <a id="6635" href="Universes.html" class="Module">Universes</a> <a id="6645" class="Keyword">public</a>

</pre>

Escardó's Universe module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="6910" class="Keyword">variable</a>
 <a id="6920" href="Prelude.Preliminaries.html#6920" class="Generalizable">𝓞</a> <a id="6922" class="Symbol">:</a> <a id="6924" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

The first line must be commented out because we define the given type ourselves for pedagogical purposes, though we will eventually import the original definition from the [Type Topology][] library.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>

<pre class="Agda">

<a id="8217" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="8276" class="Keyword">open</a> <a id="8281" class="Keyword">import</a> <a id="8288" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="8302" class="Keyword">renaming</a> <a id="8311" class="Symbol">(</a><a id="8312" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="8316" class="Symbol">to</a> <a id="8319" class="Keyword">infix</a> <a id="8325" class="Number">0</a> <a id="_≡_"></a><a id="8327" href="Prelude.Preliminaries.html#8327" class="Datatype Operator">_≡_</a><a id="8330" class="Symbol">)</a>

<a id="8333" class="Keyword">open</a> <a id="8338" class="Keyword">import</a> <a id="8345" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="8354" class="Keyword">using</a> <a id="8360" class="Symbol">(</a><a id="8361" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="8364" class="Symbol">;</a> <a id="8366" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="8372" class="Symbol">;</a> <a id="8374" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="8382" class="Symbol">;</a> <a id="8384" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="8393" class="Symbol">;</a> <a id="8395" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="8401" class="Symbol">;</a> <a id="8403" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="8405" class="Symbol">;</a> <a id="8407" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="8435" href="MGS-MLTT.html#956" class="Function">¬</a><a id="8436" class="Symbol">;</a> <a id="8438" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="8440" class="Symbol">;</a> <a id="8442" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="8445" class="Symbol">;</a> <a id="8447" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="8450" class="Symbol">;</a> <a id="8452" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="8453" class="Symbol">;</a> <a id="8455" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="8456" class="Symbol">;</a> <a id="8458" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="8459" class="Symbol">;</a> <a id="8461" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="8464" class="Symbol">;</a> <a id="8466" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="8480" class="Symbol">;</a> <a id="8482" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="8496" class="Symbol">;</a> <a id="8498" href="MGS-MLTT.html#3744" class="Function">id</a><a id="8500" class="Symbol">;</a> <a id="8502" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="8505" class="Symbol">;</a> <a id="8507" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="8509" class="Symbol">)</a>

<a id="8512" class="Keyword">open</a> <a id="8517" class="Keyword">import</a> <a id="8524" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="8541" class="Keyword">using</a> <a id="8547" class="Symbol">(</a><a id="8548" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="8556" class="Symbol">;</a> <a id="8558" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="8565" class="Symbol">;</a> <a id="8567" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="8577" class="Symbol">)</a>

<a id="8580" class="Keyword">open</a> <a id="8585" class="Keyword">import</a> <a id="8592" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="8618" class="Keyword">using</a> <a id="8624" class="Symbol">(</a><a id="8625" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="8631" class="Symbol">;</a> <a id="8633" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="8647" class="Symbol">;</a> <a id="8649" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="8656" class="Symbol">;</a>
 <a id="8659" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8671" class="Symbol">;</a> <a id="8673" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8688" class="Symbol">;</a> <a id="8690" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="8697" class="Symbol">;</a> <a id="8699" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="8709" class="Symbol">;</a> <a id="8711" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="8725" class="Symbol">;</a>
 <a id="8728" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="8759" class="Symbol">;</a> <a id="8761" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="8764" class="Symbol">;</a> <a id="8766" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="8769" class="Symbol">;</a> <a id="8771" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="8788" class="Symbol">;</a> <a id="8790" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="8807" class="Symbol">;</a>
 <a id="8810" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="8859" class="Symbol">)</a>

<a id="8862" class="Keyword">open</a> <a id="8867" class="Keyword">import</a> <a id="8874" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="8887" class="Keyword">renaming</a> <a id="8896" class="Symbol">(</a><a id="8897" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="8901" class="Symbol">to</a> <a id="_∈_"></a><a id="8904" href="Prelude.Preliminaries.html#8904" class="Function Operator">_∈₀_</a><a id="8908" class="Symbol">;</a> <a id="8910" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="8914" class="Symbol">to</a> <a id="_⊆_"></a><a id="8917" href="Prelude.Preliminaries.html#8917" class="Function Operator">_⊆₀_</a><a id="8921" class="Symbol">;</a> <a id="8923" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="8941" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="8944" href="Prelude.Preliminaries.html#8944" class="Function">∈₀-is-subsingleton</a><a id="8962" class="Symbol">)</a>
 <a id="8965" class="Keyword">using</a> <a id="8971" class="Symbol">(</a><a id="8972" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="8973" class="Symbol">;</a> <a id="8975" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="8996" class="Symbol">;</a> <a id="8998" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="9017" class="Symbol">;</a> <a id="9019" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="9041" class="Symbol">;</a> <a id="9043" href="MGS-Powerset.html#382" class="Function">propext</a><a id="9050" class="Symbol">;</a> <a id="9052" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="9058" class="Symbol">;</a> <a id="9060" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="9061" class="Symbol">)</a>

<a id="9064" class="Keyword">open</a> <a id="9069" class="Keyword">import</a> <a id="9076" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="9091" class="Keyword">using</a> <a id="9097" class="Symbol">(</a><a id="9098" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="9101" class="Symbol">;</a> <a id="9103" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="9107" class="Symbol">;</a> <a id="9109" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="9126" class="Symbol">;</a> <a id="9128" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="9140" class="Symbol">;</a> <a id="9142" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="9155" class="Symbol">;</a> <a id="9157" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="9168" class="Symbol">;</a>
 <a id="9171" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="9177" class="Symbol">;</a> <a id="9179" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="9182" class="Symbol">;</a> <a id="9184" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="9211" class="Symbol">;</a> <a id="9213" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="9230" class="Symbol">;</a> <a id="9232" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="9249" class="Symbol">;</a> <a id="9251" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="9266" class="Symbol">)</a>

<a id="9269" class="Keyword">open</a> <a id="9274" class="Keyword">import</a> <a id="9281" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="9302" class="Keyword">using</a> <a id="9308" class="Symbol">(</a><a id="9309" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="9321" class="Symbol">)</a>

<a id="9324" class="Keyword">open</a> <a id="9329" class="Keyword">import</a> <a id="9336" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="9357" class="Keyword">using</a> <a id="9363" class="Symbol">(</a><a id="9364" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="9366" class="Symbol">;</a> <a id="9368" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="9371" class="Symbol">)</a>

<a id="9374" class="Keyword">open</a> <a id="9379" class="Keyword">import</a> <a id="9386" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="9414" class="Keyword">using</a> <a id="9420" class="Symbol">(</a><a id="9421" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="9424" class="Symbol">;</a> <a id="9426" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="9432" class="Symbol">;</a> <a id="9434" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="9455" class="Symbol">;</a>
 <a id="9458" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="9480" class="Symbol">;</a> <a id="9482" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9487" class="Symbol">;</a> <a id="9489" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="9507" class="Symbol">;</a> <a id="9509" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="9516" class="Symbol">)</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.





#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from [Martín Escardó][]'s \href{https://github.com/martinescardo/TypeTopology}{Type Topology} library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

[Escardó][] has an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}. We highly recommend Martín's notes to anyone wanting more details than we provide here about [MLTT][] and the Univalent Foundations/HoTT extensions thereof.

Following [Escardó][], we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module [Escardó][] defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).<sup>[2](Prelude.Preliminaries.html#fn2)</sup>

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





#### <a id="dependent-pair-type">Dependent pair type</a>

Given universes 𝓤 and 𝓥, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the **Sigma type** (or **dependent pair type**), denoted by `Σ(x ꞉ X), Y x`, generalizes the Cartesian product `X × Y` by allowing the type `Y x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, `Σ(x ꞉ X), Y x` is inhabited by the pairs `(x , y)` such that `x : X` and `y : Y x`.

In the [Type Topology][] library, the dependent pair type is defined in a stardard way (cf. the [Agda Standard Library][]) as a record type.

<pre class="Agda">

<a id="13170" class="Keyword">module</a> <a id="hide-sigma"></a><a id="13177" href="Prelude.Preliminaries.html#13177" class="Module">hide-sigma</a> <a id="13188" class="Keyword">where</a>

 <a id="13196" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="13203" href="Prelude.Preliminaries.html#13203" class="Record">Σ</a> <a id="13205" class="Symbol">{</a><a id="13206" href="Prelude.Preliminaries.html#13206" class="Bound">𝓤</a> <a id="13208" href="Prelude.Preliminaries.html#13208" class="Bound">𝓥</a><a id="13209" class="Symbol">}</a> <a id="13211" class="Symbol">{</a><a id="13212" href="Prelude.Preliminaries.html#13212" class="Bound">X</a> <a id="13214" class="Symbol">:</a> <a id="13216" href="Prelude.Preliminaries.html#13206" class="Bound">𝓤</a> <a id="13218" href="Universes.html#403" class="Function Operator">̇</a> <a id="13220" class="Symbol">}</a> <a id="13222" class="Symbol">(</a><a id="13223" href="Prelude.Preliminaries.html#13223" class="Bound">Y</a> <a id="13225" class="Symbol">:</a> <a id="13227" href="Prelude.Preliminaries.html#13212" class="Bound">X</a> <a id="13229" class="Symbol">→</a> <a id="13231" href="Prelude.Preliminaries.html#13208" class="Bound">𝓥</a> <a id="13233" href="Universes.html#403" class="Function Operator">̇</a> <a id="13235" class="Symbol">)</a> <a id="13237" class="Symbol">:</a> <a id="13239" href="Prelude.Preliminaries.html#13206" class="Bound">𝓤</a> <a id="13241" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13243" href="Prelude.Preliminaries.html#13208" class="Bound">𝓥</a> <a id="13245" href="Universes.html#403" class="Function Operator">̇</a>  <a id="13248" class="Keyword">where</a>
  <a id="13256" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="13268" href="Prelude.Preliminaries.html#13268" class="InductiveConstructor Operator">_,_</a>
  <a id="13274" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="13283" href="Prelude.Preliminaries.html#13283" class="Field">pr₁</a> <a id="13287" class="Symbol">:</a> <a id="13289" href="Prelude.Preliminaries.html#13212" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="13294" href="Prelude.Preliminaries.html#13294" class="Field">pr₂</a> <a id="13298" class="Symbol">:</a> <a id="13300" href="Prelude.Preliminaries.html#13223" class="Bound">Y</a> <a id="13302" href="Prelude.Preliminaries.html#13283" class="Field">pr₁</a>

 <a id="13308" class="Keyword">infixr</a> <a id="13315" class="Number">50</a> <a id="13318" href="Prelude.Preliminaries.html#13268" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="13639" href="Prelude.Preliminaries.html#13639" class="Function">-Σ</a> <a id="13642" class="Symbol">:</a> <a id="13644" class="Symbol">{</a><a id="13645" href="Prelude.Preliminaries.html#13645" class="Bound">𝓤</a> <a id="13647" href="Prelude.Preliminaries.html#13647" class="Bound">𝓥</a> <a id="13649" class="Symbol">:</a> <a id="13651" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13659" class="Symbol">}</a> <a id="13661" class="Symbol">(</a><a id="13662" href="Prelude.Preliminaries.html#13662" class="Bound">X</a> <a id="13664" class="Symbol">:</a> <a id="13666" href="Prelude.Preliminaries.html#13645" class="Bound">𝓤</a> <a id="13668" href="Universes.html#403" class="Function Operator">̇</a> <a id="13670" class="Symbol">)</a> <a id="13672" class="Symbol">(</a><a id="13673" href="Prelude.Preliminaries.html#13673" class="Bound">Y</a> <a id="13675" class="Symbol">:</a> <a id="13677" href="Prelude.Preliminaries.html#13662" class="Bound">X</a> <a id="13679" class="Symbol">→</a> <a id="13681" href="Prelude.Preliminaries.html#13647" class="Bound">𝓥</a> <a id="13683" href="Universes.html#403" class="Function Operator">̇</a> <a id="13685" class="Symbol">)</a> <a id="13687" class="Symbol">→</a> <a id="13689" href="Prelude.Preliminaries.html#13645" class="Bound">𝓤</a> <a id="13691" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13693" href="Prelude.Preliminaries.html#13647" class="Bound">𝓥</a> <a id="13695" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="13698" href="Prelude.Preliminaries.html#13639" class="Function">-Σ</a> <a id="13701" href="Prelude.Preliminaries.html#13701" class="Bound">X</a> <a id="13703" href="Prelude.Preliminaries.html#13703" class="Bound">Y</a> <a id="13705" class="Symbol">=</a> <a id="13707" href="Prelude.Preliminaries.html#13203" class="Record">Σ</a> <a id="13709" href="Prelude.Preliminaries.html#13703" class="Bound">Y</a>

 <a id="13713" class="Keyword">syntax</a> <a id="13720" href="Prelude.Preliminaries.html#13639" class="Function">-Σ</a> <a id="13723" class="Bound">X</a> <a id="13725" class="Symbol">(λ</a> <a id="13728" class="Bound">x</a> <a id="13730" class="Symbol">→</a> <a id="13732" class="Bound">Y</a><a id="13733" class="Symbol">)</a> <a id="13735" class="Symbol">=</a> <a id="13737" class="Function">Σ</a> <a id="13739" class="Bound">x</a> <a id="13741" class="Function">꞉</a> <a id="13743" class="Bound">X</a> <a id="13745" class="Function">,</a> <a id="13747" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="14120" href="Prelude.Preliminaries.html#14120" class="Function Operator">_×_</a> <a id="14124" class="Symbol">:</a> <a id="14126" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="14128" href="Universes.html#403" class="Function Operator">̇</a> <a id="14130" class="Symbol">→</a> <a id="14132" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14134" href="Universes.html#403" class="Function Operator">̇</a> <a id="14136" class="Symbol">→</a> <a id="14138" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="14140" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14142" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14144" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14147" href="Prelude.Preliminaries.html#14147" class="Bound">X</a> <a id="14149" href="Prelude.Preliminaries.html#14120" class="Function Operator">×</a> <a id="14151" href="Prelude.Preliminaries.html#14151" class="Bound">Y</a> <a id="14153" class="Symbol">=</a> <a id="14155" href="Prelude.Preliminaries.html#13639" class="Function">Σ</a> <a id="14157" href="Prelude.Preliminaries.html#14157" class="Bound">x</a> <a id="14159" href="Prelude.Preliminaries.html#13639" class="Function">꞉</a> <a id="14161" href="Prelude.Preliminaries.html#14147" class="Bound">X</a> <a id="14163" href="Prelude.Preliminaries.html#13639" class="Function">,</a> <a id="14165" href="Prelude.Preliminaries.html#14151" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="14375" class="Keyword">open</a> <a id="14380" class="Keyword">import</a> <a id="14387" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14398" class="Keyword">renaming</a> <a id="14407" class="Symbol">(</a><a id="14408" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14412" class="Symbol">to</a> <a id="14415" class="Keyword">infixr</a> <a id="14422" class="Number">50</a> <a id="_,_"></a><a id="14425" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">_,_</a><a id="14428" class="Symbol">)</a>
<a id="14430" class="Keyword">open</a> <a id="14435" class="Keyword">import</a> <a id="14442" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14451" class="Keyword">using</a> <a id="14457" class="Symbol">(</a><a id="14458" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14461" class="Symbol">;</a> <a id="14463" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14466" class="Symbol">;</a> <a id="14468" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14471" class="Symbol">;</a> <a id="14473" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14475" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.<sup>[3](Prelude.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="14951" class="Keyword">module</a> <a id="14958" href="Prelude.Preliminaries.html#14958" class="Module">_</a> <a id="14960" class="Symbol">{</a><a id="14961" href="Prelude.Preliminaries.html#14961" class="Bound">𝓤</a> <a id="14963" class="Symbol">:</a> <a id="14965" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14973" class="Symbol">}</a> <a id="14975" class="Keyword">where</a>

 <a id="14983" href="Prelude.Preliminaries.html#14983" class="Function Operator">∣_∣</a> <a id="14987" href="Prelude.Preliminaries.html#14987" class="Function">fst</a> <a id="14991" class="Symbol">:</a> <a id="14993" class="Symbol">{</a><a id="14994" href="Prelude.Preliminaries.html#14994" class="Bound">X</a> <a id="14996" class="Symbol">:</a> <a id="14998" href="Prelude.Preliminaries.html#14961" class="Bound">𝓤</a> <a id="15000" href="Universes.html#403" class="Function Operator">̇</a> <a id="15002" class="Symbol">}{</a><a id="15004" href="Prelude.Preliminaries.html#15004" class="Bound">Y</a> <a id="15006" class="Symbol">:</a> <a id="15008" href="Prelude.Preliminaries.html#14994" class="Bound">X</a> <a id="15010" class="Symbol">→</a> <a id="15012" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="15014" href="Universes.html#403" class="Function Operator">̇</a><a id="15015" class="Symbol">}</a> <a id="15017" class="Symbol">→</a> <a id="15019" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="15021" href="Prelude.Preliminaries.html#15004" class="Bound">Y</a> <a id="15023" class="Symbol">→</a> <a id="15025" href="Prelude.Preliminaries.html#14994" class="Bound">X</a>
 <a id="15028" href="Prelude.Preliminaries.html#14983" class="Function Operator">∣</a> <a id="15030" href="Prelude.Preliminaries.html#15030" class="Bound">x</a> <a id="15032" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="15034" href="Prelude.Preliminaries.html#15034" class="Bound">y</a> <a id="15036" href="Prelude.Preliminaries.html#14983" class="Function Operator">∣</a> <a id="15038" class="Symbol">=</a> <a id="15040" href="Prelude.Preliminaries.html#15030" class="Bound">x</a>
 <a id="15043" href="Prelude.Preliminaries.html#14987" class="Function">fst</a> <a id="15047" class="Symbol">(</a><a id="15048" href="Prelude.Preliminaries.html#15048" class="Bound">x</a> <a id="15050" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="15052" href="Prelude.Preliminaries.html#15052" class="Bound">y</a><a id="15053" class="Symbol">)</a> <a id="15055" class="Symbol">=</a> <a id="15057" href="Prelude.Preliminaries.html#15048" class="Bound">x</a>

 <a id="15061" href="Prelude.Preliminaries.html#15061" class="Function Operator">∥_∥</a> <a id="15065" href="Prelude.Preliminaries.html#15065" class="Function">snd</a> <a id="15069" class="Symbol">:</a> <a id="15071" class="Symbol">{</a><a id="15072" href="Prelude.Preliminaries.html#15072" class="Bound">X</a> <a id="15074" class="Symbol">:</a> <a id="15076" href="Prelude.Preliminaries.html#14961" class="Bound">𝓤</a> <a id="15078" href="Universes.html#403" class="Function Operator">̇</a> <a id="15080" class="Symbol">}{</a><a id="15082" href="Prelude.Preliminaries.html#15082" class="Bound">Y</a> <a id="15084" class="Symbol">:</a> <a id="15086" href="Prelude.Preliminaries.html#15072" class="Bound">X</a> <a id="15088" class="Symbol">→</a> <a id="15090" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="15092" href="Universes.html#403" class="Function Operator">̇</a> <a id="15094" class="Symbol">}</a> <a id="15096" class="Symbol">→</a> <a id="15098" class="Symbol">(</a><a id="15099" href="Prelude.Preliminaries.html#15099" class="Bound">z</a> <a id="15101" class="Symbol">:</a> <a id="15103" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="15105" href="Prelude.Preliminaries.html#15082" class="Bound">Y</a><a id="15106" class="Symbol">)</a> <a id="15108" class="Symbol">→</a> <a id="15110" href="Prelude.Preliminaries.html#15082" class="Bound">Y</a> <a id="15112" class="Symbol">(</a><a id="15113" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="15117" href="Prelude.Preliminaries.html#15099" class="Bound">z</a><a id="15118" class="Symbol">)</a>
 <a id="15121" href="Prelude.Preliminaries.html#15061" class="Function Operator">∥</a> <a id="15123" href="Prelude.Preliminaries.html#15123" class="Bound">x</a> <a id="15125" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="15127" href="Prelude.Preliminaries.html#15127" class="Bound">y</a> <a id="15129" href="Prelude.Preliminaries.html#15061" class="Function Operator">∥</a> <a id="15131" class="Symbol">=</a> <a id="15133" href="Prelude.Preliminaries.html#15127" class="Bound">y</a>
 <a id="15136" href="Prelude.Preliminaries.html#15065" class="Function">snd</a> <a id="15140" class="Symbol">(</a><a id="15141" href="Prelude.Preliminaries.html#15141" class="Bound">x</a> <a id="15143" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="15145" href="Prelude.Preliminaries.html#15145" class="Bound">y</a><a id="15146" class="Symbol">)</a> <a id="15148" class="Symbol">=</a> <a id="15150" href="Prelude.Preliminaries.html#15145" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="15427" class="Keyword">module</a> <a id="hide-pi"></a><a id="15434" href="Prelude.Preliminaries.html#15434" class="Module">hide-pi</a> <a id="15442" class="Symbol">{</a><a id="15443" href="Prelude.Preliminaries.html#15443" class="Bound">𝓤</a> <a id="15445" href="Prelude.Preliminaries.html#15445" class="Bound">𝓦</a> <a id="15447" class="Symbol">:</a> <a id="15449" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="15457" class="Symbol">}</a> <a id="15459" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="15467" href="Prelude.Preliminaries.html#15467" class="Function">Π</a> <a id="15469" class="Symbol">:</a> <a id="15471" class="Symbol">{</a><a id="15472" href="Prelude.Preliminaries.html#15472" class="Bound">X</a> <a id="15474" class="Symbol">:</a> <a id="15476" href="Prelude.Preliminaries.html#15443" class="Bound">𝓤</a> <a id="15478" href="Universes.html#403" class="Function Operator">̇</a> <a id="15480" class="Symbol">}</a> <a id="15482" class="Symbol">(</a><a id="15483" href="Prelude.Preliminaries.html#15483" class="Bound">A</a> <a id="15485" class="Symbol">:</a> <a id="15487" href="Prelude.Preliminaries.html#15472" class="Bound">X</a> <a id="15489" class="Symbol">→</a> <a id="15491" href="Prelude.Preliminaries.html#15445" class="Bound">𝓦</a> <a id="15493" href="Universes.html#403" class="Function Operator">̇</a> <a id="15495" class="Symbol">)</a> <a id="15497" class="Symbol">→</a> <a id="15499" href="Prelude.Preliminaries.html#15443" class="Bound">𝓤</a> <a id="15501" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="15503" href="Prelude.Preliminaries.html#15445" class="Bound">𝓦</a> <a id="15505" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="15508" href="Prelude.Preliminaries.html#15467" class="Function">Π</a> <a id="15510" class="Symbol">{</a><a id="15511" href="Prelude.Preliminaries.html#15511" class="Bound">X</a><a id="15512" class="Symbol">}</a> <a id="15514" href="Prelude.Preliminaries.html#15514" class="Bound">A</a> <a id="15516" class="Symbol">=</a> <a id="15518" class="Symbol">(</a><a id="15519" href="Prelude.Preliminaries.html#15519" class="Bound">x</a> <a id="15521" class="Symbol">:</a> <a id="15523" href="Prelude.Preliminaries.html#15511" class="Bound">X</a><a id="15524" class="Symbol">)</a> <a id="15526" class="Symbol">→</a> <a id="15528" href="Prelude.Preliminaries.html#15514" class="Bound">A</a> <a id="15530" href="Prelude.Preliminaries.html#15519" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="15534" href="Prelude.Preliminaries.html#15534" class="Function">-Π</a> <a id="15537" class="Symbol">:</a> <a id="15539" class="Symbol">(</a><a id="15540" href="Prelude.Preliminaries.html#15540" class="Bound">X</a> <a id="15542" class="Symbol">:</a> <a id="15544" href="Prelude.Preliminaries.html#15443" class="Bound">𝓤</a> <a id="15546" href="Universes.html#403" class="Function Operator">̇</a> <a id="15548" class="Symbol">)(</a><a id="15550" href="Prelude.Preliminaries.html#15550" class="Bound">Y</a> <a id="15552" class="Symbol">:</a> <a id="15554" href="Prelude.Preliminaries.html#15540" class="Bound">X</a> <a id="15556" class="Symbol">→</a> <a id="15558" href="Prelude.Preliminaries.html#15445" class="Bound">𝓦</a> <a id="15560" href="Universes.html#403" class="Function Operator">̇</a> <a id="15562" class="Symbol">)</a> <a id="15564" class="Symbol">→</a> <a id="15566" href="Prelude.Preliminaries.html#15443" class="Bound">𝓤</a> <a id="15568" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="15570" href="Prelude.Preliminaries.html#15445" class="Bound">𝓦</a> <a id="15572" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="15575" href="Prelude.Preliminaries.html#15534" class="Function">-Π</a> <a id="15578" href="Prelude.Preliminaries.html#15578" class="Bound">X</a> <a id="15580" href="Prelude.Preliminaries.html#15580" class="Bound">Y</a> <a id="15582" class="Symbol">=</a> <a id="15584" href="Prelude.Preliminaries.html#15467" class="Function">Π</a> <a id="15586" href="Prelude.Preliminaries.html#15580" class="Bound">Y</a>

 <a id="15590" class="Keyword">infixr</a> <a id="15597" class="Number">-1</a> <a id="15600" href="Prelude.Preliminaries.html#15534" class="Function">-Π</a>
 <a id="15604" class="Keyword">syntax</a> <a id="15611" href="Prelude.Preliminaries.html#15534" class="Function">-Π</a> <a id="15614" class="Bound">A</a> <a id="15616" class="Symbol">(λ</a> <a id="15619" class="Bound">x</a> <a id="15621" class="Symbol">→</a> <a id="15623" class="Bound">b</a><a id="15624" class="Symbol">)</a> <a id="15626" class="Symbol">=</a> <a id="15628" class="Function">Π</a> <a id="15630" class="Bound">x</a> <a id="15632" class="Function">꞉</a> <a id="15634" class="Bound">A</a> <a id="15636" class="Function">,</a> <a id="15638" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="15928" class="Keyword">open</a> <a id="15933" class="Keyword">import</a> <a id="15940" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="15951" class="Keyword">renaming</a> <a id="15960" class="Symbol">(</a><a id="15961" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="15965" class="Symbol">to</a> <a id="15968" class="Keyword">infixr</a> <a id="15975" class="Number">50</a> <a id="_,_"></a><a id="15978" href="Prelude.Preliminaries.html#15978" class="InductiveConstructor Operator">_,_</a><a id="15981" class="Symbol">)</a> <a id="15983" class="Keyword">public</a>
<a id="15990" class="Keyword">open</a> <a id="15995" class="Keyword">import</a> <a id="16002" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="16011" class="Keyword">using</a> <a id="16017" class="Symbol">(</a><a id="16018" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="16021" class="Symbol">;</a> <a id="16023" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="16026" class="Symbol">;</a> <a id="16028" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="16031" class="Symbol">;</a> <a id="16033" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="16035" class="Symbol">;</a> <a id="16037" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="16038" class="Symbol">)</a> <a id="16040" class="Keyword">public</a>


<a id="16049" class="Keyword">module</a> <a id="16056" href="Prelude.Preliminaries.html#16056" class="Module">_</a> <a id="16058" class="Symbol">{</a><a id="16059" href="Prelude.Preliminaries.html#16059" class="Bound">𝓨</a> <a id="16061" href="Prelude.Preliminaries.html#16061" class="Bound">𝓩</a> <a id="16063" class="Symbol">:</a> <a id="16065" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="16073" class="Symbol">}{</a><a id="16075" href="Prelude.Preliminaries.html#16075" class="Bound">I</a> <a id="16077" class="Symbol">:</a> <a id="16079" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="16081" href="Universes.html#403" class="Function Operator">̇</a><a id="16082" class="Symbol">}{</a><a id="16084" href="Prelude.Preliminaries.html#16084" class="Bound">B</a> <a id="16086" class="Symbol">:</a> <a id="16088" href="Prelude.Preliminaries.html#16075" class="Bound">I</a> <a id="16090" class="Symbol">→</a> <a id="16092" href="Prelude.Preliminaries.html#16059" class="Bound">𝓨</a> <a id="16094" href="Universes.html#403" class="Function Operator">̇</a><a id="16095" class="Symbol">}{</a><a id="16097" href="Prelude.Preliminaries.html#16097" class="Bound">C</a> <a id="16099" class="Symbol">:</a> <a id="16101" href="Prelude.Preliminaries.html#16075" class="Bound">I</a> <a id="16103" class="Symbol">→</a> <a id="16105" href="Prelude.Preliminaries.html#16061" class="Bound">𝓩</a> <a id="16107" href="Universes.html#403" class="Function Operator">̇</a><a id="16108" class="Symbol">}</a> <a id="16110" class="Keyword">where</a>
 <a id="16117" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="16140" href="Prelude.Preliminaries.html#16140" class="Function">zip</a> <a id="16144" class="Symbol">:</a> <a id="16146" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="16148" href="Prelude.Preliminaries.html#16084" class="Bound">B</a> <a id="16150" class="Symbol">→</a> <a id="16152" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="16154" href="Prelude.Preliminaries.html#16097" class="Bound">C</a> <a id="16156" class="Symbol">→</a> <a id="16158" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="16160" class="Symbol">(λ</a> <a id="16163" href="Prelude.Preliminaries.html#16163" class="Bound">i</a> <a id="16165" class="Symbol">→</a> <a id="16167" class="Symbol">(</a><a id="16168" href="Prelude.Preliminaries.html#16084" class="Bound">B</a> <a id="16170" href="Prelude.Preliminaries.html#16163" class="Bound">i</a><a id="16171" class="Symbol">)</a> <a id="16173" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="16175" class="Symbol">(</a><a id="16176" href="Prelude.Preliminaries.html#16097" class="Bound">C</a> <a id="16178" href="Prelude.Preliminaries.html#16163" class="Bound">i</a><a id="16179" class="Symbol">))</a>
 <a id="16183" href="Prelude.Preliminaries.html#16140" class="Function">zip</a> <a id="16187" href="Prelude.Preliminaries.html#16187" class="Bound">f</a> <a id="16189" href="Prelude.Preliminaries.html#16189" class="Bound">a</a> <a id="16191" class="Symbol">=</a> <a id="16193" class="Symbol">λ</a> <a id="16195" href="Prelude.Preliminaries.html#16195" class="Bound">i</a> <a id="16197" class="Symbol">→</a> <a id="16199" class="Symbol">(</a><a id="16200" href="Prelude.Preliminaries.html#16187" class="Bound">f</a> <a id="16202" href="Prelude.Preliminaries.html#16195" class="Bound">i</a> <a id="16204" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="16206" href="Prelude.Preliminaries.html#16189" class="Bound">a</a> <a id="16208" href="Prelude.Preliminaries.html#16195" class="Bound">i</a><a id="16209" class="Symbol">)</a>

 <a id="16213" href="Prelude.Preliminaries.html#16213" class="Function">eval</a> <a id="16218" class="Symbol">:</a> <a id="16220" class="Symbol">{</a><a id="16221" href="Prelude.Preliminaries.html#16221" class="Bound">Y</a> <a id="16223" class="Symbol">:</a> <a id="16225" href="Prelude.Preliminaries.html#16059" class="Bound">𝓨</a> <a id="16227" href="Universes.html#403" class="Function Operator">̇</a><a id="16228" class="Symbol">}{</a><a id="16230" href="Prelude.Preliminaries.html#16230" class="Bound">Z</a> <a id="16232" class="Symbol">:</a> <a id="16234" href="Prelude.Preliminaries.html#16061" class="Bound">𝓩</a> <a id="16236" href="Universes.html#403" class="Function Operator">̇</a><a id="16237" class="Symbol">}</a> <a id="16239" class="Symbol">→</a> <a id="16241" class="Symbol">((</a><a id="16243" href="Prelude.Preliminaries.html#16221" class="Bound">Y</a> <a id="16245" class="Symbol">→</a> <a id="16247" href="Prelude.Preliminaries.html#16230" class="Bound">Z</a><a id="16248" class="Symbol">)</a> <a id="16250" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="16252" href="Prelude.Preliminaries.html#16221" class="Bound">Y</a><a id="16253" class="Symbol">)</a> <a id="16255" class="Symbol">→</a> <a id="16257" href="Prelude.Preliminaries.html#16230" class="Bound">Z</a>
 <a id="16260" href="Prelude.Preliminaries.html#16213" class="Function">eval</a> <a id="16265" class="Symbol">(</a><a id="16266" href="Prelude.Preliminaries.html#16266" class="Bound">f</a> <a id="16268" href="Prelude.Preliminaries.html#14425" class="InductiveConstructor Operator">,</a> <a id="16270" href="Prelude.Preliminaries.html#16270" class="Bound">a</a><a id="16271" class="Symbol">)</a> <a id="16273" class="Symbol">=</a> <a id="16275" href="Prelude.Preliminaries.html#16266" class="Bound">f</a> <a id="16277" href="Prelude.Preliminaries.html#16270" class="Bound">a</a>

<a id="16280" class="Keyword">module</a> <a id="16287" href="Prelude.Preliminaries.html#16287" class="Module">_</a> <a id="16289" class="Symbol">{</a><a id="16290" href="Prelude.Preliminaries.html#16290" class="Bound">𝓨</a> <a id="16292" class="Symbol">:</a> <a id="16294" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="16302" class="Symbol">}{</a><a id="16304" href="Prelude.Preliminaries.html#16304" class="Bound">I</a> <a id="16306" href="Prelude.Preliminaries.html#16306" class="Bound">J</a> <a id="16308" class="Symbol">:</a> <a id="16310" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="16312" href="Universes.html#403" class="Function Operator">̇</a><a id="16313" class="Symbol">}{</a><a id="16315" href="Prelude.Preliminaries.html#16315" class="Bound">B</a> <a id="16317" class="Symbol">:</a> <a id="16319" href="Prelude.Preliminaries.html#16304" class="Bound">I</a> <a id="16321" class="Symbol">→</a> <a id="16323" href="Prelude.Preliminaries.html#16290" class="Bound">𝓨</a> <a id="16325" href="Universes.html#403" class="Function Operator">̇</a><a id="16326" class="Symbol">}</a> <a id="16328" class="Keyword">where</a>

 <a id="16336" href="Prelude.Preliminaries.html#16336" class="Function">dapp</a> <a id="16341" class="Symbol">:</a> <a id="16343" class="Symbol">(∀</a> <a id="16346" href="Prelude.Preliminaries.html#16346" class="Bound">i</a> <a id="16348" class="Symbol">→</a> <a id="16350" class="Symbol">(</a><a id="16351" href="Prelude.Preliminaries.html#16306" class="Bound">J</a> <a id="16353" class="Symbol">→</a> <a id="16355" class="Symbol">(</a><a id="16356" href="Prelude.Preliminaries.html#16315" class="Bound">B</a> <a id="16358" href="Prelude.Preliminaries.html#16346" class="Bound">i</a><a id="16359" class="Symbol">))</a> <a id="16362" class="Symbol">→</a> <a id="16364" class="Symbol">(</a><a id="16365" href="Prelude.Preliminaries.html#16315" class="Bound">B</a> <a id="16367" href="Prelude.Preliminaries.html#16346" class="Bound">i</a><a id="16368" class="Symbol">))</a> <a id="16371" class="Symbol">→</a> <a id="16373" class="Symbol">(∀</a> <a id="16376" href="Prelude.Preliminaries.html#16376" class="Bound">i</a> <a id="16378" class="Symbol">→</a> <a id="16380" class="Symbol">(</a><a id="16381" href="Prelude.Preliminaries.html#16306" class="Bound">J</a> <a id="16383" class="Symbol">→</a> <a id="16385" class="Symbol">(</a><a id="16386" href="Prelude.Preliminaries.html#16315" class="Bound">B</a> <a id="16388" href="Prelude.Preliminaries.html#16376" class="Bound">i</a><a id="16389" class="Symbol">)))</a> <a id="16393" class="Symbol">→</a> <a id="16395" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="16397" href="Prelude.Preliminaries.html#16315" class="Bound">B</a>
 <a id="16400" href="Prelude.Preliminaries.html#16336" class="Function">dapp</a> <a id="16405" href="Prelude.Preliminaries.html#16405" class="Bound">f</a> <a id="16407" href="Prelude.Preliminaries.html#16407" class="Bound">a</a> <a id="16409" class="Symbol">=</a> <a id="16411" class="Symbol">λ</a> <a id="16413" href="Prelude.Preliminaries.html#16413" class="Bound">i</a> <a id="16415" class="Symbol">→</a> <a id="16417" class="Symbol">(</a><a id="16418" href="Prelude.Preliminaries.html#16405" class="Bound">f</a> <a id="16420" href="Prelude.Preliminaries.html#16413" class="Bound">i</a><a id="16421" class="Symbol">)</a> <a id="16423" class="Symbol">(</a><a id="16424" href="Prelude.Preliminaries.html#16407" class="Bound">a</a> <a id="16426" href="Prelude.Preliminaries.html#16413" class="Bound">i</a><a id="16427" class="Symbol">)</a>

</pre>

----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> Generally speaking, we have made a concerted effort to avoid duplicating types that were already defined in libraries that came before ours.  However, it is very likely that our library overlaps to some extent with other libraries with which we are as yet unfamiliar.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3"> Here we put the definition inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.</span>



<br>
<br>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

