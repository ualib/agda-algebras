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

This section describes the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

**Notation**. Here is an acronym that we use frequently.

  * [MLTT][] = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

#### <a id="options">Options</a>

All Agda programs begin by setting some options and by importing from existing libraries (in our case, the [Type Topology][] library by [Martín Escardó][]). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

<pre class="Agda">

<a id="1087" class="Symbol">{-#</a> <a id="1091" class="Keyword">OPTIONS</a> <a id="1099" class="Pragma">--without-K</a> <a id="1111" class="Pragma">--exact-split</a> <a id="1125" class="Pragma">--safe</a> <a id="1132" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda assumes when type-checking the program to verify its correctness.

* `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`; we would use the following `OPTIONS` line in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

but this is never done in publicly released versions of the UALib.





#### <a id="modules">Modules</a>

The `OPTIONS` line is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="2979" class="Keyword">module</a> <a id="2986" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="3008" class="Keyword">where</a>

</pre>

Sometimes we may wish to pass in parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. For instance, we often start an (anonymous) module, in which the fixed signature 𝑆 will be assumed until the end of the module, with the line `module _ {𝑆 : Signature 𝓞 𝓥} where...` The module started with this line is anonymous because the underscore `_` appears instead of a module name.

Agda determines where a model begins and ends by indentation.  This can take some getting used to, but after a short time it will seem quite natural.

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

<a id="5303" class="Keyword">open</a> <a id="5308" class="Keyword">import</a> <a id="5315" href="Universes.html" class="Module">Universes</a> <a id="5325" class="Keyword">public</a>

</pre>

Escardó's Universe module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="5590" class="Keyword">variable</a>
 <a id="5600" href="Prelude.Preliminaries.html#5600" class="Generalizable">𝓞</a> <a id="5602" class="Symbol">:</a> <a id="5604" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

The first three import lines have to be commented out because we will redefine the given types for pedagogical purposes in this module.

<pre class="Agda">

<a id="6788" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6862" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="6896" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6955" class="Keyword">open</a> <a id="6960" class="Keyword">import</a> <a id="6967" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6976" class="Keyword">using</a> <a id="6982" class="Symbol">(</a><a id="6983" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="6986" class="Symbol">;</a> <a id="6988" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="6994" class="Symbol">;</a> <a id="6996" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7004" class="Symbol">;</a> <a id="7006" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7015" class="Symbol">;</a> <a id="7017" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7023" class="Symbol">;</a> <a id="7025" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7027" class="Symbol">;</a> <a id="7029" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7057" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7058" class="Symbol">;</a> <a id="7060" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7062" class="Symbol">;</a> <a id="7064" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7067" class="Symbol">;</a> <a id="7069" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7072" class="Symbol">;</a> <a id="7074" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7075" class="Symbol">;</a> <a id="7077" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7078" class="Symbol">;</a> <a id="7080" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7081" class="Symbol">;</a> <a id="7083" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7086" class="Symbol">;</a> <a id="7088" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7102" class="Symbol">;</a> <a id="7104" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7118" class="Symbol">;</a> <a id="7120" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7122" class="Symbol">;</a> <a id="7124" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7127" class="Symbol">;</a> <a id="7129" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7131" class="Symbol">)</a>

<a id="7134" class="Keyword">open</a> <a id="7139" class="Keyword">import</a> <a id="7146" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7163" class="Keyword">using</a> <a id="7169" class="Symbol">(</a><a id="7170" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7178" class="Symbol">;</a> <a id="7180" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7187" class="Symbol">;</a> <a id="7189" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7199" class="Symbol">)</a>

<a id="7202" class="Keyword">open</a> <a id="7207" class="Keyword">import</a> <a id="7214" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7240" class="Keyword">using</a> <a id="7246" class="Symbol">(</a><a id="7247" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7253" class="Symbol">;</a> <a id="7255" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7269" class="Symbol">;</a> <a id="7271" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7278" class="Symbol">;</a>
 <a id="7281" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7293" class="Symbol">;</a> <a id="7295" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7310" class="Symbol">;</a> <a id="7312" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7319" class="Symbol">;</a> <a id="7321" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7331" class="Symbol">;</a> <a id="7333" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7347" class="Symbol">;</a>
 <a id="7350" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7381" class="Symbol">;</a> <a id="7383" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7386" class="Symbol">;</a> <a id="7388" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7391" class="Symbol">;</a> <a id="7393" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7410" class="Symbol">;</a> <a id="7412" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7429" class="Symbol">;</a>
 <a id="7432" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7481" class="Symbol">)</a>

<a id="7484" class="Keyword">open</a> <a id="7489" class="Keyword">import</a> <a id="7496" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7509" class="Keyword">renaming</a> <a id="7518" class="Symbol">(</a><a id="7519" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7523" class="Symbol">to</a> <a id="_∈_"></a><a id="7526" href="Prelude.Preliminaries.html#7526" class="Function Operator">_∈₀_</a><a id="7530" class="Symbol">;</a> <a id="7532" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7536" class="Symbol">to</a> <a id="_⊆_"></a><a id="7539" href="Prelude.Preliminaries.html#7539" class="Function Operator">_⊆₀_</a><a id="7543" class="Symbol">;</a> <a id="7545" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7563" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7566" href="Prelude.Preliminaries.html#7566" class="Function">∈₀-is-subsingleton</a><a id="7584" class="Symbol">)</a>
 <a id="7587" class="Keyword">using</a> <a id="7593" class="Symbol">(</a><a id="7594" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7595" class="Symbol">;</a> <a id="7597" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7618" class="Symbol">;</a> <a id="7620" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7639" class="Symbol">;</a> <a id="7641" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7663" class="Symbol">;</a> <a id="7665" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7672" class="Symbol">;</a> <a id="7674" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7680" class="Symbol">;</a> <a id="7682" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7683" class="Symbol">)</a>

<a id="7686" class="Keyword">open</a> <a id="7691" class="Keyword">import</a> <a id="7698" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7713" class="Keyword">using</a> <a id="7719" class="Symbol">(</a><a id="7720" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7723" class="Symbol">;</a> <a id="7725" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7729" class="Symbol">;</a> <a id="7731" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7748" class="Symbol">;</a> <a id="7750" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7762" class="Symbol">;</a> <a id="7764" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7777" class="Symbol">;</a> <a id="7779" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7790" class="Symbol">;</a>
 <a id="7793" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7799" class="Symbol">;</a> <a id="7801" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7804" class="Symbol">;</a> <a id="7806" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="7833" class="Symbol">;</a> <a id="7835" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7852" class="Symbol">;</a> <a id="7854" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7871" class="Symbol">;</a> <a id="7873" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7888" class="Symbol">)</a>

<a id="7891" class="Keyword">open</a> <a id="7896" class="Keyword">import</a> <a id="7903" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7924" class="Keyword">using</a> <a id="7930" class="Symbol">(</a><a id="7931" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7943" class="Symbol">)</a>

<a id="7946" class="Keyword">open</a> <a id="7951" class="Keyword">import</a> <a id="7958" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="7979" class="Keyword">using</a> <a id="7985" class="Symbol">(</a><a id="7986" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="7988" class="Symbol">;</a> <a id="7990" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="7993" class="Symbol">)</a>

<a id="7996" class="Keyword">open</a> <a id="8001" class="Keyword">import</a> <a id="8008" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8036" class="Keyword">using</a> <a id="8042" class="Symbol">(</a><a id="8043" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8046" class="Symbol">;</a> <a id="8048" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8054" class="Symbol">;</a> <a id="8056" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8077" class="Symbol">;</a>
 <a id="8080" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8102" class="Symbol">;</a> <a id="8104" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8109" class="Symbol">;</a> <a id="8111" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8129" class="Symbol">;</a> <a id="8131" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8138" class="Symbol">)</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.





#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from [Escardó][]'s \href{https://github.com/martinescardo/TypeTopology}{Type Topology} library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

[Escardó][] has an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}. We highly recommend Martín's notes to anyone wanting more details than we provide here about [MLTT][] and the Univalent Foundations/HoTT extensions thereof.

Following [Escardó][], we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module [Escardó][] defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).<sup>1</sup>

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

<a id="11751" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11758" href="Prelude.Preliminaries.html#11758" class="Module">hide-sigma</a> <a id="11769" class="Keyword">where</a>

 <a id="11777" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11784" href="Prelude.Preliminaries.html#11784" class="Record">Σ</a> <a id="11786" class="Symbol">{</a><a id="11787" href="Prelude.Preliminaries.html#11787" class="Bound">𝓤</a> <a id="11789" href="Prelude.Preliminaries.html#11789" class="Bound">𝓥</a><a id="11790" class="Symbol">}</a> <a id="11792" class="Symbol">{</a><a id="11793" href="Prelude.Preliminaries.html#11793" class="Bound">X</a> <a id="11795" class="Symbol">:</a> <a id="11797" href="Prelude.Preliminaries.html#11787" class="Bound">𝓤</a> <a id="11799" href="Universes.html#403" class="Function Operator">̇</a> <a id="11801" class="Symbol">}</a> <a id="11803" class="Symbol">(</a><a id="11804" href="Prelude.Preliminaries.html#11804" class="Bound">Y</a> <a id="11806" class="Symbol">:</a> <a id="11808" href="Prelude.Preliminaries.html#11793" class="Bound">X</a> <a id="11810" class="Symbol">→</a> <a id="11812" href="Prelude.Preliminaries.html#11789" class="Bound">𝓥</a> <a id="11814" href="Universes.html#403" class="Function Operator">̇</a> <a id="11816" class="Symbol">)</a> <a id="11818" class="Symbol">:</a> <a id="11820" href="Prelude.Preliminaries.html#11787" class="Bound">𝓤</a> <a id="11822" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11824" href="Prelude.Preliminaries.html#11789" class="Bound">𝓥</a> <a id="11826" href="Universes.html#403" class="Function Operator">̇</a>  <a id="11829" class="Keyword">where</a>
  <a id="11837" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="11849" href="Prelude.Preliminaries.html#11849" class="InductiveConstructor Operator">_,_</a>
  <a id="11855" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="11864" href="Prelude.Preliminaries.html#11864" class="Field">pr₁</a> <a id="11868" class="Symbol">:</a> <a id="11870" href="Prelude.Preliminaries.html#11793" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="11875" href="Prelude.Preliminaries.html#11875" class="Field">pr₂</a> <a id="11879" class="Symbol">:</a> <a id="11881" href="Prelude.Preliminaries.html#11804" class="Bound">Y</a> <a id="11883" href="Prelude.Preliminaries.html#11864" class="Field">pr₁</a>

 <a id="11889" class="Keyword">infixr</a> <a id="11896" class="Number">50</a> <a id="11899" href="Prelude.Preliminaries.html#11849" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  [Escardó][] makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12240" href="Prelude.Preliminaries.html#12240" class="Function">-Σ</a> <a id="12243" class="Symbol">:</a> <a id="12245" class="Symbol">{</a><a id="12246" href="Prelude.Preliminaries.html#12246" class="Bound">𝓤</a> <a id="12248" href="Prelude.Preliminaries.html#12248" class="Bound">𝓥</a> <a id="12250" class="Symbol">:</a> <a id="12252" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12260" class="Symbol">}</a> <a id="12262" class="Symbol">(</a><a id="12263" href="Prelude.Preliminaries.html#12263" class="Bound">X</a> <a id="12265" class="Symbol">:</a> <a id="12267" href="Prelude.Preliminaries.html#12246" class="Bound">𝓤</a> <a id="12269" href="Universes.html#403" class="Function Operator">̇</a> <a id="12271" class="Symbol">)</a> <a id="12273" class="Symbol">(</a><a id="12274" href="Prelude.Preliminaries.html#12274" class="Bound">Y</a> <a id="12276" class="Symbol">:</a> <a id="12278" href="Prelude.Preliminaries.html#12263" class="Bound">X</a> <a id="12280" class="Symbol">→</a> <a id="12282" href="Prelude.Preliminaries.html#12248" class="Bound">𝓥</a> <a id="12284" href="Universes.html#403" class="Function Operator">̇</a> <a id="12286" class="Symbol">)</a> <a id="12288" class="Symbol">→</a> <a id="12290" href="Prelude.Preliminaries.html#12246" class="Bound">𝓤</a> <a id="12292" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12294" href="Prelude.Preliminaries.html#12248" class="Bound">𝓥</a> <a id="12296" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12299" href="Prelude.Preliminaries.html#12240" class="Function">-Σ</a> <a id="12302" href="Prelude.Preliminaries.html#12302" class="Bound">X</a> <a id="12304" href="Prelude.Preliminaries.html#12304" class="Bound">Y</a> <a id="12306" class="Symbol">=</a> <a id="12308" href="Prelude.Preliminaries.html#11784" class="Record">Σ</a> <a id="12310" href="Prelude.Preliminaries.html#12304" class="Bound">Y</a>

 <a id="12314" class="Keyword">syntax</a> <a id="12321" href="Prelude.Preliminaries.html#12240" class="Function">-Σ</a> <a id="12324" class="Bound">X</a> <a id="12326" class="Symbol">(λ</a> <a id="12329" class="Bound">x</a> <a id="12331" class="Symbol">→</a> <a id="12333" class="Bound">Y</a><a id="12334" class="Symbol">)</a> <a id="12336" class="Symbol">=</a> <a id="12338" class="Function">Σ</a> <a id="12340" class="Bound">x</a> <a id="12342" class="Function">꞉</a> <a id="12344" class="Bound">X</a> <a id="12346" class="Function">,</a> <a id="12348" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12721" href="Prelude.Preliminaries.html#12721" class="Function Operator">_×_</a> <a id="12725" class="Symbol">:</a> <a id="12727" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12729" href="Universes.html#403" class="Function Operator">̇</a> <a id="12731" class="Symbol">→</a> <a id="12733" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12735" href="Universes.html#403" class="Function Operator">̇</a> <a id="12737" class="Symbol">→</a> <a id="12739" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12741" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12743" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12745" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12748" href="Prelude.Preliminaries.html#12748" class="Bound">X</a> <a id="12750" href="Prelude.Preliminaries.html#12721" class="Function Operator">×</a> <a id="12752" href="Prelude.Preliminaries.html#12752" class="Bound">Y</a> <a id="12754" class="Symbol">=</a> <a id="12756" href="Prelude.Preliminaries.html#12240" class="Function">Σ</a> <a id="12758" href="Prelude.Preliminaries.html#12758" class="Bound">x</a> <a id="12760" href="Prelude.Preliminaries.html#12240" class="Function">꞉</a> <a id="12762" href="Prelude.Preliminaries.html#12748" class="Bound">X</a> <a id="12764" href="Prelude.Preliminaries.html#12240" class="Function">,</a> <a id="12766" href="Prelude.Preliminaries.html#12752" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="12976" class="Keyword">open</a> <a id="12981" class="Keyword">import</a> <a id="12988" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12999" class="Keyword">renaming</a> <a id="13008" class="Symbol">(</a><a id="13009" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13013" class="Symbol">to</a> <a id="13016" class="Keyword">infixr</a> <a id="13023" class="Number">50</a> <a id="_,_"></a><a id="13026" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">_,_</a><a id="13029" class="Symbol">)</a>
<a id="13031" class="Keyword">open</a> <a id="13036" class="Keyword">import</a> <a id="13043" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13052" class="Keyword">using</a> <a id="13058" class="Symbol">(</a><a id="13059" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13062" class="Symbol">;</a> <a id="13064" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13067" class="Symbol">;</a> <a id="13069" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13072" class="Symbol">;</a> <a id="13074" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13076" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13511" class="Keyword">module</a> <a id="13518" href="Prelude.Preliminaries.html#13518" class="Module">_</a> <a id="13520" class="Symbol">{</a><a id="13521" href="Prelude.Preliminaries.html#13521" class="Bound">𝓤</a> <a id="13523" class="Symbol">:</a> <a id="13525" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13533" class="Symbol">}</a> <a id="13535" class="Keyword">where</a>

 <a id="13543" href="Prelude.Preliminaries.html#13543" class="Function Operator">∣_∣</a> <a id="13547" href="Prelude.Preliminaries.html#13547" class="Function">fst</a> <a id="13551" class="Symbol">:</a> <a id="13553" class="Symbol">{</a><a id="13554" href="Prelude.Preliminaries.html#13554" class="Bound">X</a> <a id="13556" class="Symbol">:</a> <a id="13558" href="Prelude.Preliminaries.html#13521" class="Bound">𝓤</a> <a id="13560" href="Universes.html#403" class="Function Operator">̇</a> <a id="13562" class="Symbol">}{</a><a id="13564" href="Prelude.Preliminaries.html#13564" class="Bound">Y</a> <a id="13566" class="Symbol">:</a> <a id="13568" href="Prelude.Preliminaries.html#13554" class="Bound">X</a> <a id="13570" class="Symbol">→</a> <a id="13572" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13574" href="Universes.html#403" class="Function Operator">̇</a><a id="13575" class="Symbol">}</a> <a id="13577" class="Symbol">→</a> <a id="13579" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13581" href="Prelude.Preliminaries.html#13564" class="Bound">Y</a> <a id="13583" class="Symbol">→</a> <a id="13585" href="Prelude.Preliminaries.html#13554" class="Bound">X</a>
 <a id="13588" href="Prelude.Preliminaries.html#13543" class="Function Operator">∣</a> <a id="13590" href="Prelude.Preliminaries.html#13590" class="Bound">x</a> <a id="13592" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="13594" href="Prelude.Preliminaries.html#13594" class="Bound">y</a> <a id="13596" href="Prelude.Preliminaries.html#13543" class="Function Operator">∣</a> <a id="13598" class="Symbol">=</a> <a id="13600" href="Prelude.Preliminaries.html#13590" class="Bound">x</a>
 <a id="13603" href="Prelude.Preliminaries.html#13547" class="Function">fst</a> <a id="13607" class="Symbol">(</a><a id="13608" href="Prelude.Preliminaries.html#13608" class="Bound">x</a> <a id="13610" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="13612" href="Prelude.Preliminaries.html#13612" class="Bound">y</a><a id="13613" class="Symbol">)</a> <a id="13615" class="Symbol">=</a> <a id="13617" href="Prelude.Preliminaries.html#13608" class="Bound">x</a>

 <a id="13621" href="Prelude.Preliminaries.html#13621" class="Function Operator">∥_∥</a> <a id="13625" href="Prelude.Preliminaries.html#13625" class="Function">snd</a> <a id="13629" class="Symbol">:</a> <a id="13631" class="Symbol">{</a><a id="13632" href="Prelude.Preliminaries.html#13632" class="Bound">X</a> <a id="13634" class="Symbol">:</a> <a id="13636" href="Prelude.Preliminaries.html#13521" class="Bound">𝓤</a> <a id="13638" href="Universes.html#403" class="Function Operator">̇</a> <a id="13640" class="Symbol">}{</a><a id="13642" href="Prelude.Preliminaries.html#13642" class="Bound">Y</a> <a id="13644" class="Symbol">:</a> <a id="13646" href="Prelude.Preliminaries.html#13632" class="Bound">X</a> <a id="13648" class="Symbol">→</a> <a id="13650" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13652" href="Universes.html#403" class="Function Operator">̇</a> <a id="13654" class="Symbol">}</a> <a id="13656" class="Symbol">→</a> <a id="13658" class="Symbol">(</a><a id="13659" href="Prelude.Preliminaries.html#13659" class="Bound">z</a> <a id="13661" class="Symbol">:</a> <a id="13663" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13665" href="Prelude.Preliminaries.html#13642" class="Bound">Y</a><a id="13666" class="Symbol">)</a> <a id="13668" class="Symbol">→</a> <a id="13670" href="Prelude.Preliminaries.html#13642" class="Bound">Y</a> <a id="13672" class="Symbol">(</a><a id="13673" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13677" href="Prelude.Preliminaries.html#13659" class="Bound">z</a><a id="13678" class="Symbol">)</a>
 <a id="13681" href="Prelude.Preliminaries.html#13621" class="Function Operator">∥</a> <a id="13683" href="Prelude.Preliminaries.html#13683" class="Bound">x</a> <a id="13685" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="13687" href="Prelude.Preliminaries.html#13687" class="Bound">y</a> <a id="13689" href="Prelude.Preliminaries.html#13621" class="Function Operator">∥</a> <a id="13691" class="Symbol">=</a> <a id="13693" href="Prelude.Preliminaries.html#13687" class="Bound">y</a>
 <a id="13696" href="Prelude.Preliminaries.html#13625" class="Function">snd</a> <a id="13700" class="Symbol">(</a><a id="13701" href="Prelude.Preliminaries.html#13701" class="Bound">x</a> <a id="13703" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="13705" href="Prelude.Preliminaries.html#13705" class="Bound">y</a><a id="13706" class="Symbol">)</a> <a id="13708" class="Symbol">=</a> <a id="13710" href="Prelude.Preliminaries.html#13705" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="13987" class="Keyword">module</a> <a id="hide-pi"></a><a id="13994" href="Prelude.Preliminaries.html#13994" class="Module">hide-pi</a> <a id="14002" class="Symbol">{</a><a id="14003" href="Prelude.Preliminaries.html#14003" class="Bound">𝓤</a> <a id="14005" href="Prelude.Preliminaries.html#14005" class="Bound">𝓦</a> <a id="14007" class="Symbol">:</a> <a id="14009" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14017" class="Symbol">}</a> <a id="14019" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14027" href="Prelude.Preliminaries.html#14027" class="Function">Π</a> <a id="14029" class="Symbol">:</a> <a id="14031" class="Symbol">{</a><a id="14032" href="Prelude.Preliminaries.html#14032" class="Bound">X</a> <a id="14034" class="Symbol">:</a> <a id="14036" href="Prelude.Preliminaries.html#14003" class="Bound">𝓤</a> <a id="14038" href="Universes.html#403" class="Function Operator">̇</a> <a id="14040" class="Symbol">}</a> <a id="14042" class="Symbol">(</a><a id="14043" href="Prelude.Preliminaries.html#14043" class="Bound">A</a> <a id="14045" class="Symbol">:</a> <a id="14047" href="Prelude.Preliminaries.html#14032" class="Bound">X</a> <a id="14049" class="Symbol">→</a> <a id="14051" href="Prelude.Preliminaries.html#14005" class="Bound">𝓦</a> <a id="14053" href="Universes.html#403" class="Function Operator">̇</a> <a id="14055" class="Symbol">)</a> <a id="14057" class="Symbol">→</a> <a id="14059" href="Prelude.Preliminaries.html#14003" class="Bound">𝓤</a> <a id="14061" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14063" href="Prelude.Preliminaries.html#14005" class="Bound">𝓦</a> <a id="14065" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14068" href="Prelude.Preliminaries.html#14027" class="Function">Π</a> <a id="14070" class="Symbol">{</a><a id="14071" href="Prelude.Preliminaries.html#14071" class="Bound">X</a><a id="14072" class="Symbol">}</a> <a id="14074" href="Prelude.Preliminaries.html#14074" class="Bound">A</a> <a id="14076" class="Symbol">=</a> <a id="14078" class="Symbol">(</a><a id="14079" href="Prelude.Preliminaries.html#14079" class="Bound">x</a> <a id="14081" class="Symbol">:</a> <a id="14083" href="Prelude.Preliminaries.html#14071" class="Bound">X</a><a id="14084" class="Symbol">)</a> <a id="14086" class="Symbol">→</a> <a id="14088" href="Prelude.Preliminaries.html#14074" class="Bound">A</a> <a id="14090" href="Prelude.Preliminaries.html#14079" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14094" href="Prelude.Preliminaries.html#14094" class="Function">-Π</a> <a id="14097" class="Symbol">:</a> <a id="14099" class="Symbol">(</a><a id="14100" href="Prelude.Preliminaries.html#14100" class="Bound">X</a> <a id="14102" class="Symbol">:</a> <a id="14104" href="Prelude.Preliminaries.html#14003" class="Bound">𝓤</a> <a id="14106" href="Universes.html#403" class="Function Operator">̇</a> <a id="14108" class="Symbol">)(</a><a id="14110" href="Prelude.Preliminaries.html#14110" class="Bound">Y</a> <a id="14112" class="Symbol">:</a> <a id="14114" href="Prelude.Preliminaries.html#14100" class="Bound">X</a> <a id="14116" class="Symbol">→</a> <a id="14118" href="Prelude.Preliminaries.html#14005" class="Bound">𝓦</a> <a id="14120" href="Universes.html#403" class="Function Operator">̇</a> <a id="14122" class="Symbol">)</a> <a id="14124" class="Symbol">→</a> <a id="14126" href="Prelude.Preliminaries.html#14003" class="Bound">𝓤</a> <a id="14128" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14130" href="Prelude.Preliminaries.html#14005" class="Bound">𝓦</a> <a id="14132" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14135" href="Prelude.Preliminaries.html#14094" class="Function">-Π</a> <a id="14138" href="Prelude.Preliminaries.html#14138" class="Bound">X</a> <a id="14140" href="Prelude.Preliminaries.html#14140" class="Bound">Y</a> <a id="14142" class="Symbol">=</a> <a id="14144" href="Prelude.Preliminaries.html#14027" class="Function">Π</a> <a id="14146" href="Prelude.Preliminaries.html#14140" class="Bound">Y</a>

 <a id="14150" class="Keyword">infixr</a> <a id="14157" class="Number">-1</a> <a id="14160" href="Prelude.Preliminaries.html#14094" class="Function">-Π</a>
 <a id="14164" class="Keyword">syntax</a> <a id="14171" href="Prelude.Preliminaries.html#14094" class="Function">-Π</a> <a id="14174" class="Bound">A</a> <a id="14176" class="Symbol">(λ</a> <a id="14179" class="Bound">x</a> <a id="14181" class="Symbol">→</a> <a id="14183" class="Bound">b</a><a id="14184" class="Symbol">)</a> <a id="14186" class="Symbol">=</a> <a id="14188" class="Function">Π</a> <a id="14190" class="Bound">x</a> <a id="14192" class="Function">꞉</a> <a id="14194" class="Bound">A</a> <a id="14196" class="Function">,</a> <a id="14198" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14488" class="Keyword">open</a> <a id="14493" class="Keyword">import</a> <a id="14500" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14511" class="Keyword">renaming</a> <a id="14520" class="Symbol">(</a><a id="14521" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14525" class="Symbol">to</a> <a id="14528" class="Keyword">infixr</a> <a id="14535" class="Number">50</a> <a id="_,_"></a><a id="14538" href="Prelude.Preliminaries.html#14538" class="InductiveConstructor Operator">_,_</a><a id="14541" class="Symbol">)</a> <a id="14543" class="Keyword">public</a>
<a id="14550" class="Keyword">open</a> <a id="14555" class="Keyword">import</a> <a id="14562" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14571" class="Keyword">using</a> <a id="14577" class="Symbol">(</a><a id="14578" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14581" class="Symbol">;</a> <a id="14583" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14586" class="Symbol">;</a> <a id="14588" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14591" class="Symbol">;</a> <a id="14593" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14595" class="Symbol">;</a> <a id="14597" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14598" class="Symbol">)</a> <a id="14600" class="Keyword">public</a>


<a id="14609" class="Keyword">module</a> <a id="14616" href="Prelude.Preliminaries.html#14616" class="Module">_</a> <a id="14618" class="Symbol">{</a><a id="14619" href="Prelude.Preliminaries.html#14619" class="Bound">𝓨</a> <a id="14621" href="Prelude.Preliminaries.html#14621" class="Bound">𝓩</a> <a id="14623" class="Symbol">:</a> <a id="14625" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14633" class="Symbol">}{</a><a id="14635" href="Prelude.Preliminaries.html#14635" class="Bound">I</a> <a id="14637" class="Symbol">:</a> <a id="14639" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14641" href="Universes.html#403" class="Function Operator">̇</a><a id="14642" class="Symbol">}{</a><a id="14644" href="Prelude.Preliminaries.html#14644" class="Bound">B</a> <a id="14646" class="Symbol">:</a> <a id="14648" href="Prelude.Preliminaries.html#14635" class="Bound">I</a> <a id="14650" class="Symbol">→</a> <a id="14652" href="Prelude.Preliminaries.html#14619" class="Bound">𝓨</a> <a id="14654" href="Universes.html#403" class="Function Operator">̇</a><a id="14655" class="Symbol">}{</a><a id="14657" href="Prelude.Preliminaries.html#14657" class="Bound">C</a> <a id="14659" class="Symbol">:</a> <a id="14661" href="Prelude.Preliminaries.html#14635" class="Bound">I</a> <a id="14663" class="Symbol">→</a> <a id="14665" href="Prelude.Preliminaries.html#14621" class="Bound">𝓩</a> <a id="14667" href="Universes.html#403" class="Function Operator">̇</a><a id="14668" class="Symbol">}</a> <a id="14670" class="Keyword">where</a>
 <a id="14677" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14700" href="Prelude.Preliminaries.html#14700" class="Function">zip</a> <a id="14704" class="Symbol">:</a> <a id="14706" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14708" href="Prelude.Preliminaries.html#14644" class="Bound">B</a> <a id="14710" class="Symbol">→</a> <a id="14712" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14714" href="Prelude.Preliminaries.html#14657" class="Bound">C</a> <a id="14716" class="Symbol">→</a> <a id="14718" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14720" class="Symbol">(λ</a> <a id="14723" href="Prelude.Preliminaries.html#14723" class="Bound">i</a> <a id="14725" class="Symbol">→</a> <a id="14727" class="Symbol">(</a><a id="14728" href="Prelude.Preliminaries.html#14644" class="Bound">B</a> <a id="14730" href="Prelude.Preliminaries.html#14723" class="Bound">i</a><a id="14731" class="Symbol">)</a> <a id="14733" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14735" class="Symbol">(</a><a id="14736" href="Prelude.Preliminaries.html#14657" class="Bound">C</a> <a id="14738" href="Prelude.Preliminaries.html#14723" class="Bound">i</a><a id="14739" class="Symbol">))</a>
 <a id="14743" href="Prelude.Preliminaries.html#14700" class="Function">zip</a> <a id="14747" href="Prelude.Preliminaries.html#14747" class="Bound">f</a> <a id="14749" href="Prelude.Preliminaries.html#14749" class="Bound">a</a> <a id="14751" class="Symbol">=</a> <a id="14753" class="Symbol">λ</a> <a id="14755" href="Prelude.Preliminaries.html#14755" class="Bound">i</a> <a id="14757" class="Symbol">→</a> <a id="14759" class="Symbol">(</a><a id="14760" href="Prelude.Preliminaries.html#14747" class="Bound">f</a> <a id="14762" href="Prelude.Preliminaries.html#14755" class="Bound">i</a> <a id="14764" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="14766" href="Prelude.Preliminaries.html#14749" class="Bound">a</a> <a id="14768" href="Prelude.Preliminaries.html#14755" class="Bound">i</a><a id="14769" class="Symbol">)</a>

 <a id="14773" href="Prelude.Preliminaries.html#14773" class="Function">eval</a> <a id="14778" class="Symbol">:</a> <a id="14780" class="Symbol">{</a><a id="14781" href="Prelude.Preliminaries.html#14781" class="Bound">Y</a> <a id="14783" class="Symbol">:</a> <a id="14785" href="Prelude.Preliminaries.html#14619" class="Bound">𝓨</a> <a id="14787" href="Universes.html#403" class="Function Operator">̇</a><a id="14788" class="Symbol">}{</a><a id="14790" href="Prelude.Preliminaries.html#14790" class="Bound">Z</a> <a id="14792" class="Symbol">:</a> <a id="14794" href="Prelude.Preliminaries.html#14621" class="Bound">𝓩</a> <a id="14796" href="Universes.html#403" class="Function Operator">̇</a><a id="14797" class="Symbol">}</a> <a id="14799" class="Symbol">→</a> <a id="14801" class="Symbol">((</a><a id="14803" href="Prelude.Preliminaries.html#14781" class="Bound">Y</a> <a id="14805" class="Symbol">→</a> <a id="14807" href="Prelude.Preliminaries.html#14790" class="Bound">Z</a><a id="14808" class="Symbol">)</a> <a id="14810" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14812" href="Prelude.Preliminaries.html#14781" class="Bound">Y</a><a id="14813" class="Symbol">)</a> <a id="14815" class="Symbol">→</a> <a id="14817" href="Prelude.Preliminaries.html#14790" class="Bound">Z</a>
 <a id="14820" href="Prelude.Preliminaries.html#14773" class="Function">eval</a> <a id="14825" class="Symbol">(</a><a id="14826" href="Prelude.Preliminaries.html#14826" class="Bound">f</a> <a id="14828" href="Prelude.Preliminaries.html#13026" class="InductiveConstructor Operator">,</a> <a id="14830" href="Prelude.Preliminaries.html#14830" class="Bound">a</a><a id="14831" class="Symbol">)</a> <a id="14833" class="Symbol">=</a> <a id="14835" href="Prelude.Preliminaries.html#14826" class="Bound">f</a> <a id="14837" href="Prelude.Preliminaries.html#14830" class="Bound">a</a>
 
<a id="14841" class="Keyword">module</a> <a id="14848" href="Prelude.Preliminaries.html#14848" class="Module">_</a> <a id="14850" class="Symbol">{</a><a id="14851" href="Prelude.Preliminaries.html#14851" class="Bound">𝓨</a> <a id="14853" class="Symbol">:</a> <a id="14855" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14863" class="Symbol">}{</a><a id="14865" href="Prelude.Preliminaries.html#14865" class="Bound">I</a> <a id="14867" href="Prelude.Preliminaries.html#14867" class="Bound">J</a> <a id="14869" class="Symbol">:</a> <a id="14871" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14873" href="Universes.html#403" class="Function Operator">̇</a><a id="14874" class="Symbol">}{</a><a id="14876" href="Prelude.Preliminaries.html#14876" class="Bound">B</a> <a id="14878" class="Symbol">:</a> <a id="14880" href="Prelude.Preliminaries.html#14865" class="Bound">I</a> <a id="14882" class="Symbol">→</a> <a id="14884" href="Prelude.Preliminaries.html#14851" class="Bound">𝓨</a> <a id="14886" href="Universes.html#403" class="Function Operator">̇</a><a id="14887" class="Symbol">}</a> <a id="14889" class="Keyword">where</a>

 <a id="14897" href="Prelude.Preliminaries.html#14897" class="Function">dapp</a> <a id="14902" class="Symbol">:</a> <a id="14904" class="Symbol">(∀</a> <a id="14907" href="Prelude.Preliminaries.html#14907" class="Bound">i</a> <a id="14909" class="Symbol">→</a> <a id="14911" class="Symbol">(</a><a id="14912" href="Prelude.Preliminaries.html#14867" class="Bound">J</a> <a id="14914" class="Symbol">→</a> <a id="14916" class="Symbol">(</a><a id="14917" href="Prelude.Preliminaries.html#14876" class="Bound">B</a> <a id="14919" href="Prelude.Preliminaries.html#14907" class="Bound">i</a><a id="14920" class="Symbol">))</a> <a id="14923" class="Symbol">→</a> <a id="14925" class="Symbol">(</a><a id="14926" href="Prelude.Preliminaries.html#14876" class="Bound">B</a> <a id="14928" href="Prelude.Preliminaries.html#14907" class="Bound">i</a><a id="14929" class="Symbol">))</a> <a id="14932" class="Symbol">→</a> <a id="14934" class="Symbol">(∀</a> <a id="14937" href="Prelude.Preliminaries.html#14937" class="Bound">i</a> <a id="14939" class="Symbol">→</a> <a id="14941" class="Symbol">(</a><a id="14942" href="Prelude.Preliminaries.html#14867" class="Bound">J</a> <a id="14944" class="Symbol">→</a> <a id="14946" class="Symbol">(</a><a id="14947" href="Prelude.Preliminaries.html#14876" class="Bound">B</a> <a id="14949" href="Prelude.Preliminaries.html#14937" class="Bound">i</a><a id="14950" class="Symbol">)))</a> <a id="14954" class="Symbol">→</a> <a id="14956" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14958" href="Prelude.Preliminaries.html#14876" class="Bound">B</a>
 <a id="14961" href="Prelude.Preliminaries.html#14897" class="Function">dapp</a> <a id="14966" href="Prelude.Preliminaries.html#14966" class="Bound">f</a> <a id="14968" href="Prelude.Preliminaries.html#14968" class="Bound">a</a> <a id="14970" class="Symbol">=</a> <a id="14972" class="Symbol">λ</a> <a id="14974" href="Prelude.Preliminaries.html#14974" class="Bound">i</a> <a id="14976" class="Symbol">→</a> <a id="14978" class="Symbol">(</a><a id="14979" href="Prelude.Preliminaries.html#14966" class="Bound">f</a> <a id="14981" href="Prelude.Preliminaries.html#14974" class="Bound">i</a><a id="14982" class="Symbol">)</a> <a id="14984" class="Symbol">(</a><a id="14985" href="Prelude.Preliminaries.html#14968" class="Bound">a</a> <a id="14987" href="Prelude.Preliminaries.html#14974" class="Bound">i</a><a id="14988" class="Symbol">)</a>

</pre>

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

