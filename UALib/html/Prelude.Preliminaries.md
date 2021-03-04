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

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12220" href="Prelude.Preliminaries.html#12220" class="Function">-Σ</a> <a id="12223" class="Symbol">:</a> <a id="12225" class="Symbol">{</a><a id="12226" href="Prelude.Preliminaries.html#12226" class="Bound">𝓤</a> <a id="12228" href="Prelude.Preliminaries.html#12228" class="Bound">𝓥</a> <a id="12230" class="Symbol">:</a> <a id="12232" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12240" class="Symbol">}</a> <a id="12242" class="Symbol">(</a><a id="12243" href="Prelude.Preliminaries.html#12243" class="Bound">X</a> <a id="12245" class="Symbol">:</a> <a id="12247" href="Prelude.Preliminaries.html#12226" class="Bound">𝓤</a> <a id="12249" href="Universes.html#403" class="Function Operator">̇</a> <a id="12251" class="Symbol">)</a> <a id="12253" class="Symbol">(</a><a id="12254" href="Prelude.Preliminaries.html#12254" class="Bound">Y</a> <a id="12256" class="Symbol">:</a> <a id="12258" href="Prelude.Preliminaries.html#12243" class="Bound">X</a> <a id="12260" class="Symbol">→</a> <a id="12262" href="Prelude.Preliminaries.html#12228" class="Bound">𝓥</a> <a id="12264" href="Universes.html#403" class="Function Operator">̇</a> <a id="12266" class="Symbol">)</a> <a id="12268" class="Symbol">→</a> <a id="12270" href="Prelude.Preliminaries.html#12226" class="Bound">𝓤</a> <a id="12272" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12274" href="Prelude.Preliminaries.html#12228" class="Bound">𝓥</a> <a id="12276" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12279" href="Prelude.Preliminaries.html#12220" class="Function">-Σ</a> <a id="12282" href="Prelude.Preliminaries.html#12282" class="Bound">X</a> <a id="12284" href="Prelude.Preliminaries.html#12284" class="Bound">Y</a> <a id="12286" class="Symbol">=</a> <a id="12288" href="Prelude.Preliminaries.html#11784" class="Record">Σ</a> <a id="12290" href="Prelude.Preliminaries.html#12284" class="Bound">Y</a>

 <a id="12294" class="Keyword">syntax</a> <a id="12301" href="Prelude.Preliminaries.html#12220" class="Function">-Σ</a> <a id="12304" class="Bound">X</a> <a id="12306" class="Symbol">(λ</a> <a id="12309" class="Bound">x</a> <a id="12311" class="Symbol">→</a> <a id="12313" class="Bound">Y</a><a id="12314" class="Symbol">)</a> <a id="12316" class="Symbol">=</a> <a id="12318" class="Function">Σ</a> <a id="12320" class="Bound">x</a> <a id="12322" class="Function">꞉</a> <a id="12324" class="Bound">X</a> <a id="12326" class="Function">,</a> <a id="12328" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12701" href="Prelude.Preliminaries.html#12701" class="Function Operator">_×_</a> <a id="12705" class="Symbol">:</a> <a id="12707" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12709" href="Universes.html#403" class="Function Operator">̇</a> <a id="12711" class="Symbol">→</a> <a id="12713" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12715" href="Universes.html#403" class="Function Operator">̇</a> <a id="12717" class="Symbol">→</a> <a id="12719" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12721" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12723" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12725" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12728" href="Prelude.Preliminaries.html#12728" class="Bound">X</a> <a id="12730" href="Prelude.Preliminaries.html#12701" class="Function Operator">×</a> <a id="12732" href="Prelude.Preliminaries.html#12732" class="Bound">Y</a> <a id="12734" class="Symbol">=</a> <a id="12736" href="Prelude.Preliminaries.html#12220" class="Function">Σ</a> <a id="12738" href="Prelude.Preliminaries.html#12738" class="Bound">x</a> <a id="12740" href="Prelude.Preliminaries.html#12220" class="Function">꞉</a> <a id="12742" href="Prelude.Preliminaries.html#12728" class="Bound">X</a> <a id="12744" href="Prelude.Preliminaries.html#12220" class="Function">,</a> <a id="12746" href="Prelude.Preliminaries.html#12732" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="12956" class="Keyword">open</a> <a id="12961" class="Keyword">import</a> <a id="12968" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12979" class="Keyword">renaming</a> <a id="12988" class="Symbol">(</a><a id="12989" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="12993" class="Symbol">to</a> <a id="12996" class="Keyword">infixr</a> <a id="13003" class="Number">50</a> <a id="_,_"></a><a id="13006" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">_,_</a><a id="13009" class="Symbol">)</a>
<a id="13011" class="Keyword">open</a> <a id="13016" class="Keyword">import</a> <a id="13023" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13032" class="Keyword">using</a> <a id="13038" class="Symbol">(</a><a id="13039" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13042" class="Symbol">;</a> <a id="13044" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13047" class="Symbol">;</a> <a id="13049" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13052" class="Symbol">;</a> <a id="13054" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13056" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13491" class="Keyword">module</a> <a id="13498" href="Prelude.Preliminaries.html#13498" class="Module">_</a> <a id="13500" class="Symbol">{</a><a id="13501" href="Prelude.Preliminaries.html#13501" class="Bound">𝓤</a> <a id="13503" class="Symbol">:</a> <a id="13505" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13513" class="Symbol">}</a> <a id="13515" class="Keyword">where</a>

 <a id="13523" href="Prelude.Preliminaries.html#13523" class="Function Operator">∣_∣</a> <a id="13527" href="Prelude.Preliminaries.html#13527" class="Function">fst</a> <a id="13531" class="Symbol">:</a> <a id="13533" class="Symbol">{</a><a id="13534" href="Prelude.Preliminaries.html#13534" class="Bound">X</a> <a id="13536" class="Symbol">:</a> <a id="13538" href="Prelude.Preliminaries.html#13501" class="Bound">𝓤</a> <a id="13540" href="Universes.html#403" class="Function Operator">̇</a> <a id="13542" class="Symbol">}{</a><a id="13544" href="Prelude.Preliminaries.html#13544" class="Bound">Y</a> <a id="13546" class="Symbol">:</a> <a id="13548" href="Prelude.Preliminaries.html#13534" class="Bound">X</a> <a id="13550" class="Symbol">→</a> <a id="13552" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13554" href="Universes.html#403" class="Function Operator">̇</a><a id="13555" class="Symbol">}</a> <a id="13557" class="Symbol">→</a> <a id="13559" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13561" href="Prelude.Preliminaries.html#13544" class="Bound">Y</a> <a id="13563" class="Symbol">→</a> <a id="13565" href="Prelude.Preliminaries.html#13534" class="Bound">X</a>
 <a id="13568" href="Prelude.Preliminaries.html#13523" class="Function Operator">∣</a> <a id="13570" href="Prelude.Preliminaries.html#13570" class="Bound">x</a> <a id="13572" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="13574" href="Prelude.Preliminaries.html#13574" class="Bound">y</a> <a id="13576" href="Prelude.Preliminaries.html#13523" class="Function Operator">∣</a> <a id="13578" class="Symbol">=</a> <a id="13580" href="Prelude.Preliminaries.html#13570" class="Bound">x</a>
 <a id="13583" href="Prelude.Preliminaries.html#13527" class="Function">fst</a> <a id="13587" class="Symbol">(</a><a id="13588" href="Prelude.Preliminaries.html#13588" class="Bound">x</a> <a id="13590" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="13592" href="Prelude.Preliminaries.html#13592" class="Bound">y</a><a id="13593" class="Symbol">)</a> <a id="13595" class="Symbol">=</a> <a id="13597" href="Prelude.Preliminaries.html#13588" class="Bound">x</a>

 <a id="13601" href="Prelude.Preliminaries.html#13601" class="Function Operator">∥_∥</a> <a id="13605" href="Prelude.Preliminaries.html#13605" class="Function">snd</a> <a id="13609" class="Symbol">:</a> <a id="13611" class="Symbol">{</a><a id="13612" href="Prelude.Preliminaries.html#13612" class="Bound">X</a> <a id="13614" class="Symbol">:</a> <a id="13616" href="Prelude.Preliminaries.html#13501" class="Bound">𝓤</a> <a id="13618" href="Universes.html#403" class="Function Operator">̇</a> <a id="13620" class="Symbol">}{</a><a id="13622" href="Prelude.Preliminaries.html#13622" class="Bound">Y</a> <a id="13624" class="Symbol">:</a> <a id="13626" href="Prelude.Preliminaries.html#13612" class="Bound">X</a> <a id="13628" class="Symbol">→</a> <a id="13630" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13632" href="Universes.html#403" class="Function Operator">̇</a> <a id="13634" class="Symbol">}</a> <a id="13636" class="Symbol">→</a> <a id="13638" class="Symbol">(</a><a id="13639" href="Prelude.Preliminaries.html#13639" class="Bound">z</a> <a id="13641" class="Symbol">:</a> <a id="13643" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13645" href="Prelude.Preliminaries.html#13622" class="Bound">Y</a><a id="13646" class="Symbol">)</a> <a id="13648" class="Symbol">→</a> <a id="13650" href="Prelude.Preliminaries.html#13622" class="Bound">Y</a> <a id="13652" class="Symbol">(</a><a id="13653" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13657" href="Prelude.Preliminaries.html#13639" class="Bound">z</a><a id="13658" class="Symbol">)</a>
 <a id="13661" href="Prelude.Preliminaries.html#13601" class="Function Operator">∥</a> <a id="13663" href="Prelude.Preliminaries.html#13663" class="Bound">x</a> <a id="13665" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="13667" href="Prelude.Preliminaries.html#13667" class="Bound">y</a> <a id="13669" href="Prelude.Preliminaries.html#13601" class="Function Operator">∥</a> <a id="13671" class="Symbol">=</a> <a id="13673" href="Prelude.Preliminaries.html#13667" class="Bound">y</a>
 <a id="13676" href="Prelude.Preliminaries.html#13605" class="Function">snd</a> <a id="13680" class="Symbol">(</a><a id="13681" href="Prelude.Preliminaries.html#13681" class="Bound">x</a> <a id="13683" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="13685" href="Prelude.Preliminaries.html#13685" class="Bound">y</a><a id="13686" class="Symbol">)</a> <a id="13688" class="Symbol">=</a> <a id="13690" href="Prelude.Preliminaries.html#13685" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="13967" class="Keyword">module</a> <a id="hide-pi"></a><a id="13974" href="Prelude.Preliminaries.html#13974" class="Module">hide-pi</a> <a id="13982" class="Symbol">{</a><a id="13983" href="Prelude.Preliminaries.html#13983" class="Bound">𝓤</a> <a id="13985" href="Prelude.Preliminaries.html#13985" class="Bound">𝓦</a> <a id="13987" class="Symbol">:</a> <a id="13989" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13997" class="Symbol">}</a> <a id="13999" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14007" href="Prelude.Preliminaries.html#14007" class="Function">Π</a> <a id="14009" class="Symbol">:</a> <a id="14011" class="Symbol">{</a><a id="14012" href="Prelude.Preliminaries.html#14012" class="Bound">X</a> <a id="14014" class="Symbol">:</a> <a id="14016" href="Prelude.Preliminaries.html#13983" class="Bound">𝓤</a> <a id="14018" href="Universes.html#403" class="Function Operator">̇</a> <a id="14020" class="Symbol">}</a> <a id="14022" class="Symbol">(</a><a id="14023" href="Prelude.Preliminaries.html#14023" class="Bound">A</a> <a id="14025" class="Symbol">:</a> <a id="14027" href="Prelude.Preliminaries.html#14012" class="Bound">X</a> <a id="14029" class="Symbol">→</a> <a id="14031" href="Prelude.Preliminaries.html#13985" class="Bound">𝓦</a> <a id="14033" href="Universes.html#403" class="Function Operator">̇</a> <a id="14035" class="Symbol">)</a> <a id="14037" class="Symbol">→</a> <a id="14039" href="Prelude.Preliminaries.html#13983" class="Bound">𝓤</a> <a id="14041" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14043" href="Prelude.Preliminaries.html#13985" class="Bound">𝓦</a> <a id="14045" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14048" href="Prelude.Preliminaries.html#14007" class="Function">Π</a> <a id="14050" class="Symbol">{</a><a id="14051" href="Prelude.Preliminaries.html#14051" class="Bound">X</a><a id="14052" class="Symbol">}</a> <a id="14054" href="Prelude.Preliminaries.html#14054" class="Bound">A</a> <a id="14056" class="Symbol">=</a> <a id="14058" class="Symbol">(</a><a id="14059" href="Prelude.Preliminaries.html#14059" class="Bound">x</a> <a id="14061" class="Symbol">:</a> <a id="14063" href="Prelude.Preliminaries.html#14051" class="Bound">X</a><a id="14064" class="Symbol">)</a> <a id="14066" class="Symbol">→</a> <a id="14068" href="Prelude.Preliminaries.html#14054" class="Bound">A</a> <a id="14070" href="Prelude.Preliminaries.html#14059" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14074" href="Prelude.Preliminaries.html#14074" class="Function">-Π</a> <a id="14077" class="Symbol">:</a> <a id="14079" class="Symbol">(</a><a id="14080" href="Prelude.Preliminaries.html#14080" class="Bound">X</a> <a id="14082" class="Symbol">:</a> <a id="14084" href="Prelude.Preliminaries.html#13983" class="Bound">𝓤</a> <a id="14086" href="Universes.html#403" class="Function Operator">̇</a> <a id="14088" class="Symbol">)(</a><a id="14090" href="Prelude.Preliminaries.html#14090" class="Bound">Y</a> <a id="14092" class="Symbol">:</a> <a id="14094" href="Prelude.Preliminaries.html#14080" class="Bound">X</a> <a id="14096" class="Symbol">→</a> <a id="14098" href="Prelude.Preliminaries.html#13985" class="Bound">𝓦</a> <a id="14100" href="Universes.html#403" class="Function Operator">̇</a> <a id="14102" class="Symbol">)</a> <a id="14104" class="Symbol">→</a> <a id="14106" href="Prelude.Preliminaries.html#13983" class="Bound">𝓤</a> <a id="14108" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14110" href="Prelude.Preliminaries.html#13985" class="Bound">𝓦</a> <a id="14112" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14115" href="Prelude.Preliminaries.html#14074" class="Function">-Π</a> <a id="14118" href="Prelude.Preliminaries.html#14118" class="Bound">X</a> <a id="14120" href="Prelude.Preliminaries.html#14120" class="Bound">Y</a> <a id="14122" class="Symbol">=</a> <a id="14124" href="Prelude.Preliminaries.html#14007" class="Function">Π</a> <a id="14126" href="Prelude.Preliminaries.html#14120" class="Bound">Y</a>

 <a id="14130" class="Keyword">infixr</a> <a id="14137" class="Number">-1</a> <a id="14140" href="Prelude.Preliminaries.html#14074" class="Function">-Π</a>
 <a id="14144" class="Keyword">syntax</a> <a id="14151" href="Prelude.Preliminaries.html#14074" class="Function">-Π</a> <a id="14154" class="Bound">A</a> <a id="14156" class="Symbol">(λ</a> <a id="14159" class="Bound">x</a> <a id="14161" class="Symbol">→</a> <a id="14163" class="Bound">b</a><a id="14164" class="Symbol">)</a> <a id="14166" class="Symbol">=</a> <a id="14168" class="Function">Π</a> <a id="14170" class="Bound">x</a> <a id="14172" class="Function">꞉</a> <a id="14174" class="Bound">A</a> <a id="14176" class="Function">,</a> <a id="14178" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14468" class="Keyword">open</a> <a id="14473" class="Keyword">import</a> <a id="14480" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14491" class="Keyword">renaming</a> <a id="14500" class="Symbol">(</a><a id="14501" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14505" class="Symbol">to</a> <a id="14508" class="Keyword">infixr</a> <a id="14515" class="Number">50</a> <a id="_,_"></a><a id="14518" href="Prelude.Preliminaries.html#14518" class="InductiveConstructor Operator">_,_</a><a id="14521" class="Symbol">)</a> <a id="14523" class="Keyword">public</a>
<a id="14530" class="Keyword">open</a> <a id="14535" class="Keyword">import</a> <a id="14542" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14551" class="Keyword">using</a> <a id="14557" class="Symbol">(</a><a id="14558" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14561" class="Symbol">;</a> <a id="14563" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14566" class="Symbol">;</a> <a id="14568" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14571" class="Symbol">;</a> <a id="14573" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14575" class="Symbol">;</a> <a id="14577" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14578" class="Symbol">)</a> <a id="14580" class="Keyword">public</a>


<a id="14589" class="Keyword">module</a> <a id="14596" href="Prelude.Preliminaries.html#14596" class="Module">_</a> <a id="14598" class="Symbol">{</a><a id="14599" href="Prelude.Preliminaries.html#14599" class="Bound">𝓨</a> <a id="14601" href="Prelude.Preliminaries.html#14601" class="Bound">𝓩</a> <a id="14603" class="Symbol">:</a> <a id="14605" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14613" class="Symbol">}{</a><a id="14615" href="Prelude.Preliminaries.html#14615" class="Bound">I</a> <a id="14617" class="Symbol">:</a> <a id="14619" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14621" href="Universes.html#403" class="Function Operator">̇</a><a id="14622" class="Symbol">}{</a><a id="14624" href="Prelude.Preliminaries.html#14624" class="Bound">B</a> <a id="14626" class="Symbol">:</a> <a id="14628" href="Prelude.Preliminaries.html#14615" class="Bound">I</a> <a id="14630" class="Symbol">→</a> <a id="14632" href="Prelude.Preliminaries.html#14599" class="Bound">𝓨</a> <a id="14634" href="Universes.html#403" class="Function Operator">̇</a><a id="14635" class="Symbol">}{</a><a id="14637" href="Prelude.Preliminaries.html#14637" class="Bound">C</a> <a id="14639" class="Symbol">:</a> <a id="14641" href="Prelude.Preliminaries.html#14615" class="Bound">I</a> <a id="14643" class="Symbol">→</a> <a id="14645" href="Prelude.Preliminaries.html#14601" class="Bound">𝓩</a> <a id="14647" href="Universes.html#403" class="Function Operator">̇</a><a id="14648" class="Symbol">}</a> <a id="14650" class="Keyword">where</a>
 <a id="14657" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14680" href="Prelude.Preliminaries.html#14680" class="Function">zip</a> <a id="14684" class="Symbol">:</a> <a id="14686" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14688" href="Prelude.Preliminaries.html#14624" class="Bound">B</a> <a id="14690" class="Symbol">→</a> <a id="14692" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14694" href="Prelude.Preliminaries.html#14637" class="Bound">C</a> <a id="14696" class="Symbol">→</a> <a id="14698" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14700" class="Symbol">(λ</a> <a id="14703" href="Prelude.Preliminaries.html#14703" class="Bound">i</a> <a id="14705" class="Symbol">→</a> <a id="14707" class="Symbol">(</a><a id="14708" href="Prelude.Preliminaries.html#14624" class="Bound">B</a> <a id="14710" href="Prelude.Preliminaries.html#14703" class="Bound">i</a><a id="14711" class="Symbol">)</a> <a id="14713" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14715" class="Symbol">(</a><a id="14716" href="Prelude.Preliminaries.html#14637" class="Bound">C</a> <a id="14718" href="Prelude.Preliminaries.html#14703" class="Bound">i</a><a id="14719" class="Symbol">))</a>
 <a id="14723" href="Prelude.Preliminaries.html#14680" class="Function">zip</a> <a id="14727" href="Prelude.Preliminaries.html#14727" class="Bound">f</a> <a id="14729" href="Prelude.Preliminaries.html#14729" class="Bound">a</a> <a id="14731" class="Symbol">=</a> <a id="14733" class="Symbol">λ</a> <a id="14735" href="Prelude.Preliminaries.html#14735" class="Bound">i</a> <a id="14737" class="Symbol">→</a> <a id="14739" class="Symbol">(</a><a id="14740" href="Prelude.Preliminaries.html#14727" class="Bound">f</a> <a id="14742" href="Prelude.Preliminaries.html#14735" class="Bound">i</a> <a id="14744" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="14746" href="Prelude.Preliminaries.html#14729" class="Bound">a</a> <a id="14748" href="Prelude.Preliminaries.html#14735" class="Bound">i</a><a id="14749" class="Symbol">)</a>

 <a id="14753" href="Prelude.Preliminaries.html#14753" class="Function">eval</a> <a id="14758" class="Symbol">:</a> <a id="14760" class="Symbol">{</a><a id="14761" href="Prelude.Preliminaries.html#14761" class="Bound">Y</a> <a id="14763" class="Symbol">:</a> <a id="14765" href="Prelude.Preliminaries.html#14599" class="Bound">𝓨</a> <a id="14767" href="Universes.html#403" class="Function Operator">̇</a><a id="14768" class="Symbol">}{</a><a id="14770" href="Prelude.Preliminaries.html#14770" class="Bound">Z</a> <a id="14772" class="Symbol">:</a> <a id="14774" href="Prelude.Preliminaries.html#14601" class="Bound">𝓩</a> <a id="14776" href="Universes.html#403" class="Function Operator">̇</a><a id="14777" class="Symbol">}</a> <a id="14779" class="Symbol">→</a> <a id="14781" class="Symbol">((</a><a id="14783" href="Prelude.Preliminaries.html#14761" class="Bound">Y</a> <a id="14785" class="Symbol">→</a> <a id="14787" href="Prelude.Preliminaries.html#14770" class="Bound">Z</a><a id="14788" class="Symbol">)</a> <a id="14790" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14792" href="Prelude.Preliminaries.html#14761" class="Bound">Y</a><a id="14793" class="Symbol">)</a> <a id="14795" class="Symbol">→</a> <a id="14797" href="Prelude.Preliminaries.html#14770" class="Bound">Z</a>
 <a id="14800" href="Prelude.Preliminaries.html#14753" class="Function">eval</a> <a id="14805" class="Symbol">(</a><a id="14806" href="Prelude.Preliminaries.html#14806" class="Bound">f</a> <a id="14808" href="Prelude.Preliminaries.html#13006" class="InductiveConstructor Operator">,</a> <a id="14810" href="Prelude.Preliminaries.html#14810" class="Bound">a</a><a id="14811" class="Symbol">)</a> <a id="14813" class="Symbol">=</a> <a id="14815" href="Prelude.Preliminaries.html#14806" class="Bound">f</a> <a id="14817" href="Prelude.Preliminaries.html#14810" class="Bound">a</a>

<a id="14820" class="Keyword">module</a> <a id="14827" href="Prelude.Preliminaries.html#14827" class="Module">_</a> <a id="14829" class="Symbol">{</a><a id="14830" href="Prelude.Preliminaries.html#14830" class="Bound">𝓨</a> <a id="14832" class="Symbol">:</a> <a id="14834" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14842" class="Symbol">}{</a><a id="14844" href="Prelude.Preliminaries.html#14844" class="Bound">I</a> <a id="14846" href="Prelude.Preliminaries.html#14846" class="Bound">J</a> <a id="14848" class="Symbol">:</a> <a id="14850" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14852" href="Universes.html#403" class="Function Operator">̇</a><a id="14853" class="Symbol">}{</a><a id="14855" href="Prelude.Preliminaries.html#14855" class="Bound">B</a> <a id="14857" class="Symbol">:</a> <a id="14859" href="Prelude.Preliminaries.html#14844" class="Bound">I</a> <a id="14861" class="Symbol">→</a> <a id="14863" href="Prelude.Preliminaries.html#14830" class="Bound">𝓨</a> <a id="14865" href="Universes.html#403" class="Function Operator">̇</a><a id="14866" class="Symbol">}</a> <a id="14868" class="Keyword">where</a>

 <a id="14876" href="Prelude.Preliminaries.html#14876" class="Function">dapp</a> <a id="14881" class="Symbol">:</a> <a id="14883" class="Symbol">(∀</a> <a id="14886" href="Prelude.Preliminaries.html#14886" class="Bound">i</a> <a id="14888" class="Symbol">→</a> <a id="14890" class="Symbol">(</a><a id="14891" href="Prelude.Preliminaries.html#14846" class="Bound">J</a> <a id="14893" class="Symbol">→</a> <a id="14895" class="Symbol">(</a><a id="14896" href="Prelude.Preliminaries.html#14855" class="Bound">B</a> <a id="14898" href="Prelude.Preliminaries.html#14886" class="Bound">i</a><a id="14899" class="Symbol">))</a> <a id="14902" class="Symbol">→</a> <a id="14904" class="Symbol">(</a><a id="14905" href="Prelude.Preliminaries.html#14855" class="Bound">B</a> <a id="14907" href="Prelude.Preliminaries.html#14886" class="Bound">i</a><a id="14908" class="Symbol">))</a> <a id="14911" class="Symbol">→</a> <a id="14913" class="Symbol">(∀</a> <a id="14916" href="Prelude.Preliminaries.html#14916" class="Bound">i</a> <a id="14918" class="Symbol">→</a> <a id="14920" class="Symbol">(</a><a id="14921" href="Prelude.Preliminaries.html#14846" class="Bound">J</a> <a id="14923" class="Symbol">→</a> <a id="14925" class="Symbol">(</a><a id="14926" href="Prelude.Preliminaries.html#14855" class="Bound">B</a> <a id="14928" href="Prelude.Preliminaries.html#14916" class="Bound">i</a><a id="14929" class="Symbol">)))</a> <a id="14933" class="Symbol">→</a> <a id="14935" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14937" href="Prelude.Preliminaries.html#14855" class="Bound">B</a>
 <a id="14940" href="Prelude.Preliminaries.html#14876" class="Function">dapp</a> <a id="14945" href="Prelude.Preliminaries.html#14945" class="Bound">f</a> <a id="14947" href="Prelude.Preliminaries.html#14947" class="Bound">a</a> <a id="14949" class="Symbol">=</a> <a id="14951" class="Symbol">λ</a> <a id="14953" href="Prelude.Preliminaries.html#14953" class="Bound">i</a> <a id="14955" class="Symbol">→</a> <a id="14957" class="Symbol">(</a><a id="14958" href="Prelude.Preliminaries.html#14945" class="Bound">f</a> <a id="14960" href="Prelude.Preliminaries.html#14953" class="Bound">i</a><a id="14961" class="Symbol">)</a> <a id="14963" class="Symbol">(</a><a id="14964" href="Prelude.Preliminaries.html#14947" class="Bound">a</a> <a id="14966" href="Prelude.Preliminaries.html#14953" class="Bound">i</a><a id="14967" class="Symbol">)</a>

</pre>

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<p></p>
<p></p>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

