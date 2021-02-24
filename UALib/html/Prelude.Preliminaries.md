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
REF: Parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

### <a id="preliminaries">Preliminaries</a>

This section describes the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

**Notation**. Here are some acronyms that we use frequently.

  * [MHE][] = [Martin Hötzel Escardó](https://www.cs.bham.ac.uk/~mhe/)
  * [MLTT][] = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

#### <a id="options">Options</a>

All Agda programs begin by setting some options and by importing from existing libraries (in our case, the [Type Topology][] library by [MHE][]). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

<pre class="Agda">

<a id="1198" class="Symbol">{-#</a> <a id="1202" class="Keyword">OPTIONS</a> <a id="1210" class="Pragma">--without-K</a> <a id="1222" class="Pragma">--exact-split</a> <a id="1236" class="Pragma">--safe</a> <a id="1243" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda assumes when type-checking the program to verify its correctness.

* `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`; we would use the following `OPTIONS` line in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

but this is never done in publicly released versions of the UALib.





#### <a id="modules">Modules</a>

The `OPTIONS` line is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="3082" class="Keyword">module</a> <a id="3089" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="3111" class="Keyword">where</a>

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

<a id="5406" class="Keyword">open</a> <a id="5411" class="Keyword">import</a> <a id="5418" href="Universes.html" class="Module">Universes</a> <a id="5428" class="Keyword">public</a>

</pre>

Escardó's Universe module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="5693" class="Keyword">variable</a>
 <a id="5703" href="Prelude.Preliminaries.html#5703" class="Generalizable">𝓞</a> <a id="5705" class="Symbol">:</a> <a id="5707" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

(The first three import lines have to be commented out because we will actually redefine the given types for pedagogical purposes in the next couple of modules.)

<pre class="Agda">

<a id="6917" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6991" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="7025" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="7084" class="Keyword">open</a> <a id="7089" class="Keyword">import</a> <a id="7096" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7105" class="Keyword">using</a> <a id="7111" class="Symbol">(</a><a id="7112" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7115" class="Symbol">;</a> <a id="7117" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7123" class="Symbol">;</a> <a id="7125" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7133" class="Symbol">;</a> <a id="7135" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7144" class="Symbol">;</a> <a id="7146" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7152" class="Symbol">;</a> <a id="7154" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7156" class="Symbol">;</a> <a id="7158" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7186" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7187" class="Symbol">;</a> <a id="7189" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7191" class="Symbol">;</a> <a id="7193" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7196" class="Symbol">;</a> <a id="7198" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7201" class="Symbol">;</a> <a id="7203" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7204" class="Symbol">;</a> <a id="7206" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7207" class="Symbol">;</a> <a id="7209" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7210" class="Symbol">;</a> <a id="7212" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7215" class="Symbol">;</a> <a id="7217" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7231" class="Symbol">;</a> <a id="7233" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7247" class="Symbol">;</a> <a id="7249" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7251" class="Symbol">;</a> <a id="7253" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7256" class="Symbol">;</a> <a id="7258" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7260" class="Symbol">)</a>

<a id="7263" class="Keyword">open</a> <a id="7268" class="Keyword">import</a> <a id="7275" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7292" class="Keyword">using</a> <a id="7298" class="Symbol">(</a><a id="7299" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7307" class="Symbol">;</a> <a id="7309" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7316" class="Symbol">;</a> <a id="7318" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7328" class="Symbol">)</a>

<a id="7331" class="Keyword">open</a> <a id="7336" class="Keyword">import</a> <a id="7343" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7369" class="Keyword">using</a> <a id="7375" class="Symbol">(</a><a id="7376" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7382" class="Symbol">;</a> <a id="7384" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7398" class="Symbol">;</a> <a id="7400" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7407" class="Symbol">;</a>
 <a id="7410" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7422" class="Symbol">;</a> <a id="7424" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7439" class="Symbol">;</a> <a id="7441" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7448" class="Symbol">;</a> <a id="7450" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7460" class="Symbol">;</a> <a id="7462" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7476" class="Symbol">;</a>
 <a id="7479" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7510" class="Symbol">;</a> <a id="7512" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7515" class="Symbol">;</a> <a id="7517" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7520" class="Symbol">;</a> <a id="7522" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7539" class="Symbol">;</a> <a id="7541" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7558" class="Symbol">;</a>
 <a id="7561" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7610" class="Symbol">)</a>

<a id="7613" class="Keyword">open</a> <a id="7618" class="Keyword">import</a> <a id="7625" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7638" class="Keyword">renaming</a> <a id="7647" class="Symbol">(</a><a id="7648" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7652" class="Symbol">to</a> <a id="_∈_"></a><a id="7655" href="Prelude.Preliminaries.html#7655" class="Function Operator">_∈₀_</a><a id="7659" class="Symbol">;</a> <a id="7661" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7665" class="Symbol">to</a> <a id="_⊆_"></a><a id="7668" href="Prelude.Preliminaries.html#7668" class="Function Operator">_⊆₀_</a><a id="7672" class="Symbol">;</a> <a id="7674" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7692" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7695" href="Prelude.Preliminaries.html#7695" class="Function">∈₀-is-subsingleton</a><a id="7713" class="Symbol">)</a>
 <a id="7716" class="Keyword">using</a> <a id="7722" class="Symbol">(</a><a id="7723" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7724" class="Symbol">;</a> <a id="7726" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7747" class="Symbol">;</a> <a id="7749" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7768" class="Symbol">;</a> <a id="7770" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7792" class="Symbol">;</a> <a id="7794" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7801" class="Symbol">;</a> <a id="7803" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7809" class="Symbol">;</a> <a id="7811" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7812" class="Symbol">)</a>

<a id="7815" class="Keyword">open</a> <a id="7820" class="Keyword">import</a> <a id="7827" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7842" class="Keyword">using</a> <a id="7848" class="Symbol">(</a><a id="7849" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7852" class="Symbol">;</a> <a id="7854" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7858" class="Symbol">;</a> <a id="7860" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7877" class="Symbol">;</a> <a id="7879" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7891" class="Symbol">;</a> <a id="7893" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7906" class="Symbol">;</a> <a id="7908" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7919" class="Symbol">;</a>
 <a id="7922" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7928" class="Symbol">;</a> <a id="7930" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7933" class="Symbol">;</a> <a id="7935" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="7962" class="Symbol">;</a> <a id="7964" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7981" class="Symbol">;</a> <a id="7983" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="8000" class="Symbol">;</a> <a id="8002" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="8017" class="Symbol">)</a>

<a id="8020" class="Keyword">open</a> <a id="8025" class="Keyword">import</a> <a id="8032" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="8053" class="Keyword">using</a> <a id="8059" class="Symbol">(</a><a id="8060" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="8072" class="Symbol">)</a>

<a id="8075" class="Keyword">open</a> <a id="8080" class="Keyword">import</a> <a id="8087" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8108" class="Keyword">using</a> <a id="8114" class="Symbol">(</a><a id="8115" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8117" class="Symbol">;</a> <a id="8119" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8122" class="Symbol">)</a>

<a id="8125" class="Keyword">open</a> <a id="8130" class="Keyword">import</a> <a id="8137" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8165" class="Keyword">using</a> <a id="8171" class="Symbol">(</a><a id="8172" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8175" class="Symbol">;</a> <a id="8177" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8183" class="Symbol">;</a> <a id="8185" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8206" class="Symbol">;</a>
 <a id="8209" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8231" class="Symbol">;</a> <a id="8233" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8238" class="Symbol">;</a> <a id="8240" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8258" class="Symbol">;</a> <a id="8260" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8267" class="Symbol">)</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.





#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from MHE's \href{https://github.com/martinescardo/TypeTopology}{Type Topology} library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

\mhe has authored an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}. We highly recommend Martin's notes to anyone wanting more details than we provide here about [MLTT][] and the Univalent Foundations/HoTT extensions thereof.

Following MHE, we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module MHE defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).<sup>1</sup>

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.

Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and MHE) denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and MHE/UALib notation.

```agda
Agda              MHE and UALib
====              ==============
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

To justify the introduction of this somewhat nonstandard notation for universe levels, MHE points out that the Agda library uses `Level` for universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for precisely this purpose.





#### <a id="dependent-pair-type">Dependent pair type</a>

Given universes 𝓤 and 𝓥, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the **Sigma type** (or **dependent pair type**), denoted by `Σ(x ꞉ X), Y x`, generalizes the Cartesian product `X × Y` by allowing the type `Y x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, `Σ(x ꞉ X), Y x` is inhabited by the pairs `(x , y)` such that `x : X` and `y : Y x`.

In the [Type Topology][] library, the dependent pair type is defined in a stardard way (cf. the [Agda Standard Library][]) as a record type.

<pre class="Agda">

<a id="11821" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11828" href="Prelude.Preliminaries.html#11828" class="Module">hide-sigma</a> <a id="11839" class="Keyword">where</a>

 <a id="11847" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11854" href="Prelude.Preliminaries.html#11854" class="Record">Σ</a> <a id="11856" class="Symbol">{</a><a id="11857" href="Prelude.Preliminaries.html#11857" class="Bound">𝓤</a> <a id="11859" href="Prelude.Preliminaries.html#11859" class="Bound">𝓥</a><a id="11860" class="Symbol">}</a> <a id="11862" class="Symbol">{</a><a id="11863" href="Prelude.Preliminaries.html#11863" class="Bound">X</a> <a id="11865" class="Symbol">:</a> <a id="11867" href="Prelude.Preliminaries.html#11857" class="Bound">𝓤</a> <a id="11869" href="Universes.html#403" class="Function Operator">̇</a> <a id="11871" class="Symbol">}</a> <a id="11873" class="Symbol">(</a><a id="11874" href="Prelude.Preliminaries.html#11874" class="Bound">Y</a> <a id="11876" class="Symbol">:</a> <a id="11878" href="Prelude.Preliminaries.html#11863" class="Bound">X</a> <a id="11880" class="Symbol">→</a> <a id="11882" href="Prelude.Preliminaries.html#11859" class="Bound">𝓥</a> <a id="11884" href="Universes.html#403" class="Function Operator">̇</a> <a id="11886" class="Symbol">)</a> <a id="11888" class="Symbol">:</a> <a id="11890" href="Prelude.Preliminaries.html#11857" class="Bound">𝓤</a> <a id="11892" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11894" href="Prelude.Preliminaries.html#11859" class="Bound">𝓥</a> <a id="11896" href="Universes.html#403" class="Function Operator">̇</a>  <a id="11899" class="Keyword">where</a>
  <a id="11907" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="11919" href="Prelude.Preliminaries.html#11919" class="InductiveConstructor Operator">_,_</a>
  <a id="11925" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="11934" href="Prelude.Preliminaries.html#11934" class="Field">pr₁</a> <a id="11938" class="Symbol">:</a> <a id="11940" href="Prelude.Preliminaries.html#11863" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="11945" href="Prelude.Preliminaries.html#11945" class="Field">pr₂</a> <a id="11949" class="Symbol">:</a> <a id="11951" href="Prelude.Preliminaries.html#11874" class="Bound">Y</a> <a id="11953" href="Prelude.Preliminaries.html#11934" class="Field">pr₁</a>

 <a id="11959" class="Keyword">infixr</a> <a id="11966" class="Number">50</a> <a id="11969" href="Prelude.Preliminaries.html#11919" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12306" href="Prelude.Preliminaries.html#12306" class="Function">-Σ</a> <a id="12309" class="Symbol">:</a> <a id="12311" class="Symbol">{</a><a id="12312" href="Prelude.Preliminaries.html#12312" class="Bound">𝓤</a> <a id="12314" href="Prelude.Preliminaries.html#12314" class="Bound">𝓥</a> <a id="12316" class="Symbol">:</a> <a id="12318" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12326" class="Symbol">}</a> <a id="12328" class="Symbol">(</a><a id="12329" href="Prelude.Preliminaries.html#12329" class="Bound">X</a> <a id="12331" class="Symbol">:</a> <a id="12333" href="Prelude.Preliminaries.html#12312" class="Bound">𝓤</a> <a id="12335" href="Universes.html#403" class="Function Operator">̇</a> <a id="12337" class="Symbol">)</a> <a id="12339" class="Symbol">(</a><a id="12340" href="Prelude.Preliminaries.html#12340" class="Bound">Y</a> <a id="12342" class="Symbol">:</a> <a id="12344" href="Prelude.Preliminaries.html#12329" class="Bound">X</a> <a id="12346" class="Symbol">→</a> <a id="12348" href="Prelude.Preliminaries.html#12314" class="Bound">𝓥</a> <a id="12350" href="Universes.html#403" class="Function Operator">̇</a> <a id="12352" class="Symbol">)</a> <a id="12354" class="Symbol">→</a> <a id="12356" href="Prelude.Preliminaries.html#12312" class="Bound">𝓤</a> <a id="12358" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12360" href="Prelude.Preliminaries.html#12314" class="Bound">𝓥</a> <a id="12362" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12365" href="Prelude.Preliminaries.html#12306" class="Function">-Σ</a> <a id="12368" href="Prelude.Preliminaries.html#12368" class="Bound">X</a> <a id="12370" href="Prelude.Preliminaries.html#12370" class="Bound">Y</a> <a id="12372" class="Symbol">=</a> <a id="12374" href="Prelude.Preliminaries.html#11854" class="Record">Σ</a> <a id="12376" href="Prelude.Preliminaries.html#12370" class="Bound">Y</a>

 <a id="12380" class="Keyword">syntax</a> <a id="12387" href="Prelude.Preliminaries.html#12306" class="Function">-Σ</a> <a id="12390" class="Bound">X</a> <a id="12392" class="Symbol">(λ</a> <a id="12395" class="Bound">x</a> <a id="12397" class="Symbol">→</a> <a id="12399" class="Bound">Y</a><a id="12400" class="Symbol">)</a> <a id="12402" class="Symbol">=</a> <a id="12404" class="Function">Σ</a> <a id="12406" class="Bound">x</a> <a id="12408" class="Function">꞉</a> <a id="12410" class="Bound">X</a> <a id="12412" class="Function">,</a> <a id="12414" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12787" href="Prelude.Preliminaries.html#12787" class="Function Operator">_×_</a> <a id="12791" class="Symbol">:</a> <a id="12793" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12795" href="Universes.html#403" class="Function Operator">̇</a> <a id="12797" class="Symbol">→</a> <a id="12799" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12801" href="Universes.html#403" class="Function Operator">̇</a> <a id="12803" class="Symbol">→</a> <a id="12805" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12807" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12809" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12811" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12814" href="Prelude.Preliminaries.html#12814" class="Bound">X</a> <a id="12816" href="Prelude.Preliminaries.html#12787" class="Function Operator">×</a> <a id="12818" href="Prelude.Preliminaries.html#12818" class="Bound">Y</a> <a id="12820" class="Symbol">=</a> <a id="12822" href="Prelude.Preliminaries.html#12306" class="Function">Σ</a> <a id="12824" href="Prelude.Preliminaries.html#12824" class="Bound">x</a> <a id="12826" href="Prelude.Preliminaries.html#12306" class="Function">꞉</a> <a id="12828" href="Prelude.Preliminaries.html#12814" class="Bound">X</a> <a id="12830" href="Prelude.Preliminaries.html#12306" class="Function">,</a> <a id="12832" href="Prelude.Preliminaries.html#12818" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13042" class="Keyword">open</a> <a id="13047" class="Keyword">import</a> <a id="13054" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13065" class="Keyword">renaming</a> <a id="13074" class="Symbol">(</a><a id="13075" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13079" class="Symbol">to</a> <a id="13082" class="Keyword">infixr</a> <a id="13089" class="Number">50</a> <a id="_,_"></a><a id="13092" href="Prelude.Preliminaries.html#13092" class="InductiveConstructor Operator">_,_</a><a id="13095" class="Symbol">)</a>
<a id="13097" class="Keyword">open</a> <a id="13102" class="Keyword">import</a> <a id="13109" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13118" class="Keyword">using</a> <a id="13124" class="Symbol">(</a><a id="13125" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13128" class="Symbol">;</a> <a id="13130" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13133" class="Symbol">;</a> <a id="13135" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13138" class="Symbol">;</a> <a id="13140" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13142" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13577" class="Keyword">module</a> <a id="13584" href="Prelude.Preliminaries.html#13584" class="Module">_</a> <a id="13586" class="Symbol">{</a><a id="13587" href="Prelude.Preliminaries.html#13587" class="Bound">𝓤</a> <a id="13589" class="Symbol">:</a> <a id="13591" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13599" class="Symbol">}</a> <a id="13601" class="Keyword">where</a>

 <a id="13609" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣_∣</a> <a id="13613" href="Prelude.Preliminaries.html#13613" class="Function">fst</a> <a id="13617" class="Symbol">:</a> <a id="13619" class="Symbol">{</a><a id="13620" href="Prelude.Preliminaries.html#13620" class="Bound">X</a> <a id="13622" class="Symbol">:</a> <a id="13624" href="Prelude.Preliminaries.html#13587" class="Bound">𝓤</a> <a id="13626" href="Universes.html#403" class="Function Operator">̇</a> <a id="13628" class="Symbol">}{</a><a id="13630" href="Prelude.Preliminaries.html#13630" class="Bound">Y</a> <a id="13632" class="Symbol">:</a> <a id="13634" href="Prelude.Preliminaries.html#13620" class="Bound">X</a> <a id="13636" class="Symbol">→</a> <a id="13638" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13640" href="Universes.html#403" class="Function Operator">̇</a><a id="13641" class="Symbol">}</a> <a id="13643" class="Symbol">→</a> <a id="13645" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13647" href="Prelude.Preliminaries.html#13630" class="Bound">Y</a> <a id="13649" class="Symbol">→</a> <a id="13651" href="Prelude.Preliminaries.html#13620" class="Bound">X</a>
 <a id="13654" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="13656" href="Prelude.Preliminaries.html#13656" class="Bound">x</a> <a id="13658" href="Prelude.Preliminaries.html#13092" class="InductiveConstructor Operator">,</a> <a id="13660" href="Prelude.Preliminaries.html#13660" class="Bound">y</a> <a id="13662" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="13664" class="Symbol">=</a> <a id="13666" href="Prelude.Preliminaries.html#13656" class="Bound">x</a>
 <a id="13669" href="Prelude.Preliminaries.html#13613" class="Function">fst</a> <a id="13673" class="Symbol">(</a><a id="13674" href="Prelude.Preliminaries.html#13674" class="Bound">x</a> <a id="13676" href="Prelude.Preliminaries.html#13092" class="InductiveConstructor Operator">,</a> <a id="13678" href="Prelude.Preliminaries.html#13678" class="Bound">y</a><a id="13679" class="Symbol">)</a> <a id="13681" class="Symbol">=</a> <a id="13683" href="Prelude.Preliminaries.html#13674" class="Bound">x</a>

 <a id="13687" href="Prelude.Preliminaries.html#13687" class="Function Operator">∥_∥</a> <a id="13691" href="Prelude.Preliminaries.html#13691" class="Function">snd</a> <a id="13695" class="Symbol">:</a> <a id="13697" class="Symbol">{</a><a id="13698" href="Prelude.Preliminaries.html#13698" class="Bound">X</a> <a id="13700" class="Symbol">:</a> <a id="13702" href="Prelude.Preliminaries.html#13587" class="Bound">𝓤</a> <a id="13704" href="Universes.html#403" class="Function Operator">̇</a> <a id="13706" class="Symbol">}{</a><a id="13708" href="Prelude.Preliminaries.html#13708" class="Bound">Y</a> <a id="13710" class="Symbol">:</a> <a id="13712" href="Prelude.Preliminaries.html#13698" class="Bound">X</a> <a id="13714" class="Symbol">→</a> <a id="13716" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13718" href="Universes.html#403" class="Function Operator">̇</a> <a id="13720" class="Symbol">}</a> <a id="13722" class="Symbol">→</a> <a id="13724" class="Symbol">(</a><a id="13725" href="Prelude.Preliminaries.html#13725" class="Bound">z</a> <a id="13727" class="Symbol">:</a> <a id="13729" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13731" href="Prelude.Preliminaries.html#13708" class="Bound">Y</a><a id="13732" class="Symbol">)</a> <a id="13734" class="Symbol">→</a> <a id="13736" href="Prelude.Preliminaries.html#13708" class="Bound">Y</a> <a id="13738" class="Symbol">(</a><a id="13739" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13743" href="Prelude.Preliminaries.html#13725" class="Bound">z</a><a id="13744" class="Symbol">)</a>
 <a id="13747" href="Prelude.Preliminaries.html#13687" class="Function Operator">∥</a> <a id="13749" href="Prelude.Preliminaries.html#13749" class="Bound">x</a> <a id="13751" href="Prelude.Preliminaries.html#13092" class="InductiveConstructor Operator">,</a> <a id="13753" href="Prelude.Preliminaries.html#13753" class="Bound">y</a> <a id="13755" href="Prelude.Preliminaries.html#13687" class="Function Operator">∥</a> <a id="13757" class="Symbol">=</a> <a id="13759" href="Prelude.Preliminaries.html#13753" class="Bound">y</a>
 <a id="13762" href="Prelude.Preliminaries.html#13691" class="Function">snd</a> <a id="13766" class="Symbol">(</a><a id="13767" href="Prelude.Preliminaries.html#13767" class="Bound">x</a> <a id="13769" href="Prelude.Preliminaries.html#13092" class="InductiveConstructor Operator">,</a> <a id="13771" href="Prelude.Preliminaries.html#13771" class="Bound">y</a><a id="13772" class="Symbol">)</a> <a id="13774" class="Symbol">=</a> <a id="13776" href="Prelude.Preliminaries.html#13771" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14045" class="Keyword">module</a> <a id="hide-pi"></a><a id="14052" href="Prelude.Preliminaries.html#14052" class="Module">hide-pi</a> <a id="14060" class="Symbol">{</a><a id="14061" href="Prelude.Preliminaries.html#14061" class="Bound">𝓤</a> <a id="14063" href="Prelude.Preliminaries.html#14063" class="Bound">𝓦</a> <a id="14065" class="Symbol">:</a> <a id="14067" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14075" class="Symbol">}</a> <a id="14077" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14085" href="Prelude.Preliminaries.html#14085" class="Function">Π</a> <a id="14087" class="Symbol">:</a> <a id="14089" class="Symbol">{</a><a id="14090" href="Prelude.Preliminaries.html#14090" class="Bound">X</a> <a id="14092" class="Symbol">:</a> <a id="14094" href="Prelude.Preliminaries.html#14061" class="Bound">𝓤</a> <a id="14096" href="Universes.html#403" class="Function Operator">̇</a> <a id="14098" class="Symbol">}</a> <a id="14100" class="Symbol">(</a><a id="14101" href="Prelude.Preliminaries.html#14101" class="Bound">A</a> <a id="14103" class="Symbol">:</a> <a id="14105" href="Prelude.Preliminaries.html#14090" class="Bound">X</a> <a id="14107" class="Symbol">→</a> <a id="14109" href="Prelude.Preliminaries.html#14063" class="Bound">𝓦</a> <a id="14111" href="Universes.html#403" class="Function Operator">̇</a> <a id="14113" class="Symbol">)</a> <a id="14115" class="Symbol">→</a> <a id="14117" href="Prelude.Preliminaries.html#14061" class="Bound">𝓤</a> <a id="14119" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14121" href="Prelude.Preliminaries.html#14063" class="Bound">𝓦</a> <a id="14123" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14126" href="Prelude.Preliminaries.html#14085" class="Function">Π</a> <a id="14128" class="Symbol">{</a><a id="14129" href="Prelude.Preliminaries.html#14129" class="Bound">X</a><a id="14130" class="Symbol">}</a> <a id="14132" href="Prelude.Preliminaries.html#14132" class="Bound">A</a> <a id="14134" class="Symbol">=</a> <a id="14136" class="Symbol">(</a><a id="14137" href="Prelude.Preliminaries.html#14137" class="Bound">x</a> <a id="14139" class="Symbol">:</a> <a id="14141" href="Prelude.Preliminaries.html#14129" class="Bound">X</a><a id="14142" class="Symbol">)</a> <a id="14144" class="Symbol">→</a> <a id="14146" href="Prelude.Preliminaries.html#14132" class="Bound">A</a> <a id="14148" href="Prelude.Preliminaries.html#14137" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14152" href="Prelude.Preliminaries.html#14152" class="Function">-Π</a> <a id="14155" class="Symbol">:</a> <a id="14157" class="Symbol">(</a><a id="14158" href="Prelude.Preliminaries.html#14158" class="Bound">X</a> <a id="14160" class="Symbol">:</a> <a id="14162" href="Prelude.Preliminaries.html#14061" class="Bound">𝓤</a> <a id="14164" href="Universes.html#403" class="Function Operator">̇</a> <a id="14166" class="Symbol">)(</a><a id="14168" href="Prelude.Preliminaries.html#14168" class="Bound">Y</a> <a id="14170" class="Symbol">:</a> <a id="14172" href="Prelude.Preliminaries.html#14158" class="Bound">X</a> <a id="14174" class="Symbol">→</a> <a id="14176" href="Prelude.Preliminaries.html#14063" class="Bound">𝓦</a> <a id="14178" href="Universes.html#403" class="Function Operator">̇</a> <a id="14180" class="Symbol">)</a> <a id="14182" class="Symbol">→</a> <a id="14184" href="Prelude.Preliminaries.html#14061" class="Bound">𝓤</a> <a id="14186" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14188" href="Prelude.Preliminaries.html#14063" class="Bound">𝓦</a> <a id="14190" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14193" href="Prelude.Preliminaries.html#14152" class="Function">-Π</a> <a id="14196" href="Prelude.Preliminaries.html#14196" class="Bound">X</a> <a id="14198" href="Prelude.Preliminaries.html#14198" class="Bound">Y</a> <a id="14200" class="Symbol">=</a> <a id="14202" href="Prelude.Preliminaries.html#14085" class="Function">Π</a> <a id="14204" href="Prelude.Preliminaries.html#14198" class="Bound">Y</a>

 <a id="14208" class="Keyword">infixr</a> <a id="14215" class="Number">-1</a> <a id="14218" href="Prelude.Preliminaries.html#14152" class="Function">-Π</a>
 <a id="14222" class="Keyword">syntax</a> <a id="14229" href="Prelude.Preliminaries.html#14152" class="Function">-Π</a> <a id="14232" class="Bound">A</a> <a id="14234" class="Symbol">(λ</a> <a id="14237" class="Bound">x</a> <a id="14239" class="Symbol">→</a> <a id="14241" class="Bound">b</a><a id="14242" class="Symbol">)</a> <a id="14244" class="Symbol">=</a> <a id="14246" class="Function">Π</a> <a id="14248" class="Bound">x</a> <a id="14250" class="Function">꞉</a> <a id="14252" class="Bound">A</a> <a id="14254" class="Function">,</a> <a id="14256" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].




----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

