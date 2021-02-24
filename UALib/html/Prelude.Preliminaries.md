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

<div class="color_box" id="mltt-ext">
  <div id="title">Backward Compatibility Note</div>
  <div id="content">The purpose of the import lines below are not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check. The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

In fact, we purposely leave off the `public` keyword from the end of these import directives, so that we are forced to (re)import each item where and when we need it.  This may seem pedantic, and may turn out to be too inconvenient for users in the end, but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.
  </div>
</div>

(The first three import lines have to be commented out because we will actually redefine the given types for pedagogical purposes in the next couple of modules.)

<pre class="Agda">

<a id="7052" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="7126" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="7160" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="7219" class="Keyword">open</a> <a id="7224" class="Keyword">import</a> <a id="7231" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7240" class="Keyword">using</a> <a id="7246" class="Symbol">(</a><a id="7247" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7250" class="Symbol">;</a> <a id="7252" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7258" class="Symbol">;</a> <a id="7260" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7268" class="Symbol">;</a> <a id="7270" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7279" class="Symbol">;</a> <a id="7281" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7287" class="Symbol">;</a> <a id="7289" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7291" class="Symbol">;</a> <a id="7293" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7321" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7322" class="Symbol">;</a> <a id="7324" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7326" class="Symbol">;</a> <a id="7328" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7331" class="Symbol">;</a> <a id="7333" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7336" class="Symbol">;</a> <a id="7338" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7339" class="Symbol">;</a> <a id="7341" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7342" class="Symbol">;</a> <a id="7344" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7345" class="Symbol">;</a> <a id="7347" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7350" class="Symbol">;</a> <a id="7352" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7366" class="Symbol">;</a> <a id="7368" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7382" class="Symbol">;</a> <a id="7384" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7386" class="Symbol">;</a> <a id="7388" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7391" class="Symbol">;</a> <a id="7393" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7395" class="Symbol">)</a>

<a id="7398" class="Keyword">open</a> <a id="7403" class="Keyword">import</a> <a id="7410" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7427" class="Keyword">using</a> <a id="7433" class="Symbol">(</a><a id="7434" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7442" class="Symbol">;</a> <a id="7444" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7451" class="Symbol">;</a> <a id="7453" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7463" class="Symbol">)</a>

<a id="7466" class="Keyword">open</a> <a id="7471" class="Keyword">import</a> <a id="7478" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7504" class="Keyword">using</a> <a id="7510" class="Symbol">(</a><a id="7511" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7517" class="Symbol">;</a> <a id="7519" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7533" class="Symbol">;</a> <a id="7535" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7542" class="Symbol">;</a>
 <a id="7545" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7557" class="Symbol">;</a> <a id="7559" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7574" class="Symbol">;</a> <a id="7576" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7583" class="Symbol">;</a> <a id="7585" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7595" class="Symbol">;</a> <a id="7597" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7611" class="Symbol">;</a>
 <a id="7614" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7645" class="Symbol">;</a> <a id="7647" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7650" class="Symbol">;</a> <a id="7652" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7655" class="Symbol">;</a> <a id="7657" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7674" class="Symbol">;</a> <a id="7676" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7693" class="Symbol">;</a>
 <a id="7696" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7745" class="Symbol">)</a>

<a id="7748" class="Keyword">open</a> <a id="7753" class="Keyword">import</a> <a id="7760" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7773" class="Keyword">renaming</a> <a id="7782" class="Symbol">(</a><a id="7783" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7787" class="Symbol">to</a> <a id="_∈_"></a><a id="7790" href="Prelude.Preliminaries.html#7790" class="Function Operator">_∈₀_</a><a id="7794" class="Symbol">;</a> <a id="7796" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7800" class="Symbol">to</a> <a id="_⊆_"></a><a id="7803" href="Prelude.Preliminaries.html#7803" class="Function Operator">_⊆₀_</a><a id="7807" class="Symbol">;</a> <a id="7809" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7827" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7830" href="Prelude.Preliminaries.html#7830" class="Function">∈₀-is-subsingleton</a><a id="7848" class="Symbol">)</a>
 <a id="7851" class="Keyword">using</a> <a id="7857" class="Symbol">(</a><a id="7858" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7859" class="Symbol">;</a> <a id="7861" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7882" class="Symbol">;</a> <a id="7884" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7903" class="Symbol">;</a> <a id="7905" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7927" class="Symbol">;</a> <a id="7929" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7936" class="Symbol">;</a> <a id="7938" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7944" class="Symbol">;</a> <a id="7946" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7947" class="Symbol">)</a>

<a id="7950" class="Keyword">open</a> <a id="7955" class="Keyword">import</a> <a id="7962" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7977" class="Keyword">using</a> <a id="7983" class="Symbol">(</a><a id="7984" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7987" class="Symbol">;</a> <a id="7989" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7993" class="Symbol">;</a> <a id="7995" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="8012" class="Symbol">;</a> <a id="8014" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="8026" class="Symbol">;</a> <a id="8028" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="8041" class="Symbol">;</a> <a id="8043" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="8054" class="Symbol">;</a>
 <a id="8057" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="8063" class="Symbol">;</a> <a id="8065" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="8068" class="Symbol">;</a> <a id="8070" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="8097" class="Symbol">;</a> <a id="8099" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="8116" class="Symbol">;</a> <a id="8118" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="8135" class="Symbol">;</a> <a id="8137" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="8152" class="Symbol">)</a>

<a id="8155" class="Keyword">open</a> <a id="8160" class="Keyword">import</a> <a id="8167" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="8188" class="Keyword">using</a> <a id="8194" class="Symbol">(</a><a id="8195" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="8207" class="Symbol">)</a>

<a id="8210" class="Keyword">open</a> <a id="8215" class="Keyword">import</a> <a id="8222" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8243" class="Keyword">using</a> <a id="8249" class="Symbol">(</a><a id="8250" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8252" class="Symbol">;</a> <a id="8254" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8257" class="Symbol">)</a>

<a id="8260" class="Keyword">open</a> <a id="8265" class="Keyword">import</a> <a id="8272" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8300" class="Keyword">using</a> <a id="8306" class="Symbol">(</a><a id="8307" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8310" class="Symbol">;</a> <a id="8312" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8318" class="Symbol">;</a> <a id="8320" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8341" class="Symbol">;</a>
 <a id="8344" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8366" class="Symbol">;</a> <a id="8368" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8373" class="Symbol">;</a> <a id="8375" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8393" class="Symbol">;</a> <a id="8395" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8402" class="Symbol">)</a>

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

<a id="11956" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11963" href="Prelude.Preliminaries.html#11963" class="Module">hide-sigma</a> <a id="11974" class="Keyword">where</a>

 <a id="11982" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11989" href="Prelude.Preliminaries.html#11989" class="Record">Σ</a> <a id="11991" class="Symbol">{</a><a id="11992" href="Prelude.Preliminaries.html#11992" class="Bound">𝓤</a> <a id="11994" href="Prelude.Preliminaries.html#11994" class="Bound">𝓥</a><a id="11995" class="Symbol">}</a> <a id="11997" class="Symbol">{</a><a id="11998" href="Prelude.Preliminaries.html#11998" class="Bound">X</a> <a id="12000" class="Symbol">:</a> <a id="12002" href="Prelude.Preliminaries.html#11992" class="Bound">𝓤</a> <a id="12004" href="Universes.html#403" class="Function Operator">̇</a> <a id="12006" class="Symbol">}</a> <a id="12008" class="Symbol">(</a><a id="12009" href="Prelude.Preliminaries.html#12009" class="Bound">Y</a> <a id="12011" class="Symbol">:</a> <a id="12013" href="Prelude.Preliminaries.html#11998" class="Bound">X</a> <a id="12015" class="Symbol">→</a> <a id="12017" href="Prelude.Preliminaries.html#11994" class="Bound">𝓥</a> <a id="12019" href="Universes.html#403" class="Function Operator">̇</a> <a id="12021" class="Symbol">)</a> <a id="12023" class="Symbol">:</a> <a id="12025" href="Prelude.Preliminaries.html#11992" class="Bound">𝓤</a> <a id="12027" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12029" href="Prelude.Preliminaries.html#11994" class="Bound">𝓥</a> <a id="12031" href="Universes.html#403" class="Function Operator">̇</a>  <a id="12034" class="Keyword">where</a>
  <a id="12042" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="12054" href="Prelude.Preliminaries.html#12054" class="InductiveConstructor Operator">_,_</a>
  <a id="12060" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="12069" href="Prelude.Preliminaries.html#12069" class="Field">pr₁</a> <a id="12073" class="Symbol">:</a> <a id="12075" href="Prelude.Preliminaries.html#11998" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="12080" href="Prelude.Preliminaries.html#12080" class="Field">pr₂</a> <a id="12084" class="Symbol">:</a> <a id="12086" href="Prelude.Preliminaries.html#12009" class="Bound">Y</a> <a id="12088" href="Prelude.Preliminaries.html#12069" class="Field">pr₁</a>

 <a id="12094" class="Keyword">infixr</a> <a id="12101" class="Number">50</a> <a id="12104" href="Prelude.Preliminaries.html#12054" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12441" href="Prelude.Preliminaries.html#12441" class="Function">-Σ</a> <a id="12444" class="Symbol">:</a> <a id="12446" class="Symbol">{</a><a id="12447" href="Prelude.Preliminaries.html#12447" class="Bound">𝓤</a> <a id="12449" href="Prelude.Preliminaries.html#12449" class="Bound">𝓥</a> <a id="12451" class="Symbol">:</a> <a id="12453" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12461" class="Symbol">}</a> <a id="12463" class="Symbol">(</a><a id="12464" href="Prelude.Preliminaries.html#12464" class="Bound">X</a> <a id="12466" class="Symbol">:</a> <a id="12468" href="Prelude.Preliminaries.html#12447" class="Bound">𝓤</a> <a id="12470" href="Universes.html#403" class="Function Operator">̇</a> <a id="12472" class="Symbol">)</a> <a id="12474" class="Symbol">(</a><a id="12475" href="Prelude.Preliminaries.html#12475" class="Bound">Y</a> <a id="12477" class="Symbol">:</a> <a id="12479" href="Prelude.Preliminaries.html#12464" class="Bound">X</a> <a id="12481" class="Symbol">→</a> <a id="12483" href="Prelude.Preliminaries.html#12449" class="Bound">𝓥</a> <a id="12485" href="Universes.html#403" class="Function Operator">̇</a> <a id="12487" class="Symbol">)</a> <a id="12489" class="Symbol">→</a> <a id="12491" href="Prelude.Preliminaries.html#12447" class="Bound">𝓤</a> <a id="12493" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12495" href="Prelude.Preliminaries.html#12449" class="Bound">𝓥</a> <a id="12497" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12500" href="Prelude.Preliminaries.html#12441" class="Function">-Σ</a> <a id="12503" href="Prelude.Preliminaries.html#12503" class="Bound">X</a> <a id="12505" href="Prelude.Preliminaries.html#12505" class="Bound">Y</a> <a id="12507" class="Symbol">=</a> <a id="12509" href="Prelude.Preliminaries.html#11989" class="Record">Σ</a> <a id="12511" href="Prelude.Preliminaries.html#12505" class="Bound">Y</a>

 <a id="12515" class="Keyword">syntax</a> <a id="12522" href="Prelude.Preliminaries.html#12441" class="Function">-Σ</a> <a id="12525" class="Bound">X</a> <a id="12527" class="Symbol">(λ</a> <a id="12530" class="Bound">x</a> <a id="12532" class="Symbol">→</a> <a id="12534" class="Bound">Y</a><a id="12535" class="Symbol">)</a> <a id="12537" class="Symbol">=</a> <a id="12539" class="Function">Σ</a> <a id="12541" class="Bound">x</a> <a id="12543" class="Function">꞉</a> <a id="12545" class="Bound">X</a> <a id="12547" class="Function">,</a> <a id="12549" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12922" href="Prelude.Preliminaries.html#12922" class="Function Operator">_×_</a> <a id="12926" class="Symbol">:</a> <a id="12928" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12930" href="Universes.html#403" class="Function Operator">̇</a> <a id="12932" class="Symbol">→</a> <a id="12934" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12936" href="Universes.html#403" class="Function Operator">̇</a> <a id="12938" class="Symbol">→</a> <a id="12940" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12942" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12944" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12946" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12949" href="Prelude.Preliminaries.html#12949" class="Bound">X</a> <a id="12951" href="Prelude.Preliminaries.html#12922" class="Function Operator">×</a> <a id="12953" href="Prelude.Preliminaries.html#12953" class="Bound">Y</a> <a id="12955" class="Symbol">=</a> <a id="12957" href="Prelude.Preliminaries.html#12441" class="Function">Σ</a> <a id="12959" href="Prelude.Preliminaries.html#12959" class="Bound">x</a> <a id="12961" href="Prelude.Preliminaries.html#12441" class="Function">꞉</a> <a id="12963" href="Prelude.Preliminaries.html#12949" class="Bound">X</a> <a id="12965" href="Prelude.Preliminaries.html#12441" class="Function">,</a> <a id="12967" href="Prelude.Preliminaries.html#12953" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13177" class="Keyword">open</a> <a id="13182" class="Keyword">import</a> <a id="13189" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13200" class="Keyword">renaming</a> <a id="13209" class="Symbol">(</a><a id="13210" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13214" class="Symbol">to</a> <a id="13217" class="Keyword">infixr</a> <a id="13224" class="Number">50</a> <a id="_,_"></a><a id="13227" href="Prelude.Preliminaries.html#13227" class="InductiveConstructor Operator">_,_</a><a id="13230" class="Symbol">)</a>
<a id="13232" class="Keyword">open</a> <a id="13237" class="Keyword">import</a> <a id="13244" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13253" class="Keyword">using</a> <a id="13259" class="Symbol">(</a><a id="13260" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13263" class="Symbol">;</a> <a id="13265" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13268" class="Symbol">;</a> <a id="13270" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13273" class="Symbol">;</a> <a id="13275" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13277" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13712" class="Keyword">module</a> <a id="13719" href="Prelude.Preliminaries.html#13719" class="Module">_</a> <a id="13721" class="Symbol">{</a><a id="13722" href="Prelude.Preliminaries.html#13722" class="Bound">𝓤</a> <a id="13724" class="Symbol">:</a> <a id="13726" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13734" class="Symbol">}</a> <a id="13736" class="Keyword">where</a>

 <a id="13744" href="Prelude.Preliminaries.html#13744" class="Function Operator">∣_∣</a> <a id="13748" href="Prelude.Preliminaries.html#13748" class="Function">fst</a> <a id="13752" class="Symbol">:</a> <a id="13754" class="Symbol">{</a><a id="13755" href="Prelude.Preliminaries.html#13755" class="Bound">X</a> <a id="13757" class="Symbol">:</a> <a id="13759" href="Prelude.Preliminaries.html#13722" class="Bound">𝓤</a> <a id="13761" href="Universes.html#403" class="Function Operator">̇</a> <a id="13763" class="Symbol">}{</a><a id="13765" href="Prelude.Preliminaries.html#13765" class="Bound">Y</a> <a id="13767" class="Symbol">:</a> <a id="13769" href="Prelude.Preliminaries.html#13755" class="Bound">X</a> <a id="13771" class="Symbol">→</a> <a id="13773" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13775" href="Universes.html#403" class="Function Operator">̇</a><a id="13776" class="Symbol">}</a> <a id="13778" class="Symbol">→</a> <a id="13780" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13782" href="Prelude.Preliminaries.html#13765" class="Bound">Y</a> <a id="13784" class="Symbol">→</a> <a id="13786" href="Prelude.Preliminaries.html#13755" class="Bound">X</a>
 <a id="13789" href="Prelude.Preliminaries.html#13744" class="Function Operator">∣</a> <a id="13791" href="Prelude.Preliminaries.html#13791" class="Bound">x</a> <a id="13793" href="Prelude.Preliminaries.html#13227" class="InductiveConstructor Operator">,</a> <a id="13795" href="Prelude.Preliminaries.html#13795" class="Bound">y</a> <a id="13797" href="Prelude.Preliminaries.html#13744" class="Function Operator">∣</a> <a id="13799" class="Symbol">=</a> <a id="13801" href="Prelude.Preliminaries.html#13791" class="Bound">x</a>
 <a id="13804" href="Prelude.Preliminaries.html#13748" class="Function">fst</a> <a id="13808" class="Symbol">(</a><a id="13809" href="Prelude.Preliminaries.html#13809" class="Bound">x</a> <a id="13811" href="Prelude.Preliminaries.html#13227" class="InductiveConstructor Operator">,</a> <a id="13813" href="Prelude.Preliminaries.html#13813" class="Bound">y</a><a id="13814" class="Symbol">)</a> <a id="13816" class="Symbol">=</a> <a id="13818" href="Prelude.Preliminaries.html#13809" class="Bound">x</a>

 <a id="13822" href="Prelude.Preliminaries.html#13822" class="Function Operator">∥_∥</a> <a id="13826" href="Prelude.Preliminaries.html#13826" class="Function">snd</a> <a id="13830" class="Symbol">:</a> <a id="13832" class="Symbol">{</a><a id="13833" href="Prelude.Preliminaries.html#13833" class="Bound">X</a> <a id="13835" class="Symbol">:</a> <a id="13837" href="Prelude.Preliminaries.html#13722" class="Bound">𝓤</a> <a id="13839" href="Universes.html#403" class="Function Operator">̇</a> <a id="13841" class="Symbol">}{</a><a id="13843" href="Prelude.Preliminaries.html#13843" class="Bound">Y</a> <a id="13845" class="Symbol">:</a> <a id="13847" href="Prelude.Preliminaries.html#13833" class="Bound">X</a> <a id="13849" class="Symbol">→</a> <a id="13851" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13853" href="Universes.html#403" class="Function Operator">̇</a> <a id="13855" class="Symbol">}</a> <a id="13857" class="Symbol">→</a> <a id="13859" class="Symbol">(</a><a id="13860" href="Prelude.Preliminaries.html#13860" class="Bound">z</a> <a id="13862" class="Symbol">:</a> <a id="13864" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13866" href="Prelude.Preliminaries.html#13843" class="Bound">Y</a><a id="13867" class="Symbol">)</a> <a id="13869" class="Symbol">→</a> <a id="13871" href="Prelude.Preliminaries.html#13843" class="Bound">Y</a> <a id="13873" class="Symbol">(</a><a id="13874" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13878" href="Prelude.Preliminaries.html#13860" class="Bound">z</a><a id="13879" class="Symbol">)</a>
 <a id="13882" href="Prelude.Preliminaries.html#13822" class="Function Operator">∥</a> <a id="13884" href="Prelude.Preliminaries.html#13884" class="Bound">x</a> <a id="13886" href="Prelude.Preliminaries.html#13227" class="InductiveConstructor Operator">,</a> <a id="13888" href="Prelude.Preliminaries.html#13888" class="Bound">y</a> <a id="13890" href="Prelude.Preliminaries.html#13822" class="Function Operator">∥</a> <a id="13892" class="Symbol">=</a> <a id="13894" href="Prelude.Preliminaries.html#13888" class="Bound">y</a>
 <a id="13897" href="Prelude.Preliminaries.html#13826" class="Function">snd</a> <a id="13901" class="Symbol">(</a><a id="13902" href="Prelude.Preliminaries.html#13902" class="Bound">x</a> <a id="13904" href="Prelude.Preliminaries.html#13227" class="InductiveConstructor Operator">,</a> <a id="13906" href="Prelude.Preliminaries.html#13906" class="Bound">y</a><a id="13907" class="Symbol">)</a> <a id="13909" class="Symbol">=</a> <a id="13911" href="Prelude.Preliminaries.html#13906" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14180" class="Keyword">module</a> <a id="hide-pi"></a><a id="14187" href="Prelude.Preliminaries.html#14187" class="Module">hide-pi</a> <a id="14195" class="Symbol">{</a><a id="14196" href="Prelude.Preliminaries.html#14196" class="Bound">𝓤</a> <a id="14198" href="Prelude.Preliminaries.html#14198" class="Bound">𝓦</a> <a id="14200" class="Symbol">:</a> <a id="14202" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14210" class="Symbol">}</a> <a id="14212" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14220" href="Prelude.Preliminaries.html#14220" class="Function">Π</a> <a id="14222" class="Symbol">:</a> <a id="14224" class="Symbol">{</a><a id="14225" href="Prelude.Preliminaries.html#14225" class="Bound">X</a> <a id="14227" class="Symbol">:</a> <a id="14229" href="Prelude.Preliminaries.html#14196" class="Bound">𝓤</a> <a id="14231" href="Universes.html#403" class="Function Operator">̇</a> <a id="14233" class="Symbol">}</a> <a id="14235" class="Symbol">(</a><a id="14236" href="Prelude.Preliminaries.html#14236" class="Bound">A</a> <a id="14238" class="Symbol">:</a> <a id="14240" href="Prelude.Preliminaries.html#14225" class="Bound">X</a> <a id="14242" class="Symbol">→</a> <a id="14244" href="Prelude.Preliminaries.html#14198" class="Bound">𝓦</a> <a id="14246" href="Universes.html#403" class="Function Operator">̇</a> <a id="14248" class="Symbol">)</a> <a id="14250" class="Symbol">→</a> <a id="14252" href="Prelude.Preliminaries.html#14196" class="Bound">𝓤</a> <a id="14254" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14256" href="Prelude.Preliminaries.html#14198" class="Bound">𝓦</a> <a id="14258" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14261" href="Prelude.Preliminaries.html#14220" class="Function">Π</a> <a id="14263" class="Symbol">{</a><a id="14264" href="Prelude.Preliminaries.html#14264" class="Bound">X</a><a id="14265" class="Symbol">}</a> <a id="14267" href="Prelude.Preliminaries.html#14267" class="Bound">A</a> <a id="14269" class="Symbol">=</a> <a id="14271" class="Symbol">(</a><a id="14272" href="Prelude.Preliminaries.html#14272" class="Bound">x</a> <a id="14274" class="Symbol">:</a> <a id="14276" href="Prelude.Preliminaries.html#14264" class="Bound">X</a><a id="14277" class="Symbol">)</a> <a id="14279" class="Symbol">→</a> <a id="14281" href="Prelude.Preliminaries.html#14267" class="Bound">A</a> <a id="14283" href="Prelude.Preliminaries.html#14272" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14287" href="Prelude.Preliminaries.html#14287" class="Function">-Π</a> <a id="14290" class="Symbol">:</a> <a id="14292" class="Symbol">(</a><a id="14293" href="Prelude.Preliminaries.html#14293" class="Bound">X</a> <a id="14295" class="Symbol">:</a> <a id="14297" href="Prelude.Preliminaries.html#14196" class="Bound">𝓤</a> <a id="14299" href="Universes.html#403" class="Function Operator">̇</a> <a id="14301" class="Symbol">)(</a><a id="14303" href="Prelude.Preliminaries.html#14303" class="Bound">Y</a> <a id="14305" class="Symbol">:</a> <a id="14307" href="Prelude.Preliminaries.html#14293" class="Bound">X</a> <a id="14309" class="Symbol">→</a> <a id="14311" href="Prelude.Preliminaries.html#14198" class="Bound">𝓦</a> <a id="14313" href="Universes.html#403" class="Function Operator">̇</a> <a id="14315" class="Symbol">)</a> <a id="14317" class="Symbol">→</a> <a id="14319" href="Prelude.Preliminaries.html#14196" class="Bound">𝓤</a> <a id="14321" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14323" href="Prelude.Preliminaries.html#14198" class="Bound">𝓦</a> <a id="14325" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14328" href="Prelude.Preliminaries.html#14287" class="Function">-Π</a> <a id="14331" href="Prelude.Preliminaries.html#14331" class="Bound">X</a> <a id="14333" href="Prelude.Preliminaries.html#14333" class="Bound">Y</a> <a id="14335" class="Symbol">=</a> <a id="14337" href="Prelude.Preliminaries.html#14220" class="Function">Π</a> <a id="14339" href="Prelude.Preliminaries.html#14333" class="Bound">Y</a>

 <a id="14343" class="Keyword">infixr</a> <a id="14350" class="Number">-1</a> <a id="14353" href="Prelude.Preliminaries.html#14287" class="Function">-Π</a>
 <a id="14357" class="Keyword">syntax</a> <a id="14364" href="Prelude.Preliminaries.html#14287" class="Function">-Π</a> <a id="14367" class="Bound">A</a> <a id="14369" class="Symbol">(λ</a> <a id="14372" class="Bound">x</a> <a id="14374" class="Symbol">→</a> <a id="14376" class="Bound">b</a><a id="14377" class="Symbol">)</a> <a id="14379" class="Symbol">=</a> <a id="14381" class="Function">Π</a> <a id="14383" class="Bound">x</a> <a id="14385" class="Function">꞉</a> <a id="14387" class="Bound">A</a> <a id="14389" class="Function">,</a> <a id="14391" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].




----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

