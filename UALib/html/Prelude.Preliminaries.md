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

<fieldset style="border: 1px #EA9258 dotted">
 <legend style="border: 1px #5F38AD solid;margin-left: 1em; padding: 0.2em 0.8em ">Agda Note</legend>

 The purpose of the import lines below are not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check. The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

 In fact, we purposely leave off the `public` keyword from the end of these import directives, so that we are forced to (re)import each item where and when we need it.  This may seem pedantic, and may turn out to be too inconvenient for users in the end, but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.
</fieldset>

(The first three import lines have to be commented out because we will actually redefine the given types for pedagogical purposes in the next couple of modules.)

<pre class="Agda">

<a id="7089" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="7163" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="7197" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="7256" class="Keyword">open</a> <a id="7261" class="Keyword">import</a> <a id="7268" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7277" class="Keyword">using</a> <a id="7283" class="Symbol">(</a><a id="7284" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7287" class="Symbol">;</a> <a id="7289" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7295" class="Symbol">;</a> <a id="7297" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7305" class="Symbol">;</a> <a id="7307" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7316" class="Symbol">;</a> <a id="7318" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7324" class="Symbol">;</a> <a id="7326" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7328" class="Symbol">;</a> <a id="7330" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7358" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7359" class="Symbol">;</a> <a id="7361" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7363" class="Symbol">;</a> <a id="7365" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7368" class="Symbol">;</a> <a id="7370" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7373" class="Symbol">;</a> <a id="7375" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7376" class="Symbol">;</a> <a id="7378" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7379" class="Symbol">;</a> <a id="7381" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7382" class="Symbol">;</a> <a id="7384" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7387" class="Symbol">;</a> <a id="7389" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7403" class="Symbol">;</a> <a id="7405" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7419" class="Symbol">;</a> <a id="7421" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7423" class="Symbol">;</a> <a id="7425" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7428" class="Symbol">;</a> <a id="7430" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7432" class="Symbol">)</a>

<a id="7435" class="Keyword">open</a> <a id="7440" class="Keyword">import</a> <a id="7447" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7464" class="Keyword">using</a> <a id="7470" class="Symbol">(</a><a id="7471" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7479" class="Symbol">;</a> <a id="7481" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7488" class="Symbol">;</a> <a id="7490" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7500" class="Symbol">)</a>

<a id="7503" class="Keyword">open</a> <a id="7508" class="Keyword">import</a> <a id="7515" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7541" class="Keyword">using</a> <a id="7547" class="Symbol">(</a><a id="7548" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7554" class="Symbol">;</a> <a id="7556" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7570" class="Symbol">;</a> <a id="7572" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7579" class="Symbol">;</a>
 <a id="7582" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7594" class="Symbol">;</a> <a id="7596" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7611" class="Symbol">;</a> <a id="7613" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7620" class="Symbol">;</a> <a id="7622" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7632" class="Symbol">;</a> <a id="7634" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7648" class="Symbol">;</a>
 <a id="7651" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7682" class="Symbol">;</a> <a id="7684" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7687" class="Symbol">;</a> <a id="7689" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7692" class="Symbol">;</a> <a id="7694" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7711" class="Symbol">;</a> <a id="7713" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7730" class="Symbol">;</a>
 <a id="7733" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7782" class="Symbol">)</a>

<a id="7785" class="Keyword">open</a> <a id="7790" class="Keyword">import</a> <a id="7797" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7810" class="Keyword">renaming</a> <a id="7819" class="Symbol">(</a><a id="7820" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7824" class="Symbol">to</a> <a id="_∈_"></a><a id="7827" href="Prelude.Preliminaries.html#7827" class="Function Operator">_∈₀_</a><a id="7831" class="Symbol">;</a> <a id="7833" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7837" class="Symbol">to</a> <a id="_⊆_"></a><a id="7840" href="Prelude.Preliminaries.html#7840" class="Function Operator">_⊆₀_</a><a id="7844" class="Symbol">;</a> <a id="7846" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7864" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7867" href="Prelude.Preliminaries.html#7867" class="Function">∈₀-is-subsingleton</a><a id="7885" class="Symbol">)</a>
 <a id="7888" class="Keyword">using</a> <a id="7894" class="Symbol">(</a><a id="7895" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7896" class="Symbol">;</a> <a id="7898" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7919" class="Symbol">;</a> <a id="7921" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7940" class="Symbol">;</a> <a id="7942" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7964" class="Symbol">;</a> <a id="7966" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7973" class="Symbol">;</a> <a id="7975" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7981" class="Symbol">;</a> <a id="7983" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7984" class="Symbol">)</a>

<a id="7987" class="Keyword">open</a> <a id="7992" class="Keyword">import</a> <a id="7999" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="8014" class="Keyword">using</a> <a id="8020" class="Symbol">(</a><a id="8021" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="8024" class="Symbol">;</a> <a id="8026" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="8030" class="Symbol">;</a> <a id="8032" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="8049" class="Symbol">;</a> <a id="8051" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="8063" class="Symbol">;</a> <a id="8065" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="8078" class="Symbol">;</a> <a id="8080" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="8091" class="Symbol">;</a>
 <a id="8094" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="8100" class="Symbol">;</a> <a id="8102" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="8105" class="Symbol">;</a> <a id="8107" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="8134" class="Symbol">;</a> <a id="8136" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="8153" class="Symbol">;</a> <a id="8155" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="8172" class="Symbol">;</a> <a id="8174" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="8189" class="Symbol">)</a>

<a id="8192" class="Keyword">open</a> <a id="8197" class="Keyword">import</a> <a id="8204" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="8225" class="Keyword">using</a> <a id="8231" class="Symbol">(</a><a id="8232" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="8244" class="Symbol">)</a>

<a id="8247" class="Keyword">open</a> <a id="8252" class="Keyword">import</a> <a id="8259" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8280" class="Keyword">using</a> <a id="8286" class="Symbol">(</a><a id="8287" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8289" class="Symbol">;</a> <a id="8291" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8294" class="Symbol">)</a>

<a id="8297" class="Keyword">open</a> <a id="8302" class="Keyword">import</a> <a id="8309" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8337" class="Keyword">using</a> <a id="8343" class="Symbol">(</a><a id="8344" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8347" class="Symbol">;</a> <a id="8349" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8355" class="Symbol">;</a> <a id="8357" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8378" class="Symbol">;</a>
 <a id="8381" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8403" class="Symbol">;</a> <a id="8405" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8410" class="Symbol">;</a> <a id="8412" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8430" class="Symbol">;</a> <a id="8432" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8439" class="Symbol">)</a>

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

<a id="11993" class="Keyword">module</a> <a id="hide-sigma"></a><a id="12000" href="Prelude.Preliminaries.html#12000" class="Module">hide-sigma</a> <a id="12011" class="Keyword">where</a>

 <a id="12019" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="12026" href="Prelude.Preliminaries.html#12026" class="Record">Σ</a> <a id="12028" class="Symbol">{</a><a id="12029" href="Prelude.Preliminaries.html#12029" class="Bound">𝓤</a> <a id="12031" href="Prelude.Preliminaries.html#12031" class="Bound">𝓥</a><a id="12032" class="Symbol">}</a> <a id="12034" class="Symbol">{</a><a id="12035" href="Prelude.Preliminaries.html#12035" class="Bound">X</a> <a id="12037" class="Symbol">:</a> <a id="12039" href="Prelude.Preliminaries.html#12029" class="Bound">𝓤</a> <a id="12041" href="Universes.html#403" class="Function Operator">̇</a> <a id="12043" class="Symbol">}</a> <a id="12045" class="Symbol">(</a><a id="12046" href="Prelude.Preliminaries.html#12046" class="Bound">Y</a> <a id="12048" class="Symbol">:</a> <a id="12050" href="Prelude.Preliminaries.html#12035" class="Bound">X</a> <a id="12052" class="Symbol">→</a> <a id="12054" href="Prelude.Preliminaries.html#12031" class="Bound">𝓥</a> <a id="12056" href="Universes.html#403" class="Function Operator">̇</a> <a id="12058" class="Symbol">)</a> <a id="12060" class="Symbol">:</a> <a id="12062" href="Prelude.Preliminaries.html#12029" class="Bound">𝓤</a> <a id="12064" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12066" href="Prelude.Preliminaries.html#12031" class="Bound">𝓥</a> <a id="12068" href="Universes.html#403" class="Function Operator">̇</a>  <a id="12071" class="Keyword">where</a>
  <a id="12079" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="12091" href="Prelude.Preliminaries.html#12091" class="InductiveConstructor Operator">_,_</a>
  <a id="12097" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="12106" href="Prelude.Preliminaries.html#12106" class="Field">pr₁</a> <a id="12110" class="Symbol">:</a> <a id="12112" href="Prelude.Preliminaries.html#12035" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="12117" href="Prelude.Preliminaries.html#12117" class="Field">pr₂</a> <a id="12121" class="Symbol">:</a> <a id="12123" href="Prelude.Preliminaries.html#12046" class="Bound">Y</a> <a id="12125" href="Prelude.Preliminaries.html#12106" class="Field">pr₁</a>

 <a id="12131" class="Keyword">infixr</a> <a id="12138" class="Number">50</a> <a id="12141" href="Prelude.Preliminaries.html#12091" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12478" href="Prelude.Preliminaries.html#12478" class="Function">-Σ</a> <a id="12481" class="Symbol">:</a> <a id="12483" class="Symbol">{</a><a id="12484" href="Prelude.Preliminaries.html#12484" class="Bound">𝓤</a> <a id="12486" href="Prelude.Preliminaries.html#12486" class="Bound">𝓥</a> <a id="12488" class="Symbol">:</a> <a id="12490" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12498" class="Symbol">}</a> <a id="12500" class="Symbol">(</a><a id="12501" href="Prelude.Preliminaries.html#12501" class="Bound">X</a> <a id="12503" class="Symbol">:</a> <a id="12505" href="Prelude.Preliminaries.html#12484" class="Bound">𝓤</a> <a id="12507" href="Universes.html#403" class="Function Operator">̇</a> <a id="12509" class="Symbol">)</a> <a id="12511" class="Symbol">(</a><a id="12512" href="Prelude.Preliminaries.html#12512" class="Bound">Y</a> <a id="12514" class="Symbol">:</a> <a id="12516" href="Prelude.Preliminaries.html#12501" class="Bound">X</a> <a id="12518" class="Symbol">→</a> <a id="12520" href="Prelude.Preliminaries.html#12486" class="Bound">𝓥</a> <a id="12522" href="Universes.html#403" class="Function Operator">̇</a> <a id="12524" class="Symbol">)</a> <a id="12526" class="Symbol">→</a> <a id="12528" href="Prelude.Preliminaries.html#12484" class="Bound">𝓤</a> <a id="12530" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12532" href="Prelude.Preliminaries.html#12486" class="Bound">𝓥</a> <a id="12534" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12537" href="Prelude.Preliminaries.html#12478" class="Function">-Σ</a> <a id="12540" href="Prelude.Preliminaries.html#12540" class="Bound">X</a> <a id="12542" href="Prelude.Preliminaries.html#12542" class="Bound">Y</a> <a id="12544" class="Symbol">=</a> <a id="12546" href="Prelude.Preliminaries.html#12026" class="Record">Σ</a> <a id="12548" href="Prelude.Preliminaries.html#12542" class="Bound">Y</a>

 <a id="12552" class="Keyword">syntax</a> <a id="12559" href="Prelude.Preliminaries.html#12478" class="Function">-Σ</a> <a id="12562" class="Bound">X</a> <a id="12564" class="Symbol">(λ</a> <a id="12567" class="Bound">x</a> <a id="12569" class="Symbol">→</a> <a id="12571" class="Bound">Y</a><a id="12572" class="Symbol">)</a> <a id="12574" class="Symbol">=</a> <a id="12576" class="Function">Σ</a> <a id="12578" class="Bound">x</a> <a id="12580" class="Function">꞉</a> <a id="12582" class="Bound">X</a> <a id="12584" class="Function">,</a> <a id="12586" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12959" href="Prelude.Preliminaries.html#12959" class="Function Operator">_×_</a> <a id="12963" class="Symbol">:</a> <a id="12965" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12967" href="Universes.html#403" class="Function Operator">̇</a> <a id="12969" class="Symbol">→</a> <a id="12971" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12973" href="Universes.html#403" class="Function Operator">̇</a> <a id="12975" class="Symbol">→</a> <a id="12977" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12979" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12981" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12983" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12986" href="Prelude.Preliminaries.html#12986" class="Bound">X</a> <a id="12988" href="Prelude.Preliminaries.html#12959" class="Function Operator">×</a> <a id="12990" href="Prelude.Preliminaries.html#12990" class="Bound">Y</a> <a id="12992" class="Symbol">=</a> <a id="12994" href="Prelude.Preliminaries.html#12478" class="Function">Σ</a> <a id="12996" href="Prelude.Preliminaries.html#12996" class="Bound">x</a> <a id="12998" href="Prelude.Preliminaries.html#12478" class="Function">꞉</a> <a id="13000" href="Prelude.Preliminaries.html#12986" class="Bound">X</a> <a id="13002" href="Prelude.Preliminaries.html#12478" class="Function">,</a> <a id="13004" href="Prelude.Preliminaries.html#12990" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13214" class="Keyword">open</a> <a id="13219" class="Keyword">import</a> <a id="13226" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13237" class="Keyword">renaming</a> <a id="13246" class="Symbol">(</a><a id="13247" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13251" class="Symbol">to</a> <a id="13254" class="Keyword">infixr</a> <a id="13261" class="Number">50</a> <a id="_,_"></a><a id="13264" href="Prelude.Preliminaries.html#13264" class="InductiveConstructor Operator">_,_</a><a id="13267" class="Symbol">)</a>
<a id="13269" class="Keyword">open</a> <a id="13274" class="Keyword">import</a> <a id="13281" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13290" class="Keyword">using</a> <a id="13296" class="Symbol">(</a><a id="13297" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13300" class="Symbol">;</a> <a id="13302" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13305" class="Symbol">;</a> <a id="13307" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13310" class="Symbol">;</a> <a id="13312" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13314" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13749" class="Keyword">module</a> <a id="13756" href="Prelude.Preliminaries.html#13756" class="Module">_</a> <a id="13758" class="Symbol">{</a><a id="13759" href="Prelude.Preliminaries.html#13759" class="Bound">𝓤</a> <a id="13761" class="Symbol">:</a> <a id="13763" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13771" class="Symbol">}</a> <a id="13773" class="Keyword">where</a>

 <a id="13781" href="Prelude.Preliminaries.html#13781" class="Function Operator">∣_∣</a> <a id="13785" href="Prelude.Preliminaries.html#13785" class="Function">fst</a> <a id="13789" class="Symbol">:</a> <a id="13791" class="Symbol">{</a><a id="13792" href="Prelude.Preliminaries.html#13792" class="Bound">X</a> <a id="13794" class="Symbol">:</a> <a id="13796" href="Prelude.Preliminaries.html#13759" class="Bound">𝓤</a> <a id="13798" href="Universes.html#403" class="Function Operator">̇</a> <a id="13800" class="Symbol">}{</a><a id="13802" href="Prelude.Preliminaries.html#13802" class="Bound">Y</a> <a id="13804" class="Symbol">:</a> <a id="13806" href="Prelude.Preliminaries.html#13792" class="Bound">X</a> <a id="13808" class="Symbol">→</a> <a id="13810" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13812" href="Universes.html#403" class="Function Operator">̇</a><a id="13813" class="Symbol">}</a> <a id="13815" class="Symbol">→</a> <a id="13817" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13819" href="Prelude.Preliminaries.html#13802" class="Bound">Y</a> <a id="13821" class="Symbol">→</a> <a id="13823" href="Prelude.Preliminaries.html#13792" class="Bound">X</a>
 <a id="13826" href="Prelude.Preliminaries.html#13781" class="Function Operator">∣</a> <a id="13828" href="Prelude.Preliminaries.html#13828" class="Bound">x</a> <a id="13830" href="Prelude.Preliminaries.html#13264" class="InductiveConstructor Operator">,</a> <a id="13832" href="Prelude.Preliminaries.html#13832" class="Bound">y</a> <a id="13834" href="Prelude.Preliminaries.html#13781" class="Function Operator">∣</a> <a id="13836" class="Symbol">=</a> <a id="13838" href="Prelude.Preliminaries.html#13828" class="Bound">x</a>
 <a id="13841" href="Prelude.Preliminaries.html#13785" class="Function">fst</a> <a id="13845" class="Symbol">(</a><a id="13846" href="Prelude.Preliminaries.html#13846" class="Bound">x</a> <a id="13848" href="Prelude.Preliminaries.html#13264" class="InductiveConstructor Operator">,</a> <a id="13850" href="Prelude.Preliminaries.html#13850" class="Bound">y</a><a id="13851" class="Symbol">)</a> <a id="13853" class="Symbol">=</a> <a id="13855" href="Prelude.Preliminaries.html#13846" class="Bound">x</a>

 <a id="13859" href="Prelude.Preliminaries.html#13859" class="Function Operator">∥_∥</a> <a id="13863" href="Prelude.Preliminaries.html#13863" class="Function">snd</a> <a id="13867" class="Symbol">:</a> <a id="13869" class="Symbol">{</a><a id="13870" href="Prelude.Preliminaries.html#13870" class="Bound">X</a> <a id="13872" class="Symbol">:</a> <a id="13874" href="Prelude.Preliminaries.html#13759" class="Bound">𝓤</a> <a id="13876" href="Universes.html#403" class="Function Operator">̇</a> <a id="13878" class="Symbol">}{</a><a id="13880" href="Prelude.Preliminaries.html#13880" class="Bound">Y</a> <a id="13882" class="Symbol">:</a> <a id="13884" href="Prelude.Preliminaries.html#13870" class="Bound">X</a> <a id="13886" class="Symbol">→</a> <a id="13888" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13890" href="Universes.html#403" class="Function Operator">̇</a> <a id="13892" class="Symbol">}</a> <a id="13894" class="Symbol">→</a> <a id="13896" class="Symbol">(</a><a id="13897" href="Prelude.Preliminaries.html#13897" class="Bound">z</a> <a id="13899" class="Symbol">:</a> <a id="13901" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13903" href="Prelude.Preliminaries.html#13880" class="Bound">Y</a><a id="13904" class="Symbol">)</a> <a id="13906" class="Symbol">→</a> <a id="13908" href="Prelude.Preliminaries.html#13880" class="Bound">Y</a> <a id="13910" class="Symbol">(</a><a id="13911" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13915" href="Prelude.Preliminaries.html#13897" class="Bound">z</a><a id="13916" class="Symbol">)</a>
 <a id="13919" href="Prelude.Preliminaries.html#13859" class="Function Operator">∥</a> <a id="13921" href="Prelude.Preliminaries.html#13921" class="Bound">x</a> <a id="13923" href="Prelude.Preliminaries.html#13264" class="InductiveConstructor Operator">,</a> <a id="13925" href="Prelude.Preliminaries.html#13925" class="Bound">y</a> <a id="13927" href="Prelude.Preliminaries.html#13859" class="Function Operator">∥</a> <a id="13929" class="Symbol">=</a> <a id="13931" href="Prelude.Preliminaries.html#13925" class="Bound">y</a>
 <a id="13934" href="Prelude.Preliminaries.html#13863" class="Function">snd</a> <a id="13938" class="Symbol">(</a><a id="13939" href="Prelude.Preliminaries.html#13939" class="Bound">x</a> <a id="13941" href="Prelude.Preliminaries.html#13264" class="InductiveConstructor Operator">,</a> <a id="13943" href="Prelude.Preliminaries.html#13943" class="Bound">y</a><a id="13944" class="Symbol">)</a> <a id="13946" class="Symbol">=</a> <a id="13948" href="Prelude.Preliminaries.html#13943" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14217" class="Keyword">module</a> <a id="hide-pi"></a><a id="14224" href="Prelude.Preliminaries.html#14224" class="Module">hide-pi</a> <a id="14232" class="Symbol">{</a><a id="14233" href="Prelude.Preliminaries.html#14233" class="Bound">𝓤</a> <a id="14235" href="Prelude.Preliminaries.html#14235" class="Bound">𝓦</a> <a id="14237" class="Symbol">:</a> <a id="14239" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14247" class="Symbol">}</a> <a id="14249" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14257" href="Prelude.Preliminaries.html#14257" class="Function">Π</a> <a id="14259" class="Symbol">:</a> <a id="14261" class="Symbol">{</a><a id="14262" href="Prelude.Preliminaries.html#14262" class="Bound">X</a> <a id="14264" class="Symbol">:</a> <a id="14266" href="Prelude.Preliminaries.html#14233" class="Bound">𝓤</a> <a id="14268" href="Universes.html#403" class="Function Operator">̇</a> <a id="14270" class="Symbol">}</a> <a id="14272" class="Symbol">(</a><a id="14273" href="Prelude.Preliminaries.html#14273" class="Bound">A</a> <a id="14275" class="Symbol">:</a> <a id="14277" href="Prelude.Preliminaries.html#14262" class="Bound">X</a> <a id="14279" class="Symbol">→</a> <a id="14281" href="Prelude.Preliminaries.html#14235" class="Bound">𝓦</a> <a id="14283" href="Universes.html#403" class="Function Operator">̇</a> <a id="14285" class="Symbol">)</a> <a id="14287" class="Symbol">→</a> <a id="14289" href="Prelude.Preliminaries.html#14233" class="Bound">𝓤</a> <a id="14291" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14293" href="Prelude.Preliminaries.html#14235" class="Bound">𝓦</a> <a id="14295" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14298" href="Prelude.Preliminaries.html#14257" class="Function">Π</a> <a id="14300" class="Symbol">{</a><a id="14301" href="Prelude.Preliminaries.html#14301" class="Bound">X</a><a id="14302" class="Symbol">}</a> <a id="14304" href="Prelude.Preliminaries.html#14304" class="Bound">A</a> <a id="14306" class="Symbol">=</a> <a id="14308" class="Symbol">(</a><a id="14309" href="Prelude.Preliminaries.html#14309" class="Bound">x</a> <a id="14311" class="Symbol">:</a> <a id="14313" href="Prelude.Preliminaries.html#14301" class="Bound">X</a><a id="14314" class="Symbol">)</a> <a id="14316" class="Symbol">→</a> <a id="14318" href="Prelude.Preliminaries.html#14304" class="Bound">A</a> <a id="14320" href="Prelude.Preliminaries.html#14309" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14324" href="Prelude.Preliminaries.html#14324" class="Function">-Π</a> <a id="14327" class="Symbol">:</a> <a id="14329" class="Symbol">(</a><a id="14330" href="Prelude.Preliminaries.html#14330" class="Bound">X</a> <a id="14332" class="Symbol">:</a> <a id="14334" href="Prelude.Preliminaries.html#14233" class="Bound">𝓤</a> <a id="14336" href="Universes.html#403" class="Function Operator">̇</a> <a id="14338" class="Symbol">)(</a><a id="14340" href="Prelude.Preliminaries.html#14340" class="Bound">Y</a> <a id="14342" class="Symbol">:</a> <a id="14344" href="Prelude.Preliminaries.html#14330" class="Bound">X</a> <a id="14346" class="Symbol">→</a> <a id="14348" href="Prelude.Preliminaries.html#14235" class="Bound">𝓦</a> <a id="14350" href="Universes.html#403" class="Function Operator">̇</a> <a id="14352" class="Symbol">)</a> <a id="14354" class="Symbol">→</a> <a id="14356" href="Prelude.Preliminaries.html#14233" class="Bound">𝓤</a> <a id="14358" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14360" href="Prelude.Preliminaries.html#14235" class="Bound">𝓦</a> <a id="14362" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14365" href="Prelude.Preliminaries.html#14324" class="Function">-Π</a> <a id="14368" href="Prelude.Preliminaries.html#14368" class="Bound">X</a> <a id="14370" href="Prelude.Preliminaries.html#14370" class="Bound">Y</a> <a id="14372" class="Symbol">=</a> <a id="14374" href="Prelude.Preliminaries.html#14257" class="Function">Π</a> <a id="14376" href="Prelude.Preliminaries.html#14370" class="Bound">Y</a>

 <a id="14380" class="Keyword">infixr</a> <a id="14387" class="Number">-1</a> <a id="14390" href="Prelude.Preliminaries.html#14324" class="Function">-Π</a>
 <a id="14394" class="Keyword">syntax</a> <a id="14401" href="Prelude.Preliminaries.html#14324" class="Function">-Π</a> <a id="14404" class="Bound">A</a> <a id="14406" class="Symbol">(λ</a> <a id="14409" class="Bound">x</a> <a id="14411" class="Symbol">→</a> <a id="14413" class="Bound">b</a><a id="14414" class="Symbol">)</a> <a id="14416" class="Symbol">=</a> <a id="14418" class="Function">Π</a> <a id="14420" class="Bound">x</a> <a id="14422" class="Function">꞉</a> <a id="14424" class="Bound">A</a> <a id="14426" class="Function">,</a> <a id="14428" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].




----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

