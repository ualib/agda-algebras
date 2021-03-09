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

An Agda program typically begins by setting some options and by importing from existing libraries (in our case, the [Type Topology][] library by [Martín Escardó][]). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

<pre class="Agda">

<a id="1096" class="Symbol">{-#</a> <a id="1100" class="Keyword">OPTIONS</a> <a id="1108" class="Pragma">--without-K</a> <a id="1120" class="Pragma">--exact-split</a> <a id="1134" class="Pragma">--safe</a> <a id="1141" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda assumes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`; we would use the following `OPTIONS` line in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

but this is never done in publicly released versions of the UALib.





#### <a id="modules">Modules</a>

The `OPTIONS` line is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="2974" class="Keyword">module</a> <a id="2981" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="3003" class="Keyword">where</a>

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

<a id="5298" class="Keyword">open</a> <a id="5303" class="Keyword">import</a> <a id="5310" href="Universes.html" class="Module">Universes</a> <a id="5320" class="Keyword">public</a>

</pre>

Escardó's Universe module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="5585" class="Keyword">variable</a>
 <a id="5595" href="Prelude.Preliminaries.html#5595" class="Generalizable">𝓞</a> <a id="5597" class="Symbol">:</a> <a id="5599" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

The first three import lines have to be commented out because we will redefine the given types for pedagogical purposes in this module.

<pre class="Agda">

<a id="6783" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6857" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="6891" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6950" class="Keyword">open</a> <a id="6955" class="Keyword">import</a> <a id="6962" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6971" class="Keyword">using</a> <a id="6977" class="Symbol">(</a><a id="6978" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="6981" class="Symbol">;</a> <a id="6983" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="6989" class="Symbol">;</a> <a id="6991" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="6999" class="Symbol">;</a> <a id="7001" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7010" class="Symbol">;</a> <a id="7012" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7018" class="Symbol">;</a> <a id="7020" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7022" class="Symbol">;</a> <a id="7024" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7052" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7053" class="Symbol">;</a> <a id="7055" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7057" class="Symbol">;</a> <a id="7059" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7062" class="Symbol">;</a> <a id="7064" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7067" class="Symbol">;</a> <a id="7069" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7070" class="Symbol">;</a> <a id="7072" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7073" class="Symbol">;</a> <a id="7075" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7076" class="Symbol">;</a> <a id="7078" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7081" class="Symbol">;</a> <a id="7083" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7097" class="Symbol">;</a> <a id="7099" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7113" class="Symbol">;</a> <a id="7115" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7117" class="Symbol">;</a> <a id="7119" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7122" class="Symbol">;</a> <a id="7124" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7126" class="Symbol">)</a>

<a id="7129" class="Keyword">open</a> <a id="7134" class="Keyword">import</a> <a id="7141" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7158" class="Keyword">using</a> <a id="7164" class="Symbol">(</a><a id="7165" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7173" class="Symbol">;</a> <a id="7175" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7182" class="Symbol">;</a> <a id="7184" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7194" class="Symbol">)</a>

<a id="7197" class="Keyword">open</a> <a id="7202" class="Keyword">import</a> <a id="7209" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7235" class="Keyword">using</a> <a id="7241" class="Symbol">(</a><a id="7242" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7248" class="Symbol">;</a> <a id="7250" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7264" class="Symbol">;</a> <a id="7266" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7273" class="Symbol">;</a>
 <a id="7276" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7288" class="Symbol">;</a> <a id="7290" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7305" class="Symbol">;</a> <a id="7307" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7314" class="Symbol">;</a> <a id="7316" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7326" class="Symbol">;</a> <a id="7328" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7342" class="Symbol">;</a>
 <a id="7345" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7376" class="Symbol">;</a> <a id="7378" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7381" class="Symbol">;</a> <a id="7383" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7386" class="Symbol">;</a> <a id="7388" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7405" class="Symbol">;</a> <a id="7407" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7424" class="Symbol">;</a>
 <a id="7427" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7476" class="Symbol">)</a>

<a id="7479" class="Keyword">open</a> <a id="7484" class="Keyword">import</a> <a id="7491" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7504" class="Keyword">renaming</a> <a id="7513" class="Symbol">(</a><a id="7514" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7518" class="Symbol">to</a> <a id="_∈_"></a><a id="7521" href="Prelude.Preliminaries.html#7521" class="Function Operator">_∈₀_</a><a id="7525" class="Symbol">;</a> <a id="7527" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7531" class="Symbol">to</a> <a id="_⊆_"></a><a id="7534" href="Prelude.Preliminaries.html#7534" class="Function Operator">_⊆₀_</a><a id="7538" class="Symbol">;</a> <a id="7540" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7558" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7561" href="Prelude.Preliminaries.html#7561" class="Function">∈₀-is-subsingleton</a><a id="7579" class="Symbol">)</a>
 <a id="7582" class="Keyword">using</a> <a id="7588" class="Symbol">(</a><a id="7589" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7590" class="Symbol">;</a> <a id="7592" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7613" class="Symbol">;</a> <a id="7615" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7634" class="Symbol">;</a> <a id="7636" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7658" class="Symbol">;</a> <a id="7660" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7667" class="Symbol">;</a> <a id="7669" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7675" class="Symbol">;</a> <a id="7677" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7678" class="Symbol">)</a>

<a id="7681" class="Keyword">open</a> <a id="7686" class="Keyword">import</a> <a id="7693" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7708" class="Keyword">using</a> <a id="7714" class="Symbol">(</a><a id="7715" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7718" class="Symbol">;</a> <a id="7720" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7724" class="Symbol">;</a> <a id="7726" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7743" class="Symbol">;</a> <a id="7745" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7757" class="Symbol">;</a> <a id="7759" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7772" class="Symbol">;</a> <a id="7774" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7785" class="Symbol">;</a>
 <a id="7788" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7794" class="Symbol">;</a> <a id="7796" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7799" class="Symbol">;</a> <a id="7801" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="7828" class="Symbol">;</a> <a id="7830" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7847" class="Symbol">;</a> <a id="7849" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7866" class="Symbol">;</a> <a id="7868" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7883" class="Symbol">)</a>

<a id="7886" class="Keyword">open</a> <a id="7891" class="Keyword">import</a> <a id="7898" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7919" class="Keyword">using</a> <a id="7925" class="Symbol">(</a><a id="7926" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7938" class="Symbol">)</a>

<a id="7941" class="Keyword">open</a> <a id="7946" class="Keyword">import</a> <a id="7953" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="7974" class="Keyword">using</a> <a id="7980" class="Symbol">(</a><a id="7981" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="7983" class="Symbol">;</a> <a id="7985" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="7988" class="Symbol">)</a>

<a id="7991" class="Keyword">open</a> <a id="7996" class="Keyword">import</a> <a id="8003" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8031" class="Keyword">using</a> <a id="8037" class="Symbol">(</a><a id="8038" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8041" class="Symbol">;</a> <a id="8043" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8049" class="Symbol">;</a> <a id="8051" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8072" class="Symbol">;</a>
 <a id="8075" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8097" class="Symbol">;</a> <a id="8099" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8104" class="Symbol">;</a> <a id="8106" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8124" class="Symbol">;</a> <a id="8126" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8133" class="Symbol">)</a>

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

<a id="11746" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11753" href="Prelude.Preliminaries.html#11753" class="Module">hide-sigma</a> <a id="11764" class="Keyword">where</a>

 <a id="11772" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11779" href="Prelude.Preliminaries.html#11779" class="Record">Σ</a> <a id="11781" class="Symbol">{</a><a id="11782" href="Prelude.Preliminaries.html#11782" class="Bound">𝓤</a> <a id="11784" href="Prelude.Preliminaries.html#11784" class="Bound">𝓥</a><a id="11785" class="Symbol">}</a> <a id="11787" class="Symbol">{</a><a id="11788" href="Prelude.Preliminaries.html#11788" class="Bound">X</a> <a id="11790" class="Symbol">:</a> <a id="11792" href="Prelude.Preliminaries.html#11782" class="Bound">𝓤</a> <a id="11794" href="Universes.html#403" class="Function Operator">̇</a> <a id="11796" class="Symbol">}</a> <a id="11798" class="Symbol">(</a><a id="11799" href="Prelude.Preliminaries.html#11799" class="Bound">Y</a> <a id="11801" class="Symbol">:</a> <a id="11803" href="Prelude.Preliminaries.html#11788" class="Bound">X</a> <a id="11805" class="Symbol">→</a> <a id="11807" href="Prelude.Preliminaries.html#11784" class="Bound">𝓥</a> <a id="11809" href="Universes.html#403" class="Function Operator">̇</a> <a id="11811" class="Symbol">)</a> <a id="11813" class="Symbol">:</a> <a id="11815" href="Prelude.Preliminaries.html#11782" class="Bound">𝓤</a> <a id="11817" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11819" href="Prelude.Preliminaries.html#11784" class="Bound">𝓥</a> <a id="11821" href="Universes.html#403" class="Function Operator">̇</a>  <a id="11824" class="Keyword">where</a>
  <a id="11832" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="11844" href="Prelude.Preliminaries.html#11844" class="InductiveConstructor Operator">_,_</a>
  <a id="11850" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="11859" href="Prelude.Preliminaries.html#11859" class="Field">pr₁</a> <a id="11863" class="Symbol">:</a> <a id="11865" href="Prelude.Preliminaries.html#11788" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="11870" href="Prelude.Preliminaries.html#11870" class="Field">pr₂</a> <a id="11874" class="Symbol">:</a> <a id="11876" href="Prelude.Preliminaries.html#11799" class="Bound">Y</a> <a id="11878" href="Prelude.Preliminaries.html#11859" class="Field">pr₁</a>

 <a id="11884" class="Keyword">infixr</a> <a id="11891" class="Number">50</a> <a id="11894" href="Prelude.Preliminaries.html#11844" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12215" href="Prelude.Preliminaries.html#12215" class="Function">-Σ</a> <a id="12218" class="Symbol">:</a> <a id="12220" class="Symbol">{</a><a id="12221" href="Prelude.Preliminaries.html#12221" class="Bound">𝓤</a> <a id="12223" href="Prelude.Preliminaries.html#12223" class="Bound">𝓥</a> <a id="12225" class="Symbol">:</a> <a id="12227" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12235" class="Symbol">}</a> <a id="12237" class="Symbol">(</a><a id="12238" href="Prelude.Preliminaries.html#12238" class="Bound">X</a> <a id="12240" class="Symbol">:</a> <a id="12242" href="Prelude.Preliminaries.html#12221" class="Bound">𝓤</a> <a id="12244" href="Universes.html#403" class="Function Operator">̇</a> <a id="12246" class="Symbol">)</a> <a id="12248" class="Symbol">(</a><a id="12249" href="Prelude.Preliminaries.html#12249" class="Bound">Y</a> <a id="12251" class="Symbol">:</a> <a id="12253" href="Prelude.Preliminaries.html#12238" class="Bound">X</a> <a id="12255" class="Symbol">→</a> <a id="12257" href="Prelude.Preliminaries.html#12223" class="Bound">𝓥</a> <a id="12259" href="Universes.html#403" class="Function Operator">̇</a> <a id="12261" class="Symbol">)</a> <a id="12263" class="Symbol">→</a> <a id="12265" href="Prelude.Preliminaries.html#12221" class="Bound">𝓤</a> <a id="12267" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12269" href="Prelude.Preliminaries.html#12223" class="Bound">𝓥</a> <a id="12271" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12274" href="Prelude.Preliminaries.html#12215" class="Function">-Σ</a> <a id="12277" href="Prelude.Preliminaries.html#12277" class="Bound">X</a> <a id="12279" href="Prelude.Preliminaries.html#12279" class="Bound">Y</a> <a id="12281" class="Symbol">=</a> <a id="12283" href="Prelude.Preliminaries.html#11779" class="Record">Σ</a> <a id="12285" href="Prelude.Preliminaries.html#12279" class="Bound">Y</a>

 <a id="12289" class="Keyword">syntax</a> <a id="12296" href="Prelude.Preliminaries.html#12215" class="Function">-Σ</a> <a id="12299" class="Bound">X</a> <a id="12301" class="Symbol">(λ</a> <a id="12304" class="Bound">x</a> <a id="12306" class="Symbol">→</a> <a id="12308" class="Bound">Y</a><a id="12309" class="Symbol">)</a> <a id="12311" class="Symbol">=</a> <a id="12313" class="Function">Σ</a> <a id="12315" class="Bound">x</a> <a id="12317" class="Function">꞉</a> <a id="12319" class="Bound">X</a> <a id="12321" class="Function">,</a> <a id="12323" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12696" href="Prelude.Preliminaries.html#12696" class="Function Operator">_×_</a> <a id="12700" class="Symbol">:</a> <a id="12702" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12704" href="Universes.html#403" class="Function Operator">̇</a> <a id="12706" class="Symbol">→</a> <a id="12708" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12710" href="Universes.html#403" class="Function Operator">̇</a> <a id="12712" class="Symbol">→</a> <a id="12714" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12716" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12718" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12720" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12723" href="Prelude.Preliminaries.html#12723" class="Bound">X</a> <a id="12725" href="Prelude.Preliminaries.html#12696" class="Function Operator">×</a> <a id="12727" href="Prelude.Preliminaries.html#12727" class="Bound">Y</a> <a id="12729" class="Symbol">=</a> <a id="12731" href="Prelude.Preliminaries.html#12215" class="Function">Σ</a> <a id="12733" href="Prelude.Preliminaries.html#12733" class="Bound">x</a> <a id="12735" href="Prelude.Preliminaries.html#12215" class="Function">꞉</a> <a id="12737" href="Prelude.Preliminaries.html#12723" class="Bound">X</a> <a id="12739" href="Prelude.Preliminaries.html#12215" class="Function">,</a> <a id="12741" href="Prelude.Preliminaries.html#12727" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="12951" class="Keyword">open</a> <a id="12956" class="Keyword">import</a> <a id="12963" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12974" class="Keyword">renaming</a> <a id="12983" class="Symbol">(</a><a id="12984" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="12988" class="Symbol">to</a> <a id="12991" class="Keyword">infixr</a> <a id="12998" class="Number">50</a> <a id="_,_"></a><a id="13001" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">_,_</a><a id="13004" class="Symbol">)</a>
<a id="13006" class="Keyword">open</a> <a id="13011" class="Keyword">import</a> <a id="13018" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13027" class="Keyword">using</a> <a id="13033" class="Symbol">(</a><a id="13034" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13037" class="Symbol">;</a> <a id="13039" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13042" class="Symbol">;</a> <a id="13044" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13047" class="Symbol">;</a> <a id="13049" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13051" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13486" class="Keyword">module</a> <a id="13493" href="Prelude.Preliminaries.html#13493" class="Module">_</a> <a id="13495" class="Symbol">{</a><a id="13496" href="Prelude.Preliminaries.html#13496" class="Bound">𝓤</a> <a id="13498" class="Symbol">:</a> <a id="13500" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13508" class="Symbol">}</a> <a id="13510" class="Keyword">where</a>

 <a id="13518" href="Prelude.Preliminaries.html#13518" class="Function Operator">∣_∣</a> <a id="13522" href="Prelude.Preliminaries.html#13522" class="Function">fst</a> <a id="13526" class="Symbol">:</a> <a id="13528" class="Symbol">{</a><a id="13529" href="Prelude.Preliminaries.html#13529" class="Bound">X</a> <a id="13531" class="Symbol">:</a> <a id="13533" href="Prelude.Preliminaries.html#13496" class="Bound">𝓤</a> <a id="13535" href="Universes.html#403" class="Function Operator">̇</a> <a id="13537" class="Symbol">}{</a><a id="13539" href="Prelude.Preliminaries.html#13539" class="Bound">Y</a> <a id="13541" class="Symbol">:</a> <a id="13543" href="Prelude.Preliminaries.html#13529" class="Bound">X</a> <a id="13545" class="Symbol">→</a> <a id="13547" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13549" href="Universes.html#403" class="Function Operator">̇</a><a id="13550" class="Symbol">}</a> <a id="13552" class="Symbol">→</a> <a id="13554" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13556" href="Prelude.Preliminaries.html#13539" class="Bound">Y</a> <a id="13558" class="Symbol">→</a> <a id="13560" href="Prelude.Preliminaries.html#13529" class="Bound">X</a>
 <a id="13563" href="Prelude.Preliminaries.html#13518" class="Function Operator">∣</a> <a id="13565" href="Prelude.Preliminaries.html#13565" class="Bound">x</a> <a id="13567" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="13569" href="Prelude.Preliminaries.html#13569" class="Bound">y</a> <a id="13571" href="Prelude.Preliminaries.html#13518" class="Function Operator">∣</a> <a id="13573" class="Symbol">=</a> <a id="13575" href="Prelude.Preliminaries.html#13565" class="Bound">x</a>
 <a id="13578" href="Prelude.Preliminaries.html#13522" class="Function">fst</a> <a id="13582" class="Symbol">(</a><a id="13583" href="Prelude.Preliminaries.html#13583" class="Bound">x</a> <a id="13585" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="13587" href="Prelude.Preliminaries.html#13587" class="Bound">y</a><a id="13588" class="Symbol">)</a> <a id="13590" class="Symbol">=</a> <a id="13592" href="Prelude.Preliminaries.html#13583" class="Bound">x</a>

 <a id="13596" href="Prelude.Preliminaries.html#13596" class="Function Operator">∥_∥</a> <a id="13600" href="Prelude.Preliminaries.html#13600" class="Function">snd</a> <a id="13604" class="Symbol">:</a> <a id="13606" class="Symbol">{</a><a id="13607" href="Prelude.Preliminaries.html#13607" class="Bound">X</a> <a id="13609" class="Symbol">:</a> <a id="13611" href="Prelude.Preliminaries.html#13496" class="Bound">𝓤</a> <a id="13613" href="Universes.html#403" class="Function Operator">̇</a> <a id="13615" class="Symbol">}{</a><a id="13617" href="Prelude.Preliminaries.html#13617" class="Bound">Y</a> <a id="13619" class="Symbol">:</a> <a id="13621" href="Prelude.Preliminaries.html#13607" class="Bound">X</a> <a id="13623" class="Symbol">→</a> <a id="13625" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13627" href="Universes.html#403" class="Function Operator">̇</a> <a id="13629" class="Symbol">}</a> <a id="13631" class="Symbol">→</a> <a id="13633" class="Symbol">(</a><a id="13634" href="Prelude.Preliminaries.html#13634" class="Bound">z</a> <a id="13636" class="Symbol">:</a> <a id="13638" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13640" href="Prelude.Preliminaries.html#13617" class="Bound">Y</a><a id="13641" class="Symbol">)</a> <a id="13643" class="Symbol">→</a> <a id="13645" href="Prelude.Preliminaries.html#13617" class="Bound">Y</a> <a id="13647" class="Symbol">(</a><a id="13648" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13652" href="Prelude.Preliminaries.html#13634" class="Bound">z</a><a id="13653" class="Symbol">)</a>
 <a id="13656" href="Prelude.Preliminaries.html#13596" class="Function Operator">∥</a> <a id="13658" href="Prelude.Preliminaries.html#13658" class="Bound">x</a> <a id="13660" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="13662" href="Prelude.Preliminaries.html#13662" class="Bound">y</a> <a id="13664" href="Prelude.Preliminaries.html#13596" class="Function Operator">∥</a> <a id="13666" class="Symbol">=</a> <a id="13668" href="Prelude.Preliminaries.html#13662" class="Bound">y</a>
 <a id="13671" href="Prelude.Preliminaries.html#13600" class="Function">snd</a> <a id="13675" class="Symbol">(</a><a id="13676" href="Prelude.Preliminaries.html#13676" class="Bound">x</a> <a id="13678" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="13680" href="Prelude.Preliminaries.html#13680" class="Bound">y</a><a id="13681" class="Symbol">)</a> <a id="13683" class="Symbol">=</a> <a id="13685" href="Prelude.Preliminaries.html#13680" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="13962" class="Keyword">module</a> <a id="hide-pi"></a><a id="13969" href="Prelude.Preliminaries.html#13969" class="Module">hide-pi</a> <a id="13977" class="Symbol">{</a><a id="13978" href="Prelude.Preliminaries.html#13978" class="Bound">𝓤</a> <a id="13980" href="Prelude.Preliminaries.html#13980" class="Bound">𝓦</a> <a id="13982" class="Symbol">:</a> <a id="13984" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13992" class="Symbol">}</a> <a id="13994" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14002" href="Prelude.Preliminaries.html#14002" class="Function">Π</a> <a id="14004" class="Symbol">:</a> <a id="14006" class="Symbol">{</a><a id="14007" href="Prelude.Preliminaries.html#14007" class="Bound">X</a> <a id="14009" class="Symbol">:</a> <a id="14011" href="Prelude.Preliminaries.html#13978" class="Bound">𝓤</a> <a id="14013" href="Universes.html#403" class="Function Operator">̇</a> <a id="14015" class="Symbol">}</a> <a id="14017" class="Symbol">(</a><a id="14018" href="Prelude.Preliminaries.html#14018" class="Bound">A</a> <a id="14020" class="Symbol">:</a> <a id="14022" href="Prelude.Preliminaries.html#14007" class="Bound">X</a> <a id="14024" class="Symbol">→</a> <a id="14026" href="Prelude.Preliminaries.html#13980" class="Bound">𝓦</a> <a id="14028" href="Universes.html#403" class="Function Operator">̇</a> <a id="14030" class="Symbol">)</a> <a id="14032" class="Symbol">→</a> <a id="14034" href="Prelude.Preliminaries.html#13978" class="Bound">𝓤</a> <a id="14036" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14038" href="Prelude.Preliminaries.html#13980" class="Bound">𝓦</a> <a id="14040" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14043" href="Prelude.Preliminaries.html#14002" class="Function">Π</a> <a id="14045" class="Symbol">{</a><a id="14046" href="Prelude.Preliminaries.html#14046" class="Bound">X</a><a id="14047" class="Symbol">}</a> <a id="14049" href="Prelude.Preliminaries.html#14049" class="Bound">A</a> <a id="14051" class="Symbol">=</a> <a id="14053" class="Symbol">(</a><a id="14054" href="Prelude.Preliminaries.html#14054" class="Bound">x</a> <a id="14056" class="Symbol">:</a> <a id="14058" href="Prelude.Preliminaries.html#14046" class="Bound">X</a><a id="14059" class="Symbol">)</a> <a id="14061" class="Symbol">→</a> <a id="14063" href="Prelude.Preliminaries.html#14049" class="Bound">A</a> <a id="14065" href="Prelude.Preliminaries.html#14054" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14069" href="Prelude.Preliminaries.html#14069" class="Function">-Π</a> <a id="14072" class="Symbol">:</a> <a id="14074" class="Symbol">(</a><a id="14075" href="Prelude.Preliminaries.html#14075" class="Bound">X</a> <a id="14077" class="Symbol">:</a> <a id="14079" href="Prelude.Preliminaries.html#13978" class="Bound">𝓤</a> <a id="14081" href="Universes.html#403" class="Function Operator">̇</a> <a id="14083" class="Symbol">)(</a><a id="14085" href="Prelude.Preliminaries.html#14085" class="Bound">Y</a> <a id="14087" class="Symbol">:</a> <a id="14089" href="Prelude.Preliminaries.html#14075" class="Bound">X</a> <a id="14091" class="Symbol">→</a> <a id="14093" href="Prelude.Preliminaries.html#13980" class="Bound">𝓦</a> <a id="14095" href="Universes.html#403" class="Function Operator">̇</a> <a id="14097" class="Symbol">)</a> <a id="14099" class="Symbol">→</a> <a id="14101" href="Prelude.Preliminaries.html#13978" class="Bound">𝓤</a> <a id="14103" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14105" href="Prelude.Preliminaries.html#13980" class="Bound">𝓦</a> <a id="14107" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14110" href="Prelude.Preliminaries.html#14069" class="Function">-Π</a> <a id="14113" href="Prelude.Preliminaries.html#14113" class="Bound">X</a> <a id="14115" href="Prelude.Preliminaries.html#14115" class="Bound">Y</a> <a id="14117" class="Symbol">=</a> <a id="14119" href="Prelude.Preliminaries.html#14002" class="Function">Π</a> <a id="14121" href="Prelude.Preliminaries.html#14115" class="Bound">Y</a>

 <a id="14125" class="Keyword">infixr</a> <a id="14132" class="Number">-1</a> <a id="14135" href="Prelude.Preliminaries.html#14069" class="Function">-Π</a>
 <a id="14139" class="Keyword">syntax</a> <a id="14146" href="Prelude.Preliminaries.html#14069" class="Function">-Π</a> <a id="14149" class="Bound">A</a> <a id="14151" class="Symbol">(λ</a> <a id="14154" class="Bound">x</a> <a id="14156" class="Symbol">→</a> <a id="14158" class="Bound">b</a><a id="14159" class="Symbol">)</a> <a id="14161" class="Symbol">=</a> <a id="14163" class="Function">Π</a> <a id="14165" class="Bound">x</a> <a id="14167" class="Function">꞉</a> <a id="14169" class="Bound">A</a> <a id="14171" class="Function">,</a> <a id="14173" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14463" class="Keyword">open</a> <a id="14468" class="Keyword">import</a> <a id="14475" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14486" class="Keyword">renaming</a> <a id="14495" class="Symbol">(</a><a id="14496" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14500" class="Symbol">to</a> <a id="14503" class="Keyword">infixr</a> <a id="14510" class="Number">50</a> <a id="_,_"></a><a id="14513" href="Prelude.Preliminaries.html#14513" class="InductiveConstructor Operator">_,_</a><a id="14516" class="Symbol">)</a> <a id="14518" class="Keyword">public</a>
<a id="14525" class="Keyword">open</a> <a id="14530" class="Keyword">import</a> <a id="14537" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14546" class="Keyword">using</a> <a id="14552" class="Symbol">(</a><a id="14553" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14556" class="Symbol">;</a> <a id="14558" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14561" class="Symbol">;</a> <a id="14563" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14566" class="Symbol">;</a> <a id="14568" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14570" class="Symbol">;</a> <a id="14572" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14573" class="Symbol">)</a> <a id="14575" class="Keyword">public</a>


<a id="14584" class="Keyword">module</a> <a id="14591" href="Prelude.Preliminaries.html#14591" class="Module">_</a> <a id="14593" class="Symbol">{</a><a id="14594" href="Prelude.Preliminaries.html#14594" class="Bound">𝓨</a> <a id="14596" href="Prelude.Preliminaries.html#14596" class="Bound">𝓩</a> <a id="14598" class="Symbol">:</a> <a id="14600" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14608" class="Symbol">}{</a><a id="14610" href="Prelude.Preliminaries.html#14610" class="Bound">I</a> <a id="14612" class="Symbol">:</a> <a id="14614" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14616" href="Universes.html#403" class="Function Operator">̇</a><a id="14617" class="Symbol">}{</a><a id="14619" href="Prelude.Preliminaries.html#14619" class="Bound">B</a> <a id="14621" class="Symbol">:</a> <a id="14623" href="Prelude.Preliminaries.html#14610" class="Bound">I</a> <a id="14625" class="Symbol">→</a> <a id="14627" href="Prelude.Preliminaries.html#14594" class="Bound">𝓨</a> <a id="14629" href="Universes.html#403" class="Function Operator">̇</a><a id="14630" class="Symbol">}{</a><a id="14632" href="Prelude.Preliminaries.html#14632" class="Bound">C</a> <a id="14634" class="Symbol">:</a> <a id="14636" href="Prelude.Preliminaries.html#14610" class="Bound">I</a> <a id="14638" class="Symbol">→</a> <a id="14640" href="Prelude.Preliminaries.html#14596" class="Bound">𝓩</a> <a id="14642" href="Universes.html#403" class="Function Operator">̇</a><a id="14643" class="Symbol">}</a> <a id="14645" class="Keyword">where</a>
 <a id="14652" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14675" href="Prelude.Preliminaries.html#14675" class="Function">zip</a> <a id="14679" class="Symbol">:</a> <a id="14681" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14683" href="Prelude.Preliminaries.html#14619" class="Bound">B</a> <a id="14685" class="Symbol">→</a> <a id="14687" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14689" href="Prelude.Preliminaries.html#14632" class="Bound">C</a> <a id="14691" class="Symbol">→</a> <a id="14693" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14695" class="Symbol">(λ</a> <a id="14698" href="Prelude.Preliminaries.html#14698" class="Bound">i</a> <a id="14700" class="Symbol">→</a> <a id="14702" class="Symbol">(</a><a id="14703" href="Prelude.Preliminaries.html#14619" class="Bound">B</a> <a id="14705" href="Prelude.Preliminaries.html#14698" class="Bound">i</a><a id="14706" class="Symbol">)</a> <a id="14708" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14710" class="Symbol">(</a><a id="14711" href="Prelude.Preliminaries.html#14632" class="Bound">C</a> <a id="14713" href="Prelude.Preliminaries.html#14698" class="Bound">i</a><a id="14714" class="Symbol">))</a>
 <a id="14718" href="Prelude.Preliminaries.html#14675" class="Function">zip</a> <a id="14722" href="Prelude.Preliminaries.html#14722" class="Bound">f</a> <a id="14724" href="Prelude.Preliminaries.html#14724" class="Bound">a</a> <a id="14726" class="Symbol">=</a> <a id="14728" class="Symbol">λ</a> <a id="14730" href="Prelude.Preliminaries.html#14730" class="Bound">i</a> <a id="14732" class="Symbol">→</a> <a id="14734" class="Symbol">(</a><a id="14735" href="Prelude.Preliminaries.html#14722" class="Bound">f</a> <a id="14737" href="Prelude.Preliminaries.html#14730" class="Bound">i</a> <a id="14739" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="14741" href="Prelude.Preliminaries.html#14724" class="Bound">a</a> <a id="14743" href="Prelude.Preliminaries.html#14730" class="Bound">i</a><a id="14744" class="Symbol">)</a>

 <a id="14748" href="Prelude.Preliminaries.html#14748" class="Function">eval</a> <a id="14753" class="Symbol">:</a> <a id="14755" class="Symbol">{</a><a id="14756" href="Prelude.Preliminaries.html#14756" class="Bound">Y</a> <a id="14758" class="Symbol">:</a> <a id="14760" href="Prelude.Preliminaries.html#14594" class="Bound">𝓨</a> <a id="14762" href="Universes.html#403" class="Function Operator">̇</a><a id="14763" class="Symbol">}{</a><a id="14765" href="Prelude.Preliminaries.html#14765" class="Bound">Z</a> <a id="14767" class="Symbol">:</a> <a id="14769" href="Prelude.Preliminaries.html#14596" class="Bound">𝓩</a> <a id="14771" href="Universes.html#403" class="Function Operator">̇</a><a id="14772" class="Symbol">}</a> <a id="14774" class="Symbol">→</a> <a id="14776" class="Symbol">((</a><a id="14778" href="Prelude.Preliminaries.html#14756" class="Bound">Y</a> <a id="14780" class="Symbol">→</a> <a id="14782" href="Prelude.Preliminaries.html#14765" class="Bound">Z</a><a id="14783" class="Symbol">)</a> <a id="14785" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14787" href="Prelude.Preliminaries.html#14756" class="Bound">Y</a><a id="14788" class="Symbol">)</a> <a id="14790" class="Symbol">→</a> <a id="14792" href="Prelude.Preliminaries.html#14765" class="Bound">Z</a>
 <a id="14795" href="Prelude.Preliminaries.html#14748" class="Function">eval</a> <a id="14800" class="Symbol">(</a><a id="14801" href="Prelude.Preliminaries.html#14801" class="Bound">f</a> <a id="14803" href="Prelude.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="14805" href="Prelude.Preliminaries.html#14805" class="Bound">a</a><a id="14806" class="Symbol">)</a> <a id="14808" class="Symbol">=</a> <a id="14810" href="Prelude.Preliminaries.html#14801" class="Bound">f</a> <a id="14812" href="Prelude.Preliminaries.html#14805" class="Bound">a</a>

<a id="14815" class="Keyword">module</a> <a id="14822" href="Prelude.Preliminaries.html#14822" class="Module">_</a> <a id="14824" class="Symbol">{</a><a id="14825" href="Prelude.Preliminaries.html#14825" class="Bound">𝓨</a> <a id="14827" class="Symbol">:</a> <a id="14829" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14837" class="Symbol">}{</a><a id="14839" href="Prelude.Preliminaries.html#14839" class="Bound">I</a> <a id="14841" href="Prelude.Preliminaries.html#14841" class="Bound">J</a> <a id="14843" class="Symbol">:</a> <a id="14845" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14847" href="Universes.html#403" class="Function Operator">̇</a><a id="14848" class="Symbol">}{</a><a id="14850" href="Prelude.Preliminaries.html#14850" class="Bound">B</a> <a id="14852" class="Symbol">:</a> <a id="14854" href="Prelude.Preliminaries.html#14839" class="Bound">I</a> <a id="14856" class="Symbol">→</a> <a id="14858" href="Prelude.Preliminaries.html#14825" class="Bound">𝓨</a> <a id="14860" href="Universes.html#403" class="Function Operator">̇</a><a id="14861" class="Symbol">}</a> <a id="14863" class="Keyword">where</a>

 <a id="14871" href="Prelude.Preliminaries.html#14871" class="Function">dapp</a> <a id="14876" class="Symbol">:</a> <a id="14878" class="Symbol">(∀</a> <a id="14881" href="Prelude.Preliminaries.html#14881" class="Bound">i</a> <a id="14883" class="Symbol">→</a> <a id="14885" class="Symbol">(</a><a id="14886" href="Prelude.Preliminaries.html#14841" class="Bound">J</a> <a id="14888" class="Symbol">→</a> <a id="14890" class="Symbol">(</a><a id="14891" href="Prelude.Preliminaries.html#14850" class="Bound">B</a> <a id="14893" href="Prelude.Preliminaries.html#14881" class="Bound">i</a><a id="14894" class="Symbol">))</a> <a id="14897" class="Symbol">→</a> <a id="14899" class="Symbol">(</a><a id="14900" href="Prelude.Preliminaries.html#14850" class="Bound">B</a> <a id="14902" href="Prelude.Preliminaries.html#14881" class="Bound">i</a><a id="14903" class="Symbol">))</a> <a id="14906" class="Symbol">→</a> <a id="14908" class="Symbol">(∀</a> <a id="14911" href="Prelude.Preliminaries.html#14911" class="Bound">i</a> <a id="14913" class="Symbol">→</a> <a id="14915" class="Symbol">(</a><a id="14916" href="Prelude.Preliminaries.html#14841" class="Bound">J</a> <a id="14918" class="Symbol">→</a> <a id="14920" class="Symbol">(</a><a id="14921" href="Prelude.Preliminaries.html#14850" class="Bound">B</a> <a id="14923" href="Prelude.Preliminaries.html#14911" class="Bound">i</a><a id="14924" class="Symbol">)))</a> <a id="14928" class="Symbol">→</a> <a id="14930" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14932" href="Prelude.Preliminaries.html#14850" class="Bound">B</a>
 <a id="14935" href="Prelude.Preliminaries.html#14871" class="Function">dapp</a> <a id="14940" href="Prelude.Preliminaries.html#14940" class="Bound">f</a> <a id="14942" href="Prelude.Preliminaries.html#14942" class="Bound">a</a> <a id="14944" class="Symbol">=</a> <a id="14946" class="Symbol">λ</a> <a id="14948" href="Prelude.Preliminaries.html#14948" class="Bound">i</a> <a id="14950" class="Symbol">→</a> <a id="14952" class="Symbol">(</a><a id="14953" href="Prelude.Preliminaries.html#14940" class="Bound">f</a> <a id="14955" href="Prelude.Preliminaries.html#14948" class="Bound">i</a><a id="14956" class="Symbol">)</a> <a id="14958" class="Symbol">(</a><a id="14959" href="Prelude.Preliminaries.html#14942" class="Bound">a</a> <a id="14961" href="Prelude.Preliminaries.html#14948" class="Bound">i</a><a id="14962" class="Symbol">)</a>

</pre>

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<p></p>
<p></p>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

