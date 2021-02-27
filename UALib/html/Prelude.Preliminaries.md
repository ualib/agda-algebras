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

(The first three import lines have to be commented out because we will actually redefine the given types for pedagogical purposes in the next couple of modules.)

<pre class="Agda">

<a id="6814" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6888" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="6922" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6981" class="Keyword">open</a> <a id="6986" class="Keyword">import</a> <a id="6993" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7002" class="Keyword">using</a> <a id="7008" class="Symbol">(</a><a id="7009" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7012" class="Symbol">;</a> <a id="7014" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7020" class="Symbol">;</a> <a id="7022" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7030" class="Symbol">;</a> <a id="7032" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7041" class="Symbol">;</a> <a id="7043" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7049" class="Symbol">;</a> <a id="7051" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7053" class="Symbol">;</a> <a id="7055" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7083" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7084" class="Symbol">;</a> <a id="7086" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7088" class="Symbol">;</a> <a id="7090" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7093" class="Symbol">;</a> <a id="7095" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7098" class="Symbol">;</a> <a id="7100" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7101" class="Symbol">;</a> <a id="7103" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7104" class="Symbol">;</a> <a id="7106" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7107" class="Symbol">;</a> <a id="7109" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7112" class="Symbol">;</a> <a id="7114" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7128" class="Symbol">;</a> <a id="7130" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7144" class="Symbol">;</a> <a id="7146" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7148" class="Symbol">;</a> <a id="7150" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7153" class="Symbol">;</a> <a id="7155" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7157" class="Symbol">)</a>

<a id="7160" class="Keyword">open</a> <a id="7165" class="Keyword">import</a> <a id="7172" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7189" class="Keyword">using</a> <a id="7195" class="Symbol">(</a><a id="7196" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7204" class="Symbol">;</a> <a id="7206" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7213" class="Symbol">;</a> <a id="7215" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7225" class="Symbol">)</a>

<a id="7228" class="Keyword">open</a> <a id="7233" class="Keyword">import</a> <a id="7240" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7266" class="Keyword">using</a> <a id="7272" class="Symbol">(</a><a id="7273" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7279" class="Symbol">;</a> <a id="7281" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7295" class="Symbol">;</a> <a id="7297" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7304" class="Symbol">;</a>
 <a id="7307" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7319" class="Symbol">;</a> <a id="7321" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7336" class="Symbol">;</a> <a id="7338" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7345" class="Symbol">;</a> <a id="7347" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7357" class="Symbol">;</a> <a id="7359" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7373" class="Symbol">;</a>
 <a id="7376" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7407" class="Symbol">;</a> <a id="7409" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7412" class="Symbol">;</a> <a id="7414" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7417" class="Symbol">;</a> <a id="7419" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7436" class="Symbol">;</a> <a id="7438" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7455" class="Symbol">;</a>
 <a id="7458" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7507" class="Symbol">)</a>

<a id="7510" class="Keyword">open</a> <a id="7515" class="Keyword">import</a> <a id="7522" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7535" class="Keyword">renaming</a> <a id="7544" class="Symbol">(</a><a id="7545" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7549" class="Symbol">to</a> <a id="_∈_"></a><a id="7552" href="Prelude.Preliminaries.html#7552" class="Function Operator">_∈₀_</a><a id="7556" class="Symbol">;</a> <a id="7558" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7562" class="Symbol">to</a> <a id="_⊆_"></a><a id="7565" href="Prelude.Preliminaries.html#7565" class="Function Operator">_⊆₀_</a><a id="7569" class="Symbol">;</a> <a id="7571" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7589" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7592" href="Prelude.Preliminaries.html#7592" class="Function">∈₀-is-subsingleton</a><a id="7610" class="Symbol">)</a>
 <a id="7613" class="Keyword">using</a> <a id="7619" class="Symbol">(</a><a id="7620" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7621" class="Symbol">;</a> <a id="7623" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7644" class="Symbol">;</a> <a id="7646" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7665" class="Symbol">;</a> <a id="7667" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7689" class="Symbol">;</a> <a id="7691" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7698" class="Symbol">;</a> <a id="7700" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7706" class="Symbol">;</a> <a id="7708" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7709" class="Symbol">)</a>

<a id="7712" class="Keyword">open</a> <a id="7717" class="Keyword">import</a> <a id="7724" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7739" class="Keyword">using</a> <a id="7745" class="Symbol">(</a><a id="7746" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7749" class="Symbol">;</a> <a id="7751" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7755" class="Symbol">;</a> <a id="7757" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7774" class="Symbol">;</a> <a id="7776" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7788" class="Symbol">;</a> <a id="7790" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7803" class="Symbol">;</a> <a id="7805" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7816" class="Symbol">;</a>
 <a id="7819" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7825" class="Symbol">;</a> <a id="7827" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7830" class="Symbol">;</a> <a id="7832" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="7859" class="Symbol">;</a> <a id="7861" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7878" class="Symbol">;</a> <a id="7880" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7897" class="Symbol">;</a> <a id="7899" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7914" class="Symbol">)</a>

<a id="7917" class="Keyword">open</a> <a id="7922" class="Keyword">import</a> <a id="7929" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7950" class="Keyword">using</a> <a id="7956" class="Symbol">(</a><a id="7957" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7969" class="Symbol">)</a>

<a id="7972" class="Keyword">open</a> <a id="7977" class="Keyword">import</a> <a id="7984" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8005" class="Keyword">using</a> <a id="8011" class="Symbol">(</a><a id="8012" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8014" class="Symbol">;</a> <a id="8016" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8019" class="Symbol">)</a>

<a id="8022" class="Keyword">open</a> <a id="8027" class="Keyword">import</a> <a id="8034" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8062" class="Keyword">using</a> <a id="8068" class="Symbol">(</a><a id="8069" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8072" class="Symbol">;</a> <a id="8074" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8080" class="Symbol">;</a> <a id="8082" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8103" class="Symbol">;</a>
 <a id="8106" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8128" class="Symbol">;</a> <a id="8130" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8135" class="Symbol">;</a> <a id="8137" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8155" class="Symbol">;</a> <a id="8157" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8164" class="Symbol">)</a>

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

<a id="11777" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11784" href="Prelude.Preliminaries.html#11784" class="Module">hide-sigma</a> <a id="11795" class="Keyword">where</a>

 <a id="11803" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11810" href="Prelude.Preliminaries.html#11810" class="Record">Σ</a> <a id="11812" class="Symbol">{</a><a id="11813" href="Prelude.Preliminaries.html#11813" class="Bound">𝓤</a> <a id="11815" href="Prelude.Preliminaries.html#11815" class="Bound">𝓥</a><a id="11816" class="Symbol">}</a> <a id="11818" class="Symbol">{</a><a id="11819" href="Prelude.Preliminaries.html#11819" class="Bound">X</a> <a id="11821" class="Symbol">:</a> <a id="11823" href="Prelude.Preliminaries.html#11813" class="Bound">𝓤</a> <a id="11825" href="Universes.html#403" class="Function Operator">̇</a> <a id="11827" class="Symbol">}</a> <a id="11829" class="Symbol">(</a><a id="11830" href="Prelude.Preliminaries.html#11830" class="Bound">Y</a> <a id="11832" class="Symbol">:</a> <a id="11834" href="Prelude.Preliminaries.html#11819" class="Bound">X</a> <a id="11836" class="Symbol">→</a> <a id="11838" href="Prelude.Preliminaries.html#11815" class="Bound">𝓥</a> <a id="11840" href="Universes.html#403" class="Function Operator">̇</a> <a id="11842" class="Symbol">)</a> <a id="11844" class="Symbol">:</a> <a id="11846" href="Prelude.Preliminaries.html#11813" class="Bound">𝓤</a> <a id="11848" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11850" href="Prelude.Preliminaries.html#11815" class="Bound">𝓥</a> <a id="11852" href="Universes.html#403" class="Function Operator">̇</a>  <a id="11855" class="Keyword">where</a>
  <a id="11863" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="11875" href="Prelude.Preliminaries.html#11875" class="InductiveConstructor Operator">_,_</a>
  <a id="11881" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="11890" href="Prelude.Preliminaries.html#11890" class="Field">pr₁</a> <a id="11894" class="Symbol">:</a> <a id="11896" href="Prelude.Preliminaries.html#11819" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="11901" href="Prelude.Preliminaries.html#11901" class="Field">pr₂</a> <a id="11905" class="Symbol">:</a> <a id="11907" href="Prelude.Preliminaries.html#11830" class="Bound">Y</a> <a id="11909" href="Prelude.Preliminaries.html#11890" class="Field">pr₁</a>

 <a id="11915" class="Keyword">infixr</a> <a id="11922" class="Number">50</a> <a id="11925" href="Prelude.Preliminaries.html#11875" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  [Escardó][] makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12266" href="Prelude.Preliminaries.html#12266" class="Function">-Σ</a> <a id="12269" class="Symbol">:</a> <a id="12271" class="Symbol">{</a><a id="12272" href="Prelude.Preliminaries.html#12272" class="Bound">𝓤</a> <a id="12274" href="Prelude.Preliminaries.html#12274" class="Bound">𝓥</a> <a id="12276" class="Symbol">:</a> <a id="12278" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12286" class="Symbol">}</a> <a id="12288" class="Symbol">(</a><a id="12289" href="Prelude.Preliminaries.html#12289" class="Bound">X</a> <a id="12291" class="Symbol">:</a> <a id="12293" href="Prelude.Preliminaries.html#12272" class="Bound">𝓤</a> <a id="12295" href="Universes.html#403" class="Function Operator">̇</a> <a id="12297" class="Symbol">)</a> <a id="12299" class="Symbol">(</a><a id="12300" href="Prelude.Preliminaries.html#12300" class="Bound">Y</a> <a id="12302" class="Symbol">:</a> <a id="12304" href="Prelude.Preliminaries.html#12289" class="Bound">X</a> <a id="12306" class="Symbol">→</a> <a id="12308" href="Prelude.Preliminaries.html#12274" class="Bound">𝓥</a> <a id="12310" href="Universes.html#403" class="Function Operator">̇</a> <a id="12312" class="Symbol">)</a> <a id="12314" class="Symbol">→</a> <a id="12316" href="Prelude.Preliminaries.html#12272" class="Bound">𝓤</a> <a id="12318" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12320" href="Prelude.Preliminaries.html#12274" class="Bound">𝓥</a> <a id="12322" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12325" href="Prelude.Preliminaries.html#12266" class="Function">-Σ</a> <a id="12328" href="Prelude.Preliminaries.html#12328" class="Bound">X</a> <a id="12330" href="Prelude.Preliminaries.html#12330" class="Bound">Y</a> <a id="12332" class="Symbol">=</a> <a id="12334" href="Prelude.Preliminaries.html#11810" class="Record">Σ</a> <a id="12336" href="Prelude.Preliminaries.html#12330" class="Bound">Y</a>

 <a id="12340" class="Keyword">syntax</a> <a id="12347" href="Prelude.Preliminaries.html#12266" class="Function">-Σ</a> <a id="12350" class="Bound">X</a> <a id="12352" class="Symbol">(λ</a> <a id="12355" class="Bound">x</a> <a id="12357" class="Symbol">→</a> <a id="12359" class="Bound">Y</a><a id="12360" class="Symbol">)</a> <a id="12362" class="Symbol">=</a> <a id="12364" class="Function">Σ</a> <a id="12366" class="Bound">x</a> <a id="12368" class="Function">꞉</a> <a id="12370" class="Bound">X</a> <a id="12372" class="Function">,</a> <a id="12374" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12747" href="Prelude.Preliminaries.html#12747" class="Function Operator">_×_</a> <a id="12751" class="Symbol">:</a> <a id="12753" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12755" href="Universes.html#403" class="Function Operator">̇</a> <a id="12757" class="Symbol">→</a> <a id="12759" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12761" href="Universes.html#403" class="Function Operator">̇</a> <a id="12763" class="Symbol">→</a> <a id="12765" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12767" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12769" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12771" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12774" href="Prelude.Preliminaries.html#12774" class="Bound">X</a> <a id="12776" href="Prelude.Preliminaries.html#12747" class="Function Operator">×</a> <a id="12778" href="Prelude.Preliminaries.html#12778" class="Bound">Y</a> <a id="12780" class="Symbol">=</a> <a id="12782" href="Prelude.Preliminaries.html#12266" class="Function">Σ</a> <a id="12784" href="Prelude.Preliminaries.html#12784" class="Bound">x</a> <a id="12786" href="Prelude.Preliminaries.html#12266" class="Function">꞉</a> <a id="12788" href="Prelude.Preliminaries.html#12774" class="Bound">X</a> <a id="12790" href="Prelude.Preliminaries.html#12266" class="Function">,</a> <a id="12792" href="Prelude.Preliminaries.html#12778" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13002" class="Keyword">open</a> <a id="13007" class="Keyword">import</a> <a id="13014" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13025" class="Keyword">renaming</a> <a id="13034" class="Symbol">(</a><a id="13035" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13039" class="Symbol">to</a> <a id="13042" class="Keyword">infixr</a> <a id="13049" class="Number">50</a> <a id="_,_"></a><a id="13052" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">_,_</a><a id="13055" class="Symbol">)</a>
<a id="13057" class="Keyword">open</a> <a id="13062" class="Keyword">import</a> <a id="13069" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13078" class="Keyword">using</a> <a id="13084" class="Symbol">(</a><a id="13085" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13088" class="Symbol">;</a> <a id="13090" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13093" class="Symbol">;</a> <a id="13095" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13098" class="Symbol">;</a> <a id="13100" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13102" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13537" class="Keyword">module</a> <a id="13544" href="Prelude.Preliminaries.html#13544" class="Module">_</a> <a id="13546" class="Symbol">{</a><a id="13547" href="Prelude.Preliminaries.html#13547" class="Bound">𝓤</a> <a id="13549" class="Symbol">:</a> <a id="13551" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13559" class="Symbol">}</a> <a id="13561" class="Keyword">where</a>

 <a id="13569" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣_∣</a> <a id="13573" href="Prelude.Preliminaries.html#13573" class="Function">fst</a> <a id="13577" class="Symbol">:</a> <a id="13579" class="Symbol">{</a><a id="13580" href="Prelude.Preliminaries.html#13580" class="Bound">X</a> <a id="13582" class="Symbol">:</a> <a id="13584" href="Prelude.Preliminaries.html#13547" class="Bound">𝓤</a> <a id="13586" href="Universes.html#403" class="Function Operator">̇</a> <a id="13588" class="Symbol">}{</a><a id="13590" href="Prelude.Preliminaries.html#13590" class="Bound">Y</a> <a id="13592" class="Symbol">:</a> <a id="13594" href="Prelude.Preliminaries.html#13580" class="Bound">X</a> <a id="13596" class="Symbol">→</a> <a id="13598" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13600" href="Universes.html#403" class="Function Operator">̇</a><a id="13601" class="Symbol">}</a> <a id="13603" class="Symbol">→</a> <a id="13605" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13607" href="Prelude.Preliminaries.html#13590" class="Bound">Y</a> <a id="13609" class="Symbol">→</a> <a id="13611" href="Prelude.Preliminaries.html#13580" class="Bound">X</a>
 <a id="13614" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="13616" href="Prelude.Preliminaries.html#13616" class="Bound">x</a> <a id="13618" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="13620" href="Prelude.Preliminaries.html#13620" class="Bound">y</a> <a id="13622" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="13624" class="Symbol">=</a> <a id="13626" href="Prelude.Preliminaries.html#13616" class="Bound">x</a>
 <a id="13629" href="Prelude.Preliminaries.html#13573" class="Function">fst</a> <a id="13633" class="Symbol">(</a><a id="13634" href="Prelude.Preliminaries.html#13634" class="Bound">x</a> <a id="13636" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="13638" href="Prelude.Preliminaries.html#13638" class="Bound">y</a><a id="13639" class="Symbol">)</a> <a id="13641" class="Symbol">=</a> <a id="13643" href="Prelude.Preliminaries.html#13634" class="Bound">x</a>

 <a id="13647" href="Prelude.Preliminaries.html#13647" class="Function Operator">∥_∥</a> <a id="13651" href="Prelude.Preliminaries.html#13651" class="Function">snd</a> <a id="13655" class="Symbol">:</a> <a id="13657" class="Symbol">{</a><a id="13658" href="Prelude.Preliminaries.html#13658" class="Bound">X</a> <a id="13660" class="Symbol">:</a> <a id="13662" href="Prelude.Preliminaries.html#13547" class="Bound">𝓤</a> <a id="13664" href="Universes.html#403" class="Function Operator">̇</a> <a id="13666" class="Symbol">}{</a><a id="13668" href="Prelude.Preliminaries.html#13668" class="Bound">Y</a> <a id="13670" class="Symbol">:</a> <a id="13672" href="Prelude.Preliminaries.html#13658" class="Bound">X</a> <a id="13674" class="Symbol">→</a> <a id="13676" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13678" href="Universes.html#403" class="Function Operator">̇</a> <a id="13680" class="Symbol">}</a> <a id="13682" class="Symbol">→</a> <a id="13684" class="Symbol">(</a><a id="13685" href="Prelude.Preliminaries.html#13685" class="Bound">z</a> <a id="13687" class="Symbol">:</a> <a id="13689" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13691" href="Prelude.Preliminaries.html#13668" class="Bound">Y</a><a id="13692" class="Symbol">)</a> <a id="13694" class="Symbol">→</a> <a id="13696" href="Prelude.Preliminaries.html#13668" class="Bound">Y</a> <a id="13698" class="Symbol">(</a><a id="13699" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13703" href="Prelude.Preliminaries.html#13685" class="Bound">z</a><a id="13704" class="Symbol">)</a>
 <a id="13707" href="Prelude.Preliminaries.html#13647" class="Function Operator">∥</a> <a id="13709" href="Prelude.Preliminaries.html#13709" class="Bound">x</a> <a id="13711" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="13713" href="Prelude.Preliminaries.html#13713" class="Bound">y</a> <a id="13715" href="Prelude.Preliminaries.html#13647" class="Function Operator">∥</a> <a id="13717" class="Symbol">=</a> <a id="13719" href="Prelude.Preliminaries.html#13713" class="Bound">y</a>
 <a id="13722" href="Prelude.Preliminaries.html#13651" class="Function">snd</a> <a id="13726" class="Symbol">(</a><a id="13727" href="Prelude.Preliminaries.html#13727" class="Bound">x</a> <a id="13729" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="13731" href="Prelude.Preliminaries.html#13731" class="Bound">y</a><a id="13732" class="Symbol">)</a> <a id="13734" class="Symbol">=</a> <a id="13736" href="Prelude.Preliminaries.html#13731" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14013" class="Keyword">module</a> <a id="hide-pi"></a><a id="14020" href="Prelude.Preliminaries.html#14020" class="Module">hide-pi</a> <a id="14028" class="Symbol">{</a><a id="14029" href="Prelude.Preliminaries.html#14029" class="Bound">𝓤</a> <a id="14031" href="Prelude.Preliminaries.html#14031" class="Bound">𝓦</a> <a id="14033" class="Symbol">:</a> <a id="14035" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14043" class="Symbol">}</a> <a id="14045" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14053" href="Prelude.Preliminaries.html#14053" class="Function">Π</a> <a id="14055" class="Symbol">:</a> <a id="14057" class="Symbol">{</a><a id="14058" href="Prelude.Preliminaries.html#14058" class="Bound">X</a> <a id="14060" class="Symbol">:</a> <a id="14062" href="Prelude.Preliminaries.html#14029" class="Bound">𝓤</a> <a id="14064" href="Universes.html#403" class="Function Operator">̇</a> <a id="14066" class="Symbol">}</a> <a id="14068" class="Symbol">(</a><a id="14069" href="Prelude.Preliminaries.html#14069" class="Bound">A</a> <a id="14071" class="Symbol">:</a> <a id="14073" href="Prelude.Preliminaries.html#14058" class="Bound">X</a> <a id="14075" class="Symbol">→</a> <a id="14077" href="Prelude.Preliminaries.html#14031" class="Bound">𝓦</a> <a id="14079" href="Universes.html#403" class="Function Operator">̇</a> <a id="14081" class="Symbol">)</a> <a id="14083" class="Symbol">→</a> <a id="14085" href="Prelude.Preliminaries.html#14029" class="Bound">𝓤</a> <a id="14087" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14089" href="Prelude.Preliminaries.html#14031" class="Bound">𝓦</a> <a id="14091" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14094" href="Prelude.Preliminaries.html#14053" class="Function">Π</a> <a id="14096" class="Symbol">{</a><a id="14097" href="Prelude.Preliminaries.html#14097" class="Bound">X</a><a id="14098" class="Symbol">}</a> <a id="14100" href="Prelude.Preliminaries.html#14100" class="Bound">A</a> <a id="14102" class="Symbol">=</a> <a id="14104" class="Symbol">(</a><a id="14105" href="Prelude.Preliminaries.html#14105" class="Bound">x</a> <a id="14107" class="Symbol">:</a> <a id="14109" href="Prelude.Preliminaries.html#14097" class="Bound">X</a><a id="14110" class="Symbol">)</a> <a id="14112" class="Symbol">→</a> <a id="14114" href="Prelude.Preliminaries.html#14100" class="Bound">A</a> <a id="14116" href="Prelude.Preliminaries.html#14105" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14120" href="Prelude.Preliminaries.html#14120" class="Function">-Π</a> <a id="14123" class="Symbol">:</a> <a id="14125" class="Symbol">(</a><a id="14126" href="Prelude.Preliminaries.html#14126" class="Bound">X</a> <a id="14128" class="Symbol">:</a> <a id="14130" href="Prelude.Preliminaries.html#14029" class="Bound">𝓤</a> <a id="14132" href="Universes.html#403" class="Function Operator">̇</a> <a id="14134" class="Symbol">)(</a><a id="14136" href="Prelude.Preliminaries.html#14136" class="Bound">Y</a> <a id="14138" class="Symbol">:</a> <a id="14140" href="Prelude.Preliminaries.html#14126" class="Bound">X</a> <a id="14142" class="Symbol">→</a> <a id="14144" href="Prelude.Preliminaries.html#14031" class="Bound">𝓦</a> <a id="14146" href="Universes.html#403" class="Function Operator">̇</a> <a id="14148" class="Symbol">)</a> <a id="14150" class="Symbol">→</a> <a id="14152" href="Prelude.Preliminaries.html#14029" class="Bound">𝓤</a> <a id="14154" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14156" href="Prelude.Preliminaries.html#14031" class="Bound">𝓦</a> <a id="14158" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14161" href="Prelude.Preliminaries.html#14120" class="Function">-Π</a> <a id="14164" href="Prelude.Preliminaries.html#14164" class="Bound">X</a> <a id="14166" href="Prelude.Preliminaries.html#14166" class="Bound">Y</a> <a id="14168" class="Symbol">=</a> <a id="14170" href="Prelude.Preliminaries.html#14053" class="Function">Π</a> <a id="14172" href="Prelude.Preliminaries.html#14166" class="Bound">Y</a>

 <a id="14176" class="Keyword">infixr</a> <a id="14183" class="Number">-1</a> <a id="14186" href="Prelude.Preliminaries.html#14120" class="Function">-Π</a>
 <a id="14190" class="Keyword">syntax</a> <a id="14197" href="Prelude.Preliminaries.html#14120" class="Function">-Π</a> <a id="14200" class="Bound">A</a> <a id="14202" class="Symbol">(λ</a> <a id="14205" class="Bound">x</a> <a id="14207" class="Symbol">→</a> <a id="14209" class="Bound">b</a><a id="14210" class="Symbol">)</a> <a id="14212" class="Symbol">=</a> <a id="14214" class="Function">Π</a> <a id="14216" class="Bound">x</a> <a id="14218" class="Function">꞉</a> <a id="14220" class="Bound">A</a> <a id="14222" class="Function">,</a> <a id="14224" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14514" class="Keyword">open</a> <a id="14519" class="Keyword">import</a> <a id="14526" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14537" class="Keyword">renaming</a> <a id="14546" class="Symbol">(</a><a id="14547" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14551" class="Symbol">to</a> <a id="14554" class="Keyword">infixr</a> <a id="14561" class="Number">50</a> <a id="_,_"></a><a id="14564" href="Prelude.Preliminaries.html#14564" class="InductiveConstructor Operator">_,_</a><a id="14567" class="Symbol">)</a> <a id="14569" class="Keyword">public</a>
<a id="14576" class="Keyword">open</a> <a id="14581" class="Keyword">import</a> <a id="14588" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14597" class="Keyword">using</a> <a id="14603" class="Symbol">(</a><a id="14604" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14607" class="Symbol">;</a> <a id="14609" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14612" class="Symbol">;</a> <a id="14614" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14617" class="Symbol">;</a> <a id="14619" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14621" class="Symbol">;</a> <a id="14623" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14624" class="Symbol">)</a> <a id="14626" class="Keyword">public</a>


<a id="14635" class="Keyword">module</a> <a id="14642" href="Prelude.Preliminaries.html#14642" class="Module">_</a> <a id="14644" class="Symbol">{</a><a id="14645" href="Prelude.Preliminaries.html#14645" class="Bound">𝓨</a> <a id="14647" href="Prelude.Preliminaries.html#14647" class="Bound">𝓩</a> <a id="14649" class="Symbol">:</a> <a id="14651" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14659" class="Symbol">}{</a><a id="14661" href="Prelude.Preliminaries.html#14661" class="Bound">I</a> <a id="14663" class="Symbol">:</a> <a id="14665" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14667" href="Universes.html#403" class="Function Operator">̇</a><a id="14668" class="Symbol">}{</a><a id="14670" href="Prelude.Preliminaries.html#14670" class="Bound">B</a> <a id="14672" class="Symbol">:</a> <a id="14674" href="Prelude.Preliminaries.html#14661" class="Bound">I</a> <a id="14676" class="Symbol">→</a> <a id="14678" href="Prelude.Preliminaries.html#14645" class="Bound">𝓨</a> <a id="14680" href="Universes.html#403" class="Function Operator">̇</a><a id="14681" class="Symbol">}{</a><a id="14683" href="Prelude.Preliminaries.html#14683" class="Bound">C</a> <a id="14685" class="Symbol">:</a> <a id="14687" href="Prelude.Preliminaries.html#14661" class="Bound">I</a> <a id="14689" class="Symbol">→</a> <a id="14691" href="Prelude.Preliminaries.html#14647" class="Bound">𝓩</a> <a id="14693" href="Universes.html#403" class="Function Operator">̇</a><a id="14694" class="Symbol">}</a> <a id="14696" class="Keyword">where</a>
 <a id="14703" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14726" href="Prelude.Preliminaries.html#14726" class="Function">zip</a> <a id="14730" class="Symbol">:</a> <a id="14732" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14734" href="Prelude.Preliminaries.html#14670" class="Bound">B</a> <a id="14736" class="Symbol">→</a> <a id="14738" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14740" href="Prelude.Preliminaries.html#14683" class="Bound">C</a> <a id="14742" class="Symbol">→</a> <a id="14744" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14746" class="Symbol">(λ</a> <a id="14749" href="Prelude.Preliminaries.html#14749" class="Bound">i</a> <a id="14751" class="Symbol">→</a> <a id="14753" class="Symbol">(</a><a id="14754" href="Prelude.Preliminaries.html#14670" class="Bound">B</a> <a id="14756" href="Prelude.Preliminaries.html#14749" class="Bound">i</a><a id="14757" class="Symbol">)</a> <a id="14759" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14761" class="Symbol">(</a><a id="14762" href="Prelude.Preliminaries.html#14683" class="Bound">C</a> <a id="14764" href="Prelude.Preliminaries.html#14749" class="Bound">i</a><a id="14765" class="Symbol">))</a>
 <a id="14769" href="Prelude.Preliminaries.html#14726" class="Function">zip</a> <a id="14773" href="Prelude.Preliminaries.html#14773" class="Bound">f</a> <a id="14775" href="Prelude.Preliminaries.html#14775" class="Bound">a</a> <a id="14777" class="Symbol">=</a> <a id="14779" class="Symbol">λ</a> <a id="14781" href="Prelude.Preliminaries.html#14781" class="Bound">i</a> <a id="14783" class="Symbol">→</a> <a id="14785" class="Symbol">(</a><a id="14786" href="Prelude.Preliminaries.html#14773" class="Bound">f</a> <a id="14788" href="Prelude.Preliminaries.html#14781" class="Bound">i</a> <a id="14790" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="14792" href="Prelude.Preliminaries.html#14775" class="Bound">a</a> <a id="14794" href="Prelude.Preliminaries.html#14781" class="Bound">i</a><a id="14795" class="Symbol">)</a>

 <a id="14799" href="Prelude.Preliminaries.html#14799" class="Function">eval</a> <a id="14804" class="Symbol">:</a> <a id="14806" class="Symbol">{</a><a id="14807" href="Prelude.Preliminaries.html#14807" class="Bound">Y</a> <a id="14809" class="Symbol">:</a> <a id="14811" href="Prelude.Preliminaries.html#14645" class="Bound">𝓨</a> <a id="14813" href="Universes.html#403" class="Function Operator">̇</a><a id="14814" class="Symbol">}{</a><a id="14816" href="Prelude.Preliminaries.html#14816" class="Bound">Z</a> <a id="14818" class="Symbol">:</a> <a id="14820" href="Prelude.Preliminaries.html#14647" class="Bound">𝓩</a> <a id="14822" href="Universes.html#403" class="Function Operator">̇</a><a id="14823" class="Symbol">}</a> <a id="14825" class="Symbol">→</a> <a id="14827" class="Symbol">((</a><a id="14829" href="Prelude.Preliminaries.html#14807" class="Bound">Y</a> <a id="14831" class="Symbol">→</a> <a id="14833" href="Prelude.Preliminaries.html#14816" class="Bound">Z</a><a id="14834" class="Symbol">)</a> <a id="14836" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14838" href="Prelude.Preliminaries.html#14807" class="Bound">Y</a><a id="14839" class="Symbol">)</a> <a id="14841" class="Symbol">→</a> <a id="14843" href="Prelude.Preliminaries.html#14816" class="Bound">Z</a>
 <a id="14846" href="Prelude.Preliminaries.html#14799" class="Function">eval</a> <a id="14851" class="Symbol">(</a><a id="14852" href="Prelude.Preliminaries.html#14852" class="Bound">f</a> <a id="14854" href="Prelude.Preliminaries.html#13052" class="InductiveConstructor Operator">,</a> <a id="14856" href="Prelude.Preliminaries.html#14856" class="Bound">a</a><a id="14857" class="Symbol">)</a> <a id="14859" class="Symbol">=</a> <a id="14861" href="Prelude.Preliminaries.html#14852" class="Bound">f</a> <a id="14863" href="Prelude.Preliminaries.html#14856" class="Bound">a</a>
 
<a id="14867" class="Keyword">module</a> <a id="14874" href="Prelude.Preliminaries.html#14874" class="Module">_</a> <a id="14876" class="Symbol">{</a><a id="14877" href="Prelude.Preliminaries.html#14877" class="Bound">𝓨</a> <a id="14879" class="Symbol">:</a> <a id="14881" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14889" class="Symbol">}{</a><a id="14891" href="Prelude.Preliminaries.html#14891" class="Bound">I</a> <a id="14893" href="Prelude.Preliminaries.html#14893" class="Bound">J</a> <a id="14895" class="Symbol">:</a> <a id="14897" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14899" href="Universes.html#403" class="Function Operator">̇</a><a id="14900" class="Symbol">}{</a><a id="14902" href="Prelude.Preliminaries.html#14902" class="Bound">B</a> <a id="14904" class="Symbol">:</a> <a id="14906" href="Prelude.Preliminaries.html#14891" class="Bound">I</a> <a id="14908" class="Symbol">→</a> <a id="14910" href="Prelude.Preliminaries.html#14877" class="Bound">𝓨</a> <a id="14912" href="Universes.html#403" class="Function Operator">̇</a><a id="14913" class="Symbol">}</a> <a id="14915" class="Keyword">where</a>

 <a id="14923" href="Prelude.Preliminaries.html#14923" class="Function">dapp</a> <a id="14928" class="Symbol">:</a> <a id="14930" class="Symbol">(∀</a> <a id="14933" href="Prelude.Preliminaries.html#14933" class="Bound">i</a> <a id="14935" class="Symbol">→</a> <a id="14937" class="Symbol">(</a><a id="14938" href="Prelude.Preliminaries.html#14893" class="Bound">J</a> <a id="14940" class="Symbol">→</a> <a id="14942" class="Symbol">(</a><a id="14943" href="Prelude.Preliminaries.html#14902" class="Bound">B</a> <a id="14945" href="Prelude.Preliminaries.html#14933" class="Bound">i</a><a id="14946" class="Symbol">))</a> <a id="14949" class="Symbol">→</a> <a id="14951" class="Symbol">(</a><a id="14952" href="Prelude.Preliminaries.html#14902" class="Bound">B</a> <a id="14954" href="Prelude.Preliminaries.html#14933" class="Bound">i</a><a id="14955" class="Symbol">))</a> <a id="14958" class="Symbol">→</a> <a id="14960" class="Symbol">(∀</a> <a id="14963" href="Prelude.Preliminaries.html#14963" class="Bound">i</a> <a id="14965" class="Symbol">→</a> <a id="14967" class="Symbol">(</a><a id="14968" href="Prelude.Preliminaries.html#14893" class="Bound">J</a> <a id="14970" class="Symbol">→</a> <a id="14972" class="Symbol">(</a><a id="14973" href="Prelude.Preliminaries.html#14902" class="Bound">B</a> <a id="14975" href="Prelude.Preliminaries.html#14963" class="Bound">i</a><a id="14976" class="Symbol">)))</a> <a id="14980" class="Symbol">→</a> <a id="14982" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14984" href="Prelude.Preliminaries.html#14902" class="Bound">B</a>
 <a id="14987" href="Prelude.Preliminaries.html#14923" class="Function">dapp</a> <a id="14992" href="Prelude.Preliminaries.html#14992" class="Bound">f</a> <a id="14994" href="Prelude.Preliminaries.html#14994" class="Bound">a</a> <a id="14996" class="Symbol">=</a> <a id="14998" class="Symbol">λ</a> <a id="15000" href="Prelude.Preliminaries.html#15000" class="Bound">i</a> <a id="15002" class="Symbol">→</a> <a id="15004" class="Symbol">(</a><a id="15005" href="Prelude.Preliminaries.html#14992" class="Bound">f</a> <a id="15007" href="Prelude.Preliminaries.html#15000" class="Bound">i</a><a id="15008" class="Symbol">)</a> <a id="15010" class="Symbol">(</a><a id="15011" href="Prelude.Preliminaries.html#14994" class="Bound">a</a> <a id="15013" href="Prelude.Preliminaries.html#15000" class="Bound">i</a><a id="15014" class="Symbol">)</a>

</pre>

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

