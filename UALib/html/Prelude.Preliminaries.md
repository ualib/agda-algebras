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

The first line must be commented out because we define the given type ourselves for pedagogical purposes, though we will eventually import the original definition from the [Type Topology][] library.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>

<pre class="Agda">

<a id="6892" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6951" class="Keyword">open</a> <a id="6956" class="Keyword">import</a> <a id="6963" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="6977" class="Keyword">renaming</a> <a id="6986" class="Symbol">(</a><a id="6987" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="6991" class="Symbol">to</a> <a id="6994" class="Keyword">infix</a> <a id="7000" class="Number">0</a> <a id="_≡_"></a><a id="7002" href="Prelude.Preliminaries.html#7002" class="Datatype Operator">_≡_</a><a id="7005" class="Symbol">)</a>

<a id="7008" class="Keyword">open</a> <a id="7013" class="Keyword">import</a> <a id="7020" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7029" class="Keyword">using</a> <a id="7035" class="Symbol">(</a><a id="7036" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7039" class="Symbol">;</a> <a id="7041" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7047" class="Symbol">;</a> <a id="7049" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7057" class="Symbol">;</a> <a id="7059" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7068" class="Symbol">;</a> <a id="7070" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7076" class="Symbol">;</a> <a id="7078" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7080" class="Symbol">;</a> <a id="7082" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7110" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7111" class="Symbol">;</a> <a id="7113" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7115" class="Symbol">;</a> <a id="7117" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7120" class="Symbol">;</a> <a id="7122" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7125" class="Symbol">;</a> <a id="7127" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7128" class="Symbol">;</a> <a id="7130" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7131" class="Symbol">;</a> <a id="7133" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7134" class="Symbol">;</a> <a id="7136" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7139" class="Symbol">;</a> <a id="7141" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7155" class="Symbol">;</a> <a id="7157" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7171" class="Symbol">;</a> <a id="7173" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7175" class="Symbol">;</a> <a id="7177" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7180" class="Symbol">;</a> <a id="7182" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7184" class="Symbol">)</a>

<a id="7187" class="Keyword">open</a> <a id="7192" class="Keyword">import</a> <a id="7199" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7216" class="Keyword">using</a> <a id="7222" class="Symbol">(</a><a id="7223" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7231" class="Symbol">;</a> <a id="7233" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7240" class="Symbol">;</a> <a id="7242" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7252" class="Symbol">)</a>

<a id="7255" class="Keyword">open</a> <a id="7260" class="Keyword">import</a> <a id="7267" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7293" class="Keyword">using</a> <a id="7299" class="Symbol">(</a><a id="7300" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7306" class="Symbol">;</a> <a id="7308" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7322" class="Symbol">;</a> <a id="7324" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7331" class="Symbol">;</a>
 <a id="7334" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7346" class="Symbol">;</a> <a id="7348" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7363" class="Symbol">;</a> <a id="7365" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7372" class="Symbol">;</a> <a id="7374" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7384" class="Symbol">;</a> <a id="7386" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7400" class="Symbol">;</a>
 <a id="7403" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7434" class="Symbol">;</a> <a id="7436" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7439" class="Symbol">;</a> <a id="7441" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7444" class="Symbol">;</a> <a id="7446" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7463" class="Symbol">;</a> <a id="7465" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7482" class="Symbol">;</a>
 <a id="7485" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7534" class="Symbol">)</a>

<a id="7537" class="Keyword">open</a> <a id="7542" class="Keyword">import</a> <a id="7549" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7562" class="Keyword">renaming</a> <a id="7571" class="Symbol">(</a><a id="7572" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7576" class="Symbol">to</a> <a id="_∈_"></a><a id="7579" href="Prelude.Preliminaries.html#7579" class="Function Operator">_∈₀_</a><a id="7583" class="Symbol">;</a> <a id="7585" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7589" class="Symbol">to</a> <a id="_⊆_"></a><a id="7592" href="Prelude.Preliminaries.html#7592" class="Function Operator">_⊆₀_</a><a id="7596" class="Symbol">;</a> <a id="7598" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7616" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7619" href="Prelude.Preliminaries.html#7619" class="Function">∈₀-is-subsingleton</a><a id="7637" class="Symbol">)</a>
 <a id="7640" class="Keyword">using</a> <a id="7646" class="Symbol">(</a><a id="7647" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7648" class="Symbol">;</a> <a id="7650" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7671" class="Symbol">;</a> <a id="7673" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7692" class="Symbol">;</a> <a id="7694" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7716" class="Symbol">;</a> <a id="7718" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7725" class="Symbol">;</a> <a id="7727" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7733" class="Symbol">;</a> <a id="7735" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7736" class="Symbol">)</a>

<a id="7739" class="Keyword">open</a> <a id="7744" class="Keyword">import</a> <a id="7751" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7766" class="Keyword">using</a> <a id="7772" class="Symbol">(</a><a id="7773" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7776" class="Symbol">;</a> <a id="7778" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7782" class="Symbol">;</a> <a id="7784" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7801" class="Symbol">;</a> <a id="7803" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7815" class="Symbol">;</a> <a id="7817" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7830" class="Symbol">;</a> <a id="7832" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7843" class="Symbol">;</a>
 <a id="7846" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7852" class="Symbol">;</a> <a id="7854" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7857" class="Symbol">;</a> <a id="7859" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="7886" class="Symbol">;</a> <a id="7888" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7905" class="Symbol">;</a> <a id="7907" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7924" class="Symbol">;</a> <a id="7926" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7941" class="Symbol">)</a>

<a id="7944" class="Keyword">open</a> <a id="7949" class="Keyword">import</a> <a id="7956" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7977" class="Keyword">using</a> <a id="7983" class="Symbol">(</a><a id="7984" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7996" class="Symbol">)</a>

<a id="7999" class="Keyword">open</a> <a id="8004" class="Keyword">import</a> <a id="8011" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8032" class="Keyword">using</a> <a id="8038" class="Symbol">(</a><a id="8039" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8041" class="Symbol">;</a> <a id="8043" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8046" class="Symbol">)</a>

<a id="8049" class="Keyword">open</a> <a id="8054" class="Keyword">import</a> <a id="8061" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8089" class="Keyword">using</a> <a id="8095" class="Symbol">(</a><a id="8096" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8099" class="Symbol">;</a> <a id="8101" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8107" class="Symbol">;</a> <a id="8109" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8130" class="Symbol">;</a>
 <a id="8133" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8155" class="Symbol">;</a> <a id="8157" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8162" class="Symbol">;</a> <a id="8164" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8182" class="Symbol">;</a> <a id="8184" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8191" class="Symbol">)</a>

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

<a id="11845" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11852" href="Prelude.Preliminaries.html#11852" class="Module">hide-sigma</a> <a id="11863" class="Keyword">where</a>

 <a id="11871" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="11878" href="Prelude.Preliminaries.html#11878" class="Record">Σ</a> <a id="11880" class="Symbol">{</a><a id="11881" href="Prelude.Preliminaries.html#11881" class="Bound">𝓤</a> <a id="11883" href="Prelude.Preliminaries.html#11883" class="Bound">𝓥</a><a id="11884" class="Symbol">}</a> <a id="11886" class="Symbol">{</a><a id="11887" href="Prelude.Preliminaries.html#11887" class="Bound">X</a> <a id="11889" class="Symbol">:</a> <a id="11891" href="Prelude.Preliminaries.html#11881" class="Bound">𝓤</a> <a id="11893" href="Universes.html#403" class="Function Operator">̇</a> <a id="11895" class="Symbol">}</a> <a id="11897" class="Symbol">(</a><a id="11898" href="Prelude.Preliminaries.html#11898" class="Bound">Y</a> <a id="11900" class="Symbol">:</a> <a id="11902" href="Prelude.Preliminaries.html#11887" class="Bound">X</a> <a id="11904" class="Symbol">→</a> <a id="11906" href="Prelude.Preliminaries.html#11883" class="Bound">𝓥</a> <a id="11908" href="Universes.html#403" class="Function Operator">̇</a> <a id="11910" class="Symbol">)</a> <a id="11912" class="Symbol">:</a> <a id="11914" href="Prelude.Preliminaries.html#11881" class="Bound">𝓤</a> <a id="11916" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11918" href="Prelude.Preliminaries.html#11883" class="Bound">𝓥</a> <a id="11920" href="Universes.html#403" class="Function Operator">̇</a>  <a id="11923" class="Keyword">where</a>
  <a id="11931" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="11943" href="Prelude.Preliminaries.html#11943" class="InductiveConstructor Operator">_,_</a>
  <a id="11949" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="11958" href="Prelude.Preliminaries.html#11958" class="Field">pr₁</a> <a id="11962" class="Symbol">:</a> <a id="11964" href="Prelude.Preliminaries.html#11887" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="11969" href="Prelude.Preliminaries.html#11969" class="Field">pr₂</a> <a id="11973" class="Symbol">:</a> <a id="11975" href="Prelude.Preliminaries.html#11898" class="Bound">Y</a> <a id="11977" href="Prelude.Preliminaries.html#11958" class="Field">pr₁</a>

 <a id="11983" class="Keyword">infixr</a> <a id="11990" class="Number">50</a> <a id="11993" href="Prelude.Preliminaries.html#11943" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12314" href="Prelude.Preliminaries.html#12314" class="Function">-Σ</a> <a id="12317" class="Symbol">:</a> <a id="12319" class="Symbol">{</a><a id="12320" href="Prelude.Preliminaries.html#12320" class="Bound">𝓤</a> <a id="12322" href="Prelude.Preliminaries.html#12322" class="Bound">𝓥</a> <a id="12324" class="Symbol">:</a> <a id="12326" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12334" class="Symbol">}</a> <a id="12336" class="Symbol">(</a><a id="12337" href="Prelude.Preliminaries.html#12337" class="Bound">X</a> <a id="12339" class="Symbol">:</a> <a id="12341" href="Prelude.Preliminaries.html#12320" class="Bound">𝓤</a> <a id="12343" href="Universes.html#403" class="Function Operator">̇</a> <a id="12345" class="Symbol">)</a> <a id="12347" class="Symbol">(</a><a id="12348" href="Prelude.Preliminaries.html#12348" class="Bound">Y</a> <a id="12350" class="Symbol">:</a> <a id="12352" href="Prelude.Preliminaries.html#12337" class="Bound">X</a> <a id="12354" class="Symbol">→</a> <a id="12356" href="Prelude.Preliminaries.html#12322" class="Bound">𝓥</a> <a id="12358" href="Universes.html#403" class="Function Operator">̇</a> <a id="12360" class="Symbol">)</a> <a id="12362" class="Symbol">→</a> <a id="12364" href="Prelude.Preliminaries.html#12320" class="Bound">𝓤</a> <a id="12366" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12368" href="Prelude.Preliminaries.html#12322" class="Bound">𝓥</a> <a id="12370" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12373" href="Prelude.Preliminaries.html#12314" class="Function">-Σ</a> <a id="12376" href="Prelude.Preliminaries.html#12376" class="Bound">X</a> <a id="12378" href="Prelude.Preliminaries.html#12378" class="Bound">Y</a> <a id="12380" class="Symbol">=</a> <a id="12382" href="Prelude.Preliminaries.html#11878" class="Record">Σ</a> <a id="12384" href="Prelude.Preliminaries.html#12378" class="Bound">Y</a>

 <a id="12388" class="Keyword">syntax</a> <a id="12395" href="Prelude.Preliminaries.html#12314" class="Function">-Σ</a> <a id="12398" class="Bound">X</a> <a id="12400" class="Symbol">(λ</a> <a id="12403" class="Bound">x</a> <a id="12405" class="Symbol">→</a> <a id="12407" class="Bound">Y</a><a id="12408" class="Symbol">)</a> <a id="12410" class="Symbol">=</a> <a id="12412" class="Function">Σ</a> <a id="12414" class="Bound">x</a> <a id="12416" class="Function">꞉</a> <a id="12418" class="Bound">X</a> <a id="12420" class="Function">,</a> <a id="12422" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12795" href="Prelude.Preliminaries.html#12795" class="Function Operator">_×_</a> <a id="12799" class="Symbol">:</a> <a id="12801" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12803" href="Universes.html#403" class="Function Operator">̇</a> <a id="12805" class="Symbol">→</a> <a id="12807" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12809" href="Universes.html#403" class="Function Operator">̇</a> <a id="12811" class="Symbol">→</a> <a id="12813" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12815" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12817" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12819" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12822" href="Prelude.Preliminaries.html#12822" class="Bound">X</a> <a id="12824" href="Prelude.Preliminaries.html#12795" class="Function Operator">×</a> <a id="12826" href="Prelude.Preliminaries.html#12826" class="Bound">Y</a> <a id="12828" class="Symbol">=</a> <a id="12830" href="Prelude.Preliminaries.html#12314" class="Function">Σ</a> <a id="12832" href="Prelude.Preliminaries.html#12832" class="Bound">x</a> <a id="12834" href="Prelude.Preliminaries.html#12314" class="Function">꞉</a> <a id="12836" href="Prelude.Preliminaries.html#12822" class="Bound">X</a> <a id="12838" href="Prelude.Preliminaries.html#12314" class="Function">,</a> <a id="12840" href="Prelude.Preliminaries.html#12826" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13050" class="Keyword">open</a> <a id="13055" class="Keyword">import</a> <a id="13062" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13073" class="Keyword">renaming</a> <a id="13082" class="Symbol">(</a><a id="13083" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13087" class="Symbol">to</a> <a id="13090" class="Keyword">infixr</a> <a id="13097" class="Number">50</a> <a id="_,_"></a><a id="13100" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">_,_</a><a id="13103" class="Symbol">)</a>
<a id="13105" class="Keyword">open</a> <a id="13110" class="Keyword">import</a> <a id="13117" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13126" class="Keyword">using</a> <a id="13132" class="Symbol">(</a><a id="13133" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13136" class="Symbol">;</a> <a id="13138" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13141" class="Symbol">;</a> <a id="13143" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13146" class="Symbol">;</a> <a id="13148" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13150" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="13585" class="Keyword">module</a> <a id="13592" href="Prelude.Preliminaries.html#13592" class="Module">_</a> <a id="13594" class="Symbol">{</a><a id="13595" href="Prelude.Preliminaries.html#13595" class="Bound">𝓤</a> <a id="13597" class="Symbol">:</a> <a id="13599" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13607" class="Symbol">}</a> <a id="13609" class="Keyword">where</a>

 <a id="13617" href="Prelude.Preliminaries.html#13617" class="Function Operator">∣_∣</a> <a id="13621" href="Prelude.Preliminaries.html#13621" class="Function">fst</a> <a id="13625" class="Symbol">:</a> <a id="13627" class="Symbol">{</a><a id="13628" href="Prelude.Preliminaries.html#13628" class="Bound">X</a> <a id="13630" class="Symbol">:</a> <a id="13632" href="Prelude.Preliminaries.html#13595" class="Bound">𝓤</a> <a id="13634" href="Universes.html#403" class="Function Operator">̇</a> <a id="13636" class="Symbol">}{</a><a id="13638" href="Prelude.Preliminaries.html#13638" class="Bound">Y</a> <a id="13640" class="Symbol">:</a> <a id="13642" href="Prelude.Preliminaries.html#13628" class="Bound">X</a> <a id="13644" class="Symbol">→</a> <a id="13646" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13648" href="Universes.html#403" class="Function Operator">̇</a><a id="13649" class="Symbol">}</a> <a id="13651" class="Symbol">→</a> <a id="13653" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13655" href="Prelude.Preliminaries.html#13638" class="Bound">Y</a> <a id="13657" class="Symbol">→</a> <a id="13659" href="Prelude.Preliminaries.html#13628" class="Bound">X</a>
 <a id="13662" href="Prelude.Preliminaries.html#13617" class="Function Operator">∣</a> <a id="13664" href="Prelude.Preliminaries.html#13664" class="Bound">x</a> <a id="13666" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="13668" href="Prelude.Preliminaries.html#13668" class="Bound">y</a> <a id="13670" href="Prelude.Preliminaries.html#13617" class="Function Operator">∣</a> <a id="13672" class="Symbol">=</a> <a id="13674" href="Prelude.Preliminaries.html#13664" class="Bound">x</a>
 <a id="13677" href="Prelude.Preliminaries.html#13621" class="Function">fst</a> <a id="13681" class="Symbol">(</a><a id="13682" href="Prelude.Preliminaries.html#13682" class="Bound">x</a> <a id="13684" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="13686" href="Prelude.Preliminaries.html#13686" class="Bound">y</a><a id="13687" class="Symbol">)</a> <a id="13689" class="Symbol">=</a> <a id="13691" href="Prelude.Preliminaries.html#13682" class="Bound">x</a>

 <a id="13695" href="Prelude.Preliminaries.html#13695" class="Function Operator">∥_∥</a> <a id="13699" href="Prelude.Preliminaries.html#13699" class="Function">snd</a> <a id="13703" class="Symbol">:</a> <a id="13705" class="Symbol">{</a><a id="13706" href="Prelude.Preliminaries.html#13706" class="Bound">X</a> <a id="13708" class="Symbol">:</a> <a id="13710" href="Prelude.Preliminaries.html#13595" class="Bound">𝓤</a> <a id="13712" href="Universes.html#403" class="Function Operator">̇</a> <a id="13714" class="Symbol">}{</a><a id="13716" href="Prelude.Preliminaries.html#13716" class="Bound">Y</a> <a id="13718" class="Symbol">:</a> <a id="13720" href="Prelude.Preliminaries.html#13706" class="Bound">X</a> <a id="13722" class="Symbol">→</a> <a id="13724" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13726" href="Universes.html#403" class="Function Operator">̇</a> <a id="13728" class="Symbol">}</a> <a id="13730" class="Symbol">→</a> <a id="13732" class="Symbol">(</a><a id="13733" href="Prelude.Preliminaries.html#13733" class="Bound">z</a> <a id="13735" class="Symbol">:</a> <a id="13737" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13739" href="Prelude.Preliminaries.html#13716" class="Bound">Y</a><a id="13740" class="Symbol">)</a> <a id="13742" class="Symbol">→</a> <a id="13744" href="Prelude.Preliminaries.html#13716" class="Bound">Y</a> <a id="13746" class="Symbol">(</a><a id="13747" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13751" href="Prelude.Preliminaries.html#13733" class="Bound">z</a><a id="13752" class="Symbol">)</a>
 <a id="13755" href="Prelude.Preliminaries.html#13695" class="Function Operator">∥</a> <a id="13757" href="Prelude.Preliminaries.html#13757" class="Bound">x</a> <a id="13759" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="13761" href="Prelude.Preliminaries.html#13761" class="Bound">y</a> <a id="13763" href="Prelude.Preliminaries.html#13695" class="Function Operator">∥</a> <a id="13765" class="Symbol">=</a> <a id="13767" href="Prelude.Preliminaries.html#13761" class="Bound">y</a>
 <a id="13770" href="Prelude.Preliminaries.html#13699" class="Function">snd</a> <a id="13774" class="Symbol">(</a><a id="13775" href="Prelude.Preliminaries.html#13775" class="Bound">x</a> <a id="13777" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="13779" href="Prelude.Preliminaries.html#13779" class="Bound">y</a><a id="13780" class="Symbol">)</a> <a id="13782" class="Symbol">=</a> <a id="13784" href="Prelude.Preliminaries.html#13779" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14061" class="Keyword">module</a> <a id="hide-pi"></a><a id="14068" href="Prelude.Preliminaries.html#14068" class="Module">hide-pi</a> <a id="14076" class="Symbol">{</a><a id="14077" href="Prelude.Preliminaries.html#14077" class="Bound">𝓤</a> <a id="14079" href="Prelude.Preliminaries.html#14079" class="Bound">𝓦</a> <a id="14081" class="Symbol">:</a> <a id="14083" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14091" class="Symbol">}</a> <a id="14093" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14101" href="Prelude.Preliminaries.html#14101" class="Function">Π</a> <a id="14103" class="Symbol">:</a> <a id="14105" class="Symbol">{</a><a id="14106" href="Prelude.Preliminaries.html#14106" class="Bound">X</a> <a id="14108" class="Symbol">:</a> <a id="14110" href="Prelude.Preliminaries.html#14077" class="Bound">𝓤</a> <a id="14112" href="Universes.html#403" class="Function Operator">̇</a> <a id="14114" class="Symbol">}</a> <a id="14116" class="Symbol">(</a><a id="14117" href="Prelude.Preliminaries.html#14117" class="Bound">A</a> <a id="14119" class="Symbol">:</a> <a id="14121" href="Prelude.Preliminaries.html#14106" class="Bound">X</a> <a id="14123" class="Symbol">→</a> <a id="14125" href="Prelude.Preliminaries.html#14079" class="Bound">𝓦</a> <a id="14127" href="Universes.html#403" class="Function Operator">̇</a> <a id="14129" class="Symbol">)</a> <a id="14131" class="Symbol">→</a> <a id="14133" href="Prelude.Preliminaries.html#14077" class="Bound">𝓤</a> <a id="14135" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14137" href="Prelude.Preliminaries.html#14079" class="Bound">𝓦</a> <a id="14139" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14142" href="Prelude.Preliminaries.html#14101" class="Function">Π</a> <a id="14144" class="Symbol">{</a><a id="14145" href="Prelude.Preliminaries.html#14145" class="Bound">X</a><a id="14146" class="Symbol">}</a> <a id="14148" href="Prelude.Preliminaries.html#14148" class="Bound">A</a> <a id="14150" class="Symbol">=</a> <a id="14152" class="Symbol">(</a><a id="14153" href="Prelude.Preliminaries.html#14153" class="Bound">x</a> <a id="14155" class="Symbol">:</a> <a id="14157" href="Prelude.Preliminaries.html#14145" class="Bound">X</a><a id="14158" class="Symbol">)</a> <a id="14160" class="Symbol">→</a> <a id="14162" href="Prelude.Preliminaries.html#14148" class="Bound">A</a> <a id="14164" href="Prelude.Preliminaries.html#14153" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14168" href="Prelude.Preliminaries.html#14168" class="Function">-Π</a> <a id="14171" class="Symbol">:</a> <a id="14173" class="Symbol">(</a><a id="14174" href="Prelude.Preliminaries.html#14174" class="Bound">X</a> <a id="14176" class="Symbol">:</a> <a id="14178" href="Prelude.Preliminaries.html#14077" class="Bound">𝓤</a> <a id="14180" href="Universes.html#403" class="Function Operator">̇</a> <a id="14182" class="Symbol">)(</a><a id="14184" href="Prelude.Preliminaries.html#14184" class="Bound">Y</a> <a id="14186" class="Symbol">:</a> <a id="14188" href="Prelude.Preliminaries.html#14174" class="Bound">X</a> <a id="14190" class="Symbol">→</a> <a id="14192" href="Prelude.Preliminaries.html#14079" class="Bound">𝓦</a> <a id="14194" href="Universes.html#403" class="Function Operator">̇</a> <a id="14196" class="Symbol">)</a> <a id="14198" class="Symbol">→</a> <a id="14200" href="Prelude.Preliminaries.html#14077" class="Bound">𝓤</a> <a id="14202" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14204" href="Prelude.Preliminaries.html#14079" class="Bound">𝓦</a> <a id="14206" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14209" href="Prelude.Preliminaries.html#14168" class="Function">-Π</a> <a id="14212" href="Prelude.Preliminaries.html#14212" class="Bound">X</a> <a id="14214" href="Prelude.Preliminaries.html#14214" class="Bound">Y</a> <a id="14216" class="Symbol">=</a> <a id="14218" href="Prelude.Preliminaries.html#14101" class="Function">Π</a> <a id="14220" href="Prelude.Preliminaries.html#14214" class="Bound">Y</a>

 <a id="14224" class="Keyword">infixr</a> <a id="14231" class="Number">-1</a> <a id="14234" href="Prelude.Preliminaries.html#14168" class="Function">-Π</a>
 <a id="14238" class="Keyword">syntax</a> <a id="14245" href="Prelude.Preliminaries.html#14168" class="Function">-Π</a> <a id="14248" class="Bound">A</a> <a id="14250" class="Symbol">(λ</a> <a id="14253" class="Bound">x</a> <a id="14255" class="Symbol">→</a> <a id="14257" class="Bound">b</a><a id="14258" class="Symbol">)</a> <a id="14260" class="Symbol">=</a> <a id="14262" class="Function">Π</a> <a id="14264" class="Bound">x</a> <a id="14266" class="Function">꞉</a> <a id="14268" class="Bound">A</a> <a id="14270" class="Function">,</a> <a id="14272" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14562" class="Keyword">open</a> <a id="14567" class="Keyword">import</a> <a id="14574" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14585" class="Keyword">renaming</a> <a id="14594" class="Symbol">(</a><a id="14595" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14599" class="Symbol">to</a> <a id="14602" class="Keyword">infixr</a> <a id="14609" class="Number">50</a> <a id="_,_"></a><a id="14612" href="Prelude.Preliminaries.html#14612" class="InductiveConstructor Operator">_,_</a><a id="14615" class="Symbol">)</a> <a id="14617" class="Keyword">public</a>
<a id="14624" class="Keyword">open</a> <a id="14629" class="Keyword">import</a> <a id="14636" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14645" class="Keyword">using</a> <a id="14651" class="Symbol">(</a><a id="14652" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14655" class="Symbol">;</a> <a id="14657" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14660" class="Symbol">;</a> <a id="14662" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14665" class="Symbol">;</a> <a id="14667" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14669" class="Symbol">;</a> <a id="14671" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14672" class="Symbol">)</a> <a id="14674" class="Keyword">public</a>


<a id="14683" class="Keyword">module</a> <a id="14690" href="Prelude.Preliminaries.html#14690" class="Module">_</a> <a id="14692" class="Symbol">{</a><a id="14693" href="Prelude.Preliminaries.html#14693" class="Bound">𝓨</a> <a id="14695" href="Prelude.Preliminaries.html#14695" class="Bound">𝓩</a> <a id="14697" class="Symbol">:</a> <a id="14699" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14707" class="Symbol">}{</a><a id="14709" href="Prelude.Preliminaries.html#14709" class="Bound">I</a> <a id="14711" class="Symbol">:</a> <a id="14713" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14715" href="Universes.html#403" class="Function Operator">̇</a><a id="14716" class="Symbol">}{</a><a id="14718" href="Prelude.Preliminaries.html#14718" class="Bound">B</a> <a id="14720" class="Symbol">:</a> <a id="14722" href="Prelude.Preliminaries.html#14709" class="Bound">I</a> <a id="14724" class="Symbol">→</a> <a id="14726" href="Prelude.Preliminaries.html#14693" class="Bound">𝓨</a> <a id="14728" href="Universes.html#403" class="Function Operator">̇</a><a id="14729" class="Symbol">}{</a><a id="14731" href="Prelude.Preliminaries.html#14731" class="Bound">C</a> <a id="14733" class="Symbol">:</a> <a id="14735" href="Prelude.Preliminaries.html#14709" class="Bound">I</a> <a id="14737" class="Symbol">→</a> <a id="14739" href="Prelude.Preliminaries.html#14695" class="Bound">𝓩</a> <a id="14741" href="Universes.html#403" class="Function Operator">̇</a><a id="14742" class="Symbol">}</a> <a id="14744" class="Keyword">where</a>
 <a id="14751" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14774" href="Prelude.Preliminaries.html#14774" class="Function">zip</a> <a id="14778" class="Symbol">:</a> <a id="14780" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14782" href="Prelude.Preliminaries.html#14718" class="Bound">B</a> <a id="14784" class="Symbol">→</a> <a id="14786" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14788" href="Prelude.Preliminaries.html#14731" class="Bound">C</a> <a id="14790" class="Symbol">→</a> <a id="14792" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14794" class="Symbol">(λ</a> <a id="14797" href="Prelude.Preliminaries.html#14797" class="Bound">i</a> <a id="14799" class="Symbol">→</a> <a id="14801" class="Symbol">(</a><a id="14802" href="Prelude.Preliminaries.html#14718" class="Bound">B</a> <a id="14804" href="Prelude.Preliminaries.html#14797" class="Bound">i</a><a id="14805" class="Symbol">)</a> <a id="14807" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14809" class="Symbol">(</a><a id="14810" href="Prelude.Preliminaries.html#14731" class="Bound">C</a> <a id="14812" href="Prelude.Preliminaries.html#14797" class="Bound">i</a><a id="14813" class="Symbol">))</a>
 <a id="14817" href="Prelude.Preliminaries.html#14774" class="Function">zip</a> <a id="14821" href="Prelude.Preliminaries.html#14821" class="Bound">f</a> <a id="14823" href="Prelude.Preliminaries.html#14823" class="Bound">a</a> <a id="14825" class="Symbol">=</a> <a id="14827" class="Symbol">λ</a> <a id="14829" href="Prelude.Preliminaries.html#14829" class="Bound">i</a> <a id="14831" class="Symbol">→</a> <a id="14833" class="Symbol">(</a><a id="14834" href="Prelude.Preliminaries.html#14821" class="Bound">f</a> <a id="14836" href="Prelude.Preliminaries.html#14829" class="Bound">i</a> <a id="14838" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="14840" href="Prelude.Preliminaries.html#14823" class="Bound">a</a> <a id="14842" href="Prelude.Preliminaries.html#14829" class="Bound">i</a><a id="14843" class="Symbol">)</a>

 <a id="14847" href="Prelude.Preliminaries.html#14847" class="Function">eval</a> <a id="14852" class="Symbol">:</a> <a id="14854" class="Symbol">{</a><a id="14855" href="Prelude.Preliminaries.html#14855" class="Bound">Y</a> <a id="14857" class="Symbol">:</a> <a id="14859" href="Prelude.Preliminaries.html#14693" class="Bound">𝓨</a> <a id="14861" href="Universes.html#403" class="Function Operator">̇</a><a id="14862" class="Symbol">}{</a><a id="14864" href="Prelude.Preliminaries.html#14864" class="Bound">Z</a> <a id="14866" class="Symbol">:</a> <a id="14868" href="Prelude.Preliminaries.html#14695" class="Bound">𝓩</a> <a id="14870" href="Universes.html#403" class="Function Operator">̇</a><a id="14871" class="Symbol">}</a> <a id="14873" class="Symbol">→</a> <a id="14875" class="Symbol">((</a><a id="14877" href="Prelude.Preliminaries.html#14855" class="Bound">Y</a> <a id="14879" class="Symbol">→</a> <a id="14881" href="Prelude.Preliminaries.html#14864" class="Bound">Z</a><a id="14882" class="Symbol">)</a> <a id="14884" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14886" href="Prelude.Preliminaries.html#14855" class="Bound">Y</a><a id="14887" class="Symbol">)</a> <a id="14889" class="Symbol">→</a> <a id="14891" href="Prelude.Preliminaries.html#14864" class="Bound">Z</a>
 <a id="14894" href="Prelude.Preliminaries.html#14847" class="Function">eval</a> <a id="14899" class="Symbol">(</a><a id="14900" href="Prelude.Preliminaries.html#14900" class="Bound">f</a> <a id="14902" href="Prelude.Preliminaries.html#13100" class="InductiveConstructor Operator">,</a> <a id="14904" href="Prelude.Preliminaries.html#14904" class="Bound">a</a><a id="14905" class="Symbol">)</a> <a id="14907" class="Symbol">=</a> <a id="14909" href="Prelude.Preliminaries.html#14900" class="Bound">f</a> <a id="14911" href="Prelude.Preliminaries.html#14904" class="Bound">a</a>

<a id="14914" class="Keyword">module</a> <a id="14921" href="Prelude.Preliminaries.html#14921" class="Module">_</a> <a id="14923" class="Symbol">{</a><a id="14924" href="Prelude.Preliminaries.html#14924" class="Bound">𝓨</a> <a id="14926" class="Symbol">:</a> <a id="14928" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14936" class="Symbol">}{</a><a id="14938" href="Prelude.Preliminaries.html#14938" class="Bound">I</a> <a id="14940" href="Prelude.Preliminaries.html#14940" class="Bound">J</a> <a id="14942" class="Symbol">:</a> <a id="14944" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14946" href="Universes.html#403" class="Function Operator">̇</a><a id="14947" class="Symbol">}{</a><a id="14949" href="Prelude.Preliminaries.html#14949" class="Bound">B</a> <a id="14951" class="Symbol">:</a> <a id="14953" href="Prelude.Preliminaries.html#14938" class="Bound">I</a> <a id="14955" class="Symbol">→</a> <a id="14957" href="Prelude.Preliminaries.html#14924" class="Bound">𝓨</a> <a id="14959" href="Universes.html#403" class="Function Operator">̇</a><a id="14960" class="Symbol">}</a> <a id="14962" class="Keyword">where</a>

 <a id="14970" href="Prelude.Preliminaries.html#14970" class="Function">dapp</a> <a id="14975" class="Symbol">:</a> <a id="14977" class="Symbol">(∀</a> <a id="14980" href="Prelude.Preliminaries.html#14980" class="Bound">i</a> <a id="14982" class="Symbol">→</a> <a id="14984" class="Symbol">(</a><a id="14985" href="Prelude.Preliminaries.html#14940" class="Bound">J</a> <a id="14987" class="Symbol">→</a> <a id="14989" class="Symbol">(</a><a id="14990" href="Prelude.Preliminaries.html#14949" class="Bound">B</a> <a id="14992" href="Prelude.Preliminaries.html#14980" class="Bound">i</a><a id="14993" class="Symbol">))</a> <a id="14996" class="Symbol">→</a> <a id="14998" class="Symbol">(</a><a id="14999" href="Prelude.Preliminaries.html#14949" class="Bound">B</a> <a id="15001" href="Prelude.Preliminaries.html#14980" class="Bound">i</a><a id="15002" class="Symbol">))</a> <a id="15005" class="Symbol">→</a> <a id="15007" class="Symbol">(∀</a> <a id="15010" href="Prelude.Preliminaries.html#15010" class="Bound">i</a> <a id="15012" class="Symbol">→</a> <a id="15014" class="Symbol">(</a><a id="15015" href="Prelude.Preliminaries.html#14940" class="Bound">J</a> <a id="15017" class="Symbol">→</a> <a id="15019" class="Symbol">(</a><a id="15020" href="Prelude.Preliminaries.html#14949" class="Bound">B</a> <a id="15022" href="Prelude.Preliminaries.html#15010" class="Bound">i</a><a id="15023" class="Symbol">)))</a> <a id="15027" class="Symbol">→</a> <a id="15029" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="15031" href="Prelude.Preliminaries.html#14949" class="Bound">B</a>
 <a id="15034" href="Prelude.Preliminaries.html#14970" class="Function">dapp</a> <a id="15039" href="Prelude.Preliminaries.html#15039" class="Bound">f</a> <a id="15041" href="Prelude.Preliminaries.html#15041" class="Bound">a</a> <a id="15043" class="Symbol">=</a> <a id="15045" class="Symbol">λ</a> <a id="15047" href="Prelude.Preliminaries.html#15047" class="Bound">i</a> <a id="15049" class="Symbol">→</a> <a id="15051" class="Symbol">(</a><a id="15052" href="Prelude.Preliminaries.html#15039" class="Bound">f</a> <a id="15054" href="Prelude.Preliminaries.html#15047" class="Bound">i</a><a id="15055" class="Symbol">)</a> <a id="15057" class="Symbol">(</a><a id="15058" href="Prelude.Preliminaries.html#15041" class="Bound">a</a> <a id="15060" href="Prelude.Preliminaries.html#15047" class="Bound">i</a><a id="15061" class="Symbol">)</a>

</pre>

----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> Generally speaking, we have made a concerted effort to avoid duplicating types that were already defined in libraries that came before ours.  However, it is very likely that our library overlaps to some extent with other libraries with which we are as yet unfamiliar.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<br>
<br>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

