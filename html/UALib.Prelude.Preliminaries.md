---
layout: default
title : UALib.Prelude.Preliminaries module (The Agda Universal Algebra Library)
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

This section describes the [UALib.Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

**Notation**. Here are some acronyms that we use frequently.

  * MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
  * MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

---------------------------------

#### <a id="options">Options</a>

All Agda programs begin by setting some options and by importing from existing libraries (in our case, the [Agda Standard Library][] and the [Type Topology][] library by MHE). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

<pre class="Agda">

<a id="1267" class="Symbol">{-#</a> <a id="1271" class="Keyword">OPTIONS</a> <a id="1279" class="Pragma">--without-K</a> <a id="1291" class="Pragma">--exact-split</a> <a id="1305" class="Pragma">--safe</a> <a id="1312" class="Symbol">#-}</a>

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

---------------------------------

#### <a id="modules">Modules</a>

The `OPTIONS` line is usually followed by the start of a module.  For example, here's how we start the Preliminaries module here.

<pre class="Agda">

<a id="3164" class="Keyword">module</a> <a id="3171" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="3199" class="Keyword">where</a>

</pre>

Sometimes we may wish to pass in parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module.  We'll see many examples later, but as a preview,

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
```

is how we often start an (anonymous) module in which the fixed signature 𝑆 will be assumed until the end of the module. (The module started with the line above would be anonymous because the underscore `_` appears instead of a module name.)

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

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.

----------------------------------

#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martin Escardo][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.

We import these now.

<pre class="Agda">

<a id="5624" class="Keyword">open</a> <a id="5629" class="Keyword">import</a> <a id="5636" href="universes.html" class="Module">universes</a> <a id="5646" class="Keyword">public</a>

<a id="5654" class="Keyword">open</a> <a id="5659" class="Keyword">import</a> <a id="5666" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="5680" class="Keyword">renaming</a> <a id="5689" class="Symbol">(</a><a id="5690" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="5694" class="Symbol">to</a> <a id="5697" class="Keyword">infix</a> <a id="5703" class="Number">0</a> <a id="_≡_"></a><a id="5705" href="UALib.Prelude.Preliminaries.html#5705" class="Datatype Operator">_≡_</a> <a id="5709" class="Symbol">;</a> <a id="5711" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5716" class="Symbol">to</a> <a id="refl"></a><a id="5719" href="UALib.Prelude.Preliminaries.html#5719" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a><a id="5723" class="Symbol">)</a> <a id="5725" class="Keyword">public</a>

<a id="5733" class="Keyword">pattern</a> <a id="refl"></a><a id="5741" href="UALib.Prelude.Preliminaries.html#5741" class="InductiveConstructor">refl</a> <a id="5746" href="UALib.Prelude.Preliminaries.html#5760" class="Bound">x</a> <a id="5748" class="Symbol">=</a> <a id="5750" href="UALib.Prelude.Preliminaries.html#5719" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5755" class="Symbol">{</a>x <a id="5758" class="Symbol">=</a> <a id="5760" href="UALib.Prelude.Preliminaries.html#5760" class="Bound">x</a><a id="5761" class="Symbol">}</a>

<a id="5764" class="Keyword">open</a> <a id="5769" class="Keyword">import</a> <a id="5776" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="5787" class="Keyword">renaming</a> <a id="5796" class="Symbol">(</a><a id="5797" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="5801" class="Symbol">to</a> <a id="5804" class="Keyword">infixr</a> <a id="5811" class="Number">50</a> <a id="_,_"></a><a id="5814" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">_,_</a><a id="5817" class="Symbol">)</a> <a id="5819" class="Keyword">public</a>

<a id="5827" class="Keyword">open</a> <a id="5832" class="Keyword">import</a> <a id="5839" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5848" class="Keyword">using</a> <a id="5854" class="Symbol">(</a><a id="5855" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="5858" class="Symbol">;</a> <a id="5860" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="5866" class="Symbol">;</a> <a id="5868" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="5876" class="Symbol">;</a> <a id="5878" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="5887" class="Symbol">;</a> <a id="5889" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="5895" class="Symbol">;</a> <a id="5897" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="5899" class="Symbol">;</a> <a id="5901" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="5904" class="Symbol">;</a> <a id="5906" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="5909" class="Symbol">;</a> <a id="5911" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="5913" class="Symbol">;</a> <a id="5915" class="Comment">-- 𝕁;</a>
 <a id="5922" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="5923" class="Symbol">;</a> <a id="5925" href="MGS-MLTT.html#956" class="Function">¬</a><a id="5926" class="Symbol">;</a> <a id="5928" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="5931" class="Symbol">;</a> <a id="5933" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="5935" class="Symbol">;</a> <a id="5937" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5940" class="Symbol">;</a> <a id="5942" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="5945" class="Symbol">;</a> <a id="5947" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="5948" class="Symbol">;</a> <a id="5950" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="5951" class="Symbol">;</a> <a id="5953" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="5954" class="Symbol">;</a> <a id="5956" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="5959" class="Symbol">;</a> <a id="5961" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="5975" class="Symbol">;</a> <a id="5977" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="5991" class="Symbol">;</a> <a id="5993" href="MGS-MLTT.html#3744" class="Function">id</a><a id="5995" class="Symbol">;</a> <a id="5997" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="6000" class="Symbol">;</a> <a id="6002" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="6004" class="Symbol">)</a> <a id="6006" class="Keyword">public</a>

<a id="6014" class="Keyword">open</a> <a id="6019" class="Keyword">import</a> <a id="6026" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="6043" class="Keyword">using</a> <a id="6049" class="Symbol">(</a><a id="6050" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="6058" class="Symbol">;</a> <a id="6060" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="6067" class="Symbol">;</a> <a id="6069" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="6079" class="Symbol">)</a> <a id="6081" class="Keyword">public</a>

<a id="6089" class="Keyword">open</a> <a id="6094" class="Keyword">import</a> <a id="6101" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="6127" class="Keyword">using</a> <a id="6133" class="Symbol">(</a><a id="6134" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="6140" class="Symbol">;</a> <a id="6142" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="6156" class="Symbol">;</a> <a id="6158" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6165" class="Symbol">;</a> <a id="6167" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="6179" class="Symbol">;</a>
 <a id="6182" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6197" class="Symbol">;</a> <a id="6199" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6206" class="Symbol">;</a> <a id="6208" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6218" class="Symbol">;</a> <a id="6220" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6234" class="Symbol">;</a> <a id="6236" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6267" class="Symbol">;</a> <a id="6269" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6272" class="Symbol">;</a>
 <a id="6275" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6278" class="Symbol">;</a> <a id="6280" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6329" class="Symbol">;</a> <a id="6331" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6348" class="Symbol">;</a> <a id="6350" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6367" class="Symbol">)</a> <a id="6369" class="Keyword">public</a>

<a id="6377" class="Keyword">open</a> <a id="6382" class="Keyword">import</a> <a id="6389" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6402" class="Keyword">renaming</a> <a id="6411" class="Symbol">(</a><a id="6412" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6416" class="Symbol">to</a> <a id="_∈_"></a><a id="6419" href="UALib.Prelude.Preliminaries.html#6419" class="Function Operator">_∈₀_</a><a id="6423" class="Symbol">;</a> <a id="6425" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6429" class="Symbol">to</a> <a id="_⊆_"></a><a id="6432" href="UALib.Prelude.Preliminaries.html#6432" class="Function Operator">_⊆₀_</a><a id="6436" class="Symbol">;</a> <a id="6438" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6456" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6459" href="UALib.Prelude.Preliminaries.html#6459" class="Function">∈₀-is-subsingleton</a><a id="6477" class="Symbol">)</a>
 <a id="6480" class="Keyword">using</a> <a id="6486" class="Symbol">(</a><a id="6487" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6488" class="Symbol">;</a> <a id="6490" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6511" class="Symbol">;</a> <a id="6513" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6532" class="Symbol">;</a> <a id="6534" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6556" class="Symbol">;</a> <a id="6558" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6565" class="Symbol">;</a> <a id="6567" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6573" class="Symbol">;</a> <a id="6575" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6576" class="Symbol">)</a> <a id="6578" class="Keyword">public</a>

<a id="6586" class="Keyword">open</a> <a id="6591" class="Keyword">import</a> <a id="6598" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6613" class="Keyword">using</a> <a id="6619" class="Symbol">(</a><a id="6620" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6623" class="Symbol">;</a> <a id="6625" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6629" class="Symbol">;</a> <a id="6631" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6648" class="Symbol">;</a> <a id="6650" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6662" class="Symbol">;</a> <a id="6664" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6677" class="Symbol">;</a> <a id="6679" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6690" class="Symbol">;</a>
 <a id="6693" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6699" class="Symbol">;</a> <a id="6701" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6704" class="Symbol">;</a> <a id="6706" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6733" class="Symbol">;</a> <a id="6735" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="6752" class="Symbol">;</a> <a id="6754" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="6771" class="Symbol">;</a> <a id="6773" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="6788" class="Symbol">)</a> <a id="6790" class="Keyword">public</a>

<a id="6798" class="Keyword">open</a> <a id="6803" class="Keyword">import</a> <a id="6810" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="6831" class="Keyword">using</a> <a id="6837" class="Symbol">(</a><a id="6838" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="6850" class="Symbol">)</a> <a id="6852" class="Keyword">public</a>

<a id="6860" class="Keyword">open</a> <a id="6865" class="Keyword">import</a> <a id="6872" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="6893" class="Keyword">using</a> <a id="6899" class="Symbol">(</a><a id="6900" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="6902" class="Symbol">;</a> <a id="6904" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="6907" class="Symbol">)</a> <a id="6909" class="Keyword">public</a>

<a id="6917" class="Keyword">open</a> <a id="6922" class="Keyword">import</a> <a id="6929" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="6957" class="Keyword">using</a> <a id="6963" class="Symbol">(</a><a id="6964" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="6967" class="Symbol">;</a> <a id="6969" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="6975" class="Symbol">;</a> <a id="6977" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="6998" class="Symbol">;</a>
 <a id="7001" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="7023" class="Symbol">;</a> <a id="7025" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="7030" class="Symbol">;</a> <a id="7032" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="7050" class="Symbol">;</a> <a id="7052" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="7059" class="Symbol">)</a> <a id="7061" class="Keyword">public</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.

-------------------------

#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from MHE's [Type Topology][] library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

[MHE][] has authored an outstanding set of notes called [Introduction to Univalent Foundations of Mathematics with Agda][]. We highly recommend these notes to anyone wanting more details than we provide here about MLTT and the Univalent Foundations/HoTT extensions thereof.

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

--------------------

#### <a id="dependent-pair-type">Dependent pair type</a>

Our preferred notations for the first and second projections of a product are `∣_∣` and `∥_∥`, respectively; however, we will sometimes use more standard alternatives, such as `pr₁` and `pr₂`, or `fst` and `snd`, for emphasis, readability, or compatibility with other libraries.

<pre class="Agda">

<a id="10257" class="Keyword">module</a> <a id="10264" href="UALib.Prelude.Preliminaries.html#10264" class="Module">_</a> <a id="10266" class="Symbol">{</a><a id="10267" href="UALib.Prelude.Preliminaries.html#10267" class="Bound">𝓤</a> <a id="10269" class="Symbol">:</a> <a id="10271" href="universes.html#551" class="Postulate">Universe</a><a id="10279" class="Symbol">}</a> <a id="10281" class="Keyword">where</a>
 <a id="10288" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣_∣</a> <a id="10292" href="UALib.Prelude.Preliminaries.html#10292" class="Function">fst</a> <a id="10296" class="Symbol">:</a> <a id="10298" class="Symbol">{</a><a id="10299" href="UALib.Prelude.Preliminaries.html#10299" class="Bound">X</a> <a id="10301" class="Symbol">:</a> <a id="10303" href="UALib.Prelude.Preliminaries.html#10267" class="Bound">𝓤</a> <a id="10305" href="universes.html#758" class="Function Operator">̇</a> <a id="10307" class="Symbol">}{</a><a id="10309" href="UALib.Prelude.Preliminaries.html#10309" class="Bound">Y</a> <a id="10311" class="Symbol">:</a> <a id="10313" href="UALib.Prelude.Preliminaries.html#10299" class="Bound">X</a> <a id="10315" class="Symbol">→</a> <a id="10317" href="universes.html#617" class="Generalizable">𝓥</a> <a id="10319" href="universes.html#758" class="Function Operator">̇</a><a id="10320" class="Symbol">}</a> <a id="10322" class="Symbol">→</a> <a id="10324" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10326" href="UALib.Prelude.Preliminaries.html#10309" class="Bound">Y</a> <a id="10328" class="Symbol">→</a> <a id="10330" href="UALib.Prelude.Preliminaries.html#10299" class="Bound">X</a>
 <a id="10333" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="10335" href="UALib.Prelude.Preliminaries.html#10335" class="Bound">x</a> <a id="10337" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">,</a> <a id="10339" href="UALib.Prelude.Preliminaries.html#10339" class="Bound">y</a> <a id="10341" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="10343" class="Symbol">=</a> <a id="10345" href="UALib.Prelude.Preliminaries.html#10335" class="Bound">x</a>
 <a id="10348" href="UALib.Prelude.Preliminaries.html#10292" class="Function">fst</a> <a id="10352" class="Symbol">(</a><a id="10353" href="UALib.Prelude.Preliminaries.html#10353" class="Bound">x</a> <a id="10355" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">,</a> <a id="10357" href="UALib.Prelude.Preliminaries.html#10357" class="Bound">y</a><a id="10358" class="Symbol">)</a> <a id="10360" class="Symbol">=</a> <a id="10362" href="UALib.Prelude.Preliminaries.html#10353" class="Bound">x</a>

 <a id="10366" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥_∥</a> <a id="10370" href="UALib.Prelude.Preliminaries.html#10370" class="Function">snd</a> <a id="10374" class="Symbol">:</a> <a id="10376" class="Symbol">{</a><a id="10377" href="UALib.Prelude.Preliminaries.html#10377" class="Bound">X</a> <a id="10379" class="Symbol">:</a> <a id="10381" href="UALib.Prelude.Preliminaries.html#10267" class="Bound">𝓤</a> <a id="10383" href="universes.html#758" class="Function Operator">̇</a> <a id="10385" class="Symbol">}{</a><a id="10387" href="UALib.Prelude.Preliminaries.html#10387" class="Bound">Y</a> <a id="10389" class="Symbol">:</a> <a id="10391" href="UALib.Prelude.Preliminaries.html#10377" class="Bound">X</a> <a id="10393" class="Symbol">→</a> <a id="10395" href="universes.html#617" class="Generalizable">𝓥</a> <a id="10397" href="universes.html#758" class="Function Operator">̇</a> <a id="10399" class="Symbol">}</a> <a id="10401" class="Symbol">→</a> <a id="10403" class="Symbol">(</a><a id="10404" href="UALib.Prelude.Preliminaries.html#10404" class="Bound">z</a> <a id="10406" class="Symbol">:</a> <a id="10408" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10410" href="UALib.Prelude.Preliminaries.html#10387" class="Bound">Y</a><a id="10411" class="Symbol">)</a> <a id="10413" class="Symbol">→</a> <a id="10415" href="UALib.Prelude.Preliminaries.html#10387" class="Bound">Y</a> <a id="10417" class="Symbol">(</a><a id="10418" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="10422" href="UALib.Prelude.Preliminaries.html#10404" class="Bound">z</a><a id="10423" class="Symbol">)</a>
 <a id="10426" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="10428" href="UALib.Prelude.Preliminaries.html#10428" class="Bound">x</a> <a id="10430" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">,</a> <a id="10432" href="UALib.Prelude.Preliminaries.html#10432" class="Bound">y</a> <a id="10434" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="10436" class="Symbol">=</a> <a id="10438" href="UALib.Prelude.Preliminaries.html#10432" class="Bound">y</a>
 <a id="10441" href="UALib.Prelude.Preliminaries.html#10370" class="Function">snd</a> <a id="10445" class="Symbol">(</a><a id="10446" href="UALib.Prelude.Preliminaries.html#10446" class="Bound">x</a> <a id="10448" href="UALib.Prelude.Preliminaries.html#5814" class="InductiveConstructor Operator">,</a> <a id="10450" href="UALib.Prelude.Preliminaries.html#10450" class="Bound">y</a><a id="10451" class="Symbol">)</a> <a id="10453" class="Symbol">=</a> <a id="10455" href="UALib.Prelude.Preliminaries.html#10450" class="Bound">y</a>

</pre>

For the dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`). The preferred notation is made available by making the index type explicit.

```agda
infixr -1 -Σ
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`
```

<div class="admonition warning">

The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

</div>

MHE explains Sigma induction as follows: "To prove that `A z` holds for all `z : Σ Y`, for a given property `A`, we just prove that we have `A (x , y)` for all `x : X` and `y : Y x`. This is called `Σ` induction or `Σ` elimination (or `uncurry`).

```agda
Σ-induction : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →            ((x : X)(y : Y x) → A (x , y))
              -------------------------------
 →            ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →      (((x , y) : Σ Y ) → A (x , y))
       ---------------------------------
 →      ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
```

The special case in which the type `Y` doesn't depend on `X` is the usual Cartesian product.

```agda
infixr 30 _×_
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y
```

------------------

#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

```agda
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇ )(Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b
```

---------------------------------------------------

#### <a id="truncation">Truncation</a>

In general, we may have many inhabitants of a given type and, via the Curry-Howard correspondence, many proofs of a given proposition.  For instance, suppose we have a type `X` and an identity relation ≡ₓ on X. Then, given two inhabitants `a` and `b` of type `X`, we may ask whether `a ≡ₓ b`.

Suppose `p` and `q` inhabit the identity type `a ≡ₓ b`; that is, `p` and `q` are proofs of `a ≡ₓ b`, in which case we write `p  q : a ≡ₓ b`.  Then we might wonder whether and in what sense are the two proofs `p` and `q` the "same."  We are asking about an identity type on the identity type ≡ₓ, and whether there is some inhabitant `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proof of `a ≡ₓ b` is unique.  (This property is sometimes called *uniqueness of identity proofs*.)

Perhaps we have two proofs, say, `r s : p ≡ₓ₁ q`. Then of course we will ask whether `r ≡ₓ₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof relevance*) is not useful or desirable.  At that point, say, at level `k`, we might assume that there is at most one proof of any identity of the form `p ≡ₓₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation).

We will see some examples of trunction later when we require it to complete some of the UALib modules leading up to the proof of Birkhoff's HSP Theorem.  Readers who want more details should refer to [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of MHE's notes, or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

We take this opportunity to define *set* (or 0-*groupoid*) in type theory.  A type X : 𝓤 ̇ with an identity relation `≡ₓ` is called a **set** if for every pair `a b : X` of elements of type `X` there is at most one proof of `a ≡ₓ b`.

This notion is formalized in the [Type Topology][] library as follows:<span class="footnote"><sup>2</sup></span>

```agda
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<p></p>

<span class="footnote"><sup>2</sup>As [MHE][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>


-----------------------------

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

