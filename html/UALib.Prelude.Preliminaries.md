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

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.

----------------------------------

#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martin Escardo][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.

We import these now.

<pre class="Agda">

<a id="5573" class="Keyword">open</a> <a id="5578" class="Keyword">import</a> <a id="5585" href="universes.html" class="Module">universes</a> <a id="5595" class="Keyword">public</a>

<a id="5603" class="Keyword">open</a> <a id="5608" class="Keyword">import</a> <a id="5615" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="5629" class="Keyword">renaming</a> <a id="5638" class="Symbol">(</a><a id="5639" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="5643" class="Symbol">to</a> <a id="5646" class="Keyword">infix</a> <a id="5652" class="Number">0</a> <a id="_≡_"></a><a id="5654" href="UALib.Prelude.Preliminaries.html#5654" class="Datatype Operator">_≡_</a> <a id="5658" class="Symbol">;</a> <a id="5660" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5665" class="Symbol">to</a> <a id="refl"></a><a id="5668" href="UALib.Prelude.Preliminaries.html#5668" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a><a id="5672" class="Symbol">)</a> <a id="5674" class="Keyword">public</a>

<a id="5682" class="Keyword">pattern</a> <a id="refl"></a><a id="5690" href="UALib.Prelude.Preliminaries.html#5690" class="InductiveConstructor">refl</a> <a id="5695" href="UALib.Prelude.Preliminaries.html#5709" class="Bound">x</a> <a id="5697" class="Symbol">=</a> <a id="5699" href="UALib.Prelude.Preliminaries.html#5668" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5704" class="Symbol">{</a>x <a id="5707" class="Symbol">=</a> <a id="5709" href="UALib.Prelude.Preliminaries.html#5709" class="Bound">x</a><a id="5710" class="Symbol">}</a>

<a id="5713" class="Keyword">open</a> <a id="5718" class="Keyword">import</a> <a id="5725" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="5736" class="Keyword">renaming</a> <a id="5745" class="Symbol">(</a><a id="5746" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="5750" class="Symbol">to</a> <a id="5753" class="Keyword">infixr</a> <a id="5760" class="Number">50</a> <a id="_,_"></a><a id="5763" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">_,_</a><a id="5766" class="Symbol">)</a> <a id="5768" class="Keyword">public</a>

<a id="5776" class="Keyword">open</a> <a id="5781" class="Keyword">import</a> <a id="5788" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5797" class="Keyword">using</a> <a id="5803" class="Symbol">(</a><a id="5804" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="5807" class="Symbol">;</a> <a id="5809" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="5815" class="Symbol">;</a> <a id="5817" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="5825" class="Symbol">;</a> <a id="5827" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="5836" class="Symbol">;</a> <a id="5838" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="5844" class="Symbol">;</a> <a id="5846" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="5848" class="Symbol">;</a>
  <a id="5852" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="5855" class="Symbol">;</a> <a id="5857" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="5860" class="Symbol">;</a> <a id="5862" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="5864" class="Symbol">;</a> <a id="5866" href="MGS-MLTT.html#4313" class="Function">𝕁</a><a id="5867" class="Symbol">;</a> <a id="5869" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="5870" class="Symbol">;</a> <a id="5872" href="MGS-MLTT.html#956" class="Function">¬</a><a id="5873" class="Symbol">;</a> <a id="5875" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="5878" class="Symbol">;</a> <a id="5880" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="5882" class="Symbol">;</a> <a id="5884" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5887" class="Symbol">;</a> <a id="5889" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="5892" class="Symbol">;</a> <a id="5894" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="5895" class="Symbol">;</a> <a id="5897" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="5898" class="Symbol">;</a> <a id="5900" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="5901" class="Symbol">;</a> <a id="5903" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="5906" class="Symbol">;</a>
  <a id="5910" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="5924" class="Symbol">;</a> <a id="5926" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="5940" class="Symbol">;</a> <a id="5942" href="MGS-MLTT.html#3744" class="Function">id</a><a id="5944" class="Symbol">;</a> <a id="5946" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="5949" class="Symbol">;</a> <a id="5951" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="5953" class="Symbol">)</a> <a id="5955" class="Keyword">public</a>

<a id="5963" class="Keyword">open</a> <a id="5968" class="Keyword">import</a> <a id="5975" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="5992" class="Keyword">using</a> <a id="5998" class="Symbol">(</a><a id="5999" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="6007" class="Symbol">;</a> <a id="6009" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="6016" class="Symbol">;</a> <a id="6018" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="6028" class="Symbol">)</a> <a id="6030" class="Keyword">public</a>

<a id="6038" class="Keyword">open</a> <a id="6043" class="Keyword">import</a> <a id="6050" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="6076" class="Keyword">using</a> <a id="6082" class="Symbol">(</a><a id="6083" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="6089" class="Symbol">;</a> <a id="6091" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="6105" class="Symbol">;</a> <a id="6107" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6114" class="Symbol">;</a>
  <a id="6118" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="6130" class="Symbol">;</a> <a id="6132" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6147" class="Symbol">;</a> <a id="6149" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6156" class="Symbol">;</a> <a id="6158" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6168" class="Symbol">;</a> <a id="6170" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6184" class="Symbol">;</a>
  <a id="6188" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6219" class="Symbol">;</a> <a id="6221" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6224" class="Symbol">;</a> <a id="6226" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6229" class="Symbol">;</a> <a id="6231" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6248" class="Symbol">;</a> <a id="6250" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6267" class="Symbol">;</a>
  <a id="6271" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6320" class="Symbol">)</a> <a id="6322" class="Keyword">public</a>

<a id="6330" class="Keyword">open</a> <a id="6335" class="Keyword">import</a> <a id="6342" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6355" class="Keyword">renaming</a> <a id="6364" class="Symbol">(</a><a id="6365" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6369" class="Symbol">to</a> <a id="_∈_"></a><a id="6372" href="UALib.Prelude.Preliminaries.html#6372" class="Function Operator">_∈₀_</a><a id="6376" class="Symbol">;</a> <a id="6378" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6382" class="Symbol">to</a> <a id="_⊆_"></a><a id="6385" href="UALib.Prelude.Preliminaries.html#6385" class="Function Operator">_⊆₀_</a><a id="6389" class="Symbol">;</a> <a id="6391" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6409" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6412" href="UALib.Prelude.Preliminaries.html#6412" class="Function">∈₀-is-subsingleton</a><a id="6430" class="Symbol">)</a>
  <a id="6434" class="Keyword">using</a> <a id="6440" class="Symbol">(</a><a id="6441" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6442" class="Symbol">;</a> <a id="6444" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6465" class="Symbol">;</a> <a id="6467" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6486" class="Symbol">;</a> <a id="6488" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6510" class="Symbol">;</a> <a id="6512" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6519" class="Symbol">;</a> <a id="6521" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6527" class="Symbol">;</a> <a id="6529" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6530" class="Symbol">)</a> <a id="6532" class="Keyword">public</a>

<a id="6540" class="Keyword">open</a> <a id="6545" class="Keyword">import</a> <a id="6552" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6567" class="Keyword">using</a> <a id="6573" class="Symbol">(</a><a id="6574" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6577" class="Symbol">;</a> <a id="6579" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6583" class="Symbol">;</a> <a id="6585" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6602" class="Symbol">;</a> <a id="6604" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6616" class="Symbol">;</a> <a id="6618" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6631" class="Symbol">;</a> <a id="6633" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6644" class="Symbol">;</a>
  <a id="6648" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6654" class="Symbol">;</a> <a id="6656" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6659" class="Symbol">;</a> <a id="6661" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6688" class="Symbol">;</a> <a id="6690" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="6707" class="Symbol">;</a> <a id="6709" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="6726" class="Symbol">;</a> <a id="6728" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="6743" class="Symbol">)</a> <a id="6745" class="Keyword">public</a>

<a id="6753" class="Keyword">open</a> <a id="6758" class="Keyword">import</a> <a id="6765" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="6786" class="Keyword">using</a> <a id="6792" class="Symbol">(</a><a id="6793" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="6805" class="Symbol">)</a> <a id="6807" class="Keyword">public</a>

<a id="6815" class="Keyword">open</a> <a id="6820" class="Keyword">import</a> <a id="6827" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="6848" class="Keyword">using</a> <a id="6854" class="Symbol">(</a><a id="6855" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="6857" class="Symbol">;</a> <a id="6859" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="6862" class="Symbol">)</a> <a id="6864" class="Keyword">public</a>

<a id="6872" class="Keyword">open</a> <a id="6877" class="Keyword">import</a> <a id="6884" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="6912" class="Keyword">using</a> <a id="6918" class="Symbol">(</a><a id="6919" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="6922" class="Symbol">;</a> <a id="6924" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="6930" class="Symbol">;</a> <a id="6932" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="6953" class="Symbol">;</a>
  <a id="6957" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="6979" class="Symbol">;</a> <a id="6981" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="6986" class="Symbol">;</a> <a id="6988" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="7006" class="Symbol">;</a> <a id="7008" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="7015" class="Symbol">)</a> <a id="7017" class="Keyword">public</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.

-------------------------

#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from MHE's \href{https://github.com/martinescardo/TypeTopology}{Type Topology} library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

\mhe has authored an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}. We highly recommend Martin's notes to anyone wanting more details than we provide here about MLTT and the Univalent Foundations/HoTT extensions thereof.

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

<a id="10339" class="Keyword">module</a> <a id="10346" href="UALib.Prelude.Preliminaries.html#10346" class="Module">_</a> <a id="10348" class="Symbol">{</a><a id="10349" href="UALib.Prelude.Preliminaries.html#10349" class="Bound">𝓤</a> <a id="10351" class="Symbol">:</a> <a id="10353" href="universes.html#551" class="Postulate">Universe</a><a id="10361" class="Symbol">}</a> <a id="10363" class="Keyword">where</a>
  <a id="10371" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣_∣</a> <a id="10375" href="UALib.Prelude.Preliminaries.html#10375" class="Function">fst</a> <a id="10379" class="Symbol">:</a> <a id="10381" class="Symbol">{</a><a id="10382" href="UALib.Prelude.Preliminaries.html#10382" class="Bound">X</a> <a id="10384" class="Symbol">:</a> <a id="10386" href="UALib.Prelude.Preliminaries.html#10349" class="Bound">𝓤</a> <a id="10388" href="universes.html#758" class="Function Operator">̇</a> <a id="10390" class="Symbol">}{</a><a id="10392" href="UALib.Prelude.Preliminaries.html#10392" class="Bound">Y</a> <a id="10394" class="Symbol">:</a> <a id="10396" href="UALib.Prelude.Preliminaries.html#10382" class="Bound">X</a> <a id="10398" class="Symbol">→</a> <a id="10400" href="universes.html#617" class="Generalizable">𝓥</a> <a id="10402" href="universes.html#758" class="Function Operator">̇</a><a id="10403" class="Symbol">}</a> <a id="10405" class="Symbol">→</a> <a id="10407" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10409" href="UALib.Prelude.Preliminaries.html#10392" class="Bound">Y</a> <a id="10411" class="Symbol">→</a> <a id="10413" href="UALib.Prelude.Preliminaries.html#10382" class="Bound">X</a>
  <a id="10417" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="10419" href="UALib.Prelude.Preliminaries.html#10419" class="Bound">x</a> <a id="10421" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="10423" href="UALib.Prelude.Preliminaries.html#10423" class="Bound">y</a> <a id="10425" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="10427" class="Symbol">=</a> <a id="10429" href="UALib.Prelude.Preliminaries.html#10419" class="Bound">x</a>
  <a id="10433" href="UALib.Prelude.Preliminaries.html#10375" class="Function">fst</a> <a id="10437" class="Symbol">(</a><a id="10438" href="UALib.Prelude.Preliminaries.html#10438" class="Bound">x</a> <a id="10440" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="10442" href="UALib.Prelude.Preliminaries.html#10442" class="Bound">y</a><a id="10443" class="Symbol">)</a> <a id="10445" class="Symbol">=</a> <a id="10447" href="UALib.Prelude.Preliminaries.html#10438" class="Bound">x</a>

  <a id="10452" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥_∥</a> <a id="10456" href="UALib.Prelude.Preliminaries.html#10456" class="Function">snd</a> <a id="10460" class="Symbol">:</a> <a id="10462" class="Symbol">{</a><a id="10463" href="UALib.Prelude.Preliminaries.html#10463" class="Bound">X</a> <a id="10465" class="Symbol">:</a> <a id="10467" href="UALib.Prelude.Preliminaries.html#10349" class="Bound">𝓤</a> <a id="10469" href="universes.html#758" class="Function Operator">̇</a> <a id="10471" class="Symbol">}{</a><a id="10473" href="UALib.Prelude.Preliminaries.html#10473" class="Bound">Y</a> <a id="10475" class="Symbol">:</a> <a id="10477" href="UALib.Prelude.Preliminaries.html#10463" class="Bound">X</a> <a id="10479" class="Symbol">→</a> <a id="10481" href="universes.html#617" class="Generalizable">𝓥</a> <a id="10483" href="universes.html#758" class="Function Operator">̇</a> <a id="10485" class="Symbol">}</a> <a id="10487" class="Symbol">→</a> <a id="10489" class="Symbol">(</a><a id="10490" href="UALib.Prelude.Preliminaries.html#10490" class="Bound">z</a> <a id="10492" class="Symbol">:</a> <a id="10494" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="10496" href="UALib.Prelude.Preliminaries.html#10473" class="Bound">Y</a><a id="10497" class="Symbol">)</a> <a id="10499" class="Symbol">→</a> <a id="10501" href="UALib.Prelude.Preliminaries.html#10473" class="Bound">Y</a> <a id="10503" class="Symbol">(</a><a id="10504" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="10508" href="UALib.Prelude.Preliminaries.html#10490" class="Bound">z</a><a id="10509" class="Symbol">)</a>
  <a id="10513" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="10515" href="UALib.Prelude.Preliminaries.html#10515" class="Bound">x</a> <a id="10517" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="10519" href="UALib.Prelude.Preliminaries.html#10519" class="Bound">y</a> <a id="10521" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="10523" class="Symbol">=</a> <a id="10525" href="UALib.Prelude.Preliminaries.html#10519" class="Bound">y</a>
  <a id="10529" href="UALib.Prelude.Preliminaries.html#10456" class="Function">snd</a> <a id="10533" class="Symbol">(</a><a id="10534" href="UALib.Prelude.Preliminaries.html#10534" class="Bound">x</a> <a id="10536" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="10538" href="UALib.Prelude.Preliminaries.html#10538" class="Bound">y</a><a id="10539" class="Symbol">)</a> <a id="10541" class="Symbol">=</a> <a id="10543" href="UALib.Prelude.Preliminaries.html#10538" class="Bound">y</a>

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

```
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

<pre class="Agda">

<a id="Π&#39;"></a><a id="12288" href="UALib.Prelude.Preliminaries.html#12288" class="Function">Π&#39;</a> <a id="12291" class="Symbol">:</a> <a id="12293" class="Symbol">{</a><a id="12294" href="UALib.Prelude.Preliminaries.html#12294" class="Bound">𝓤</a> <a id="12296" href="UALib.Prelude.Preliminaries.html#12296" class="Bound">𝓦</a> <a id="12298" class="Symbol">:</a> <a id="12300" href="universes.html#551" class="Postulate">Universe</a><a id="12308" class="Symbol">}{</a><a id="12310" href="UALib.Prelude.Preliminaries.html#12310" class="Bound">X</a> <a id="12312" class="Symbol">:</a> <a id="12314" href="UALib.Prelude.Preliminaries.html#12294" class="Bound">𝓤</a> <a id="12316" href="universes.html#758" class="Function Operator">̇</a> <a id="12318" class="Symbol">}</a> <a id="12320" class="Symbol">(</a><a id="12321" href="UALib.Prelude.Preliminaries.html#12321" class="Bound">A</a> <a id="12323" class="Symbol">:</a> <a id="12325" href="UALib.Prelude.Preliminaries.html#12310" class="Bound">X</a> <a id="12327" class="Symbol">→</a> <a id="12329" href="UALib.Prelude.Preliminaries.html#12296" class="Bound">𝓦</a> <a id="12331" href="universes.html#758" class="Function Operator">̇</a> <a id="12333" class="Symbol">)</a> <a id="12335" class="Symbol">→</a> <a id="12337" href="UALib.Prelude.Preliminaries.html#12294" class="Bound">𝓤</a> <a id="12339" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12341" href="UALib.Prelude.Preliminaries.html#12296" class="Bound">𝓦</a> <a id="12343" href="universes.html#758" class="Function Operator">̇</a>
<a id="12345" href="UALib.Prelude.Preliminaries.html#12288" class="Function">Π&#39;</a> <a id="12348" class="Symbol">{</a><a id="12349" href="UALib.Prelude.Preliminaries.html#12349" class="Bound">𝓤</a><a id="12350" class="Symbol">}</a> <a id="12352" class="Symbol">{</a><a id="12353" href="UALib.Prelude.Preliminaries.html#12353" class="Bound">𝓦</a><a id="12354" class="Symbol">}</a> <a id="12356" class="Symbol">{</a><a id="12357" href="UALib.Prelude.Preliminaries.html#12357" class="Bound">X</a><a id="12358" class="Symbol">}</a> <a id="12360" href="UALib.Prelude.Preliminaries.html#12360" class="Bound">A</a> <a id="12362" class="Symbol">=</a> <a id="12364" class="Symbol">(</a><a id="12365" href="UALib.Prelude.Preliminaries.html#12365" class="Bound">x</a> <a id="12367" class="Symbol">:</a> <a id="12369" href="UALib.Prelude.Preliminaries.html#12357" class="Bound">X</a><a id="12370" class="Symbol">)</a> <a id="12372" class="Symbol">→</a> <a id="12374" href="UALib.Prelude.Preliminaries.html#12360" class="Bound">A</a> <a id="12376" href="UALib.Prelude.Preliminaries.html#12365" class="Bound">x</a>

<a id="-Π&#39;"></a><a id="12379" href="UALib.Prelude.Preliminaries.html#12379" class="Function">-Π&#39;</a> <a id="12383" class="Symbol">:</a> <a id="12385" class="Symbol">{</a><a id="12386" href="UALib.Prelude.Preliminaries.html#12386" class="Bound">𝓤</a> <a id="12388" href="UALib.Prelude.Preliminaries.html#12388" class="Bound">𝓦</a> <a id="12390" class="Symbol">:</a> <a id="12392" href="universes.html#551" class="Postulate">Universe</a><a id="12400" class="Symbol">}(</a><a id="12402" href="UALib.Prelude.Preliminaries.html#12402" class="Bound">X</a> <a id="12404" class="Symbol">:</a> <a id="12406" href="UALib.Prelude.Preliminaries.html#12386" class="Bound">𝓤</a> <a id="12408" href="universes.html#758" class="Function Operator">̇</a> <a id="12410" class="Symbol">)(</a><a id="12412" href="UALib.Prelude.Preliminaries.html#12412" class="Bound">Y</a> <a id="12414" class="Symbol">:</a> <a id="12416" href="UALib.Prelude.Preliminaries.html#12402" class="Bound">X</a> <a id="12418" class="Symbol">→</a> <a id="12420" href="UALib.Prelude.Preliminaries.html#12388" class="Bound">𝓦</a> <a id="12422" href="universes.html#758" class="Function Operator">̇</a> <a id="12424" class="Symbol">)</a> <a id="12426" class="Symbol">→</a> <a id="12428" href="UALib.Prelude.Preliminaries.html#12386" class="Bound">𝓤</a> <a id="12430" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12432" href="UALib.Prelude.Preliminaries.html#12388" class="Bound">𝓦</a> <a id="12434" href="universes.html#758" class="Function Operator">̇</a>
<a id="12436" href="UALib.Prelude.Preliminaries.html#12379" class="Function">-Π&#39;</a> <a id="12440" href="UALib.Prelude.Preliminaries.html#12440" class="Bound">X</a> <a id="12442" href="UALib.Prelude.Preliminaries.html#12442" class="Bound">Y</a> <a id="12444" class="Symbol">=</a> <a id="12446" href="UALib.Prelude.Preliminaries.html#12288" class="Function">Π&#39;</a> <a id="12449" href="UALib.Prelude.Preliminaries.html#12442" class="Bound">Y</a>
<a id="12451" class="Keyword">infixr</a> <a id="12458" class="Number">-1</a> <a id="12461" href="UALib.Prelude.Preliminaries.html#12379" class="Function">-Π&#39;</a>
<a id="12465" class="Keyword">syntax</a> <a id="12472" href="UALib.Prelude.Preliminaries.html#12379" class="Function">-Π&#39;</a> <a id="12476" class="Bound">A</a> <a id="12478" class="Symbol">(λ</a> <a id="12481" class="Bound">x</a> <a id="12483" class="Symbol">→</a> <a id="12485" class="Bound">b</a><a id="12486" class="Symbol">)</a> <a id="12488" class="Symbol">=</a> <a id="12490" class="Function">Π&#39;</a> <a id="12493" class="Bound">x</a> <a id="12495" class="Function">꞉</a> <a id="12497" class="Bound">A</a> <a id="12499" class="Function">,</a> <a id="12501" class="Bound">b</a>

</pre>

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

<br></br>

<span class="footnote"><sup>2</sup>As [MHE][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

<p></p>

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

