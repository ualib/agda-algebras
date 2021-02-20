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

#### <a id="options">Options</a>

All Agda programs begin by setting some options and by importing from existing libraries (in our case, the [Agda Standard Library][] and the [Type Topology][] library by MHE). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

<pre class="Agda">

<a id="1232" class="Symbol">{-#</a> <a id="1236" class="Keyword">OPTIONS</a> <a id="1244" class="Pragma">--without-K</a> <a id="1256" class="Pragma">--exact-split</a> <a id="1270" class="Pragma">--safe</a> <a id="1277" class="Symbol">#-}</a>

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

The `OPTIONS` line is usually followed by the start of a module.  For example, here's how we start the Preliminaries module here.

<pre class="Agda">

<a id="3098" class="Keyword">module</a> <a id="3105" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="3133" class="Keyword">where</a>

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





#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martin Escardo][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.

We import these now.

<pre class="Agda">

<a id="5475" class="Keyword">open</a> <a id="5480" class="Keyword">import</a> <a id="5487" href="universes.html" class="Module">universes</a> <a id="5497" class="Keyword">public</a>

<a id="5505" class="Keyword">open</a> <a id="5510" class="Keyword">import</a> <a id="5517" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="5531" class="Keyword">renaming</a> <a id="5540" class="Symbol">(</a><a id="5541" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="5545" class="Symbol">to</a> <a id="5548" class="Keyword">infix</a> <a id="5554" class="Number">0</a> <a id="_≡_"></a><a id="5556" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">_≡_</a> <a id="5560" class="Symbol">;</a> <a id="5562" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5567" class="Symbol">to</a> <a id="refl"></a><a id="5570" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a><a id="5574" class="Symbol">)</a> <a id="5576" class="Keyword">public</a>

<a id="5584" class="Keyword">pattern</a> <a id="refl"></a><a id="5592" href="UALib.Prelude.Preliminaries.html#5592" class="InductiveConstructor">refl</a> <a id="5597" href="UALib.Prelude.Preliminaries.html#5611" class="Bound">x</a> <a id="5599" class="Symbol">=</a> <a id="5601" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5606" class="Symbol">{</a>x <a id="5609" class="Symbol">=</a> <a id="5611" href="UALib.Prelude.Preliminaries.html#5611" class="Bound">x</a><a id="5612" class="Symbol">}</a>

<a id="5615" class="Keyword">open</a> <a id="5620" class="Keyword">import</a> <a id="5627" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="5638" class="Keyword">renaming</a> <a id="5647" class="Symbol">(</a><a id="5648" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="5652" class="Symbol">to</a> <a id="5655" class="Keyword">infixr</a> <a id="5662" class="Number">50</a> <a id="_,_"></a><a id="5665" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">_,_</a><a id="5668" class="Symbol">)</a> <a id="5670" class="Keyword">public</a>

<a id="5678" class="Keyword">open</a> <a id="5683" class="Keyword">import</a> <a id="5690" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5699" class="Keyword">using</a> <a id="5705" class="Symbol">(</a><a id="5706" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="5709" class="Symbol">;</a> <a id="5711" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="5717" class="Symbol">;</a> <a id="5719" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="5727" class="Symbol">;</a> <a id="5729" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="5738" class="Symbol">;</a> <a id="5740" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="5746" class="Symbol">;</a> <a id="5748" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="5750" class="Symbol">;</a> <a id="5752" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="5755" class="Symbol">;</a> <a id="5757" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="5760" class="Symbol">;</a> <a id="5762" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="5765" class="Symbol">;</a> <a id="5767" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="5769" class="Symbol">;</a> <a id="5771" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="5772" class="Symbol">;</a>
  <a id="5776" href="MGS-MLTT.html#956" class="Function">¬</a><a id="5777" class="Symbol">;</a> <a id="5779" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="5781" class="Symbol">;</a> <a id="5783" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5786" class="Symbol">;</a> <a id="5788" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="5791" class="Symbol">;</a> <a id="5793" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="5794" class="Symbol">;</a> <a id="5796" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="5797" class="Symbol">;</a> <a id="5799" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="5800" class="Symbol">;</a> <a id="5802" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="5805" class="Symbol">;</a> <a id="5807" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="5821" class="Symbol">;</a> <a id="5823" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="5837" class="Symbol">;</a> <a id="5839" href="MGS-MLTT.html#3744" class="Function">id</a><a id="5841" class="Symbol">;</a> <a id="5843" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="5846" class="Symbol">;</a> <a id="5848" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="5850" class="Symbol">)</a> <a id="5852" class="Keyword">public</a>

<a id="5860" class="Keyword">open</a> <a id="5865" class="Keyword">import</a> <a id="5872" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="5889" class="Keyword">using</a> <a id="5895" class="Symbol">(</a><a id="5896" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="5904" class="Symbol">;</a> <a id="5906" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="5913" class="Symbol">;</a> <a id="5915" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="5925" class="Symbol">)</a> <a id="5927" class="Keyword">public</a>

<a id="5935" class="Keyword">open</a> <a id="5940" class="Keyword">import</a> <a id="5947" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5973" class="Keyword">using</a> <a id="5979" class="Symbol">(</a><a id="5980" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5986" class="Symbol">;</a> <a id="5988" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="6002" class="Symbol">;</a> <a id="6004" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6011" class="Symbol">;</a>
  <a id="6015" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="6027" class="Symbol">;</a> <a id="6029" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6044" class="Symbol">;</a> <a id="6046" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6053" class="Symbol">;</a> <a id="6055" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6065" class="Symbol">;</a> <a id="6067" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6081" class="Symbol">;</a>
  <a id="6085" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6116" class="Symbol">;</a> <a id="6118" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6121" class="Symbol">;</a> <a id="6123" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6126" class="Symbol">;</a> <a id="6128" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6145" class="Symbol">;</a> <a id="6147" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6164" class="Symbol">;</a>
  <a id="6168" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6217" class="Symbol">)</a> <a id="6219" class="Keyword">public</a>

<a id="6227" class="Keyword">open</a> <a id="6232" class="Keyword">import</a> <a id="6239" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6252" class="Keyword">renaming</a> <a id="6261" class="Symbol">(</a><a id="6262" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6266" class="Symbol">to</a> <a id="_∈_"></a><a id="6269" href="UALib.Prelude.Preliminaries.html#6269" class="Function Operator">_∈₀_</a><a id="6273" class="Symbol">;</a> <a id="6275" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6279" class="Symbol">to</a> <a id="_⊆_"></a><a id="6282" href="UALib.Prelude.Preliminaries.html#6282" class="Function Operator">_⊆₀_</a><a id="6286" class="Symbol">;</a> <a id="6288" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6306" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6309" href="UALib.Prelude.Preliminaries.html#6309" class="Function">∈₀-is-subsingleton</a><a id="6327" class="Symbol">)</a>
  <a id="6331" class="Keyword">using</a> <a id="6337" class="Symbol">(</a><a id="6338" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6339" class="Symbol">;</a> <a id="6341" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6362" class="Symbol">;</a> <a id="6364" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6383" class="Symbol">;</a> <a id="6385" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6407" class="Symbol">;</a> <a id="6409" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6416" class="Symbol">;</a> <a id="6418" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6424" class="Symbol">;</a> <a id="6426" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6427" class="Symbol">)</a> <a id="6429" class="Keyword">public</a>

<a id="6437" class="Keyword">open</a> <a id="6442" class="Keyword">import</a> <a id="6449" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6464" class="Keyword">using</a> <a id="6470" class="Symbol">(</a><a id="6471" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6474" class="Symbol">;</a> <a id="6476" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6480" class="Symbol">;</a> <a id="6482" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6499" class="Symbol">;</a> <a id="6501" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6513" class="Symbol">;</a> <a id="6515" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6528" class="Symbol">;</a> <a id="6530" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6541" class="Symbol">;</a>
  <a id="6545" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6551" class="Symbol">;</a> <a id="6553" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6556" class="Symbol">;</a> <a id="6558" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6585" class="Symbol">;</a> <a id="6587" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="6604" class="Symbol">;</a> <a id="6606" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="6623" class="Symbol">;</a> <a id="6625" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="6640" class="Symbol">)</a> <a id="6642" class="Keyword">public</a>

<a id="6650" class="Keyword">open</a> <a id="6655" class="Keyword">import</a> <a id="6662" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="6683" class="Keyword">using</a> <a id="6689" class="Symbol">(</a><a id="6690" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="6702" class="Symbol">)</a> <a id="6704" class="Keyword">public</a>

<a id="6712" class="Keyword">open</a> <a id="6717" class="Keyword">import</a> <a id="6724" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="6745" class="Keyword">using</a> <a id="6751" class="Symbol">(</a><a id="6752" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="6754" class="Symbol">;</a> <a id="6756" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="6759" class="Symbol">)</a> <a id="6761" class="Keyword">public</a>

<a id="6769" class="Keyword">open</a> <a id="6774" class="Keyword">import</a> <a id="6781" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="6809" class="Keyword">using</a> <a id="6815" class="Symbol">(</a><a id="6816" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="6819" class="Symbol">;</a> <a id="6821" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="6827" class="Symbol">;</a> <a id="6829" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="6850" class="Symbol">;</a>
  <a id="6854" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="6876" class="Symbol">;</a> <a id="6878" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="6883" class="Symbol">;</a> <a id="6885" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="6903" class="Symbol">;</a> <a id="6905" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="6912" class="Symbol">)</a> <a id="6914" class="Keyword">public</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.





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





#### <a id="dependent-pair-type">Dependent pair type</a>

The **Sigma type** `Σ(x : A) , B x`, also known as the **dependent pair type**, generalizes the Cartesian product `A × B` by allowing the type `B x` of the second argument of the ordered pair to depend on the value `x` of the first.  Escardó defines this type in a stardard way (cf. the [Agda Standard Library][]) as a record type.


```agda
record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 constructor _,_
 field
  pr₁ : X
  pr₂ : Y pr₁

infixr 50 _,_
```

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in his [TypeTopology][] library by making the index type explicit, as follows.

```agda
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → Y) = Σ x ꞉ X , Y
```

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

```agda
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y
```


The definition of Σ (and thus, of ×) above comes equipped with first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="11626" class="Keyword">module</a> <a id="11633" href="UALib.Prelude.Preliminaries.html#11633" class="Module">_</a> <a id="11635" class="Symbol">{</a><a id="11636" href="UALib.Prelude.Preliminaries.html#11636" class="Bound">𝓤</a> <a id="11638" class="Symbol">:</a> <a id="11640" href="universes.html#551" class="Postulate">Universe</a><a id="11648" class="Symbol">}</a> <a id="11650" class="Keyword">where</a>

  <a id="11659" href="UALib.Prelude.Preliminaries.html#11659" class="Function Operator">∣_∣</a> <a id="11663" href="UALib.Prelude.Preliminaries.html#11663" class="Function">fst</a> <a id="11667" class="Symbol">:</a> <a id="11669" class="Symbol">{</a><a id="11670" href="UALib.Prelude.Preliminaries.html#11670" class="Bound">X</a> <a id="11672" class="Symbol">:</a> <a id="11674" href="UALib.Prelude.Preliminaries.html#11636" class="Bound">𝓤</a> <a id="11676" href="universes.html#758" class="Function Operator">̇</a> <a id="11678" class="Symbol">}{</a><a id="11680" href="UALib.Prelude.Preliminaries.html#11680" class="Bound">Y</a> <a id="11682" class="Symbol">:</a> <a id="11684" href="UALib.Prelude.Preliminaries.html#11670" class="Bound">X</a> <a id="11686" class="Symbol">→</a> <a id="11688" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11690" href="universes.html#758" class="Function Operator">̇</a><a id="11691" class="Symbol">}</a> <a id="11693" class="Symbol">→</a> <a id="11695" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="11697" href="UALib.Prelude.Preliminaries.html#11680" class="Bound">Y</a> <a id="11699" class="Symbol">→</a> <a id="11701" href="UALib.Prelude.Preliminaries.html#11670" class="Bound">X</a>
  <a id="11705" href="UALib.Prelude.Preliminaries.html#11659" class="Function Operator">∣</a> <a id="11707" href="UALib.Prelude.Preliminaries.html#11707" class="Bound">x</a> <a id="11709" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="11711" href="UALib.Prelude.Preliminaries.html#11711" class="Bound">y</a> <a id="11713" href="UALib.Prelude.Preliminaries.html#11659" class="Function Operator">∣</a> <a id="11715" class="Symbol">=</a> <a id="11717" href="UALib.Prelude.Preliminaries.html#11707" class="Bound">x</a>
  <a id="11721" href="UALib.Prelude.Preliminaries.html#11663" class="Function">fst</a> <a id="11725" class="Symbol">(</a><a id="11726" href="UALib.Prelude.Preliminaries.html#11726" class="Bound">x</a> <a id="11728" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="11730" href="UALib.Prelude.Preliminaries.html#11730" class="Bound">y</a><a id="11731" class="Symbol">)</a> <a id="11733" class="Symbol">=</a> <a id="11735" href="UALib.Prelude.Preliminaries.html#11726" class="Bound">x</a>

  <a id="11740" href="UALib.Prelude.Preliminaries.html#11740" class="Function Operator">∥_∥</a> <a id="11744" href="UALib.Prelude.Preliminaries.html#11744" class="Function">snd</a> <a id="11748" class="Symbol">:</a> <a id="11750" class="Symbol">{</a><a id="11751" href="UALib.Prelude.Preliminaries.html#11751" class="Bound">X</a> <a id="11753" class="Symbol">:</a> <a id="11755" href="UALib.Prelude.Preliminaries.html#11636" class="Bound">𝓤</a> <a id="11757" href="universes.html#758" class="Function Operator">̇</a> <a id="11759" class="Symbol">}{</a><a id="11761" href="UALib.Prelude.Preliminaries.html#11761" class="Bound">Y</a> <a id="11763" class="Symbol">:</a> <a id="11765" href="UALib.Prelude.Preliminaries.html#11751" class="Bound">X</a> <a id="11767" class="Symbol">→</a> <a id="11769" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11771" href="universes.html#758" class="Function Operator">̇</a> <a id="11773" class="Symbol">}</a> <a id="11775" class="Symbol">→</a> <a id="11777" class="Symbol">(</a><a id="11778" href="UALib.Prelude.Preliminaries.html#11778" class="Bound">z</a> <a id="11780" class="Symbol">:</a> <a id="11782" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="11784" href="UALib.Prelude.Preliminaries.html#11761" class="Bound">Y</a><a id="11785" class="Symbol">)</a> <a id="11787" class="Symbol">→</a> <a id="11789" href="UALib.Prelude.Preliminaries.html#11761" class="Bound">Y</a> <a id="11791" class="Symbol">(</a><a id="11792" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="11796" href="UALib.Prelude.Preliminaries.html#11778" class="Bound">z</a><a id="11797" class="Symbol">)</a>
  <a id="11801" href="UALib.Prelude.Preliminaries.html#11740" class="Function Operator">∥</a> <a id="11803" href="UALib.Prelude.Preliminaries.html#11803" class="Bound">x</a> <a id="11805" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="11807" href="UALib.Prelude.Preliminaries.html#11807" class="Bound">y</a> <a id="11809" href="UALib.Prelude.Preliminaries.html#11740" class="Function Operator">∥</a> <a id="11811" class="Symbol">=</a> <a id="11813" href="UALib.Prelude.Preliminaries.html#11807" class="Bound">y</a>
  <a id="11817" href="UALib.Prelude.Preliminaries.html#11744" class="Function">snd</a> <a id="11821" class="Symbol">(</a><a id="11822" href="UALib.Prelude.Preliminaries.html#11822" class="Bound">x</a> <a id="11824" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a> <a id="11826" href="UALib.Prelude.Preliminaries.html#11826" class="Bound">y</a><a id="11827" class="Symbol">)</a> <a id="11829" class="Symbol">=</a> <a id="11831" href="UALib.Prelude.Preliminaries.html#11826" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

```agda

Π : {𝓤 𝓦 : Universe}{X : 𝓤 ̇ } (A : X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓦 ̇
Π {𝓤} {𝓦} {X} A = (x : X) → A x

-Π : {𝓤 𝓦 : Universe}(X : 𝓤 ̇ )(Y : X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓦 ̇
-Π X Y = Π Y

infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b
```


**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



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

<span class="footnote"><sup>2</sup>As [MHE][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

----------------------------------------

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

