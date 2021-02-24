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

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.





#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martin Escardo][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.

Here is a list of all the types we use.

**Backward compatibility notice**: We are no longer adding the keyword `public` to the end of the import lines below.  This is to force us to (re)import these definitions and types where and when we need them.  This is sometimes a little bit inconvenient, but it makes the dependencies clearer, and since dependencies reveal the foundations upon which the library is built, it is important that we keep them in the foreground.

<pre class="Agda">

<a id="5900" class="Keyword">open</a> <a id="5905" class="Keyword">import</a> <a id="5912" href="universes.html" class="Module">universes</a> <a id="5922" class="Keyword">public</a>

<a id="5930" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6004" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="6038" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6097" class="Keyword">open</a> <a id="6102" class="Keyword">import</a> <a id="6109" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6118" class="Keyword">using</a> <a id="6124" class="Symbol">(</a><a id="6125" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="6128" class="Symbol">;</a> <a id="6130" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="6136" class="Symbol">;</a> <a id="6138" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="6146" class="Symbol">;</a> <a id="6148" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="6157" class="Symbol">;</a> <a id="6159" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="6165" class="Symbol">;</a> <a id="6167" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="6169" class="Symbol">;</a> <a id="6171" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="6199" href="MGS-MLTT.html#956" class="Function">¬</a><a id="6200" class="Symbol">;</a> <a id="6202" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="6204" class="Symbol">;</a> <a id="6206" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6209" class="Symbol">;</a> <a id="6211" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="6214" class="Symbol">;</a> <a id="6216" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="6217" class="Symbol">;</a> <a id="6219" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="6220" class="Symbol">;</a> <a id="6222" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="6223" class="Symbol">;</a> <a id="6225" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="6228" class="Symbol">;</a> <a id="6230" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="6244" class="Symbol">;</a> <a id="6246" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="6260" class="Symbol">;</a> <a id="6262" href="MGS-MLTT.html#3744" class="Function">id</a><a id="6264" class="Symbol">;</a> <a id="6266" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="6269" class="Symbol">;</a> <a id="6271" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="6273" class="Symbol">)</a>

<a id="6276" class="Keyword">open</a> <a id="6281" class="Keyword">import</a> <a id="6288" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="6305" class="Keyword">using</a> <a id="6311" class="Symbol">(</a><a id="6312" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="6320" class="Symbol">;</a> <a id="6322" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="6329" class="Symbol">;</a> <a id="6331" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="6341" class="Symbol">)</a>

<a id="6344" class="Keyword">open</a> <a id="6349" class="Keyword">import</a> <a id="6356" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="6382" class="Keyword">using</a> <a id="6388" class="Symbol">(</a><a id="6389" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="6395" class="Symbol">;</a> <a id="6397" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="6411" class="Symbol">;</a> <a id="6413" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6420" class="Symbol">;</a>
 <a id="6423" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="6435" class="Symbol">;</a> <a id="6437" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6452" class="Symbol">;</a> <a id="6454" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6461" class="Symbol">;</a> <a id="6463" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6473" class="Symbol">;</a> <a id="6475" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6489" class="Symbol">;</a>
 <a id="6492" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6523" class="Symbol">;</a> <a id="6525" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6528" class="Symbol">;</a> <a id="6530" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6533" class="Symbol">;</a> <a id="6535" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6552" class="Symbol">;</a> <a id="6554" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6571" class="Symbol">;</a>
 <a id="6574" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6623" class="Symbol">)</a>

<a id="6626" class="Keyword">open</a> <a id="6631" class="Keyword">import</a> <a id="6638" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6651" class="Keyword">renaming</a> <a id="6660" class="Symbol">(</a><a id="6661" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6665" class="Symbol">to</a> <a id="_∈_"></a><a id="6668" href="Prelude.Preliminaries.html#6668" class="Function Operator">_∈₀_</a><a id="6672" class="Symbol">;</a> <a id="6674" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6678" class="Symbol">to</a> <a id="_⊆_"></a><a id="6681" href="Prelude.Preliminaries.html#6681" class="Function Operator">_⊆₀_</a><a id="6685" class="Symbol">;</a> <a id="6687" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6705" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6708" href="Prelude.Preliminaries.html#6708" class="Function">∈₀-is-subsingleton</a><a id="6726" class="Symbol">)</a>
 <a id="6729" class="Keyword">using</a> <a id="6735" class="Symbol">(</a><a id="6736" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6737" class="Symbol">;</a> <a id="6739" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6760" class="Symbol">;</a> <a id="6762" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6781" class="Symbol">;</a> <a id="6783" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6805" class="Symbol">;</a> <a id="6807" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6814" class="Symbol">;</a> <a id="6816" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6822" class="Symbol">;</a> <a id="6824" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6825" class="Symbol">)</a>

<a id="6828" class="Keyword">open</a> <a id="6833" class="Keyword">import</a> <a id="6840" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6855" class="Keyword">using</a> <a id="6861" class="Symbol">(</a><a id="6862" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6865" class="Symbol">;</a> <a id="6867" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6871" class="Symbol">;</a> <a id="6873" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6890" class="Symbol">;</a> <a id="6892" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6904" class="Symbol">;</a> <a id="6906" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6919" class="Symbol">;</a> <a id="6921" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6932" class="Symbol">;</a>
 <a id="6935" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6941" class="Symbol">;</a> <a id="6943" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6946" class="Symbol">;</a> <a id="6948" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6975" class="Symbol">;</a> <a id="6977" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="6994" class="Symbol">;</a> <a id="6996" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7013" class="Symbol">;</a> <a id="7015" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7030" class="Symbol">)</a>

<a id="7033" class="Keyword">open</a> <a id="7038" class="Keyword">import</a> <a id="7045" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7066" class="Keyword">using</a> <a id="7072" class="Symbol">(</a><a id="7073" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7085" class="Symbol">)</a>

<a id="7088" class="Keyword">open</a> <a id="7093" class="Keyword">import</a> <a id="7100" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="7121" class="Keyword">using</a> <a id="7127" class="Symbol">(</a><a id="7128" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="7130" class="Symbol">;</a> <a id="7132" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="7135" class="Symbol">)</a>

<a id="7138" class="Keyword">open</a> <a id="7143" class="Keyword">import</a> <a id="7150" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="7178" class="Keyword">using</a> <a id="7184" class="Symbol">(</a><a id="7185" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="7188" class="Symbol">;</a> <a id="7190" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="7196" class="Symbol">;</a> <a id="7198" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="7219" class="Symbol">;</a>
 <a id="7222" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="7244" class="Symbol">;</a> <a id="7246" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="7251" class="Symbol">;</a> <a id="7253" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="7271" class="Symbol">;</a> <a id="7273" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="7280" class="Symbol">)</a>

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

<a id="10834" class="Keyword">module</a> <a id="hide-sigma"></a><a id="10841" href="Prelude.Preliminaries.html#10841" class="Module">hide-sigma</a> <a id="10852" class="Keyword">where</a>

 <a id="10860" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="10867" href="Prelude.Preliminaries.html#10867" class="Record">Σ</a> <a id="10869" class="Symbol">{</a><a id="10870" href="Prelude.Preliminaries.html#10870" class="Bound">𝓤</a> <a id="10872" href="Prelude.Preliminaries.html#10872" class="Bound">𝓥</a><a id="10873" class="Symbol">}</a> <a id="10875" class="Symbol">{</a><a id="10876" href="Prelude.Preliminaries.html#10876" class="Bound">X</a> <a id="10878" class="Symbol">:</a> <a id="10880" href="Prelude.Preliminaries.html#10870" class="Bound">𝓤</a> <a id="10882" href="universes.html#758" class="Function Operator">̇</a> <a id="10884" class="Symbol">}</a> <a id="10886" class="Symbol">(</a><a id="10887" href="Prelude.Preliminaries.html#10887" class="Bound">Y</a> <a id="10889" class="Symbol">:</a> <a id="10891" href="Prelude.Preliminaries.html#10876" class="Bound">X</a> <a id="10893" class="Symbol">→</a> <a id="10895" href="Prelude.Preliminaries.html#10872" class="Bound">𝓥</a> <a id="10897" href="universes.html#758" class="Function Operator">̇</a> <a id="10899" class="Symbol">)</a> <a id="10901" class="Symbol">:</a> <a id="10903" href="Prelude.Preliminaries.html#10870" class="Bound">𝓤</a> <a id="10905" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10907" href="Prelude.Preliminaries.html#10872" class="Bound">𝓥</a> <a id="10909" href="universes.html#758" class="Function Operator">̇</a>  <a id="10912" class="Keyword">where</a>
  <a id="10920" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="10932" href="Prelude.Preliminaries.html#10932" class="InductiveConstructor Operator">_,_</a>
  <a id="10938" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="10947" href="Prelude.Preliminaries.html#10947" class="Field">pr₁</a> <a id="10951" class="Symbol">:</a> <a id="10953" href="Prelude.Preliminaries.html#10876" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="10958" href="Prelude.Preliminaries.html#10958" class="Field">pr₂</a> <a id="10962" class="Symbol">:</a> <a id="10964" href="Prelude.Preliminaries.html#10887" class="Bound">Y</a> <a id="10966" href="Prelude.Preliminaries.html#10947" class="Field">pr₁</a>

 <a id="10972" class="Keyword">infixr</a> <a id="10979" class="Number">50</a> <a id="10982" href="Prelude.Preliminaries.html#10932" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="11319" href="Prelude.Preliminaries.html#11319" class="Function">-Σ</a> <a id="11322" class="Symbol">:</a> <a id="11324" class="Symbol">{</a><a id="11325" href="Prelude.Preliminaries.html#11325" class="Bound">𝓤</a> <a id="11327" href="Prelude.Preliminaries.html#11327" class="Bound">𝓥</a> <a id="11329" class="Symbol">:</a> <a id="11331" href="universes.html#551" class="Postulate">Universe</a><a id="11339" class="Symbol">}</a> <a id="11341" class="Symbol">(</a><a id="11342" href="Prelude.Preliminaries.html#11342" class="Bound">X</a> <a id="11344" class="Symbol">:</a> <a id="11346" href="Prelude.Preliminaries.html#11325" class="Bound">𝓤</a> <a id="11348" href="universes.html#758" class="Function Operator">̇</a> <a id="11350" class="Symbol">)</a> <a id="11352" class="Symbol">(</a><a id="11353" href="Prelude.Preliminaries.html#11353" class="Bound">Y</a> <a id="11355" class="Symbol">:</a> <a id="11357" href="Prelude.Preliminaries.html#11342" class="Bound">X</a> <a id="11359" class="Symbol">→</a> <a id="11361" href="Prelude.Preliminaries.html#11327" class="Bound">𝓥</a> <a id="11363" href="universes.html#758" class="Function Operator">̇</a> <a id="11365" class="Symbol">)</a> <a id="11367" class="Symbol">→</a> <a id="11369" href="Prelude.Preliminaries.html#11325" class="Bound">𝓤</a> <a id="11371" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11373" href="Prelude.Preliminaries.html#11327" class="Bound">𝓥</a> <a id="11375" href="universes.html#758" class="Function Operator">̇</a>
 <a id="11378" href="Prelude.Preliminaries.html#11319" class="Function">-Σ</a> <a id="11381" href="Prelude.Preliminaries.html#11381" class="Bound">X</a> <a id="11383" href="Prelude.Preliminaries.html#11383" class="Bound">Y</a> <a id="11385" class="Symbol">=</a> <a id="11387" href="Prelude.Preliminaries.html#10867" class="Record">Σ</a> <a id="11389" href="Prelude.Preliminaries.html#11383" class="Bound">Y</a>

 <a id="11393" class="Keyword">syntax</a> <a id="11400" href="Prelude.Preliminaries.html#11319" class="Function">-Σ</a> <a id="11403" class="Bound">X</a> <a id="11405" class="Symbol">(λ</a> <a id="11408" class="Bound">x</a> <a id="11410" class="Symbol">→</a> <a id="11412" class="Bound">Y</a><a id="11413" class="Symbol">)</a> <a id="11415" class="Symbol">=</a> <a id="11417" class="Function">Σ</a> <a id="11419" class="Bound">x</a> <a id="11421" class="Function">꞉</a> <a id="11423" class="Bound">X</a> <a id="11425" class="Function">,</a> <a id="11427" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="11800" href="Prelude.Preliminaries.html#11800" class="Function Operator">_×_</a> <a id="11804" class="Symbol">:</a> <a id="11806" href="universes.html#615" class="Generalizable">𝓤</a> <a id="11808" href="universes.html#758" class="Function Operator">̇</a> <a id="11810" class="Symbol">→</a> <a id="11812" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11814" href="universes.html#758" class="Function Operator">̇</a> <a id="11816" class="Symbol">→</a> <a id="11818" href="universes.html#615" class="Generalizable">𝓤</a> <a id="11820" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11822" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11824" href="universes.html#758" class="Function Operator">̇</a>
 <a id="11827" href="Prelude.Preliminaries.html#11827" class="Bound">X</a> <a id="11829" href="Prelude.Preliminaries.html#11800" class="Function Operator">×</a> <a id="11831" href="Prelude.Preliminaries.html#11831" class="Bound">Y</a> <a id="11833" class="Symbol">=</a> <a id="11835" href="Prelude.Preliminaries.html#11319" class="Function">Σ</a> <a id="11837" href="Prelude.Preliminaries.html#11837" class="Bound">x</a> <a id="11839" href="Prelude.Preliminaries.html#11319" class="Function">꞉</a> <a id="11841" href="Prelude.Preliminaries.html#11827" class="Bound">X</a> <a id="11843" href="Prelude.Preliminaries.html#11319" class="Function">,</a> <a id="11845" href="Prelude.Preliminaries.html#11831" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="12055" class="Keyword">open</a> <a id="12060" class="Keyword">import</a> <a id="12067" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12078" class="Keyword">renaming</a> <a id="12087" class="Symbol">(</a><a id="12088" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="12092" class="Symbol">to</a> <a id="12095" class="Keyword">infixr</a> <a id="12102" class="Number">50</a> <a id="_,_"></a><a id="12105" href="Prelude.Preliminaries.html#12105" class="InductiveConstructor Operator">_,_</a><a id="12108" class="Symbol">)</a>
<a id="12110" class="Keyword">open</a> <a id="12115" class="Keyword">import</a> <a id="12122" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="12131" class="Keyword">using</a> <a id="12137" class="Symbol">(</a><a id="12138" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="12141" class="Symbol">;</a> <a id="12143" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="12146" class="Symbol">;</a> <a id="12148" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="12151" class="Symbol">;</a> <a id="12153" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="12155" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="12590" class="Keyword">module</a> <a id="12597" href="Prelude.Preliminaries.html#12597" class="Module">_</a> <a id="12599" class="Symbol">{</a><a id="12600" href="Prelude.Preliminaries.html#12600" class="Bound">𝓤</a> <a id="12602" class="Symbol">:</a> <a id="12604" href="universes.html#551" class="Postulate">Universe</a><a id="12612" class="Symbol">}</a> <a id="12614" class="Keyword">where</a>

 <a id="12622" href="Prelude.Preliminaries.html#12622" class="Function Operator">∣_∣</a> <a id="12626" href="Prelude.Preliminaries.html#12626" class="Function">fst</a> <a id="12630" class="Symbol">:</a> <a id="12632" class="Symbol">{</a><a id="12633" href="Prelude.Preliminaries.html#12633" class="Bound">X</a> <a id="12635" class="Symbol">:</a> <a id="12637" href="Prelude.Preliminaries.html#12600" class="Bound">𝓤</a> <a id="12639" href="universes.html#758" class="Function Operator">̇</a> <a id="12641" class="Symbol">}{</a><a id="12643" href="Prelude.Preliminaries.html#12643" class="Bound">Y</a> <a id="12645" class="Symbol">:</a> <a id="12647" href="Prelude.Preliminaries.html#12633" class="Bound">X</a> <a id="12649" class="Symbol">→</a> <a id="12651" href="universes.html#617" class="Generalizable">𝓥</a> <a id="12653" href="universes.html#758" class="Function Operator">̇</a><a id="12654" class="Symbol">}</a> <a id="12656" class="Symbol">→</a> <a id="12658" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12660" href="Prelude.Preliminaries.html#12643" class="Bound">Y</a> <a id="12662" class="Symbol">→</a> <a id="12664" href="Prelude.Preliminaries.html#12633" class="Bound">X</a>
 <a id="12667" href="Prelude.Preliminaries.html#12622" class="Function Operator">∣</a> <a id="12669" href="Prelude.Preliminaries.html#12669" class="Bound">x</a> <a id="12671" href="Prelude.Preliminaries.html#12105" class="InductiveConstructor Operator">,</a> <a id="12673" href="Prelude.Preliminaries.html#12673" class="Bound">y</a> <a id="12675" href="Prelude.Preliminaries.html#12622" class="Function Operator">∣</a> <a id="12677" class="Symbol">=</a> <a id="12679" href="Prelude.Preliminaries.html#12669" class="Bound">x</a>
 <a id="12682" href="Prelude.Preliminaries.html#12626" class="Function">fst</a> <a id="12686" class="Symbol">(</a><a id="12687" href="Prelude.Preliminaries.html#12687" class="Bound">x</a> <a id="12689" href="Prelude.Preliminaries.html#12105" class="InductiveConstructor Operator">,</a> <a id="12691" href="Prelude.Preliminaries.html#12691" class="Bound">y</a><a id="12692" class="Symbol">)</a> <a id="12694" class="Symbol">=</a> <a id="12696" href="Prelude.Preliminaries.html#12687" class="Bound">x</a>

 <a id="12700" href="Prelude.Preliminaries.html#12700" class="Function Operator">∥_∥</a> <a id="12704" href="Prelude.Preliminaries.html#12704" class="Function">snd</a> <a id="12708" class="Symbol">:</a> <a id="12710" class="Symbol">{</a><a id="12711" href="Prelude.Preliminaries.html#12711" class="Bound">X</a> <a id="12713" class="Symbol">:</a> <a id="12715" href="Prelude.Preliminaries.html#12600" class="Bound">𝓤</a> <a id="12717" href="universes.html#758" class="Function Operator">̇</a> <a id="12719" class="Symbol">}{</a><a id="12721" href="Prelude.Preliminaries.html#12721" class="Bound">Y</a> <a id="12723" class="Symbol">:</a> <a id="12725" href="Prelude.Preliminaries.html#12711" class="Bound">X</a> <a id="12727" class="Symbol">→</a> <a id="12729" href="universes.html#617" class="Generalizable">𝓥</a> <a id="12731" href="universes.html#758" class="Function Operator">̇</a> <a id="12733" class="Symbol">}</a> <a id="12735" class="Symbol">→</a> <a id="12737" class="Symbol">(</a><a id="12738" href="Prelude.Preliminaries.html#12738" class="Bound">z</a> <a id="12740" class="Symbol">:</a> <a id="12742" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12744" href="Prelude.Preliminaries.html#12721" class="Bound">Y</a><a id="12745" class="Symbol">)</a> <a id="12747" class="Symbol">→</a> <a id="12749" href="Prelude.Preliminaries.html#12721" class="Bound">Y</a> <a id="12751" class="Symbol">(</a><a id="12752" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12756" href="Prelude.Preliminaries.html#12738" class="Bound">z</a><a id="12757" class="Symbol">)</a>
 <a id="12760" href="Prelude.Preliminaries.html#12700" class="Function Operator">∥</a> <a id="12762" href="Prelude.Preliminaries.html#12762" class="Bound">x</a> <a id="12764" href="Prelude.Preliminaries.html#12105" class="InductiveConstructor Operator">,</a> <a id="12766" href="Prelude.Preliminaries.html#12766" class="Bound">y</a> <a id="12768" href="Prelude.Preliminaries.html#12700" class="Function Operator">∥</a> <a id="12770" class="Symbol">=</a> <a id="12772" href="Prelude.Preliminaries.html#12766" class="Bound">y</a>
 <a id="12775" href="Prelude.Preliminaries.html#12704" class="Function">snd</a> <a id="12779" class="Symbol">(</a><a id="12780" href="Prelude.Preliminaries.html#12780" class="Bound">x</a> <a id="12782" href="Prelude.Preliminaries.html#12105" class="InductiveConstructor Operator">,</a> <a id="12784" href="Prelude.Preliminaries.html#12784" class="Bound">y</a><a id="12785" class="Symbol">)</a> <a id="12787" class="Symbol">=</a> <a id="12789" href="Prelude.Preliminaries.html#12784" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="13058" class="Keyword">module</a> <a id="hide-pi"></a><a id="13065" href="Prelude.Preliminaries.html#13065" class="Module">hide-pi</a> <a id="13073" class="Symbol">{</a><a id="13074" href="Prelude.Preliminaries.html#13074" class="Bound">𝓤</a> <a id="13076" href="Prelude.Preliminaries.html#13076" class="Bound">𝓦</a> <a id="13078" class="Symbol">:</a> <a id="13080" href="universes.html#551" class="Postulate">Universe</a><a id="13088" class="Symbol">}</a> <a id="13090" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="13098" href="Prelude.Preliminaries.html#13098" class="Function">Π</a> <a id="13100" class="Symbol">:</a> <a id="13102" class="Symbol">{</a><a id="13103" href="Prelude.Preliminaries.html#13103" class="Bound">X</a> <a id="13105" class="Symbol">:</a> <a id="13107" href="Prelude.Preliminaries.html#13074" class="Bound">𝓤</a> <a id="13109" href="universes.html#758" class="Function Operator">̇</a> <a id="13111" class="Symbol">}</a> <a id="13113" class="Symbol">(</a><a id="13114" href="Prelude.Preliminaries.html#13114" class="Bound">A</a> <a id="13116" class="Symbol">:</a> <a id="13118" href="Prelude.Preliminaries.html#13103" class="Bound">X</a> <a id="13120" class="Symbol">→</a> <a id="13122" href="Prelude.Preliminaries.html#13076" class="Bound">𝓦</a> <a id="13124" href="universes.html#758" class="Function Operator">̇</a> <a id="13126" class="Symbol">)</a> <a id="13128" class="Symbol">→</a> <a id="13130" href="Prelude.Preliminaries.html#13074" class="Bound">𝓤</a> <a id="13132" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13134" href="Prelude.Preliminaries.html#13076" class="Bound">𝓦</a> <a id="13136" href="universes.html#758" class="Function Operator">̇</a>
 <a id="13139" href="Prelude.Preliminaries.html#13098" class="Function">Π</a> <a id="13141" class="Symbol">{</a><a id="13142" href="Prelude.Preliminaries.html#13142" class="Bound">X</a><a id="13143" class="Symbol">}</a> <a id="13145" href="Prelude.Preliminaries.html#13145" class="Bound">A</a> <a id="13147" class="Symbol">=</a> <a id="13149" class="Symbol">(</a><a id="13150" href="Prelude.Preliminaries.html#13150" class="Bound">x</a> <a id="13152" class="Symbol">:</a> <a id="13154" href="Prelude.Preliminaries.html#13142" class="Bound">X</a><a id="13155" class="Symbol">)</a> <a id="13157" class="Symbol">→</a> <a id="13159" href="Prelude.Preliminaries.html#13145" class="Bound">A</a> <a id="13161" href="Prelude.Preliminaries.html#13150" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="13165" href="Prelude.Preliminaries.html#13165" class="Function">-Π</a> <a id="13168" class="Symbol">:</a> <a id="13170" class="Symbol">(</a><a id="13171" href="Prelude.Preliminaries.html#13171" class="Bound">X</a> <a id="13173" class="Symbol">:</a> <a id="13175" href="Prelude.Preliminaries.html#13074" class="Bound">𝓤</a> <a id="13177" href="universes.html#758" class="Function Operator">̇</a> <a id="13179" class="Symbol">)(</a><a id="13181" href="Prelude.Preliminaries.html#13181" class="Bound">Y</a> <a id="13183" class="Symbol">:</a> <a id="13185" href="Prelude.Preliminaries.html#13171" class="Bound">X</a> <a id="13187" class="Symbol">→</a> <a id="13189" href="Prelude.Preliminaries.html#13076" class="Bound">𝓦</a> <a id="13191" href="universes.html#758" class="Function Operator">̇</a> <a id="13193" class="Symbol">)</a> <a id="13195" class="Symbol">→</a> <a id="13197" href="Prelude.Preliminaries.html#13074" class="Bound">𝓤</a> <a id="13199" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13201" href="Prelude.Preliminaries.html#13076" class="Bound">𝓦</a> <a id="13203" href="universes.html#758" class="Function Operator">̇</a>
 <a id="13206" href="Prelude.Preliminaries.html#13165" class="Function">-Π</a> <a id="13209" href="Prelude.Preliminaries.html#13209" class="Bound">X</a> <a id="13211" href="Prelude.Preliminaries.html#13211" class="Bound">Y</a> <a id="13213" class="Symbol">=</a> <a id="13215" href="Prelude.Preliminaries.html#13098" class="Function">Π</a> <a id="13217" href="Prelude.Preliminaries.html#13211" class="Bound">Y</a>

 <a id="13221" class="Keyword">infixr</a> <a id="13228" class="Number">-1</a> <a id="13231" href="Prelude.Preliminaries.html#13165" class="Function">-Π</a>
 <a id="13235" class="Keyword">syntax</a> <a id="13242" href="Prelude.Preliminaries.html#13165" class="Function">-Π</a> <a id="13245" class="Bound">A</a> <a id="13247" class="Symbol">(λ</a> <a id="13250" class="Bound">x</a> <a id="13252" class="Symbol">→</a> <a id="13254" class="Bound">b</a><a id="13255" class="Symbol">)</a> <a id="13257" class="Symbol">=</a> <a id="13259" class="Function">Π</a> <a id="13261" class="Bound">x</a> <a id="13263" class="Function">꞉</a> <a id="13265" class="Bound">A</a> <a id="13267" class="Function">,</a> <a id="13269" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].




----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}

