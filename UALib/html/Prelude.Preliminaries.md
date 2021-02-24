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

<a id="3098" class="Keyword">module</a> <a id="3105" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="3127" class="Keyword">where</a>

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

<a id="5916" class="Keyword">open</a> <a id="5921" class="Keyword">import</a> <a id="5928" href="universes.html" class="Module">universes</a> <a id="5938" class="Keyword">public</a>

<a id="5946" class="Comment">-- open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)</a>
<a id="6020" class="Comment">-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}</a>

<a id="6054" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="6113" class="Keyword">open</a> <a id="6118" class="Keyword">import</a> <a id="6125" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6134" class="Keyword">using</a> <a id="6140" class="Symbol">(</a><a id="6141" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="6144" class="Symbol">;</a> <a id="6146" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="6152" class="Symbol">;</a> <a id="6154" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="6162" class="Symbol">;</a> <a id="6164" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="6173" class="Symbol">;</a> <a id="6175" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="6181" class="Symbol">;</a> <a id="6183" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="6185" class="Symbol">;</a> <a id="6187" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="6215" href="MGS-MLTT.html#956" class="Function">¬</a><a id="6216" class="Symbol">;</a> <a id="6218" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="6220" class="Symbol">;</a> <a id="6222" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6225" class="Symbol">;</a> <a id="6227" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="6230" class="Symbol">;</a> <a id="6232" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="6233" class="Symbol">;</a> <a id="6235" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="6236" class="Symbol">;</a> <a id="6238" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="6239" class="Symbol">;</a> <a id="6241" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="6244" class="Symbol">;</a> <a id="6246" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="6260" class="Symbol">;</a> <a id="6262" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="6276" class="Symbol">;</a> <a id="6278" href="MGS-MLTT.html#3744" class="Function">id</a><a id="6280" class="Symbol">;</a> <a id="6282" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="6285" class="Symbol">;</a> <a id="6287" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="6289" class="Symbol">)</a>

<a id="6292" class="Keyword">open</a> <a id="6297" class="Keyword">import</a> <a id="6304" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="6321" class="Keyword">using</a> <a id="6327" class="Symbol">(</a><a id="6328" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="6336" class="Symbol">;</a> <a id="6338" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="6345" class="Symbol">;</a> <a id="6347" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="6357" class="Symbol">)</a>

<a id="6360" class="Keyword">open</a> <a id="6365" class="Keyword">import</a> <a id="6372" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="6398" class="Keyword">using</a> <a id="6404" class="Symbol">(</a><a id="6405" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="6411" class="Symbol">;</a> <a id="6413" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="6427" class="Symbol">;</a> <a id="6429" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6436" class="Symbol">;</a>
 <a id="6439" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="6451" class="Symbol">;</a> <a id="6453" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6468" class="Symbol">;</a> <a id="6470" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6477" class="Symbol">;</a> <a id="6479" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6489" class="Symbol">;</a> <a id="6491" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6505" class="Symbol">;</a>
 <a id="6508" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6539" class="Symbol">;</a> <a id="6541" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6544" class="Symbol">;</a> <a id="6546" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6549" class="Symbol">;</a> <a id="6551" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6568" class="Symbol">;</a> <a id="6570" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6587" class="Symbol">;</a>
 <a id="6590" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6639" class="Symbol">)</a>

<a id="6642" class="Keyword">open</a> <a id="6647" class="Keyword">import</a> <a id="6654" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6667" class="Keyword">renaming</a> <a id="6676" class="Symbol">(</a><a id="6677" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6681" class="Symbol">to</a> <a id="_∈_"></a><a id="6684" href="Prelude.Preliminaries.html#6684" class="Function Operator">_∈₀_</a><a id="6688" class="Symbol">;</a> <a id="6690" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6694" class="Symbol">to</a> <a id="_⊆_"></a><a id="6697" href="Prelude.Preliminaries.html#6697" class="Function Operator">_⊆₀_</a><a id="6701" class="Symbol">;</a> <a id="6703" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6721" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6724" href="Prelude.Preliminaries.html#6724" class="Function">∈₀-is-subsingleton</a><a id="6742" class="Symbol">)</a>
 <a id="6745" class="Keyword">using</a> <a id="6751" class="Symbol">(</a><a id="6752" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6753" class="Symbol">;</a> <a id="6755" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6776" class="Symbol">;</a> <a id="6778" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6797" class="Symbol">;</a> <a id="6799" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6821" class="Symbol">;</a> <a id="6823" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6830" class="Symbol">;</a> <a id="6832" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6838" class="Symbol">;</a> <a id="6840" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6841" class="Symbol">)</a>

<a id="6844" class="Keyword">open</a> <a id="6849" class="Keyword">import</a> <a id="6856" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6871" class="Keyword">using</a> <a id="6877" class="Symbol">(</a><a id="6878" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6881" class="Symbol">;</a> <a id="6883" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6887" class="Symbol">;</a> <a id="6889" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6906" class="Symbol">;</a> <a id="6908" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6920" class="Symbol">;</a> <a id="6922" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6935" class="Symbol">;</a> <a id="6937" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6948" class="Symbol">;</a>
 <a id="6951" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6957" class="Symbol">;</a> <a id="6959" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6962" class="Symbol">;</a> <a id="6964" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6991" class="Symbol">;</a> <a id="6993" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="7010" class="Symbol">;</a> <a id="7012" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="7029" class="Symbol">;</a> <a id="7031" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="7046" class="Symbol">)</a>

<a id="7049" class="Keyword">open</a> <a id="7054" class="Keyword">import</a> <a id="7061" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="7082" class="Keyword">using</a> <a id="7088" class="Symbol">(</a><a id="7089" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="7101" class="Symbol">)</a>

<a id="7104" class="Keyword">open</a> <a id="7109" class="Keyword">import</a> <a id="7116" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="7137" class="Keyword">using</a> <a id="7143" class="Symbol">(</a><a id="7144" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="7146" class="Symbol">;</a> <a id="7148" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="7151" class="Symbol">)</a>

<a id="7154" class="Keyword">open</a> <a id="7159" class="Keyword">import</a> <a id="7166" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="7194" class="Keyword">using</a> <a id="7200" class="Symbol">(</a><a id="7201" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="7204" class="Symbol">;</a> <a id="7206" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="7212" class="Symbol">;</a> <a id="7214" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="7235" class="Symbol">;</a>
 <a id="7238" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="7260" class="Symbol">;</a> <a id="7262" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="7267" class="Symbol">;</a> <a id="7269" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="7287" class="Symbol">;</a> <a id="7289" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="7296" class="Symbol">)</a>

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

Given universes 𝓤 and 𝓥, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the **Sigma type** (or **dependent pair type**), denoted by `Σ(x ꞉ X), Y x`, generalizes the Cartesian product `X × Y` by allowing the type `Y x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, `Σ(x ꞉ X), Y x` is inhabited by the pairs `(x , y)` such that `x : X` and `y : Y x`.

In the [Type Topology][] library, the dependent pair type is defined in a stardard way (cf. the [Agda Standard Library][]) as a record type.

<pre class="Agda">

<a id="10846" class="Keyword">module</a> <a id="hide-sigma"></a><a id="10853" href="Prelude.Preliminaries.html#10853" class="Module">hide-sigma</a> <a id="10864" class="Keyword">where</a>

 <a id="10872" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="10879" href="Prelude.Preliminaries.html#10879" class="Record">Σ</a> <a id="10881" class="Symbol">{</a><a id="10882" href="Prelude.Preliminaries.html#10882" class="Bound">𝓤</a> <a id="10884" href="Prelude.Preliminaries.html#10884" class="Bound">𝓥</a><a id="10885" class="Symbol">}</a> <a id="10887" class="Symbol">{</a><a id="10888" href="Prelude.Preliminaries.html#10888" class="Bound">X</a> <a id="10890" class="Symbol">:</a> <a id="10892" href="Prelude.Preliminaries.html#10882" class="Bound">𝓤</a> <a id="10894" href="universes.html#758" class="Function Operator">̇</a> <a id="10896" class="Symbol">}</a> <a id="10898" class="Symbol">(</a><a id="10899" href="Prelude.Preliminaries.html#10899" class="Bound">Y</a> <a id="10901" class="Symbol">:</a> <a id="10903" href="Prelude.Preliminaries.html#10888" class="Bound">X</a> <a id="10905" class="Symbol">→</a> <a id="10907" href="Prelude.Preliminaries.html#10884" class="Bound">𝓥</a> <a id="10909" href="universes.html#758" class="Function Operator">̇</a> <a id="10911" class="Symbol">)</a> <a id="10913" class="Symbol">:</a> <a id="10915" href="Prelude.Preliminaries.html#10882" class="Bound">𝓤</a> <a id="10917" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10919" href="Prelude.Preliminaries.html#10884" class="Bound">𝓥</a> <a id="10921" href="universes.html#758" class="Function Operator">̇</a>  <a id="10924" class="Keyword">where</a>
  <a id="10932" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="10944" href="Prelude.Preliminaries.html#10944" class="InductiveConstructor Operator">_,_</a>
  <a id="10950" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="10959" href="Prelude.Preliminaries.html#10959" class="Field">pr₁</a> <a id="10963" class="Symbol">:</a> <a id="10965" href="Prelude.Preliminaries.html#10888" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="10970" href="Prelude.Preliminaries.html#10970" class="Field">pr₂</a> <a id="10974" class="Symbol">:</a> <a id="10976" href="Prelude.Preliminaries.html#10899" class="Bound">Y</a> <a id="10978" href="Prelude.Preliminaries.html#10959" class="Field">pr₁</a>

 <a id="10984" class="Keyword">infixr</a> <a id="10991" class="Number">50</a> <a id="10994" href="Prelude.Preliminaries.html#10944" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`).  Escardó makes this preferred notation available in the [TypeTopology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="11331" href="Prelude.Preliminaries.html#11331" class="Function">-Σ</a> <a id="11334" class="Symbol">:</a> <a id="11336" class="Symbol">{</a><a id="11337" href="Prelude.Preliminaries.html#11337" class="Bound">𝓤</a> <a id="11339" href="Prelude.Preliminaries.html#11339" class="Bound">𝓥</a> <a id="11341" class="Symbol">:</a> <a id="11343" href="universes.html#551" class="Postulate">Universe</a><a id="11351" class="Symbol">}</a> <a id="11353" class="Symbol">(</a><a id="11354" href="Prelude.Preliminaries.html#11354" class="Bound">X</a> <a id="11356" class="Symbol">:</a> <a id="11358" href="Prelude.Preliminaries.html#11337" class="Bound">𝓤</a> <a id="11360" href="universes.html#758" class="Function Operator">̇</a> <a id="11362" class="Symbol">)</a> <a id="11364" class="Symbol">(</a><a id="11365" href="Prelude.Preliminaries.html#11365" class="Bound">Y</a> <a id="11367" class="Symbol">:</a> <a id="11369" href="Prelude.Preliminaries.html#11354" class="Bound">X</a> <a id="11371" class="Symbol">→</a> <a id="11373" href="Prelude.Preliminaries.html#11339" class="Bound">𝓥</a> <a id="11375" href="universes.html#758" class="Function Operator">̇</a> <a id="11377" class="Symbol">)</a> <a id="11379" class="Symbol">→</a> <a id="11381" href="Prelude.Preliminaries.html#11337" class="Bound">𝓤</a> <a id="11383" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11385" href="Prelude.Preliminaries.html#11339" class="Bound">𝓥</a> <a id="11387" href="universes.html#758" class="Function Operator">̇</a>
 <a id="11390" href="Prelude.Preliminaries.html#11331" class="Function">-Σ</a> <a id="11393" href="Prelude.Preliminaries.html#11393" class="Bound">X</a> <a id="11395" href="Prelude.Preliminaries.html#11395" class="Bound">Y</a> <a id="11397" class="Symbol">=</a> <a id="11399" href="Prelude.Preliminaries.html#10879" class="Record">Σ</a> <a id="11401" href="Prelude.Preliminaries.html#11395" class="Bound">Y</a>

 <a id="11405" class="Keyword">syntax</a> <a id="11412" href="Prelude.Preliminaries.html#11331" class="Function">-Σ</a> <a id="11415" class="Bound">X</a> <a id="11417" class="Symbol">(λ</a> <a id="11420" class="Bound">x</a> <a id="11422" class="Symbol">→</a> <a id="11424" class="Bound">Y</a><a id="11425" class="Symbol">)</a> <a id="11427" class="Symbol">=</a> <a id="11429" class="Function">Σ</a> <a id="11431" class="Bound">x</a> <a id="11433" class="Function">꞉</a> <a id="11435" class="Bound">X</a> <a id="11437" class="Function">,</a> <a id="11439" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="11812" href="Prelude.Preliminaries.html#11812" class="Function Operator">_×_</a> <a id="11816" class="Symbol">:</a> <a id="11818" href="universes.html#615" class="Generalizable">𝓤</a> <a id="11820" href="universes.html#758" class="Function Operator">̇</a> <a id="11822" class="Symbol">→</a> <a id="11824" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11826" href="universes.html#758" class="Function Operator">̇</a> <a id="11828" class="Symbol">→</a> <a id="11830" href="universes.html#615" class="Generalizable">𝓤</a> <a id="11832" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11834" href="universes.html#617" class="Generalizable">𝓥</a> <a id="11836" href="universes.html#758" class="Function Operator">̇</a>
 <a id="11839" href="Prelude.Preliminaries.html#11839" class="Bound">X</a> <a id="11841" href="Prelude.Preliminaries.html#11812" class="Function Operator">×</a> <a id="11843" href="Prelude.Preliminaries.html#11843" class="Bound">Y</a> <a id="11845" class="Symbol">=</a> <a id="11847" href="Prelude.Preliminaries.html#11331" class="Function">Σ</a> <a id="11849" href="Prelude.Preliminaries.html#11849" class="Bound">x</a> <a id="11851" href="Prelude.Preliminaries.html#11331" class="Function">꞉</a> <a id="11853" href="Prelude.Preliminaries.html#11839" class="Bound">X</a> <a id="11855" href="Prelude.Preliminaries.html#11331" class="Function">,</a> <a id="11857" href="Prelude.Preliminaries.html#11843" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="12067" class="Keyword">open</a> <a id="12072" class="Keyword">import</a> <a id="12079" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="12090" class="Keyword">renaming</a> <a id="12099" class="Symbol">(</a><a id="12100" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="12104" class="Symbol">to</a> <a id="12107" class="Keyword">infixr</a> <a id="12114" class="Number">50</a> <a id="_,_"></a><a id="12117" href="Prelude.Preliminaries.html#12117" class="InductiveConstructor Operator">_,_</a><a id="12120" class="Symbol">)</a>
<a id="12122" class="Keyword">open</a> <a id="12127" class="Keyword">import</a> <a id="12134" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="12143" class="Keyword">using</a> <a id="12149" class="Symbol">(</a><a id="12150" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="12153" class="Symbol">;</a> <a id="12155" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="12158" class="Symbol">;</a> <a id="12160" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="12163" class="Symbol">;</a> <a id="12165" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="12167" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="12602" class="Keyword">module</a> <a id="12609" href="Prelude.Preliminaries.html#12609" class="Module">_</a> <a id="12611" class="Symbol">{</a><a id="12612" href="Prelude.Preliminaries.html#12612" class="Bound">𝓤</a> <a id="12614" class="Symbol">:</a> <a id="12616" href="universes.html#551" class="Postulate">Universe</a><a id="12624" class="Symbol">}</a> <a id="12626" class="Keyword">where</a>

 <a id="12634" href="Prelude.Preliminaries.html#12634" class="Function Operator">∣_∣</a> <a id="12638" href="Prelude.Preliminaries.html#12638" class="Function">fst</a> <a id="12642" class="Symbol">:</a> <a id="12644" class="Symbol">{</a><a id="12645" href="Prelude.Preliminaries.html#12645" class="Bound">X</a> <a id="12647" class="Symbol">:</a> <a id="12649" href="Prelude.Preliminaries.html#12612" class="Bound">𝓤</a> <a id="12651" href="universes.html#758" class="Function Operator">̇</a> <a id="12653" class="Symbol">}{</a><a id="12655" href="Prelude.Preliminaries.html#12655" class="Bound">Y</a> <a id="12657" class="Symbol">:</a> <a id="12659" href="Prelude.Preliminaries.html#12645" class="Bound">X</a> <a id="12661" class="Symbol">→</a> <a id="12663" href="universes.html#617" class="Generalizable">𝓥</a> <a id="12665" href="universes.html#758" class="Function Operator">̇</a><a id="12666" class="Symbol">}</a> <a id="12668" class="Symbol">→</a> <a id="12670" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12672" href="Prelude.Preliminaries.html#12655" class="Bound">Y</a> <a id="12674" class="Symbol">→</a> <a id="12676" href="Prelude.Preliminaries.html#12645" class="Bound">X</a>
 <a id="12679" href="Prelude.Preliminaries.html#12634" class="Function Operator">∣</a> <a id="12681" href="Prelude.Preliminaries.html#12681" class="Bound">x</a> <a id="12683" href="Prelude.Preliminaries.html#12117" class="InductiveConstructor Operator">,</a> <a id="12685" href="Prelude.Preliminaries.html#12685" class="Bound">y</a> <a id="12687" href="Prelude.Preliminaries.html#12634" class="Function Operator">∣</a> <a id="12689" class="Symbol">=</a> <a id="12691" href="Prelude.Preliminaries.html#12681" class="Bound">x</a>
 <a id="12694" href="Prelude.Preliminaries.html#12638" class="Function">fst</a> <a id="12698" class="Symbol">(</a><a id="12699" href="Prelude.Preliminaries.html#12699" class="Bound">x</a> <a id="12701" href="Prelude.Preliminaries.html#12117" class="InductiveConstructor Operator">,</a> <a id="12703" href="Prelude.Preliminaries.html#12703" class="Bound">y</a><a id="12704" class="Symbol">)</a> <a id="12706" class="Symbol">=</a> <a id="12708" href="Prelude.Preliminaries.html#12699" class="Bound">x</a>

 <a id="12712" href="Prelude.Preliminaries.html#12712" class="Function Operator">∥_∥</a> <a id="12716" href="Prelude.Preliminaries.html#12716" class="Function">snd</a> <a id="12720" class="Symbol">:</a> <a id="12722" class="Symbol">{</a><a id="12723" href="Prelude.Preliminaries.html#12723" class="Bound">X</a> <a id="12725" class="Symbol">:</a> <a id="12727" href="Prelude.Preliminaries.html#12612" class="Bound">𝓤</a> <a id="12729" href="universes.html#758" class="Function Operator">̇</a> <a id="12731" class="Symbol">}{</a><a id="12733" href="Prelude.Preliminaries.html#12733" class="Bound">Y</a> <a id="12735" class="Symbol">:</a> <a id="12737" href="Prelude.Preliminaries.html#12723" class="Bound">X</a> <a id="12739" class="Symbol">→</a> <a id="12741" href="universes.html#617" class="Generalizable">𝓥</a> <a id="12743" href="universes.html#758" class="Function Operator">̇</a> <a id="12745" class="Symbol">}</a> <a id="12747" class="Symbol">→</a> <a id="12749" class="Symbol">(</a><a id="12750" href="Prelude.Preliminaries.html#12750" class="Bound">z</a> <a id="12752" class="Symbol">:</a> <a id="12754" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12756" href="Prelude.Preliminaries.html#12733" class="Bound">Y</a><a id="12757" class="Symbol">)</a> <a id="12759" class="Symbol">→</a> <a id="12761" href="Prelude.Preliminaries.html#12733" class="Bound">Y</a> <a id="12763" class="Symbol">(</a><a id="12764" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12768" href="Prelude.Preliminaries.html#12750" class="Bound">z</a><a id="12769" class="Symbol">)</a>
 <a id="12772" href="Prelude.Preliminaries.html#12712" class="Function Operator">∥</a> <a id="12774" href="Prelude.Preliminaries.html#12774" class="Bound">x</a> <a id="12776" href="Prelude.Preliminaries.html#12117" class="InductiveConstructor Operator">,</a> <a id="12778" href="Prelude.Preliminaries.html#12778" class="Bound">y</a> <a id="12780" href="Prelude.Preliminaries.html#12712" class="Function Operator">∥</a> <a id="12782" class="Symbol">=</a> <a id="12784" href="Prelude.Preliminaries.html#12778" class="Bound">y</a>
 <a id="12787" href="Prelude.Preliminaries.html#12716" class="Function">snd</a> <a id="12791" class="Symbol">(</a><a id="12792" href="Prelude.Preliminaries.html#12792" class="Bound">x</a> <a id="12794" href="Prelude.Preliminaries.html#12117" class="InductiveConstructor Operator">,</a> <a id="12796" href="Prelude.Preliminaries.html#12796" class="Bound">y</a><a id="12797" class="Symbol">)</a> <a id="12799" class="Symbol">=</a> <a id="12801" href="Prelude.Preliminaries.html#12796" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="13070" class="Keyword">module</a> <a id="hide-pi"></a><a id="13077" href="Prelude.Preliminaries.html#13077" class="Module">hide-pi</a> <a id="13085" class="Symbol">{</a><a id="13086" href="Prelude.Preliminaries.html#13086" class="Bound">𝓤</a> <a id="13088" href="Prelude.Preliminaries.html#13088" class="Bound">𝓦</a> <a id="13090" class="Symbol">:</a> <a id="13092" href="universes.html#551" class="Postulate">Universe</a><a id="13100" class="Symbol">}</a> <a id="13102" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="13110" href="Prelude.Preliminaries.html#13110" class="Function">Π</a> <a id="13112" class="Symbol">:</a> <a id="13114" class="Symbol">{</a><a id="13115" href="Prelude.Preliminaries.html#13115" class="Bound">X</a> <a id="13117" class="Symbol">:</a> <a id="13119" href="Prelude.Preliminaries.html#13086" class="Bound">𝓤</a> <a id="13121" href="universes.html#758" class="Function Operator">̇</a> <a id="13123" class="Symbol">}</a> <a id="13125" class="Symbol">(</a><a id="13126" href="Prelude.Preliminaries.html#13126" class="Bound">A</a> <a id="13128" class="Symbol">:</a> <a id="13130" href="Prelude.Preliminaries.html#13115" class="Bound">X</a> <a id="13132" class="Symbol">→</a> <a id="13134" href="Prelude.Preliminaries.html#13088" class="Bound">𝓦</a> <a id="13136" href="universes.html#758" class="Function Operator">̇</a> <a id="13138" class="Symbol">)</a> <a id="13140" class="Symbol">→</a> <a id="13142" href="Prelude.Preliminaries.html#13086" class="Bound">𝓤</a> <a id="13144" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13146" href="Prelude.Preliminaries.html#13088" class="Bound">𝓦</a> <a id="13148" href="universes.html#758" class="Function Operator">̇</a>
 <a id="13151" href="Prelude.Preliminaries.html#13110" class="Function">Π</a> <a id="13153" class="Symbol">{</a><a id="13154" href="Prelude.Preliminaries.html#13154" class="Bound">X</a><a id="13155" class="Symbol">}</a> <a id="13157" href="Prelude.Preliminaries.html#13157" class="Bound">A</a> <a id="13159" class="Symbol">=</a> <a id="13161" class="Symbol">(</a><a id="13162" href="Prelude.Preliminaries.html#13162" class="Bound">x</a> <a id="13164" class="Symbol">:</a> <a id="13166" href="Prelude.Preliminaries.html#13154" class="Bound">X</a><a id="13167" class="Symbol">)</a> <a id="13169" class="Symbol">→</a> <a id="13171" href="Prelude.Preliminaries.html#13157" class="Bound">A</a> <a id="13173" href="Prelude.Preliminaries.html#13162" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="13177" href="Prelude.Preliminaries.html#13177" class="Function">-Π</a> <a id="13180" class="Symbol">:</a> <a id="13182" class="Symbol">(</a><a id="13183" href="Prelude.Preliminaries.html#13183" class="Bound">X</a> <a id="13185" class="Symbol">:</a> <a id="13187" href="Prelude.Preliminaries.html#13086" class="Bound">𝓤</a> <a id="13189" href="universes.html#758" class="Function Operator">̇</a> <a id="13191" class="Symbol">)(</a><a id="13193" href="Prelude.Preliminaries.html#13193" class="Bound">Y</a> <a id="13195" class="Symbol">:</a> <a id="13197" href="Prelude.Preliminaries.html#13183" class="Bound">X</a> <a id="13199" class="Symbol">→</a> <a id="13201" href="Prelude.Preliminaries.html#13088" class="Bound">𝓦</a> <a id="13203" href="universes.html#758" class="Function Operator">̇</a> <a id="13205" class="Symbol">)</a> <a id="13207" class="Symbol">→</a> <a id="13209" href="Prelude.Preliminaries.html#13086" class="Bound">𝓤</a> <a id="13211" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="13213" href="Prelude.Preliminaries.html#13088" class="Bound">𝓦</a> <a id="13215" href="universes.html#758" class="Function Operator">̇</a>
 <a id="13218" href="Prelude.Preliminaries.html#13177" class="Function">-Π</a> <a id="13221" href="Prelude.Preliminaries.html#13221" class="Bound">X</a> <a id="13223" href="Prelude.Preliminaries.html#13223" class="Bound">Y</a> <a id="13225" class="Symbol">=</a> <a id="13227" href="Prelude.Preliminaries.html#13110" class="Function">Π</a> <a id="13229" href="Prelude.Preliminaries.html#13223" class="Bound">Y</a>

 <a id="13233" class="Keyword">infixr</a> <a id="13240" class="Number">-1</a> <a id="13243" href="Prelude.Preliminaries.html#13177" class="Function">-Π</a>
 <a id="13247" class="Keyword">syntax</a> <a id="13254" href="Prelude.Preliminaries.html#13177" class="Function">-Π</a> <a id="13257" class="Bound">A</a> <a id="13259" class="Symbol">(λ</a> <a id="13262" class="Bound">x</a> <a id="13264" class="Symbol">→</a> <a id="13266" class="Bound">b</a><a id="13267" class="Symbol">)</a> <a id="13269" class="Symbol">=</a> <a id="13271" class="Function">Π</a> <a id="13273" class="Bound">x</a> <a id="13275" class="Function">꞉</a> <a id="13277" class="Bound">A</a> <a id="13279" class="Function">,</a> <a id="13281" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].




----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

----------------------------------------

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

