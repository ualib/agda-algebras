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

This is the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

### <a id="logical-foundations">Logical foundations</a>

For the benefit of readers who are not proficient in Agda or type theory, we briefly describe some of the type theoretic foundations of the [Agda UALib][], as well as the most important basic types and features that are used throughout the library.

The [UALib][] is based on a minimal version of [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) (MLTT) which is the same or very close to the type theory on which Martin Escardo's [Type Topology][] Agda library is based.  We won't go into great detail here because there are already other very nice resources available, such as the section on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda) of the lecture notes by Escardó just mentioned, the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), and the [HoTT Book][].

We begin by recalling the handful of objects that are assumed at the jumping-off point for MLTT: "primitive" types (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type), and an infinite collection of *universes* (types of types) and universe variables to denote them (for which we will use upper-case caligraphic letters like `𝓤`, `𝓥`, `𝓦`, etc., typically from the latter half of the English alphabet, following Escardó's convention).

#### <a id="options">Options</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2509" class="Symbol">{-#</a> <a id="2513" class="Keyword">OPTIONS</a> <a id="2521" class="Pragma">--without-K</a> <a id="2533" class="Pragma">--exact-split</a> <a id="2547" class="Pragma">--safe</a> <a id="2554" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="modules">Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4256" class="Keyword">module</a> <a id="4263" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="4285" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.


#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.  The first of these is the `Universes` module which we import now.

<pre class="Agda">

<a id="5290" class="Keyword">open</a> <a id="5295" class="Keyword">import</a> <a id="5302" href="Universes.html" class="Module">Universes</a> <a id="5312" class="Keyword">public</a>

</pre>

Since we used the `public` directive, the `Universes` module will be available to all modules that import [Prelude.Preliminaries][].

Escardó's `Universe` module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="5713" class="Keyword">variable</a>
 <a id="5723" href="Prelude.Preliminaries.html#5723" class="Generalizable">𝓞</a> <a id="5725" class="Symbol">:</a> <a id="5727" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

The first line must be commented out because we define the given type ourselves for pedagogical purposes, though we will eventually import the original definition from the [Type Topology][] library.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>

<pre class="Agda">

<a id="7020" class="Comment">-- open import Sigma-Type renaming (_,_ to infixr 50 _,_)</a>

<a id="7079" class="Keyword">open</a> <a id="7084" class="Keyword">import</a> <a id="7091" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="7105" class="Keyword">renaming</a> <a id="7114" class="Symbol">(</a><a id="7115" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="7119" class="Symbol">to</a> <a id="7122" class="Keyword">infix</a> <a id="7128" class="Number">0</a> <a id="_≡_"></a><a id="7130" href="Prelude.Preliminaries.html#7130" class="Datatype Operator">_≡_</a><a id="7133" class="Symbol">)</a>

<a id="7136" class="Keyword">open</a> <a id="7141" class="Keyword">import</a> <a id="7148" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="7157" class="Keyword">using</a> <a id="7163" class="Symbol">(</a><a id="7164" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="7167" class="Symbol">;</a> <a id="7169" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="7175" class="Symbol">;</a> <a id="7177" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="7185" class="Symbol">;</a> <a id="7187" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="7196" class="Symbol">;</a> <a id="7198" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="7204" class="Symbol">;</a> <a id="7206" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="7208" class="Symbol">;</a> <a id="7210" class="Comment">-- _×_; pr₁; pr₂; -Σ; Π;</a>
   <a id="7238" href="MGS-MLTT.html#956" class="Function">¬</a><a id="7239" class="Symbol">;</a> <a id="7241" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="7243" class="Symbol">;</a> <a id="7245" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="7248" class="Symbol">;</a> <a id="7250" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="7253" class="Symbol">;</a> <a id="7255" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="7256" class="Symbol">;</a> <a id="7258" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="7259" class="Symbol">;</a> <a id="7261" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="7262" class="Symbol">;</a> <a id="7264" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="7267" class="Symbol">;</a> <a id="7269" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="7283" class="Symbol">;</a> <a id="7285" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="7299" class="Symbol">;</a> <a id="7301" href="MGS-MLTT.html#3744" class="Function">id</a><a id="7303" class="Symbol">;</a> <a id="7305" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="7308" class="Symbol">;</a> <a id="7310" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="7312" class="Symbol">)</a>

<a id="7315" class="Keyword">open</a> <a id="7320" class="Keyword">import</a> <a id="7327" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="7344" class="Keyword">using</a> <a id="7350" class="Symbol">(</a><a id="7351" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="7359" class="Symbol">;</a> <a id="7361" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="7368" class="Symbol">;</a> <a id="7370" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="7380" class="Symbol">)</a>

<a id="7383" class="Keyword">open</a> <a id="7388" class="Keyword">import</a> <a id="7395" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="7421" class="Keyword">using</a> <a id="7427" class="Symbol">(</a><a id="7428" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="7434" class="Symbol">;</a> <a id="7436" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="7450" class="Symbol">;</a> <a id="7452" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="7459" class="Symbol">;</a>
 <a id="7462" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7474" class="Symbol">;</a> <a id="7476" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7491" class="Symbol">;</a> <a id="7493" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="7500" class="Symbol">;</a> <a id="7502" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="7512" class="Symbol">;</a> <a id="7514" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="7528" class="Symbol">;</a>
 <a id="7531" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="7562" class="Symbol">;</a> <a id="7564" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="7567" class="Symbol">;</a> <a id="7569" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="7572" class="Symbol">;</a> <a id="7574" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="7591" class="Symbol">;</a> <a id="7593" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="7610" class="Symbol">;</a>
 <a id="7613" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="7662" class="Symbol">)</a>

<a id="7665" class="Keyword">open</a> <a id="7670" class="Keyword">import</a> <a id="7677" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="7690" class="Keyword">renaming</a> <a id="7699" class="Symbol">(</a><a id="7700" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="7704" class="Symbol">to</a> <a id="_∈_"></a><a id="7707" href="Prelude.Preliminaries.html#7707" class="Function Operator">_∈₀_</a><a id="7711" class="Symbol">;</a> <a id="7713" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="7717" class="Symbol">to</a> <a id="_⊆_"></a><a id="7720" href="Prelude.Preliminaries.html#7720" class="Function Operator">_⊆₀_</a><a id="7724" class="Symbol">;</a> <a id="7726" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="7744" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="7747" href="Prelude.Preliminaries.html#7747" class="Function">∈₀-is-subsingleton</a><a id="7765" class="Symbol">)</a>
 <a id="7768" class="Keyword">using</a> <a id="7774" class="Symbol">(</a><a id="7775" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="7776" class="Symbol">;</a> <a id="7778" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="7799" class="Symbol">;</a> <a id="7801" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="7820" class="Symbol">;</a> <a id="7822" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="7844" class="Symbol">;</a> <a id="7846" href="MGS-Powerset.html#382" class="Function">propext</a><a id="7853" class="Symbol">;</a> <a id="7855" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="7861" class="Symbol">;</a> <a id="7863" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="7864" class="Symbol">)</a>

<a id="7867" class="Keyword">open</a> <a id="7872" class="Keyword">import</a> <a id="7879" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="7894" class="Keyword">using</a> <a id="7900" class="Symbol">(</a><a id="7901" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="7904" class="Symbol">;</a> <a id="7906" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="7910" class="Symbol">;</a> <a id="7912" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="7929" class="Symbol">;</a> <a id="7931" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="7943" class="Symbol">;</a> <a id="7945" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="7958" class="Symbol">;</a> <a id="7960" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="7971" class="Symbol">;</a>
 <a id="7974" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="7980" class="Symbol">;</a> <a id="7982" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="7985" class="Symbol">;</a> <a id="7987" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="8014" class="Symbol">;</a> <a id="8016" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="8033" class="Symbol">;</a> <a id="8035" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="8052" class="Symbol">;</a> <a id="8054" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="8069" class="Symbol">)</a>

<a id="8072" class="Keyword">open</a> <a id="8077" class="Keyword">import</a> <a id="8084" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="8105" class="Keyword">using</a> <a id="8111" class="Symbol">(</a><a id="8112" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="8124" class="Symbol">)</a>

<a id="8127" class="Keyword">open</a> <a id="8132" class="Keyword">import</a> <a id="8139" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="8160" class="Keyword">using</a> <a id="8166" class="Symbol">(</a><a id="8167" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="8169" class="Symbol">;</a> <a id="8171" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="8174" class="Symbol">)</a>

<a id="8177" class="Keyword">open</a> <a id="8182" class="Keyword">import</a> <a id="8189" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="8217" class="Keyword">using</a> <a id="8223" class="Symbol">(</a><a id="8224" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="8227" class="Symbol">;</a> <a id="8229" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="8235" class="Symbol">;</a> <a id="8237" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="8258" class="Symbol">;</a>
 <a id="8261" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="8283" class="Symbol">;</a> <a id="8285" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8290" class="Symbol">;</a> <a id="8292" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="8310" class="Symbol">;</a> <a id="8312" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8319" class="Symbol">)</a>

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

<a id="11973" class="Keyword">module</a> <a id="hide-sigma"></a><a id="11980" href="Prelude.Preliminaries.html#11980" class="Module">hide-sigma</a> <a id="11991" class="Keyword">where</a>

 <a id="11999" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="12006" href="Prelude.Preliminaries.html#12006" class="Record">Σ</a> <a id="12008" class="Symbol">{</a><a id="12009" href="Prelude.Preliminaries.html#12009" class="Bound">𝓤</a> <a id="12011" href="Prelude.Preliminaries.html#12011" class="Bound">𝓥</a><a id="12012" class="Symbol">}</a> <a id="12014" class="Symbol">{</a><a id="12015" href="Prelude.Preliminaries.html#12015" class="Bound">X</a> <a id="12017" class="Symbol">:</a> <a id="12019" href="Prelude.Preliminaries.html#12009" class="Bound">𝓤</a> <a id="12021" href="Universes.html#403" class="Function Operator">̇</a> <a id="12023" class="Symbol">}</a> <a id="12025" class="Symbol">(</a><a id="12026" href="Prelude.Preliminaries.html#12026" class="Bound">Y</a> <a id="12028" class="Symbol">:</a> <a id="12030" href="Prelude.Preliminaries.html#12015" class="Bound">X</a> <a id="12032" class="Symbol">→</a> <a id="12034" href="Prelude.Preliminaries.html#12011" class="Bound">𝓥</a> <a id="12036" href="Universes.html#403" class="Function Operator">̇</a> <a id="12038" class="Symbol">)</a> <a id="12040" class="Symbol">:</a> <a id="12042" href="Prelude.Preliminaries.html#12009" class="Bound">𝓤</a> <a id="12044" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12046" href="Prelude.Preliminaries.html#12011" class="Bound">𝓥</a> <a id="12048" href="Universes.html#403" class="Function Operator">̇</a>  <a id="12051" class="Keyword">where</a>
  <a id="12059" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="12071" href="Prelude.Preliminaries.html#12071" class="InductiveConstructor Operator">_,_</a>
  <a id="12077" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="12086" href="Prelude.Preliminaries.html#12086" class="Field">pr₁</a> <a id="12090" class="Symbol">:</a> <a id="12092" href="Prelude.Preliminaries.html#12015" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="12097" href="Prelude.Preliminaries.html#12097" class="Field">pr₂</a> <a id="12101" class="Symbol">:</a> <a id="12103" href="Prelude.Preliminaries.html#12026" class="Bound">Y</a> <a id="12105" href="Prelude.Preliminaries.html#12086" class="Field">pr₁</a>

 <a id="12111" class="Keyword">infixr</a> <a id="12118" class="Number">50</a> <a id="12121" href="Prelude.Preliminaries.html#12071" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="12442" href="Prelude.Preliminaries.html#12442" class="Function">-Σ</a> <a id="12445" class="Symbol">:</a> <a id="12447" class="Symbol">{</a><a id="12448" href="Prelude.Preliminaries.html#12448" class="Bound">𝓤</a> <a id="12450" href="Prelude.Preliminaries.html#12450" class="Bound">𝓥</a> <a id="12452" class="Symbol">:</a> <a id="12454" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12462" class="Symbol">}</a> <a id="12464" class="Symbol">(</a><a id="12465" href="Prelude.Preliminaries.html#12465" class="Bound">X</a> <a id="12467" class="Symbol">:</a> <a id="12469" href="Prelude.Preliminaries.html#12448" class="Bound">𝓤</a> <a id="12471" href="Universes.html#403" class="Function Operator">̇</a> <a id="12473" class="Symbol">)</a> <a id="12475" class="Symbol">(</a><a id="12476" href="Prelude.Preliminaries.html#12476" class="Bound">Y</a> <a id="12478" class="Symbol">:</a> <a id="12480" href="Prelude.Preliminaries.html#12465" class="Bound">X</a> <a id="12482" class="Symbol">→</a> <a id="12484" href="Prelude.Preliminaries.html#12450" class="Bound">𝓥</a> <a id="12486" href="Universes.html#403" class="Function Operator">̇</a> <a id="12488" class="Symbol">)</a> <a id="12490" class="Symbol">→</a> <a id="12492" href="Prelude.Preliminaries.html#12448" class="Bound">𝓤</a> <a id="12494" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12496" href="Prelude.Preliminaries.html#12450" class="Bound">𝓥</a> <a id="12498" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12501" href="Prelude.Preliminaries.html#12442" class="Function">-Σ</a> <a id="12504" href="Prelude.Preliminaries.html#12504" class="Bound">X</a> <a id="12506" href="Prelude.Preliminaries.html#12506" class="Bound">Y</a> <a id="12508" class="Symbol">=</a> <a id="12510" href="Prelude.Preliminaries.html#12006" class="Record">Σ</a> <a id="12512" href="Prelude.Preliminaries.html#12506" class="Bound">Y</a>

 <a id="12516" class="Keyword">syntax</a> <a id="12523" href="Prelude.Preliminaries.html#12442" class="Function">-Σ</a> <a id="12526" class="Bound">X</a> <a id="12528" class="Symbol">(λ</a> <a id="12531" class="Bound">x</a> <a id="12533" class="Symbol">→</a> <a id="12535" class="Bound">Y</a><a id="12536" class="Symbol">)</a> <a id="12538" class="Symbol">=</a> <a id="12540" class="Function">Σ</a> <a id="12542" class="Bound">x</a> <a id="12544" class="Function">꞉</a> <a id="12546" class="Bound">X</a> <a id="12548" class="Function">,</a> <a id="12550" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="12923" href="Prelude.Preliminaries.html#12923" class="Function Operator">_×_</a> <a id="12927" class="Symbol">:</a> <a id="12929" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12931" href="Universes.html#403" class="Function Operator">̇</a> <a id="12933" class="Symbol">→</a> <a id="12935" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12937" href="Universes.html#403" class="Function Operator">̇</a> <a id="12939" class="Symbol">→</a> <a id="12941" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="12943" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12945" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12947" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12950" href="Prelude.Preliminaries.html#12950" class="Bound">X</a> <a id="12952" href="Prelude.Preliminaries.html#12923" class="Function Operator">×</a> <a id="12954" href="Prelude.Preliminaries.html#12954" class="Bound">Y</a> <a id="12956" class="Symbol">=</a> <a id="12958" href="Prelude.Preliminaries.html#12442" class="Function">Σ</a> <a id="12960" href="Prelude.Preliminaries.html#12960" class="Bound">x</a> <a id="12962" href="Prelude.Preliminaries.html#12442" class="Function">꞉</a> <a id="12964" href="Prelude.Preliminaries.html#12950" class="Bound">X</a> <a id="12966" href="Prelude.Preliminaries.html#12442" class="Function">,</a> <a id="12968" href="Prelude.Preliminaries.html#12954" class="Bound">Y</a>

</pre>

Now that we have repeated these definitions from the [Type Topology][] for illustration purposes, let us import the original definitions that we will use throughout the [UALib][].

<pre class="Agda">

<a id="13178" class="Keyword">open</a> <a id="13183" class="Keyword">import</a> <a id="13190" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13201" class="Keyword">renaming</a> <a id="13210" class="Symbol">(</a><a id="13211" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13215" class="Symbol">to</a> <a id="13218" class="Keyword">infixr</a> <a id="13225" class="Number">50</a> <a id="_,_"></a><a id="13228" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">_,_</a><a id="13231" class="Symbol">)</a>
<a id="13233" class="Keyword">open</a> <a id="13238" class="Keyword">import</a> <a id="13245" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13254" class="Keyword">using</a> <a id="13260" class="Symbol">(</a><a id="13261" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13264" class="Symbol">;</a> <a id="13266" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13269" class="Symbol">;</a> <a id="13271" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13274" class="Symbol">;</a> <a id="13276" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13278" class="Symbol">)</a>

</pre>

The definition of Σ (and thus, of ×) is accompanied by first and second projection functions, `pr₁` and `pr₂`.  Sometimes we prefer to use `∣_∣` and `∥_∥` for these projections, respectively. However, we will alternate between these and other standard alternatives, such as , or `fst` and `snd`, for emphasis or readability.  We define these alternative notations for projections out of pairs as follows.<sup>[3](Prelude.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="13754" class="Keyword">module</a> <a id="13761" href="Prelude.Preliminaries.html#13761" class="Module">_</a> <a id="13763" class="Symbol">{</a><a id="13764" href="Prelude.Preliminaries.html#13764" class="Bound">𝓤</a> <a id="13766" class="Symbol">:</a> <a id="13768" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13776" class="Symbol">}</a> <a id="13778" class="Keyword">where</a>

 <a id="13786" href="Prelude.Preliminaries.html#13786" class="Function Operator">∣_∣</a> <a id="13790" href="Prelude.Preliminaries.html#13790" class="Function">fst</a> <a id="13794" class="Symbol">:</a> <a id="13796" class="Symbol">{</a><a id="13797" href="Prelude.Preliminaries.html#13797" class="Bound">X</a> <a id="13799" class="Symbol">:</a> <a id="13801" href="Prelude.Preliminaries.html#13764" class="Bound">𝓤</a> <a id="13803" href="Universes.html#403" class="Function Operator">̇</a> <a id="13805" class="Symbol">}{</a><a id="13807" href="Prelude.Preliminaries.html#13807" class="Bound">Y</a> <a id="13809" class="Symbol">:</a> <a id="13811" href="Prelude.Preliminaries.html#13797" class="Bound">X</a> <a id="13813" class="Symbol">→</a> <a id="13815" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13817" href="Universes.html#403" class="Function Operator">̇</a><a id="13818" class="Symbol">}</a> <a id="13820" class="Symbol">→</a> <a id="13822" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13824" href="Prelude.Preliminaries.html#13807" class="Bound">Y</a> <a id="13826" class="Symbol">→</a> <a id="13828" href="Prelude.Preliminaries.html#13797" class="Bound">X</a>
 <a id="13831" href="Prelude.Preliminaries.html#13786" class="Function Operator">∣</a> <a id="13833" href="Prelude.Preliminaries.html#13833" class="Bound">x</a> <a id="13835" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="13837" href="Prelude.Preliminaries.html#13837" class="Bound">y</a> <a id="13839" href="Prelude.Preliminaries.html#13786" class="Function Operator">∣</a> <a id="13841" class="Symbol">=</a> <a id="13843" href="Prelude.Preliminaries.html#13833" class="Bound">x</a>
 <a id="13846" href="Prelude.Preliminaries.html#13790" class="Function">fst</a> <a id="13850" class="Symbol">(</a><a id="13851" href="Prelude.Preliminaries.html#13851" class="Bound">x</a> <a id="13853" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="13855" href="Prelude.Preliminaries.html#13855" class="Bound">y</a><a id="13856" class="Symbol">)</a> <a id="13858" class="Symbol">=</a> <a id="13860" href="Prelude.Preliminaries.html#13851" class="Bound">x</a>

 <a id="13864" href="Prelude.Preliminaries.html#13864" class="Function Operator">∥_∥</a> <a id="13868" href="Prelude.Preliminaries.html#13868" class="Function">snd</a> <a id="13872" class="Symbol">:</a> <a id="13874" class="Symbol">{</a><a id="13875" href="Prelude.Preliminaries.html#13875" class="Bound">X</a> <a id="13877" class="Symbol">:</a> <a id="13879" href="Prelude.Preliminaries.html#13764" class="Bound">𝓤</a> <a id="13881" href="Universes.html#403" class="Function Operator">̇</a> <a id="13883" class="Symbol">}{</a><a id="13885" href="Prelude.Preliminaries.html#13885" class="Bound">Y</a> <a id="13887" class="Symbol">:</a> <a id="13889" href="Prelude.Preliminaries.html#13875" class="Bound">X</a> <a id="13891" class="Symbol">→</a> <a id="13893" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13895" href="Universes.html#403" class="Function Operator">̇</a> <a id="13897" class="Symbol">}</a> <a id="13899" class="Symbol">→</a> <a id="13901" class="Symbol">(</a><a id="13902" href="Prelude.Preliminaries.html#13902" class="Bound">z</a> <a id="13904" class="Symbol">:</a> <a id="13906" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13908" href="Prelude.Preliminaries.html#13885" class="Bound">Y</a><a id="13909" class="Symbol">)</a> <a id="13911" class="Symbol">→</a> <a id="13913" href="Prelude.Preliminaries.html#13885" class="Bound">Y</a> <a id="13915" class="Symbol">(</a><a id="13916" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13920" href="Prelude.Preliminaries.html#13902" class="Bound">z</a><a id="13921" class="Symbol">)</a>
 <a id="13924" href="Prelude.Preliminaries.html#13864" class="Function Operator">∥</a> <a id="13926" href="Prelude.Preliminaries.html#13926" class="Bound">x</a> <a id="13928" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="13930" href="Prelude.Preliminaries.html#13930" class="Bound">y</a> <a id="13932" href="Prelude.Preliminaries.html#13864" class="Function Operator">∥</a> <a id="13934" class="Symbol">=</a> <a id="13936" href="Prelude.Preliminaries.html#13930" class="Bound">y</a>
 <a id="13939" href="Prelude.Preliminaries.html#13868" class="Function">snd</a> <a id="13943" class="Symbol">(</a><a id="13944" href="Prelude.Preliminaries.html#13944" class="Bound">x</a> <a id="13946" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="13948" href="Prelude.Preliminaries.html#13948" class="Bound">y</a><a id="13949" class="Symbol">)</a> <a id="13951" class="Symbol">=</a> <a id="13953" href="Prelude.Preliminaries.html#13948" class="Bound">y</a>

</pre>




#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

<pre class="Agda">

<a id="14230" class="Keyword">module</a> <a id="hide-pi"></a><a id="14237" href="Prelude.Preliminaries.html#14237" class="Module">hide-pi</a> <a id="14245" class="Symbol">{</a><a id="14246" href="Prelude.Preliminaries.html#14246" class="Bound">𝓤</a> <a id="14248" href="Prelude.Preliminaries.html#14248" class="Bound">𝓦</a> <a id="14250" class="Symbol">:</a> <a id="14252" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14260" class="Symbol">}</a> <a id="14262" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="14270" href="Prelude.Preliminaries.html#14270" class="Function">Π</a> <a id="14272" class="Symbol">:</a> <a id="14274" class="Symbol">{</a><a id="14275" href="Prelude.Preliminaries.html#14275" class="Bound">X</a> <a id="14277" class="Symbol">:</a> <a id="14279" href="Prelude.Preliminaries.html#14246" class="Bound">𝓤</a> <a id="14281" href="Universes.html#403" class="Function Operator">̇</a> <a id="14283" class="Symbol">}</a> <a id="14285" class="Symbol">(</a><a id="14286" href="Prelude.Preliminaries.html#14286" class="Bound">A</a> <a id="14288" class="Symbol">:</a> <a id="14290" href="Prelude.Preliminaries.html#14275" class="Bound">X</a> <a id="14292" class="Symbol">→</a> <a id="14294" href="Prelude.Preliminaries.html#14248" class="Bound">𝓦</a> <a id="14296" href="Universes.html#403" class="Function Operator">̇</a> <a id="14298" class="Symbol">)</a> <a id="14300" class="Symbol">→</a> <a id="14302" href="Prelude.Preliminaries.html#14246" class="Bound">𝓤</a> <a id="14304" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14306" href="Prelude.Preliminaries.html#14248" class="Bound">𝓦</a> <a id="14308" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14311" href="Prelude.Preliminaries.html#14270" class="Function">Π</a> <a id="14313" class="Symbol">{</a><a id="14314" href="Prelude.Preliminaries.html#14314" class="Bound">X</a><a id="14315" class="Symbol">}</a> <a id="14317" href="Prelude.Preliminaries.html#14317" class="Bound">A</a> <a id="14319" class="Symbol">=</a> <a id="14321" class="Symbol">(</a><a id="14322" href="Prelude.Preliminaries.html#14322" class="Bound">x</a> <a id="14324" class="Symbol">:</a> <a id="14326" href="Prelude.Preliminaries.html#14314" class="Bound">X</a><a id="14327" class="Symbol">)</a> <a id="14329" class="Symbol">→</a> <a id="14331" href="Prelude.Preliminaries.html#14317" class="Bound">A</a> <a id="14333" href="Prelude.Preliminaries.html#14322" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="14337" href="Prelude.Preliminaries.html#14337" class="Function">-Π</a> <a id="14340" class="Symbol">:</a> <a id="14342" class="Symbol">(</a><a id="14343" href="Prelude.Preliminaries.html#14343" class="Bound">X</a> <a id="14345" class="Symbol">:</a> <a id="14347" href="Prelude.Preliminaries.html#14246" class="Bound">𝓤</a> <a id="14349" href="Universes.html#403" class="Function Operator">̇</a> <a id="14351" class="Symbol">)(</a><a id="14353" href="Prelude.Preliminaries.html#14353" class="Bound">Y</a> <a id="14355" class="Symbol">:</a> <a id="14357" href="Prelude.Preliminaries.html#14343" class="Bound">X</a> <a id="14359" class="Symbol">→</a> <a id="14361" href="Prelude.Preliminaries.html#14248" class="Bound">𝓦</a> <a id="14363" href="Universes.html#403" class="Function Operator">̇</a> <a id="14365" class="Symbol">)</a> <a id="14367" class="Symbol">→</a> <a id="14369" href="Prelude.Preliminaries.html#14246" class="Bound">𝓤</a> <a id="14371" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="14373" href="Prelude.Preliminaries.html#14248" class="Bound">𝓦</a> <a id="14375" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="14378" href="Prelude.Preliminaries.html#14337" class="Function">-Π</a> <a id="14381" href="Prelude.Preliminaries.html#14381" class="Bound">X</a> <a id="14383" href="Prelude.Preliminaries.html#14383" class="Bound">Y</a> <a id="14385" class="Symbol">=</a> <a id="14387" href="Prelude.Preliminaries.html#14270" class="Function">Π</a> <a id="14389" href="Prelude.Preliminaries.html#14383" class="Bound">Y</a>

 <a id="14393" class="Keyword">infixr</a> <a id="14400" class="Number">-1</a> <a id="14403" href="Prelude.Preliminaries.html#14337" class="Function">-Π</a>
 <a id="14407" class="Keyword">syntax</a> <a id="14414" href="Prelude.Preliminaries.html#14337" class="Function">-Π</a> <a id="14417" class="Bound">A</a> <a id="14419" class="Symbol">(λ</a> <a id="14422" class="Bound">x</a> <a id="14424" class="Symbol">→</a> <a id="14426" class="Bound">b</a><a id="14427" class="Symbol">)</a> <a id="14429" class="Symbol">=</a> <a id="14431" class="Function">Π</a> <a id="14433" class="Bound">x</a> <a id="14435" class="Function">꞉</a> <a id="14437" class="Bound">A</a> <a id="14439" class="Function">,</a> <a id="14441" class="Bound">b</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].



#### <a id="general-composition">General composition of functions</a>

<pre class="Agda">

<a id="14731" class="Keyword">open</a> <a id="14736" class="Keyword">import</a> <a id="14743" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="14754" class="Keyword">renaming</a> <a id="14763" class="Symbol">(</a><a id="14764" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="14768" class="Symbol">to</a> <a id="14771" class="Keyword">infixr</a> <a id="14778" class="Number">50</a> <a id="_,_"></a><a id="14781" href="Prelude.Preliminaries.html#14781" class="InductiveConstructor Operator">_,_</a><a id="14784" class="Symbol">)</a> <a id="14786" class="Keyword">public</a>
<a id="14793" class="Keyword">open</a> <a id="14798" class="Keyword">import</a> <a id="14805" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="14814" class="Keyword">using</a> <a id="14820" class="Symbol">(</a><a id="14821" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="14824" class="Symbol">;</a> <a id="14826" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="14829" class="Symbol">;</a> <a id="14831" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="14834" class="Symbol">;</a> <a id="14836" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="14838" class="Symbol">;</a> <a id="14840" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="14841" class="Symbol">)</a> <a id="14843" class="Keyword">public</a>


<a id="14852" class="Keyword">module</a> <a id="14859" href="Prelude.Preliminaries.html#14859" class="Module">_</a> <a id="14861" class="Symbol">{</a><a id="14862" href="Prelude.Preliminaries.html#14862" class="Bound">𝓨</a> <a id="14864" href="Prelude.Preliminaries.html#14864" class="Bound">𝓩</a> <a id="14866" class="Symbol">:</a> <a id="14868" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="14876" class="Symbol">}{</a><a id="14878" href="Prelude.Preliminaries.html#14878" class="Bound">I</a> <a id="14880" class="Symbol">:</a> <a id="14882" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="14884" href="Universes.html#403" class="Function Operator">̇</a><a id="14885" class="Symbol">}{</a><a id="14887" href="Prelude.Preliminaries.html#14887" class="Bound">B</a> <a id="14889" class="Symbol">:</a> <a id="14891" href="Prelude.Preliminaries.html#14878" class="Bound">I</a> <a id="14893" class="Symbol">→</a> <a id="14895" href="Prelude.Preliminaries.html#14862" class="Bound">𝓨</a> <a id="14897" href="Universes.html#403" class="Function Operator">̇</a><a id="14898" class="Symbol">}{</a><a id="14900" href="Prelude.Preliminaries.html#14900" class="Bound">C</a> <a id="14902" class="Symbol">:</a> <a id="14904" href="Prelude.Preliminaries.html#14878" class="Bound">I</a> <a id="14906" class="Symbol">→</a> <a id="14908" href="Prelude.Preliminaries.html#14864" class="Bound">𝓩</a> <a id="14910" href="Universes.html#403" class="Function Operator">̇</a><a id="14911" class="Symbol">}</a> <a id="14913" class="Keyword">where</a>
 <a id="14920" class="Comment">-- {Y : 𝓨 ̇}{Z : 𝓩 ̇}</a>
 <a id="14943" href="Prelude.Preliminaries.html#14943" class="Function">zip</a> <a id="14947" class="Symbol">:</a> <a id="14949" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14951" href="Prelude.Preliminaries.html#14887" class="Bound">B</a> <a id="14953" class="Symbol">→</a> <a id="14955" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14957" href="Prelude.Preliminaries.html#14900" class="Bound">C</a> <a id="14959" class="Symbol">→</a> <a id="14961" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="14963" class="Symbol">(λ</a> <a id="14966" href="Prelude.Preliminaries.html#14966" class="Bound">i</a> <a id="14968" class="Symbol">→</a> <a id="14970" class="Symbol">(</a><a id="14971" href="Prelude.Preliminaries.html#14887" class="Bound">B</a> <a id="14973" href="Prelude.Preliminaries.html#14966" class="Bound">i</a><a id="14974" class="Symbol">)</a> <a id="14976" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="14978" class="Symbol">(</a><a id="14979" href="Prelude.Preliminaries.html#14900" class="Bound">C</a> <a id="14981" href="Prelude.Preliminaries.html#14966" class="Bound">i</a><a id="14982" class="Symbol">))</a>
 <a id="14986" href="Prelude.Preliminaries.html#14943" class="Function">zip</a> <a id="14990" href="Prelude.Preliminaries.html#14990" class="Bound">f</a> <a id="14992" href="Prelude.Preliminaries.html#14992" class="Bound">a</a> <a id="14994" class="Symbol">=</a> <a id="14996" class="Symbol">λ</a> <a id="14998" href="Prelude.Preliminaries.html#14998" class="Bound">i</a> <a id="15000" class="Symbol">→</a> <a id="15002" class="Symbol">(</a><a id="15003" href="Prelude.Preliminaries.html#14990" class="Bound">f</a> <a id="15005" href="Prelude.Preliminaries.html#14998" class="Bound">i</a> <a id="15007" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="15009" href="Prelude.Preliminaries.html#14992" class="Bound">a</a> <a id="15011" href="Prelude.Preliminaries.html#14998" class="Bound">i</a><a id="15012" class="Symbol">)</a>

 <a id="15016" href="Prelude.Preliminaries.html#15016" class="Function">eval</a> <a id="15021" class="Symbol">:</a> <a id="15023" class="Symbol">{</a><a id="15024" href="Prelude.Preliminaries.html#15024" class="Bound">Y</a> <a id="15026" class="Symbol">:</a> <a id="15028" href="Prelude.Preliminaries.html#14862" class="Bound">𝓨</a> <a id="15030" href="Universes.html#403" class="Function Operator">̇</a><a id="15031" class="Symbol">}{</a><a id="15033" href="Prelude.Preliminaries.html#15033" class="Bound">Z</a> <a id="15035" class="Symbol">:</a> <a id="15037" href="Prelude.Preliminaries.html#14864" class="Bound">𝓩</a> <a id="15039" href="Universes.html#403" class="Function Operator">̇</a><a id="15040" class="Symbol">}</a> <a id="15042" class="Symbol">→</a> <a id="15044" class="Symbol">((</a><a id="15046" href="Prelude.Preliminaries.html#15024" class="Bound">Y</a> <a id="15048" class="Symbol">→</a> <a id="15050" href="Prelude.Preliminaries.html#15033" class="Bound">Z</a><a id="15051" class="Symbol">)</a> <a id="15053" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="15055" href="Prelude.Preliminaries.html#15024" class="Bound">Y</a><a id="15056" class="Symbol">)</a> <a id="15058" class="Symbol">→</a> <a id="15060" href="Prelude.Preliminaries.html#15033" class="Bound">Z</a>
 <a id="15063" href="Prelude.Preliminaries.html#15016" class="Function">eval</a> <a id="15068" class="Symbol">(</a><a id="15069" href="Prelude.Preliminaries.html#15069" class="Bound">f</a> <a id="15071" href="Prelude.Preliminaries.html#13228" class="InductiveConstructor Operator">,</a> <a id="15073" href="Prelude.Preliminaries.html#15073" class="Bound">a</a><a id="15074" class="Symbol">)</a> <a id="15076" class="Symbol">=</a> <a id="15078" href="Prelude.Preliminaries.html#15069" class="Bound">f</a> <a id="15080" href="Prelude.Preliminaries.html#15073" class="Bound">a</a>

<a id="15083" class="Keyword">module</a> <a id="15090" href="Prelude.Preliminaries.html#15090" class="Module">_</a> <a id="15092" class="Symbol">{</a><a id="15093" href="Prelude.Preliminaries.html#15093" class="Bound">𝓨</a> <a id="15095" class="Symbol">:</a> <a id="15097" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="15105" class="Symbol">}{</a><a id="15107" href="Prelude.Preliminaries.html#15107" class="Bound">I</a> <a id="15109" href="Prelude.Preliminaries.html#15109" class="Bound">J</a> <a id="15111" class="Symbol">:</a> <a id="15113" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="15115" href="Universes.html#403" class="Function Operator">̇</a><a id="15116" class="Symbol">}{</a><a id="15118" href="Prelude.Preliminaries.html#15118" class="Bound">B</a> <a id="15120" class="Symbol">:</a> <a id="15122" href="Prelude.Preliminaries.html#15107" class="Bound">I</a> <a id="15124" class="Symbol">→</a> <a id="15126" href="Prelude.Preliminaries.html#15093" class="Bound">𝓨</a> <a id="15128" href="Universes.html#403" class="Function Operator">̇</a><a id="15129" class="Symbol">}</a> <a id="15131" class="Keyword">where</a>

 <a id="15139" href="Prelude.Preliminaries.html#15139" class="Function">dapp</a> <a id="15144" class="Symbol">:</a> <a id="15146" class="Symbol">(∀</a> <a id="15149" href="Prelude.Preliminaries.html#15149" class="Bound">i</a> <a id="15151" class="Symbol">→</a> <a id="15153" class="Symbol">(</a><a id="15154" href="Prelude.Preliminaries.html#15109" class="Bound">J</a> <a id="15156" class="Symbol">→</a> <a id="15158" class="Symbol">(</a><a id="15159" href="Prelude.Preliminaries.html#15118" class="Bound">B</a> <a id="15161" href="Prelude.Preliminaries.html#15149" class="Bound">i</a><a id="15162" class="Symbol">))</a> <a id="15165" class="Symbol">→</a> <a id="15167" class="Symbol">(</a><a id="15168" href="Prelude.Preliminaries.html#15118" class="Bound">B</a> <a id="15170" href="Prelude.Preliminaries.html#15149" class="Bound">i</a><a id="15171" class="Symbol">))</a> <a id="15174" class="Symbol">→</a> <a id="15176" class="Symbol">(∀</a> <a id="15179" href="Prelude.Preliminaries.html#15179" class="Bound">i</a> <a id="15181" class="Symbol">→</a> <a id="15183" class="Symbol">(</a><a id="15184" href="Prelude.Preliminaries.html#15109" class="Bound">J</a> <a id="15186" class="Symbol">→</a> <a id="15188" class="Symbol">(</a><a id="15189" href="Prelude.Preliminaries.html#15118" class="Bound">B</a> <a id="15191" href="Prelude.Preliminaries.html#15179" class="Bound">i</a><a id="15192" class="Symbol">)))</a> <a id="15196" class="Symbol">→</a> <a id="15198" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="15200" href="Prelude.Preliminaries.html#15118" class="Bound">B</a>
 <a id="15203" href="Prelude.Preliminaries.html#15139" class="Function">dapp</a> <a id="15208" href="Prelude.Preliminaries.html#15208" class="Bound">f</a> <a id="15210" href="Prelude.Preliminaries.html#15210" class="Bound">a</a> <a id="15212" class="Symbol">=</a> <a id="15214" class="Symbol">λ</a> <a id="15216" href="Prelude.Preliminaries.html#15216" class="Bound">i</a> <a id="15218" class="Symbol">→</a> <a id="15220" class="Symbol">(</a><a id="15221" href="Prelude.Preliminaries.html#15208" class="Bound">f</a> <a id="15223" href="Prelude.Preliminaries.html#15216" class="Bound">i</a><a id="15224" class="Symbol">)</a> <a id="15226" class="Symbol">(</a><a id="15227" href="Prelude.Preliminaries.html#15210" class="Bound">a</a> <a id="15229" href="Prelude.Preliminaries.html#15216" class="Bound">i</a><a id="15230" class="Symbol">)</a>

</pre>

----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> Generally speaking, we have made a concerted effort to avoid duplicating types that were already defined in libraries that came before ours.  However, it is very likely that our library overlaps to some extent with other libraries with which we are as yet unfamiliar.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3"> Here we put the definition inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.</span>



<br>
<br>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


{% include UALib.Links.md %}



<!--

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
-->
