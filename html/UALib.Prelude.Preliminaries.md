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


#### Options


All Agda programs begin by setting some options, which effect how Agda behaves, and by importing from existing libraries (in our case, the [Agda Standard Library][] and the [Type Topology][] library by MHE). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, we start each Agda source file in the library with the following line:

<pre class="Agda">
<a id="1244" class="Symbol">{-#</a> <a id="1248" class="Keyword">OPTIONS</a> <a id="1256" class="Pragma">--without-K</a> <a id="1268" class="Pragma">--exact-split</a> <a id="1282" class="Pragma">--safe</a> <a id="1289" class="Symbol">#-}</a>
</pre>

This specifies the Agda `OPTIONS` that we will use throughout the library.

  * `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

  * `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

  * `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must remove the `--safe` flag and insert the `--allow-unsolved-metas` flag, so we could use the following in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

#### Modules

The `OPTIONS` line is usually followed by the start of a module.  For example, here's how we start the Preliminaries module here.

<pre class="Agda">

<a id="2969" class="Keyword">module</a> <a id="2976" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="3004" class="Keyword">where</a>

</pre>

Sometimes we may wish to pass in some parameters that will be assumed throughout the module.  For instance, when working with algebras, we often consider algebras of a particular fixed signature, and this is something we could fix as a parameter.  We'll see some examples soon enough, but as a preview,

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

Actually, for illustration purposes, we have here an example that Agda wouldn't normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope.

In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.  This is done as follows.

<pre class="Agda">
<a id="5095" class="Comment">-- open import universes public</a>

<a id="5128" class="Comment">-- variable</a>
<a id="5140" class="Comment">--   𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓠 𝓡 𝓢 𝓧 : Universe</a>
</pre>

#### Imports from Type Topology

Throughout we use many of the nice tools that Martin Escardo has developed and made available in his [Type Topology][] repository of Agda code for Univalent Foundations.

We import these now.

<pre class="Agda">
<a id="5427" class="Keyword">open</a> <a id="5432" class="Keyword">import</a> <a id="5439" href="universes.html" class="Module">universes</a> <a id="5449" class="Keyword">public</a>

<a id="5457" class="Keyword">open</a> <a id="5462" class="Keyword">import</a> <a id="5469" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="5483" class="Keyword">renaming</a> <a id="5492" class="Symbol">(</a><a id="5493" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="5497" class="Symbol">to</a> <a id="5500" class="Keyword">infix</a> <a id="5506" class="Number">0</a> <a id="_≡_"></a><a id="5508" href="UALib.Prelude.Preliminaries.html#5508" class="Datatype Operator">_≡_</a> <a id="5512" class="Symbol">;</a> <a id="5514" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5519" class="Symbol">to</a> <a id="refl"></a><a id="5522" href="UALib.Prelude.Preliminaries.html#5522" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a><a id="5526" class="Symbol">)</a> <a id="5528" class="Keyword">public</a>

<a id="5536" class="Keyword">pattern</a> <a id="refl"></a><a id="5544" href="UALib.Prelude.Preliminaries.html#5544" class="InductiveConstructor">refl</a> <a id="5549" href="UALib.Prelude.Preliminaries.html#5563" class="Bound">x</a> <a id="5551" class="Symbol">=</a> <a id="5553" href="UALib.Prelude.Preliminaries.html#5522" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5558" class="Symbol">{</a>x <a id="5561" class="Symbol">=</a> <a id="5563" href="UALib.Prelude.Preliminaries.html#5563" class="Bound">x</a><a id="5564" class="Symbol">}</a>

<a id="5567" class="Keyword">open</a> <a id="5572" class="Keyword">import</a> <a id="5579" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="5590" class="Keyword">renaming</a> <a id="5599" class="Symbol">(</a><a id="5600" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="5604" class="Symbol">to</a> <a id="5607" class="Keyword">infixr</a> <a id="5614" class="Number">50</a> <a id="_,_"></a><a id="5617" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">_,_</a><a id="5620" class="Symbol">)</a> <a id="5622" class="Keyword">public</a>

<a id="5630" class="Keyword">open</a> <a id="5635" class="Keyword">import</a> <a id="5642" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5651" class="Keyword">using</a> <a id="5657" class="Symbol">(</a><a id="5658" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="5661" class="Symbol">;</a> <a id="5663" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="5669" class="Symbol">;</a> <a id="5671" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="5679" class="Symbol">;</a> <a id="5681" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="5690" class="Symbol">;</a> <a id="5692" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="5698" class="Symbol">;</a> <a id="5700" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="5702" class="Symbol">;</a> <a id="5704" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="5707" class="Symbol">;</a> <a id="5709" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="5712" class="Symbol">;</a> <a id="5714" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="5716" class="Symbol">;</a> <a id="5718" class="Comment">-- 𝕁;</a>
 <a id="5725" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="5726" class="Symbol">;</a> <a id="5728" href="MGS-MLTT.html#956" class="Function">¬</a><a id="5729" class="Symbol">;</a> <a id="5731" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="5734" class="Symbol">;</a> <a id="5736" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="5738" class="Symbol">;</a> <a id="5740" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5743" class="Symbol">;</a> <a id="5745" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="5748" class="Symbol">;</a> <a id="5750" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="5751" class="Symbol">;</a> <a id="5753" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="5754" class="Symbol">;</a> <a id="5756" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="5757" class="Symbol">;</a> <a id="5759" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="5762" class="Symbol">;</a> <a id="5764" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="5778" class="Symbol">;</a> <a id="5780" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="5794" class="Symbol">;</a> <a id="5796" href="MGS-MLTT.html#3744" class="Function">id</a><a id="5798" class="Symbol">;</a> <a id="5800" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="5803" class="Symbol">;</a> <a id="5805" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="5807" class="Symbol">)</a> <a id="5809" class="Keyword">public</a>

<a id="5817" class="Keyword">open</a> <a id="5822" class="Keyword">import</a> <a id="5829" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="5846" class="Keyword">using</a> <a id="5852" class="Symbol">(</a><a id="5853" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="5861" class="Symbol">;</a> <a id="5863" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="5870" class="Symbol">;</a> <a id="5872" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="5882" class="Symbol">)</a> <a id="5884" class="Keyword">public</a>

<a id="5892" class="Keyword">open</a> <a id="5897" class="Keyword">import</a> <a id="5904" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5930" class="Keyword">using</a> <a id="5936" class="Symbol">(</a><a id="5937" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5943" class="Symbol">;</a> <a id="5945" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="5959" class="Symbol">;</a> <a id="5961" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5968" class="Symbol">;</a> <a id="5970" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="5982" class="Symbol">;</a>
 <a id="5985" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="6000" class="Symbol">;</a> <a id="6002" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="6009" class="Symbol">;</a> <a id="6011" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="6021" class="Symbol">;</a> <a id="6023" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6037" class="Symbol">;</a> <a id="6039" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="6070" class="Symbol">;</a> <a id="6072" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="6075" class="Symbol">;</a>
 <a id="6078" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="6081" class="Symbol">;</a> <a id="6083" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="6132" class="Symbol">;</a> <a id="6134" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="6151" class="Symbol">;</a> <a id="6153" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="6170" class="Symbol">)</a> <a id="6172" class="Keyword">public</a>

<a id="6180" class="Keyword">open</a> <a id="6185" class="Keyword">import</a> <a id="6192" href="MGS-Powerset.html" class="Module">MGS-Powerset</a> <a id="6205" class="Keyword">renaming</a> <a id="6214" class="Symbol">(</a><a id="6215" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="6219" class="Symbol">to</a> <a id="_∈_"></a><a id="6222" href="UALib.Prelude.Preliminaries.html#6222" class="Function Operator">_∈₀_</a><a id="6226" class="Symbol">;</a> <a id="6228" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="6232" class="Symbol">to</a> <a id="_⊆_"></a><a id="6235" href="UALib.Prelude.Preliminaries.html#6235" class="Function Operator">_⊆₀_</a><a id="6239" class="Symbol">;</a> <a id="6241" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="6259" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="6262" href="UALib.Prelude.Preliminaries.html#6262" class="Function">∈₀-is-subsingleton</a><a id="6280" class="Symbol">)</a>
 <a id="6283" class="Keyword">using</a> <a id="6289" class="Symbol">(</a><a id="6290" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="6291" class="Symbol">;</a> <a id="6293" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="6314" class="Symbol">;</a> <a id="6316" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="6335" class="Symbol">;</a> <a id="6337" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="6359" class="Symbol">;</a> <a id="6361" href="MGS-Powerset.html#382" class="Function">propext</a><a id="6368" class="Symbol">;</a> <a id="6370" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="6376" class="Symbol">;</a> <a id="6378" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="6379" class="Symbol">)</a> <a id="6381" class="Keyword">public</a>

<a id="6389" class="Keyword">open</a> <a id="6394" class="Keyword">import</a> <a id="6401" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="6416" class="Keyword">using</a> <a id="6422" class="Symbol">(</a><a id="6423" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="6426" class="Symbol">;</a> <a id="6428" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="6432" class="Symbol">;</a> <a id="6434" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="6451" class="Symbol">;</a> <a id="6453" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="6465" class="Symbol">;</a> <a id="6467" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="6480" class="Symbol">;</a> <a id="6482" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="6493" class="Symbol">;</a>
 <a id="6496" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="6502" class="Symbol">;</a> <a id="6504" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="6507" class="Symbol">;</a> <a id="6509" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="6536" class="Symbol">;</a> <a id="6538" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="6555" class="Symbol">;</a> <a id="6557" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="6574" class="Symbol">;</a> <a id="6576" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="6591" class="Symbol">)</a> <a id="6593" class="Keyword">public</a>

<a id="6601" class="Keyword">open</a> <a id="6606" class="Keyword">import</a> <a id="6613" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="6634" class="Keyword">using</a> <a id="6640" class="Symbol">(</a><a id="6641" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="6653" class="Symbol">)</a> <a id="6655" class="Keyword">public</a>

<a id="6663" class="Keyword">open</a> <a id="6668" class="Keyword">import</a> <a id="6675" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="6696" class="Keyword">using</a> <a id="6702" class="Symbol">(</a><a id="6703" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="6705" class="Symbol">;</a> <a id="6707" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="6710" class="Symbol">)</a> <a id="6712" class="Keyword">public</a>

<a id="6720" class="Keyword">open</a> <a id="6725" class="Keyword">import</a> <a id="6732" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="6760" class="Keyword">using</a> <a id="6766" class="Symbol">(</a><a id="6767" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="6770" class="Symbol">;</a> <a id="6772" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="6778" class="Symbol">;</a> <a id="6780" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="6801" class="Symbol">;</a>
 <a id="6804" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="6826" class="Symbol">;</a> <a id="6828" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="6833" class="Symbol">;</a> <a id="6835" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="6853" class="Symbol">;</a> <a id="6855" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="6862" class="Symbol">)</a> <a id="6864" class="Keyword">public</a>
</pre>

Notice that we have carefully specified which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting the `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes clear exactly which parts of the Martin Escardo (and Martin-Löf!) type theory we are using.

To conclude this preliminary model, we define some syntactic sugar for the first and second projections of a pair.

<pre class="Agda">
<a id="7472" class="Keyword">module</a> <a id="7479" href="UALib.Prelude.Preliminaries.html#7479" class="Module">_</a> <a id="7481" class="Symbol">{</a><a id="7482" href="UALib.Prelude.Preliminaries.html#7482" class="Bound">𝓤</a> <a id="7484" class="Symbol">:</a> <a id="7486" href="universes.html#551" class="Postulate">Universe</a><a id="7494" class="Symbol">}</a> <a id="7496" class="Keyword">where</a>
 <a id="7503" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣_∣</a> <a id="7507" href="UALib.Prelude.Preliminaries.html#7507" class="Function">fst</a> <a id="7511" class="Symbol">:</a> <a id="7513" class="Symbol">{</a><a id="7514" href="UALib.Prelude.Preliminaries.html#7514" class="Bound">X</a> <a id="7516" class="Symbol">:</a> <a id="7518" href="UALib.Prelude.Preliminaries.html#7482" class="Bound">𝓤</a> <a id="7520" href="universes.html#758" class="Function Operator">̇</a> <a id="7522" class="Symbol">}{</a><a id="7524" href="UALib.Prelude.Preliminaries.html#7524" class="Bound">Y</a> <a id="7526" class="Symbol">:</a> <a id="7528" href="UALib.Prelude.Preliminaries.html#7514" class="Bound">X</a> <a id="7530" class="Symbol">→</a> <a id="7532" href="universes.html#617" class="Generalizable">𝓥</a> <a id="7534" href="universes.html#758" class="Function Operator">̇</a><a id="7535" class="Symbol">}</a> <a id="7537" class="Symbol">→</a> <a id="7539" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="7541" href="UALib.Prelude.Preliminaries.html#7524" class="Bound">Y</a> <a id="7543" class="Symbol">→</a> <a id="7545" href="UALib.Prelude.Preliminaries.html#7514" class="Bound">X</a>
 <a id="7548" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="7550" href="UALib.Prelude.Preliminaries.html#7550" class="Bound">x</a> <a id="7552" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="7554" href="UALib.Prelude.Preliminaries.html#7554" class="Bound">y</a> <a id="7556" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="7558" class="Symbol">=</a> <a id="7560" href="UALib.Prelude.Preliminaries.html#7550" class="Bound">x</a>
 <a id="7563" href="UALib.Prelude.Preliminaries.html#7507" class="Function">fst</a> <a id="7567" class="Symbol">(</a><a id="7568" href="UALib.Prelude.Preliminaries.html#7568" class="Bound">x</a> <a id="7570" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="7572" href="UALib.Prelude.Preliminaries.html#7572" class="Bound">y</a><a id="7573" class="Symbol">)</a> <a id="7575" class="Symbol">=</a> <a id="7577" href="UALib.Prelude.Preliminaries.html#7568" class="Bound">x</a>

 <a id="7581" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥_∥</a> <a id="7585" href="UALib.Prelude.Preliminaries.html#7585" class="Function">snd</a> <a id="7589" class="Symbol">:</a> <a id="7591" class="Symbol">{</a><a id="7592" href="UALib.Prelude.Preliminaries.html#7592" class="Bound">X</a> <a id="7594" class="Symbol">:</a> <a id="7596" href="UALib.Prelude.Preliminaries.html#7482" class="Bound">𝓤</a> <a id="7598" href="universes.html#758" class="Function Operator">̇</a> <a id="7600" class="Symbol">}{</a><a id="7602" href="UALib.Prelude.Preliminaries.html#7602" class="Bound">Y</a> <a id="7604" class="Symbol">:</a> <a id="7606" href="UALib.Prelude.Preliminaries.html#7592" class="Bound">X</a> <a id="7608" class="Symbol">→</a> <a id="7610" href="universes.html#617" class="Generalizable">𝓥</a> <a id="7612" href="universes.html#758" class="Function Operator">̇</a> <a id="7614" class="Symbol">}</a> <a id="7616" class="Symbol">→</a> <a id="7618" class="Symbol">(</a><a id="7619" href="UALib.Prelude.Preliminaries.html#7619" class="Bound">z</a> <a id="7621" class="Symbol">:</a> <a id="7623" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="7625" href="UALib.Prelude.Preliminaries.html#7602" class="Bound">Y</a><a id="7626" class="Symbol">)</a> <a id="7628" class="Symbol">→</a> <a id="7630" href="UALib.Prelude.Preliminaries.html#7602" class="Bound">Y</a> <a id="7632" class="Symbol">(</a><a id="7633" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="7637" href="UALib.Prelude.Preliminaries.html#7619" class="Bound">z</a><a id="7638" class="Symbol">)</a>
 <a id="7641" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="7643" href="UALib.Prelude.Preliminaries.html#7643" class="Bound">x</a> <a id="7645" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="7647" href="UALib.Prelude.Preliminaries.html#7647" class="Bound">y</a> <a id="7649" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="7651" class="Symbol">=</a> <a id="7653" href="UALib.Prelude.Preliminaries.html#7647" class="Bound">y</a>
 <a id="7656" href="UALib.Prelude.Preliminaries.html#7585" class="Function">snd</a> <a id="7660" class="Symbol">(</a><a id="7661" href="UALib.Prelude.Preliminaries.html#7661" class="Bound">x</a> <a id="7663" href="UALib.Prelude.Preliminaries.html#5617" class="InductiveConstructor Operator">,</a> <a id="7665" href="UALib.Prelude.Preliminaries.html#7665" class="Bound">y</a><a id="7666" class="Symbol">)</a> <a id="7668" class="Symbol">=</a> <a id="7670" href="UALib.Prelude.Preliminaries.html#7665" class="Bound">y</a>
</pre>

Both of these alternative notations,

```agda
fst (x , y) ≡ x, snd(x , y) ≡ y
```

and

```agda
∣ (x , y) ∣ = x, ∥ (x , y) ∥ = y
```

will be used frequently throughout the library.

-------------------------------------

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

