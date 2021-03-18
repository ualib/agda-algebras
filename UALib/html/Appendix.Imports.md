---
layout: default
title : Appendix.Imports module (The Agda Universal Algebra Library)
date : 2021-03-18
author: William DeMeo
---

This is the [Appendix.Imports][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="233" class="Symbol">{-#</a> <a id="237" class="Keyword">OPTIONS</a> <a id="245" class="Pragma">--without-K</a> <a id="257" class="Pragma">--exact-split</a> <a id="271" class="Pragma">--safe</a> <a id="278" class="Symbol">#-}</a>

<a id="283" class="Keyword">module</a> <a id="290" href="Appendix.Imports.html" class="Module">Appendix.Imports</a> <a id="307" class="Keyword">where</a>

</pre>

### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.  The first of these is the `Universes` module which we import now.

<pre class="Agda">

<a id="674" class="Keyword">open</a> <a id="679" class="Keyword">import</a> <a id="686" href="Universes.html" class="Module">Universes</a> <a id="696" class="Keyword">public</a>

</pre>

Since we used the `public` directive, the `Universes` module will be available to all modules that import [Prelude.Preliminaries][].

Escardó's `Universe` module includes a number of symbols used to denote universes. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="1097" class="Keyword">variable</a>
 <a id="1107" href="Appendix.Imports.html#1107" class="Generalizable">𝓞</a> <a id="1109" class="Symbol">:</a> <a id="1111" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

Below is a list of all other types from Escardó's [Type Topology][] library that we will import in the [UALib][] at one place or another.

The purpose of the import lines below is not actually to effect the stated imports. (In fact, we could comment all of them out and the entire [UALib][] will still type-check.) The reason for including these import statements here is to give readers and users an overview of all the dependencies of the library.

We leave off the `public` keyword from the end of these import directives on purpose so that we are forced to (re)import each item where and when we need it.  This may seem pedantic (and may turn out to be too inconvenient for users in the end) but it makes the dependencies clearer, and dependencies reveal the foundations upon which the library is built.  Since we are very interested in foundations(!), we try to keep all dependencies in the foreground, and resist the temptation to store them all in a single file that we never have to think about again.

The first line must be commented out because we define the given type ourselves for pedagogical purposes, though we will eventually import the original definition from the [Type Topology][] library.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>

<pre class="Agda">

<a id="2404" class="Keyword">open</a> <a id="2409" class="Keyword">import</a> <a id="2416" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="2427" class="Keyword">renaming</a> <a id="2436" class="Symbol">(</a><a id="2437" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="2441" class="Symbol">to</a> <a id="2444" class="Keyword">infixr</a> <a id="2451" class="Number">50</a> <a id="_,_"></a><a id="2454" href="Appendix.Imports.html#2454" class="InductiveConstructor Operator">_,_</a><a id="2457" class="Symbol">)</a>

<a id="2460" class="Keyword">open</a> <a id="2465" class="Keyword">import</a> <a id="2472" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="2486" class="Keyword">renaming</a> <a id="2495" class="Symbol">(</a><a id="2496" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="2500" class="Symbol">to</a> <a id="2503" class="Keyword">infix</a> <a id="2509" class="Number">0</a> <a id="_≡_"></a><a id="2511" href="Appendix.Imports.html#2511" class="Datatype Operator">_≡_</a><a id="2514" class="Symbol">)</a>

<a id="2517" class="Keyword">open</a> <a id="2522" class="Keyword">import</a> <a id="2529" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2538" class="Keyword">using</a> <a id="2544" class="Symbol">(</a><a id="2545" href="MGS-MLTT.html#3813" class="Function Operator">_∘_</a><a id="2548" class="Symbol">;</a> <a id="2550" href="MGS-MLTT.html#3944" class="Function">domain</a><a id="2556" class="Symbol">;</a> <a id="2558" href="MGS-MLTT.html#4021" class="Function">codomain</a><a id="2566" class="Symbol">;</a> <a id="2568" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="2577" class="Symbol">;</a>
 <a id="2580" href="MGS-MLTT.html#5997" class="Function Operator">_≡⟨_⟩_</a><a id="2586" class="Symbol">;</a> <a id="2588" href="MGS-MLTT.html#6079" class="Function Operator">_∎</a><a id="2590" class="Symbol">;</a> <a id="2592" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="2595" class="Symbol">;</a> <a id="2597" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="2600" class="Symbol">;</a> <a id="2602" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="2605" class="Symbol">;</a> <a id="2607" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="2609" class="Symbol">;</a> <a id="2611" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="2612" class="Symbol">;</a> <a id="2614" href="MGS-MLTT.html#956" class="Function">¬</a><a id="2615" class="Symbol">;</a> <a id="2617" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="2619" class="Symbol">;</a> <a id="2621" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="2624" class="Symbol">;</a> <a id="2626" href="MGS-MLTT.html#2104" class="Datatype Operator">_+_</a><a id="2629" class="Symbol">;</a> <a id="2631" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="2632" class="Symbol">;</a> <a id="2634" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="2635" class="Symbol">;</a> <a id="2637" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="2638" class="Symbol">;</a> <a id="2640" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="2643" class="Symbol">;</a>
 <a id="2646" href="MGS-MLTT.html#7133" class="Function">lr-implication</a><a id="2660" class="Symbol">;</a> <a id="2662" href="MGS-MLTT.html#7214" class="Function">rl-implication</a><a id="2676" class="Symbol">;</a> <a id="2678" href="MGS-MLTT.html#3744" class="Function">id</a><a id="2680" class="Symbol">;</a> <a id="2682" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="2685" class="Symbol">;</a> <a id="2687" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="2689" class="Symbol">)</a>

<a id="2692" class="Keyword">open</a> <a id="2697" class="Keyword">import</a> <a id="2704" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="2721" class="Keyword">using</a> <a id="2727" class="Symbol">(</a><a id="2728" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="2736" class="Symbol">;</a> <a id="2738" href="MGS-Equivalences.html#979" class="Function">inverse</a><a id="2745" class="Symbol">;</a> <a id="2747" href="MGS-Equivalences.html#370" class="Function">invertible</a><a id="2757" class="Symbol">)</a>

<a id="2760" class="Keyword">open</a> <a id="2765" class="Keyword">import</a> <a id="2772" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="2798" class="Keyword">using</a> <a id="2804" class="Symbol">(</a><a id="2805" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="2811" class="Symbol">;</a> <a id="2813" href="MGS-Subsingleton-Theorems.html#3729" class="Function">global-hfunext</a><a id="2827" class="Symbol">;</a> <a id="2829" href="MGS-Equivalences.html#6164" class="Function Operator">_●_</a><a id="2832" class="Symbol">;</a> <a id="2834" href="MGS-Equivalences.html#5035" class="Function Operator">_≃_</a><a id="2837" class="Symbol">;</a>
 <a id="2840" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="2847" class="Symbol">;</a> <a id="2849" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="2863" class="Symbol">;</a> <a id="2865" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="2877" class="Symbol">;</a> <a id="2879" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="2894" class="Symbol">;</a> <a id="2896" href="MGS-Basic-UF.html#1827" class="Function">is-prop</a><a id="2903" class="Symbol">;</a> <a id="2905" href="MGS-Subsingleton-Theorems.html#2964" class="Function">Univalence</a><a id="2915" class="Symbol">;</a>
 <a id="2918" href="MGS-Subsingleton-Theorems.html#3528" class="Function">univalence-gives-global-dfunext</a><a id="2949" class="Symbol">;</a> <a id="2951" href="MGS-Subsingleton-Theorems.html#393" class="Function">Π-is-subsingleton</a><a id="2968" class="Symbol">;</a> <a id="2970" href="MGS-Solved-Exercises.html#6049" class="Function">Σ-is-subsingleton</a><a id="2987" class="Symbol">;</a>
 <a id="2990" href="MGS-Solved-Exercises.html#5136" class="Function">logically-equivalent-subsingletons-are-equivalent</a><a id="3039" class="Symbol">)</a>

<a id="3042" class="Keyword">open</a> <a id="3047" class="Keyword">import</a> <a id="3054" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="3069" class="Keyword">using</a> <a id="3075" class="Symbol">(</a><a id="3076" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="3082" class="Symbol">;</a> <a id="3084" href="MGS-Embeddings.html#6370" class="Function Operator">_↪_</a><a id="3087" class="Symbol">;</a> <a id="3089" href="MGS-Basic-UF.html#6463" class="Function">Nat</a><a id="3092" class="Symbol">;</a> <a id="3094" href="MGS-Embeddings.html#5408" class="Function">NatΠ</a><a id="3098" class="Symbol">;</a> <a id="3100" href="MGS-Embeddings.html#384" class="Function">is-embedding</a><a id="3112" class="Symbol">;</a>
 <a id="3115" href="MGS-Embeddings.html#5502" class="Function">NatΠ-is-embedding</a><a id="3132" class="Symbol">;</a> <a id="3134" href="MGS-Embeddings.html#1089" class="Function">pr₁-embedding</a><a id="3147" class="Symbol">;</a> <a id="3149" href="MGS-Embeddings.html#1742" class="Function">∘-embedding</a><a id="3160" class="Symbol">;</a> <a id="3162" href="MGS-Embeddings.html#1623" class="Function">id-is-embedding</a><a id="3177" class="Symbol">;</a>
 <a id="3180" href="MGS-Embeddings.html#3808" class="Function">embedding-gives-ap-is-equiv</a><a id="3207" class="Symbol">;</a> <a id="3209" href="MGS-Embeddings.html#4830" class="Function">embeddings-are-lc</a><a id="3226" class="Symbol">;</a> <a id="3228" href="MGS-Solved-Exercises.html#6381" class="Function">×-is-subsingleton</a><a id="3245" class="Symbol">)</a>

<a id="3248" class="Keyword">open</a> <a id="3253" class="Keyword">import</a> <a id="3260" href="MGS-Solved-Exercises.html" class="Module">MGS-Solved-Exercises</a> <a id="3281" class="Keyword">using</a> <a id="3287" class="Symbol">(</a><a id="3288" href="MGS-Solved-Exercises.html#4076" class="Function">to-subtype-≡</a><a id="3300" class="Symbol">)</a>

<a id="3303" class="Keyword">open</a> <a id="3308" class="Keyword">import</a> <a id="3315" href="MGS-Unique-Existence.html" class="Module">MGS-Unique-Existence</a> <a id="3336" class="Keyword">using</a> <a id="3342" class="Symbol">(</a><a id="3343" href="MGS-Unique-Existence.html#387" class="Function">∃!</a><a id="3345" class="Symbol">;</a> <a id="3347" href="MGS-Unique-Existence.html#453" class="Function">-∃!</a><a id="3350" class="Symbol">)</a>

<a id="3353" class="Keyword">open</a> <a id="3358" class="Keyword">import</a> <a id="3365" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="3393" class="Keyword">using</a> <a id="3399" class="Symbol">(</a><a id="3400" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="3403" class="Symbol">;</a> <a id="3405" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="3411" class="Symbol">;</a> <a id="3413" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="3418" class="Symbol">;</a> <a id="3420" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="3427" class="Symbol">;</a>
 <a id="3430" href="MGS-Embeddings.html#1410" class="Function">equivs-are-embeddings</a><a id="3451" class="Symbol">;</a> <a id="3453" href="MGS-Equivalences.html#2127" class="Function">invertibles-are-equivs</a><a id="3475" class="Symbol">;</a> <a id="3477" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="3495" class="Symbol">)</a>

<a id="3498" class="Keyword">open</a> <a id="3503" class="Keyword">import</a> <a id="3510" href="MGS-Powerset.html" class="Module">MGS-Powerset</a>
 <a id="3524" class="Keyword">renaming</a> <a id="3533" class="Symbol">(</a><a id="3534" href="MGS-Powerset.html#4924" class="Function Operator">_∈_</a> <a id="3538" class="Symbol">to</a> <a id="_∈_"></a><a id="3541" href="Appendix.Imports.html#3541" class="Function Operator">_∈₀_</a><a id="3545" class="Symbol">;</a> <a id="3547" href="MGS-Powerset.html#4976" class="Function Operator">_⊆_</a> <a id="3551" class="Symbol">to</a> <a id="_⊆_"></a><a id="3554" href="Appendix.Imports.html#3554" class="Function Operator">_⊆₀_</a><a id="3558" class="Symbol">;</a> <a id="3560" href="MGS-Powerset.html#5040" class="Function">∈-is-subsingleton</a> <a id="3578" class="Symbol">to</a> <a id="∈-is-subsingleton"></a><a id="3581" href="Appendix.Imports.html#3581" class="Function">∈₀-is-subsingleton</a><a id="3599" class="Symbol">)</a>
 <a id="3602" class="Keyword">using</a> <a id="3608" class="Symbol">(</a><a id="3609" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="3610" class="Symbol">;</a> <a id="3612" href="MGS-Solved-Exercises.html#1652" class="Function">equiv-to-subsingleton</a><a id="3633" class="Symbol">;</a> <a id="3635" href="MGS-Powerset.html#4586" class="Function">powersets-are-sets&#39;</a><a id="3654" class="Symbol">;</a> <a id="3656" href="MGS-Powerset.html#6079" class="Function">subset-extensionality&#39;</a><a id="3678" class="Symbol">;</a>
 <a id="3681" href="MGS-Powerset.html#382" class="Function">propext</a><a id="3688" class="Symbol">;</a> <a id="3690" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="3696" class="Symbol">;</a> <a id="3698" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="3699" class="Symbol">)</a>

</pre>

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.


