---
layout: default
title : Overture.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [Overture.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="300" class="Symbol">{-#</a> <a id="304" class="Keyword">OPTIONS</a> <a id="312" class="Pragma">--without-K</a> <a id="324" class="Pragma">--exact-split</a> <a id="338" class="Pragma">--safe</a> <a id="345" class="Symbol">#-}</a>

<a id="350" class="Keyword">module</a> <a id="357" href="Overture.Extensionality.html" class="Module">Overture.Extensionality</a> <a id="381" class="Keyword">where</a>

<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="Overture.Equality.html" class="Module">Overture.Equality</a> <a id="418" class="Keyword">public</a>

</pre>

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  Those already familiar with function extensionality may wish to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose `f` and `g` are defined on `A = ℤ` (the integers) as follows: `f x := x + 2` and `g x := ((2 * x) - 8)/2 + 6`.  Should we call `f` and `g` equal? Are they the "same" function?  What does that even mean?

It's hard to resist the urge to reduce `g` to `x + 2` and proclaim that `f` and `g` are equal. Indeed, this is often an acceptable answer and the discussion normally ends there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions `f` and `g` above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions, `f` and `g`, both of which take a list as argument and produce as output a correctly sorted version of the input list?  Suppose `f` is defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while `g` uses [quick sort](https://en.wikipedia.org/wiki/Quicksort).  Probably few of us would call `f` and `g` the "same" in this case.

In the examples above, it is common to say that the two functions are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same *external* output when given the same input, but they are not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their *internal* definitions differ.

In this module, we describe types that manifest this notion of *extensional equality of functions*, or *function extensionality*.<sup>[1](Overture.Extensionality.html#fn1)</sup>

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

<pre class="Agda">

<a id="2885" class="Keyword">module</a> <a id="hide-∼"></a><a id="2892" href="Overture.Extensionality.html#2892" class="Module">hide-∼</a> <a id="2899" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2907" href="Overture.Extensionality.html#2907" class="Function Operator">_∼_</a> <a id="2911" class="Symbol">:</a> <a id="2913" class="Symbol">{</a><a id="2914" href="Overture.Extensionality.html#2914" class="Bound">A</a> <a id="2916" class="Symbol">:</a> <a id="2918" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2920" href="Universes.html#403" class="Function Operator">̇</a> <a id="2922" class="Symbol">}</a> <a id="2924" class="Symbol">{</a><a id="2925" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Overture.Extensionality.html#2914" class="Bound">A</a> <a id="2931" class="Symbol">→</a> <a id="2933" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2935" href="Universes.html#403" class="Function Operator">̇</a> <a id="2937" class="Symbol">}</a> <a id="2939" class="Symbol">→</a> <a id="2941" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2943" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2945" class="Symbol">→</a> <a id="2947" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2949" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2951" class="Symbol">→</a> <a id="2953" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2955" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2957" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2959" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2962" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2964" href="Overture.Extensionality.html#2907" class="Function Operator">∼</a> <a id="2966" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2968" class="Symbol">=</a> <a id="2970" class="Symbol">∀</a> <a id="2972" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2974" class="Symbol">→</a> <a id="2976" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2978" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2980" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="2982" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2984" href="Overture.Extensionality.html#2972" class="Bound">x</a>

 <a id="2988" class="Keyword">infix</a> <a id="2994" class="Number">0</a> <a id="2996" href="Overture.Extensionality.html#2907" class="Function Operator">_∼_</a>

<a id="3001" class="Keyword">open</a> <a id="3006" class="Keyword">import</a> <a id="3013" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="3040" class="Keyword">using</a> <a id="3046" class="Symbol">(</a><a id="3047" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3050" class="Symbol">)</a> <a id="3052" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, and import the original definition below.)

<pre class="Agda">

<a id="3519" class="Keyword">module</a> <a id="hide-funext"></a><a id="3526" href="Overture.Extensionality.html#3526" class="Module">hide-funext</a> <a id="3538" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3546" href="Overture.Extensionality.html#3546" class="Function">funext</a> <a id="3553" class="Symbol">:</a> <a id="3555" class="Symbol">∀</a> <a id="3557" href="Overture.Extensionality.html#3557" class="Bound">𝓤</a> <a id="3559" href="Overture.Extensionality.html#3559" class="Bound">𝓦</a>  <a id="3562" class="Symbol">→</a> <a id="3564" href="Overture.Extensionality.html#3557" class="Bound">𝓤</a> <a id="3566" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3568" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3570" href="Overture.Extensionality.html#3559" class="Bound">𝓦</a> <a id="3572" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3574" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3577" href="Overture.Extensionality.html#3546" class="Function">funext</a> <a id="3584" href="Overture.Extensionality.html#3584" class="Bound">𝓤</a> <a id="3586" href="Overture.Extensionality.html#3586" class="Bound">𝓦</a> <a id="3588" class="Symbol">=</a> <a id="3590" class="Symbol">{</a><a id="3591" href="Overture.Extensionality.html#3591" class="Bound">A</a> <a id="3593" class="Symbol">:</a> <a id="3595" href="Overture.Extensionality.html#3584" class="Bound">𝓤</a> <a id="3597" href="Universes.html#403" class="Function Operator">̇</a> <a id="3599" class="Symbol">}</a> <a id="3601" class="Symbol">{</a><a id="3602" href="Overture.Extensionality.html#3602" class="Bound">B</a> <a id="3604" class="Symbol">:</a> <a id="3606" href="Overture.Extensionality.html#3586" class="Bound">𝓦</a> <a id="3608" href="Universes.html#403" class="Function Operator">̇</a> <a id="3610" class="Symbol">}</a> <a id="3612" class="Symbol">{</a><a id="3613" href="Overture.Extensionality.html#3613" class="Bound">f</a> <a id="3615" href="Overture.Extensionality.html#3615" class="Bound">g</a> <a id="3617" class="Symbol">:</a> <a id="3619" href="Overture.Extensionality.html#3591" class="Bound">A</a> <a id="3621" class="Symbol">→</a> <a id="3623" href="Overture.Extensionality.html#3602" class="Bound">B</a><a id="3624" class="Symbol">}</a> <a id="3626" class="Symbol">→</a> <a id="3628" href="Overture.Extensionality.html#3613" class="Bound">f</a> <a id="3630" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3632" href="Overture.Extensionality.html#3615" class="Bound">g</a> <a id="3634" class="Symbol">→</a> <a id="3636" href="Overture.Extensionality.html#3613" class="Bound">f</a> <a id="3638" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3640" href="Overture.Extensionality.html#3615" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3751" href="Overture.Extensionality.html#3751" class="Function">dfunext</a> <a id="3759" class="Symbol">:</a> <a id="3761" class="Symbol">∀</a> <a id="3763" href="Overture.Extensionality.html#3763" class="Bound">𝓤</a> <a id="3765" href="Overture.Extensionality.html#3765" class="Bound">𝓦</a> <a id="3767" class="Symbol">→</a> <a id="3769" href="Overture.Extensionality.html#3763" class="Bound">𝓤</a> <a id="3771" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3773" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3775" href="Overture.Extensionality.html#3765" class="Bound">𝓦</a> <a id="3777" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3779" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3782" href="Overture.Extensionality.html#3751" class="Function">dfunext</a> <a id="3790" href="Overture.Extensionality.html#3790" class="Bound">𝓤</a> <a id="3792" href="Overture.Extensionality.html#3792" class="Bound">𝓦</a> <a id="3794" class="Symbol">=</a> <a id="3796" class="Symbol">{</a><a id="3797" href="Overture.Extensionality.html#3797" class="Bound">A</a> <a id="3799" class="Symbol">:</a> <a id="3801" href="Overture.Extensionality.html#3790" class="Bound">𝓤</a> <a id="3803" href="Universes.html#403" class="Function Operator">̇</a> <a id="3805" class="Symbol">}{</a><a id="3807" href="Overture.Extensionality.html#3807" class="Bound">B</a> <a id="3809" class="Symbol">:</a> <a id="3811" href="Overture.Extensionality.html#3797" class="Bound">A</a> <a id="3813" class="Symbol">→</a> <a id="3815" href="Overture.Extensionality.html#3792" class="Bound">𝓦</a> <a id="3817" href="Universes.html#403" class="Function Operator">̇</a> <a id="3819" class="Symbol">}{</a><a id="3821" href="Overture.Extensionality.html#3821" class="Bound">f</a> <a id="3823" href="Overture.Extensionality.html#3823" class="Bound">g</a> <a id="3825" class="Symbol">:</a> <a id="3827" class="Symbol">∀(</a><a id="3829" href="Overture.Extensionality.html#3829" class="Bound">x</a> <a id="3831" class="Symbol">:</a> <a id="3833" href="Overture.Extensionality.html#3797" class="Bound">A</a><a id="3834" class="Symbol">)</a> <a id="3836" class="Symbol">→</a> <a id="3838" href="Overture.Extensionality.html#3807" class="Bound">B</a> <a id="3840" href="Overture.Extensionality.html#3829" class="Bound">x</a><a id="3841" class="Symbol">}</a> <a id="3843" class="Symbol">→</a>  <a id="3846" href="Overture.Extensionality.html#3821" class="Bound">f</a> <a id="3848" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3850" href="Overture.Extensionality.html#3823" class="Bound">g</a>  <a id="3853" class="Symbol">→</a>  <a id="3856" href="Overture.Extensionality.html#3821" class="Bound">f</a> <a id="3858" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3860" href="Overture.Extensionality.html#3823" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5269" href="Overture.Extensionality.html#5269" class="Function">global-funext</a> <a id="5283" class="Symbol">:</a> <a id="5285" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5289" href="Overture.Extensionality.html#5269" class="Function">global-funext</a> <a id="5303" class="Symbol">=</a> <a id="5305" class="Symbol">∀</a>  <a id="5308" class="Symbol">{</a><a id="5309" href="Overture.Extensionality.html#5309" class="Bound">𝓤</a> <a id="5311" href="Overture.Extensionality.html#5311" class="Bound">𝓥</a><a id="5312" class="Symbol">}</a> <a id="5314" class="Symbol">→</a> <a id="5316" href="Overture.Extensionality.html#3546" class="Function">funext</a> <a id="5323" href="Overture.Extensionality.html#5309" class="Bound">𝓤</a> <a id="5325" href="Overture.Extensionality.html#5311" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5329" href="Overture.Extensionality.html#5329" class="Function">global-dfunext</a> <a id="5344" class="Symbol">:</a> <a id="5346" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5350" href="Overture.Extensionality.html#5329" class="Function">global-dfunext</a> <a id="5365" class="Symbol">=</a> <a id="5367" class="Symbol">∀</a> <a id="5369" class="Symbol">{</a><a id="5370" href="Overture.Extensionality.html#5370" class="Bound">𝓤</a> <a id="5372" href="Overture.Extensionality.html#5372" class="Bound">𝓥</a><a id="5373" class="Symbol">}</a> <a id="5375" class="Symbol">→</a> <a id="5377" href="Overture.Extensionality.html#3751" class="Function">dfunext</a> <a id="5385" href="Overture.Extensionality.html#5370" class="Bound">𝓤</a> <a id="5387" href="Overture.Extensionality.html#5372" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Overture.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5683" class="Keyword">open</a> <a id="5688" class="Keyword">import</a> <a id="5695" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5722" class="Keyword">using</a> <a id="5728" class="Symbol">(</a><a id="5729" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5735" class="Symbol">;</a> <a id="5737" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5744" class="Symbol">)</a> <a id="5746" class="Keyword">public</a>
<a id="5753" class="Keyword">open</a> <a id="5758" class="Keyword">import</a> <a id="5765" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5791" class="Keyword">using</a> <a id="5797" class="Symbol">(</a><a id="5798" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5812" class="Symbol">)</a> <a id="5814" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6091" class="Keyword">open</a> <a id="6096" class="Keyword">import</a> <a id="6103" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6112" class="Keyword">using</a> <a id="6118" class="Symbol">(</a><a id="6119" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6122" class="Symbol">)</a> <a id="6124" class="Keyword">public</a>

<a id="extfun"></a><a id="6132" href="Overture.Extensionality.html#6132" class="Function">extfun</a> <a id="6139" class="Symbol">:</a> <a id="6141" class="Symbol">{</a><a id="6142" href="Overture.Extensionality.html#6142" class="Bound">A</a> <a id="6144" class="Symbol">:</a> <a id="6146" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6148" href="Universes.html#403" class="Function Operator">̇</a><a id="6149" class="Symbol">}{</a><a id="6151" href="Overture.Extensionality.html#6151" class="Bound">B</a> <a id="6153" class="Symbol">:</a> <a id="6155" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6157" href="Universes.html#403" class="Function Operator">̇</a><a id="6158" class="Symbol">}{</a><a id="6160" href="Overture.Extensionality.html#6160" class="Bound">f</a> <a id="6162" href="Overture.Extensionality.html#6162" class="Bound">g</a> <a id="6164" class="Symbol">:</a> <a id="6166" href="Overture.Extensionality.html#6142" class="Bound">A</a> <a id="6168" class="Symbol">→</a> <a id="6170" href="Overture.Extensionality.html#6151" class="Bound">B</a><a id="6171" class="Symbol">}</a> <a id="6173" class="Symbol">→</a> <a id="6175" href="Overture.Extensionality.html#6160" class="Bound">f</a> <a id="6177" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6179" href="Overture.Extensionality.html#6162" class="Bound">g</a>  <a id="6182" class="Symbol">→</a>  <a id="6185" href="Overture.Extensionality.html#6160" class="Bound">f</a> <a id="6187" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6189" href="Overture.Extensionality.html#6162" class="Bound">g</a>
<a id="6191" href="Overture.Extensionality.html#6132" class="Function">extfun</a> <a id="6198" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6203" class="Symbol">_</a> <a id="6205" class="Symbol">=</a> <a id="6207" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6333" href="Overture.Extensionality.html#6333" class="Function">extdfun</a> <a id="6341" class="Symbol">:</a> <a id="6343" class="Symbol">{</a><a id="6344" href="Overture.Extensionality.html#6344" class="Bound">A</a> <a id="6346" class="Symbol">:</a> <a id="6348" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6350" href="Universes.html#403" class="Function Operator">̇</a> <a id="6352" class="Symbol">}{</a><a id="6354" href="Overture.Extensionality.html#6354" class="Bound">B</a> <a id="6356" class="Symbol">:</a> <a id="6358" href="Overture.Extensionality.html#6344" class="Bound">A</a> <a id="6360" class="Symbol">→</a> <a id="6362" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6364" href="Universes.html#403" class="Function Operator">̇</a> <a id="6366" class="Symbol">}(</a><a id="6368" href="Overture.Extensionality.html#6368" class="Bound">f</a> <a id="6370" href="Overture.Extensionality.html#6370" class="Bound">g</a> <a id="6372" class="Symbol">:</a> <a id="6374" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6376" href="Overture.Extensionality.html#6354" class="Bound">B</a><a id="6377" class="Symbol">)</a> <a id="6379" class="Symbol">→</a> <a id="6381" href="Overture.Extensionality.html#6368" class="Bound">f</a> <a id="6383" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6385" href="Overture.Extensionality.html#6370" class="Bound">g</a> <a id="6387" class="Symbol">→</a> <a id="6389" href="Overture.Extensionality.html#6368" class="Bound">f</a> <a id="6391" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6393" href="Overture.Extensionality.html#6370" class="Bound">g</a>
<a id="6395" href="Overture.Extensionality.html#6333" class="Function">extdfun</a> <a id="6403" class="Symbol">_</a> <a id="6405" class="Symbol">_</a> <a id="6407" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6412" class="Symbol">_</a> <a id="6414" class="Symbol">=</a> <a id="6416" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.

In the definition of `funext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `funext` is an assertion (which may or may not hold). In the definition of `extfun`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `extfun` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8308" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8315" href="Overture.Extensionality.html#8315" class="Module">hide-tt-defs</a> <a id="8328" class="Symbol">{</a><a id="8329" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8331" class="Symbol">:</a> <a id="8333" href="Universes.html#205" class="Postulate">Universe</a><a id="8341" class="Symbol">}</a> <a id="8343" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8351" href="Overture.Extensionality.html#8351" class="Function">is-center</a> <a id="8361" class="Symbol">:</a> <a id="8363" class="Symbol">(</a><a id="8364" href="Overture.Extensionality.html#8364" class="Bound">A</a> <a id="8366" class="Symbol">:</a> <a id="8368" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8370" href="Universes.html#403" class="Function Operator">̇</a> <a id="8372" class="Symbol">)</a> <a id="8374" class="Symbol">→</a> <a id="8376" href="Overture.Extensionality.html#8364" class="Bound">A</a> <a id="8378" class="Symbol">→</a> <a id="8380" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8382" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8385" href="Overture.Extensionality.html#8351" class="Function">is-center</a> <a id="8395" href="Overture.Extensionality.html#8395" class="Bound">A</a> <a id="8397" href="Overture.Extensionality.html#8397" class="Bound">c</a> <a id="8399" class="Symbol">=</a> <a id="8401" class="Symbol">(</a><a id="8402" href="Overture.Extensionality.html#8402" class="Bound">x</a> <a id="8404" class="Symbol">:</a> <a id="8406" href="Overture.Extensionality.html#8395" class="Bound">A</a><a id="8407" class="Symbol">)</a> <a id="8409" class="Symbol">→</a> <a id="8411" href="Overture.Extensionality.html#8397" class="Bound">c</a> <a id="8413" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8415" href="Overture.Extensionality.html#8402" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8419" href="Overture.Extensionality.html#8419" class="Function">is-singleton</a> <a id="8432" class="Symbol">:</a> <a id="8434" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8436" href="Universes.html#403" class="Function Operator">̇</a> <a id="8438" class="Symbol">→</a> <a id="8440" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8442" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8445" href="Overture.Extensionality.html#8419" class="Function">is-singleton</a> <a id="8458" href="Overture.Extensionality.html#8458" class="Bound">A</a> <a id="8460" class="Symbol">=</a> <a id="8462" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8464" href="Overture.Extensionality.html#8464" class="Bound">c</a> <a id="8466" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8468" href="Overture.Extensionality.html#8458" class="Bound">A</a> <a id="8470" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8472" href="Overture.Extensionality.html#8351" class="Function">is-center</a> <a id="8482" href="Overture.Extensionality.html#8458" class="Bound">A</a> <a id="8484" href="Overture.Extensionality.html#8464" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8488" href="Overture.Extensionality.html#8488" class="Function">is-subsingleton</a> <a id="8504" class="Symbol">:</a> <a id="8506" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8508" href="Universes.html#403" class="Function Operator">̇</a> <a id="8510" class="Symbol">→</a> <a id="8512" href="Overture.Extensionality.html#8329" class="Bound">𝓤</a> <a id="8514" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8517" href="Overture.Extensionality.html#8488" class="Function">is-subsingleton</a> <a id="8533" href="Overture.Extensionality.html#8533" class="Bound">A</a> <a id="8535" class="Symbol">=</a> <a id="8537" class="Symbol">(</a><a id="8538" href="Overture.Extensionality.html#8538" class="Bound">x</a> <a id="8540" href="Overture.Extensionality.html#8540" class="Bound">y</a> <a id="8542" class="Symbol">:</a> <a id="8544" href="Overture.Extensionality.html#8533" class="Bound">A</a><a id="8545" class="Symbol">)</a> <a id="8547" class="Symbol">→</a> <a id="8549" href="Overture.Extensionality.html#8538" class="Bound">x</a> <a id="8551" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8553" href="Overture.Extensionality.html#8540" class="Bound">y</a>

</pre>

We import the original definitions of the last three types as follows. (The [first footnote](Overture.Equality.html#fn1) of [Overture.Equality][] explains why we both define and import certain types.)

<pre class="Agda">

<a id="8784" class="Keyword">open</a> <a id="8789" class="Keyword">import</a> <a id="8796" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8809" class="Keyword">using</a> <a id="8815" class="Symbol">(</a><a id="8816" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8825" class="Symbol">;</a> <a id="8827" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8839" class="Symbol">;</a> <a id="8841" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8856" class="Symbol">)</a> <a id="8858" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9275" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9282" href="Overture.Extensionality.html#9282" class="Module">hide-tt-defs&#39;</a> <a id="9296" class="Symbol">{</a><a id="9297" href="Overture.Extensionality.html#9297" class="Bound">𝓤</a> <a id="9299" href="Overture.Extensionality.html#9299" class="Bound">𝓦</a> <a id="9301" class="Symbol">:</a> <a id="9303" href="Universes.html#205" class="Postulate">Universe</a><a id="9311" class="Symbol">}</a> <a id="9313" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9321" href="Overture.Extensionality.html#9321" class="Function">fiber</a> <a id="9327" class="Symbol">:</a> <a id="9329" class="Symbol">{</a><a id="9330" href="Overture.Extensionality.html#9330" class="Bound">A</a> <a id="9332" class="Symbol">:</a> <a id="9334" href="Overture.Extensionality.html#9297" class="Bound">𝓤</a> <a id="9336" href="Universes.html#403" class="Function Operator">̇</a> <a id="9338" class="Symbol">}</a> <a id="9340" class="Symbol">{</a><a id="9341" href="Overture.Extensionality.html#9341" class="Bound">B</a> <a id="9343" class="Symbol">:</a> <a id="9345" href="Overture.Extensionality.html#9299" class="Bound">𝓦</a> <a id="9347" href="Universes.html#403" class="Function Operator">̇</a> <a id="9349" class="Symbol">}</a> <a id="9351" class="Symbol">(</a><a id="9352" href="Overture.Extensionality.html#9352" class="Bound">f</a> <a id="9354" class="Symbol">:</a> <a id="9356" href="Overture.Extensionality.html#9330" class="Bound">A</a> <a id="9358" class="Symbol">→</a> <a id="9360" href="Overture.Extensionality.html#9341" class="Bound">B</a><a id="9361" class="Symbol">)</a> <a id="9363" class="Symbol">→</a> <a id="9365" href="Overture.Extensionality.html#9341" class="Bound">B</a> <a id="9367" class="Symbol">→</a> <a id="9369" href="Overture.Extensionality.html#9297" class="Bound">𝓤</a> <a id="9371" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9373" href="Overture.Extensionality.html#9299" class="Bound">𝓦</a> <a id="9375" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9378" href="Overture.Extensionality.html#9321" class="Function">fiber</a> <a id="9384" class="Symbol">{</a><a id="9385" href="Overture.Extensionality.html#9385" class="Bound">A</a><a id="9386" class="Symbol">}</a> <a id="9388" href="Overture.Extensionality.html#9388" class="Bound">f</a> <a id="9390" href="Overture.Extensionality.html#9390" class="Bound">y</a> <a id="9392" class="Symbol">=</a> <a id="9394" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9396" href="Overture.Extensionality.html#9396" class="Bound">x</a> <a id="9398" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9400" href="Overture.Extensionality.html#9385" class="Bound">A</a> <a id="9402" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9404" href="Overture.Extensionality.html#9388" class="Bound">f</a> <a id="9406" href="Overture.Extensionality.html#9396" class="Bound">x</a> <a id="9408" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="9410" href="Overture.Extensionality.html#9390" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9516" href="Overture.Extensionality.html#9516" class="Function">is-equiv</a> <a id="9525" class="Symbol">:</a> <a id="9527" class="Symbol">{</a><a id="9528" href="Overture.Extensionality.html#9528" class="Bound">A</a> <a id="9530" class="Symbol">:</a> <a id="9532" href="Overture.Extensionality.html#9297" class="Bound">𝓤</a> <a id="9534" href="Universes.html#403" class="Function Operator">̇</a> <a id="9536" class="Symbol">}</a> <a id="9538" class="Symbol">{</a><a id="9539" href="Overture.Extensionality.html#9539" class="Bound">B</a> <a id="9541" class="Symbol">:</a> <a id="9543" href="Overture.Extensionality.html#9299" class="Bound">𝓦</a> <a id="9545" href="Universes.html#403" class="Function Operator">̇</a> <a id="9547" class="Symbol">}</a> <a id="9549" class="Symbol">→</a> <a id="9551" class="Symbol">(</a><a id="9552" href="Overture.Extensionality.html#9528" class="Bound">A</a> <a id="9554" class="Symbol">→</a> <a id="9556" href="Overture.Extensionality.html#9539" class="Bound">B</a><a id="9557" class="Symbol">)</a> <a id="9559" class="Symbol">→</a> <a id="9561" href="Overture.Extensionality.html#9297" class="Bound">𝓤</a> <a id="9563" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9565" href="Overture.Extensionality.html#9299" class="Bound">𝓦</a> <a id="9567" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9570" href="Overture.Extensionality.html#9516" class="Function">is-equiv</a> <a id="9579" href="Overture.Extensionality.html#9579" class="Bound">f</a> <a id="9581" class="Symbol">=</a> <a id="9583" class="Symbol">∀</a> <a id="9585" href="Overture.Extensionality.html#9585" class="Bound">y</a> <a id="9587" class="Symbol">→</a> <a id="9589" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9602" class="Symbol">(</a><a id="9603" href="Overture.Extensionality.html#9321" class="Function">fiber</a> <a id="9609" href="Overture.Extensionality.html#9579" class="Bound">f</a> <a id="9611" href="Overture.Extensionality.html#9585" class="Bound">y</a><a id="9612" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="9819" class="Keyword">open</a> <a id="9824" class="Keyword">import</a> <a id="9831" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9848" class="Keyword">using</a> <a id="9854" class="Symbol">(</a><a id="9855" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9860" class="Symbol">;</a> <a id="9862" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9870" class="Symbol">)</a> <a id="9872" class="Keyword">public</a>

<a id="9880" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9887" href="Overture.Extensionality.html#9887" class="Module">hide-hfunext</a> <a id="9900" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9908" href="Overture.Extensionality.html#9908" class="Function">hfunext</a> <a id="9916" class="Symbol">:</a>  <a id="9919" class="Symbol">∀</a> <a id="9921" href="Overture.Extensionality.html#9921" class="Bound">𝓤</a> <a id="9923" href="Overture.Extensionality.html#9923" class="Bound">𝓦</a> <a id="9925" class="Symbol">→</a> <a id="9927" class="Symbol">(</a><a id="9928" href="Overture.Extensionality.html#9921" class="Bound">𝓤</a> <a id="9930" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9932" href="Overture.Extensionality.html#9923" class="Bound">𝓦</a><a id="9933" class="Symbol">)</a><a id="9934" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9936" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9939" href="Overture.Extensionality.html#9908" class="Function">hfunext</a> <a id="9947" href="Overture.Extensionality.html#9947" class="Bound">𝓤</a> <a id="9949" href="Overture.Extensionality.html#9949" class="Bound">𝓦</a> <a id="9951" class="Symbol">=</a> <a id="9953" class="Symbol">{</a><a id="9954" href="Overture.Extensionality.html#9954" class="Bound">A</a> <a id="9956" class="Symbol">:</a> <a id="9958" href="Overture.Extensionality.html#9947" class="Bound">𝓤</a> <a id="9960" href="Universes.html#403" class="Function Operator">̇</a><a id="9961" class="Symbol">}{</a><a id="9963" href="Overture.Extensionality.html#9963" class="Bound">B</a> <a id="9965" class="Symbol">:</a> <a id="9967" href="Overture.Extensionality.html#9954" class="Bound">A</a> <a id="9969" class="Symbol">→</a> <a id="9971" href="Overture.Extensionality.html#9949" class="Bound">𝓦</a> <a id="9973" href="Universes.html#403" class="Function Operator">̇</a><a id="9974" class="Symbol">}</a> <a id="9976" class="Symbol">(</a><a id="9977" href="Overture.Extensionality.html#9977" class="Bound">f</a> <a id="9979" href="Overture.Extensionality.html#9979" class="Bound">g</a> <a id="9981" class="Symbol">:</a> <a id="9983" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9985" href="Overture.Extensionality.html#9963" class="Bound">B</a><a id="9986" class="Symbol">)</a> <a id="9988" class="Symbol">→</a> <a id="9990" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="9999" class="Symbol">(</a><a id="10000" href="Overture.Extensionality.html#6333" class="Function">extdfun</a> <a id="10008" href="Overture.Extensionality.html#9977" class="Bound">f</a> <a id="10010" href="Overture.Extensionality.html#9979" class="Bound">g</a><a id="10011" class="Symbol">)</a>
<a id="10013" class="Keyword">open</a> <a id="10018" class="Keyword">import</a> <a id="10025" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10053" class="Keyword">using</a> <a id="10059" class="Symbol">(</a><a id="10060" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10067" class="Symbol">)</a> <a id="10069" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>3</sup> <span class="footnote" id="fn3"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>4</sup><span class="footnote" id="fn4">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

<br>
<br>

[← Overture.Equality](Overture.Equality.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
