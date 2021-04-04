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

<a id="3001" class="Keyword">open</a> <a id="3006" class="Keyword">import</a> <a id="3013" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3022" class="Keyword">using</a> <a id="3028" class="Symbol">(</a><a id="3029" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3032" class="Symbol">)</a> <a id="3034" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside a hidden submodule, and import the original definition below.)

<pre class="Agda">

<a id="3492" class="Keyword">module</a> <a id="hide-funext"></a><a id="3499" href="Overture.Extensionality.html#3499" class="Module">hide-funext</a> <a id="3511" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3519" href="Overture.Extensionality.html#3519" class="Function">funext</a> <a id="3526" class="Symbol">:</a> <a id="3528" class="Symbol">∀</a> <a id="3530" href="Overture.Extensionality.html#3530" class="Bound">𝓤</a> <a id="3532" href="Overture.Extensionality.html#3532" class="Bound">𝓦</a>  <a id="3535" class="Symbol">→</a> <a id="3537" href="Overture.Extensionality.html#3530" class="Bound">𝓤</a> <a id="3539" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3541" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3543" href="Overture.Extensionality.html#3532" class="Bound">𝓦</a> <a id="3545" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3547" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3550" href="Overture.Extensionality.html#3519" class="Function">funext</a> <a id="3557" href="Overture.Extensionality.html#3557" class="Bound">𝓤</a> <a id="3559" href="Overture.Extensionality.html#3559" class="Bound">𝓦</a> <a id="3561" class="Symbol">=</a> <a id="3563" class="Symbol">{</a><a id="3564" href="Overture.Extensionality.html#3564" class="Bound">A</a> <a id="3566" class="Symbol">:</a> <a id="3568" href="Overture.Extensionality.html#3557" class="Bound">𝓤</a> <a id="3570" href="Universes.html#403" class="Function Operator">̇</a> <a id="3572" class="Symbol">}</a> <a id="3574" class="Symbol">{</a><a id="3575" href="Overture.Extensionality.html#3575" class="Bound">B</a> <a id="3577" class="Symbol">:</a> <a id="3579" href="Overture.Extensionality.html#3559" class="Bound">𝓦</a> <a id="3581" href="Universes.html#403" class="Function Operator">̇</a> <a id="3583" class="Symbol">}</a> <a id="3585" class="Symbol">{</a><a id="3586" href="Overture.Extensionality.html#3586" class="Bound">f</a> <a id="3588" href="Overture.Extensionality.html#3588" class="Bound">g</a> <a id="3590" class="Symbol">:</a> <a id="3592" href="Overture.Extensionality.html#3564" class="Bound">A</a> <a id="3594" class="Symbol">→</a> <a id="3596" href="Overture.Extensionality.html#3575" class="Bound">B</a><a id="3597" class="Symbol">}</a> <a id="3599" class="Symbol">→</a> <a id="3601" href="Overture.Extensionality.html#3586" class="Bound">f</a> <a id="3603" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3605" href="Overture.Extensionality.html#3588" class="Bound">g</a> <a id="3607" class="Symbol">→</a> <a id="3609" href="Overture.Extensionality.html#3586" class="Bound">f</a> <a id="3611" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3613" href="Overture.Extensionality.html#3588" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3724" href="Overture.Extensionality.html#3724" class="Function">dfunext</a> <a id="3732" class="Symbol">:</a> <a id="3734" class="Symbol">∀</a> <a id="3736" href="Overture.Extensionality.html#3736" class="Bound">𝓤</a> <a id="3738" href="Overture.Extensionality.html#3738" class="Bound">𝓦</a> <a id="3740" class="Symbol">→</a> <a id="3742" href="Overture.Extensionality.html#3736" class="Bound">𝓤</a> <a id="3744" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3746" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3748" href="Overture.Extensionality.html#3738" class="Bound">𝓦</a> <a id="3750" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3752" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3755" href="Overture.Extensionality.html#3724" class="Function">dfunext</a> <a id="3763" href="Overture.Extensionality.html#3763" class="Bound">𝓤</a> <a id="3765" href="Overture.Extensionality.html#3765" class="Bound">𝓦</a> <a id="3767" class="Symbol">=</a> <a id="3769" class="Symbol">{</a><a id="3770" href="Overture.Extensionality.html#3770" class="Bound">A</a> <a id="3772" class="Symbol">:</a> <a id="3774" href="Overture.Extensionality.html#3763" class="Bound">𝓤</a> <a id="3776" href="Universes.html#403" class="Function Operator">̇</a> <a id="3778" class="Symbol">}{</a><a id="3780" href="Overture.Extensionality.html#3780" class="Bound">B</a> <a id="3782" class="Symbol">:</a> <a id="3784" href="Overture.Extensionality.html#3770" class="Bound">A</a> <a id="3786" class="Symbol">→</a> <a id="3788" href="Overture.Extensionality.html#3765" class="Bound">𝓦</a> <a id="3790" href="Universes.html#403" class="Function Operator">̇</a> <a id="3792" class="Symbol">}{</a><a id="3794" href="Overture.Extensionality.html#3794" class="Bound">f</a> <a id="3796" href="Overture.Extensionality.html#3796" class="Bound">g</a> <a id="3798" class="Symbol">:</a> <a id="3800" class="Symbol">∀(</a><a id="3802" href="Overture.Extensionality.html#3802" class="Bound">x</a> <a id="3804" class="Symbol">:</a> <a id="3806" href="Overture.Extensionality.html#3770" class="Bound">A</a><a id="3807" class="Symbol">)</a> <a id="3809" class="Symbol">→</a> <a id="3811" href="Overture.Extensionality.html#3780" class="Bound">B</a> <a id="3813" href="Overture.Extensionality.html#3802" class="Bound">x</a><a id="3814" class="Symbol">}</a> <a id="3816" class="Symbol">→</a>  <a id="3819" href="Overture.Extensionality.html#3794" class="Bound">f</a> <a id="3821" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3823" href="Overture.Extensionality.html#3796" class="Bound">g</a>  <a id="3826" class="Symbol">→</a>  <a id="3829" href="Overture.Extensionality.html#3794" class="Bound">f</a> <a id="3831" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3833" href="Overture.Extensionality.html#3796" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="4619" class="Keyword">open</a> <a id="4624" class="Keyword">import</a> <a id="4631" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="4658" class="Keyword">using</a> <a id="4664" class="Symbol">(</a><a id="4665" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="4671" class="Symbol">;</a> <a id="4673" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="4680" class="Symbol">)</a> <a id="4682" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.  Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Escardó denote this universe by 𝓤ω (which is an alias for Agda's `Setω` universe).<sup>[3](Overture.Extensionality.html#fn3)</sup> The types `global-funext` and `global-dfunext` defined in the [Type Topology][] library are the following.

<pre class="Agda">

<a id="5509" class="Keyword">module</a> <a id="hide-global-funext"></a><a id="5516" href="Overture.Extensionality.html#5516" class="Module">hide-global-funext</a> <a id="5535" class="Keyword">where</a>

 <a id="hide-global-funext.global-funext"></a><a id="5543" href="Overture.Extensionality.html#5543" class="Function">global-funext</a> <a id="5557" class="Symbol">:</a> <a id="5559" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5563" href="Overture.Extensionality.html#5543" class="Function">global-funext</a> <a id="5577" class="Symbol">=</a> <a id="5579" class="Symbol">∀</a>  <a id="5582" class="Symbol">{</a><a id="5583" href="Overture.Extensionality.html#5583" class="Bound">𝓤</a> <a id="5585" href="Overture.Extensionality.html#5585" class="Bound">𝓥</a><a id="5586" class="Symbol">}</a> <a id="5588" class="Symbol">→</a> <a id="5590" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a> <a id="5597" href="Overture.Extensionality.html#5583" class="Bound">𝓤</a> <a id="5599" href="Overture.Extensionality.html#5585" class="Bound">𝓥</a>

 <a id="hide-global-funext.global-dfunext"></a><a id="5603" href="Overture.Extensionality.html#5603" class="Function">global-dfunext</a> <a id="5618" class="Symbol">:</a> <a id="5620" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5624" href="Overture.Extensionality.html#5603" class="Function">global-dfunext</a> <a id="5639" class="Symbol">=</a> <a id="5641" class="Symbol">∀</a> <a id="5643" class="Symbol">{</a><a id="5644" href="Overture.Extensionality.html#5644" class="Bound">𝓤</a> <a id="5646" href="Overture.Extensionality.html#5646" class="Bound">𝓥</a><a id="5647" class="Symbol">}</a> <a id="5649" class="Symbol">→</a> <a id="5651" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a> <a id="5659" href="Overture.Extensionality.html#5644" class="Bound">𝓤</a> <a id="5661" href="Overture.Extensionality.html#5646" class="Bound">𝓥</a>

</pre>


**ATTENTION!** (backward incompatibility)  
We have decided to remove from the latest version of the [UALib][] all instances of global function extensionality and limit ourselves to local applications of the principle.  This has the advantage of making transparent precisely how and where the library depends on function extensionality.  (It also prepares the way for moving to a univalence-based version of the library that we plan to undertake very soon.)  The price we pay for this precision is a library that is littered with many function extensionality postulates. We will try to clean this up in the near future (but ultimately we will probably remove all of these postulates in favor of *univalence*).



The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="extfun"></a><a id="6472" href="Overture.Extensionality.html#6472" class="Function">extfun</a> <a id="6479" class="Symbol">:</a> <a id="6481" class="Symbol">{</a><a id="6482" href="Overture.Extensionality.html#6482" class="Bound">A</a> <a id="6484" class="Symbol">:</a> <a id="6486" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6488" href="Universes.html#403" class="Function Operator">̇</a><a id="6489" class="Symbol">}{</a><a id="6491" href="Overture.Extensionality.html#6491" class="Bound">B</a> <a id="6493" class="Symbol">:</a> <a id="6495" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6497" href="Universes.html#403" class="Function Operator">̇</a><a id="6498" class="Symbol">}{</a><a id="6500" href="Overture.Extensionality.html#6500" class="Bound">f</a> <a id="6502" href="Overture.Extensionality.html#6502" class="Bound">g</a> <a id="6504" class="Symbol">:</a> <a id="6506" href="Overture.Extensionality.html#6482" class="Bound">A</a> <a id="6508" class="Symbol">→</a> <a id="6510" href="Overture.Extensionality.html#6491" class="Bound">B</a><a id="6511" class="Symbol">}</a> <a id="6513" class="Symbol">→</a> <a id="6515" href="Overture.Extensionality.html#6500" class="Bound">f</a> <a id="6517" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6519" href="Overture.Extensionality.html#6502" class="Bound">g</a>  <a id="6522" class="Symbol">→</a>  <a id="6525" href="Overture.Extensionality.html#6500" class="Bound">f</a> <a id="6527" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6529" href="Overture.Extensionality.html#6502" class="Bound">g</a>
<a id="6531" href="Overture.Extensionality.html#6472" class="Function">extfun</a> <a id="6538" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6543" class="Symbol">_</a> <a id="6545" class="Symbol">=</a> <a id="6547" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6673" href="Overture.Extensionality.html#6673" class="Function">extdfun</a> <a id="6681" class="Symbol">:</a> <a id="6683" class="Symbol">{</a><a id="6684" href="Overture.Extensionality.html#6684" class="Bound">A</a> <a id="6686" class="Symbol">:</a> <a id="6688" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6690" href="Universes.html#403" class="Function Operator">̇</a> <a id="6692" class="Symbol">}{</a><a id="6694" href="Overture.Extensionality.html#6694" class="Bound">B</a> <a id="6696" class="Symbol">:</a> <a id="6698" href="Overture.Extensionality.html#6684" class="Bound">A</a> <a id="6700" class="Symbol">→</a> <a id="6702" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6704" href="Universes.html#403" class="Function Operator">̇</a> <a id="6706" class="Symbol">}(</a><a id="6708" href="Overture.Extensionality.html#6708" class="Bound">f</a> <a id="6710" href="Overture.Extensionality.html#6710" class="Bound">g</a> <a id="6712" class="Symbol">:</a> <a id="6714" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6716" href="Overture.Extensionality.html#6694" class="Bound">B</a><a id="6717" class="Symbol">)</a> <a id="6719" class="Symbol">→</a> <a id="6721" href="Overture.Extensionality.html#6708" class="Bound">f</a> <a id="6723" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6725" href="Overture.Extensionality.html#6710" class="Bound">g</a> <a id="6727" class="Symbol">→</a> <a id="6729" href="Overture.Extensionality.html#6708" class="Bound">f</a> <a id="6731" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6733" href="Overture.Extensionality.html#6710" class="Bound">g</a>
<a id="6735" href="Overture.Extensionality.html#6673" class="Function">extdfun</a> <a id="6743" class="Symbol">_</a> <a id="6745" class="Symbol">_</a> <a id="6747" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6752" class="Symbol">_</a> <a id="6754" class="Symbol">=</a> <a id="6756" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.

In the definition of `funext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `funext` is an assertion (which may or may not hold). In the definition of `extfun`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `extfun` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

<pre class="Agda">

<a id="8729" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8736" href="Overture.Extensionality.html#8736" class="Module">hide-tt-defs</a> <a id="8749" class="Symbol">{</a><a id="8750" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8752" class="Symbol">:</a> <a id="8754" href="Universes.html#205" class="Postulate">Universe</a><a id="8762" class="Symbol">}</a> <a id="8764" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8772" href="Overture.Extensionality.html#8772" class="Function">is-center</a> <a id="8782" class="Symbol">:</a> <a id="8784" class="Symbol">(</a><a id="8785" href="Overture.Extensionality.html#8785" class="Bound">A</a> <a id="8787" class="Symbol">:</a> <a id="8789" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8791" href="Universes.html#403" class="Function Operator">̇</a> <a id="8793" class="Symbol">)</a> <a id="8795" class="Symbol">→</a> <a id="8797" href="Overture.Extensionality.html#8785" class="Bound">A</a> <a id="8799" class="Symbol">→</a> <a id="8801" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8803" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8806" href="Overture.Extensionality.html#8772" class="Function">is-center</a> <a id="8816" href="Overture.Extensionality.html#8816" class="Bound">A</a> <a id="8818" href="Overture.Extensionality.html#8818" class="Bound">c</a> <a id="8820" class="Symbol">=</a> <a id="8822" class="Symbol">(</a><a id="8823" href="Overture.Extensionality.html#8823" class="Bound">x</a> <a id="8825" class="Symbol">:</a> <a id="8827" href="Overture.Extensionality.html#8816" class="Bound">A</a><a id="8828" class="Symbol">)</a> <a id="8830" class="Symbol">→</a> <a id="8832" href="Overture.Extensionality.html#8818" class="Bound">c</a> <a id="8834" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8836" href="Overture.Extensionality.html#8823" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8840" href="Overture.Extensionality.html#8840" class="Function">is-singleton</a> <a id="8853" class="Symbol">:</a> <a id="8855" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8857" href="Universes.html#403" class="Function Operator">̇</a> <a id="8859" class="Symbol">→</a> <a id="8861" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8863" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8866" href="Overture.Extensionality.html#8840" class="Function">is-singleton</a> <a id="8879" href="Overture.Extensionality.html#8879" class="Bound">A</a> <a id="8881" class="Symbol">=</a> <a id="8883" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8885" href="Overture.Extensionality.html#8885" class="Bound">c</a> <a id="8887" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8889" href="Overture.Extensionality.html#8879" class="Bound">A</a> <a id="8891" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8893" href="Overture.Extensionality.html#8772" class="Function">is-center</a> <a id="8903" href="Overture.Extensionality.html#8879" class="Bound">A</a> <a id="8905" href="Overture.Extensionality.html#8885" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8909" href="Overture.Extensionality.html#8909" class="Function">is-subsingleton</a> <a id="8925" class="Symbol">:</a> <a id="8927" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8929" href="Universes.html#403" class="Function Operator">̇</a> <a id="8931" class="Symbol">→</a> <a id="8933" href="Overture.Extensionality.html#8750" class="Bound">𝓤</a> <a id="8935" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8938" href="Overture.Extensionality.html#8909" class="Function">is-subsingleton</a> <a id="8954" href="Overture.Extensionality.html#8954" class="Bound">A</a> <a id="8956" class="Symbol">=</a> <a id="8958" class="Symbol">(</a><a id="8959" href="Overture.Extensionality.html#8959" class="Bound">x</a> <a id="8961" href="Overture.Extensionality.html#8961" class="Bound">y</a> <a id="8963" class="Symbol">:</a> <a id="8965" href="Overture.Extensionality.html#8954" class="Bound">A</a><a id="8966" class="Symbol">)</a> <a id="8968" class="Symbol">→</a> <a id="8970" href="Overture.Extensionality.html#8959" class="Bound">x</a> <a id="8972" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8974" href="Overture.Extensionality.html#8961" class="Bound">y</a>

<a id="8977" class="Keyword">open</a> <a id="8982" class="Keyword">import</a> <a id="8989" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9002" class="Keyword">using</a> <a id="9008" class="Symbol">(</a><a id="9009" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9018" class="Symbol">;</a> <a id="9020" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9032" class="Symbol">;</a> <a id="9034" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9049" class="Symbol">)</a> <a id="9051" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9468" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9475" href="Overture.Extensionality.html#9475" class="Module">hide-tt-defs&#39;</a> <a id="9489" class="Symbol">{</a><a id="9490" href="Overture.Extensionality.html#9490" class="Bound">𝓤</a> <a id="9492" href="Overture.Extensionality.html#9492" class="Bound">𝓦</a> <a id="9494" class="Symbol">:</a> <a id="9496" href="Universes.html#205" class="Postulate">Universe</a><a id="9504" class="Symbol">}</a> <a id="9506" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9514" href="Overture.Extensionality.html#9514" class="Function">fiber</a> <a id="9520" class="Symbol">:</a> <a id="9522" class="Symbol">{</a><a id="9523" href="Overture.Extensionality.html#9523" class="Bound">A</a> <a id="9525" class="Symbol">:</a> <a id="9527" href="Overture.Extensionality.html#9490" class="Bound">𝓤</a> <a id="9529" href="Universes.html#403" class="Function Operator">̇</a> <a id="9531" class="Symbol">}</a> <a id="9533" class="Symbol">{</a><a id="9534" href="Overture.Extensionality.html#9534" class="Bound">B</a> <a id="9536" class="Symbol">:</a> <a id="9538" href="Overture.Extensionality.html#9492" class="Bound">𝓦</a> <a id="9540" href="Universes.html#403" class="Function Operator">̇</a> <a id="9542" class="Symbol">}</a> <a id="9544" class="Symbol">(</a><a id="9545" href="Overture.Extensionality.html#9545" class="Bound">f</a> <a id="9547" class="Symbol">:</a> <a id="9549" href="Overture.Extensionality.html#9523" class="Bound">A</a> <a id="9551" class="Symbol">→</a> <a id="9553" href="Overture.Extensionality.html#9534" class="Bound">B</a><a id="9554" class="Symbol">)</a> <a id="9556" class="Symbol">→</a> <a id="9558" href="Overture.Extensionality.html#9534" class="Bound">B</a> <a id="9560" class="Symbol">→</a> <a id="9562" href="Overture.Extensionality.html#9490" class="Bound">𝓤</a> <a id="9564" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9566" href="Overture.Extensionality.html#9492" class="Bound">𝓦</a> <a id="9568" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9571" href="Overture.Extensionality.html#9514" class="Function">fiber</a> <a id="9577" class="Symbol">{</a><a id="9578" href="Overture.Extensionality.html#9578" class="Bound">A</a><a id="9579" class="Symbol">}</a> <a id="9581" href="Overture.Extensionality.html#9581" class="Bound">f</a> <a id="9583" href="Overture.Extensionality.html#9583" class="Bound">y</a> <a id="9585" class="Symbol">=</a> <a id="9587" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9589" href="Overture.Extensionality.html#9589" class="Bound">x</a> <a id="9591" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9593" href="Overture.Extensionality.html#9578" class="Bound">A</a> <a id="9595" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9597" href="Overture.Extensionality.html#9581" class="Bound">f</a> <a id="9599" href="Overture.Extensionality.html#9589" class="Bound">x</a> <a id="9601" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="9603" href="Overture.Extensionality.html#9583" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9709" href="Overture.Extensionality.html#9709" class="Function">is-equiv</a> <a id="9718" class="Symbol">:</a> <a id="9720" class="Symbol">{</a><a id="9721" href="Overture.Extensionality.html#9721" class="Bound">A</a> <a id="9723" class="Symbol">:</a> <a id="9725" href="Overture.Extensionality.html#9490" class="Bound">𝓤</a> <a id="9727" href="Universes.html#403" class="Function Operator">̇</a> <a id="9729" class="Symbol">}</a> <a id="9731" class="Symbol">{</a><a id="9732" href="Overture.Extensionality.html#9732" class="Bound">B</a> <a id="9734" class="Symbol">:</a> <a id="9736" href="Overture.Extensionality.html#9492" class="Bound">𝓦</a> <a id="9738" href="Universes.html#403" class="Function Operator">̇</a> <a id="9740" class="Symbol">}</a> <a id="9742" class="Symbol">→</a> <a id="9744" class="Symbol">(</a><a id="9745" href="Overture.Extensionality.html#9721" class="Bound">A</a> <a id="9747" class="Symbol">→</a> <a id="9749" href="Overture.Extensionality.html#9732" class="Bound">B</a><a id="9750" class="Symbol">)</a> <a id="9752" class="Symbol">→</a> <a id="9754" href="Overture.Extensionality.html#9490" class="Bound">𝓤</a> <a id="9756" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9758" href="Overture.Extensionality.html#9492" class="Bound">𝓦</a> <a id="9760" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9763" href="Overture.Extensionality.html#9709" class="Function">is-equiv</a> <a id="9772" href="Overture.Extensionality.html#9772" class="Bound">f</a> <a id="9774" class="Symbol">=</a> <a id="9776" class="Symbol">∀</a> <a id="9778" href="Overture.Extensionality.html#9778" class="Bound">y</a> <a id="9780" class="Symbol">→</a> <a id="9782" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9795" class="Symbol">(</a><a id="9796" href="Overture.Extensionality.html#9514" class="Function">fiber</a> <a id="9802" href="Overture.Extensionality.html#9772" class="Bound">f</a> <a id="9804" href="Overture.Extensionality.html#9778" class="Bound">y</a><a id="9805" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="10012" class="Keyword">open</a> <a id="10017" class="Keyword">import</a> <a id="10024" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10041" class="Keyword">using</a> <a id="10047" class="Symbol">(</a><a id="10048" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10053" class="Symbol">;</a> <a id="10055" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10063" class="Symbol">)</a> <a id="10065" class="Keyword">public</a>

<a id="10073" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10080" href="Overture.Extensionality.html#10080" class="Module">hide-hfunext</a> <a id="10093" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10101" href="Overture.Extensionality.html#10101" class="Function">hfunext</a> <a id="10109" class="Symbol">:</a>  <a id="10112" class="Symbol">∀</a> <a id="10114" href="Overture.Extensionality.html#10114" class="Bound">𝓤</a> <a id="10116" href="Overture.Extensionality.html#10116" class="Bound">𝓦</a> <a id="10118" class="Symbol">→</a> <a id="10120" class="Symbol">(</a><a id="10121" href="Overture.Extensionality.html#10114" class="Bound">𝓤</a> <a id="10123" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10125" href="Overture.Extensionality.html#10116" class="Bound">𝓦</a><a id="10126" class="Symbol">)</a><a id="10127" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="10129" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10132" href="Overture.Extensionality.html#10101" class="Function">hfunext</a> <a id="10140" href="Overture.Extensionality.html#10140" class="Bound">𝓤</a> <a id="10142" href="Overture.Extensionality.html#10142" class="Bound">𝓦</a> <a id="10144" class="Symbol">=</a> <a id="10146" class="Symbol">{</a><a id="10147" href="Overture.Extensionality.html#10147" class="Bound">A</a> <a id="10149" class="Symbol">:</a> <a id="10151" href="Overture.Extensionality.html#10140" class="Bound">𝓤</a> <a id="10153" href="Universes.html#403" class="Function Operator">̇</a><a id="10154" class="Symbol">}{</a><a id="10156" href="Overture.Extensionality.html#10156" class="Bound">B</a> <a id="10158" class="Symbol">:</a> <a id="10160" href="Overture.Extensionality.html#10147" class="Bound">A</a> <a id="10162" class="Symbol">→</a> <a id="10164" href="Overture.Extensionality.html#10142" class="Bound">𝓦</a> <a id="10166" href="Universes.html#403" class="Function Operator">̇</a><a id="10167" class="Symbol">}</a> <a id="10169" class="Symbol">(</a><a id="10170" href="Overture.Extensionality.html#10170" class="Bound">f</a> <a id="10172" href="Overture.Extensionality.html#10172" class="Bound">g</a> <a id="10174" class="Symbol">:</a> <a id="10176" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10178" href="Overture.Extensionality.html#10156" class="Bound">B</a><a id="10179" class="Symbol">)</a> <a id="10181" class="Symbol">→</a> <a id="10183" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10192" class="Symbol">(</a><a id="10193" href="Overture.Extensionality.html#6673" class="Function">extdfun</a> <a id="10201" href="Overture.Extensionality.html#10170" class="Bound">f</a> <a id="10203" href="Overture.Extensionality.html#10172" class="Bound">g</a><a id="10204" class="Symbol">)</a>

<a id="10207" class="Keyword">open</a> <a id="10212" class="Keyword">import</a> <a id="10219" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10246" class="Keyword">using</a> <a id="10252" class="Symbol">(</a><a id="10253" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10260" class="Symbol">)</a> <a id="10262" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>

<sup>3</sup> <span class="footnote" id="fn3"> For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).

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
