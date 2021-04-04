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

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, and import the original definition below.)

<pre class="Agda">

<a id="3501" class="Keyword">module</a> <a id="hide-funext"></a><a id="3508" href="Overture.Extensionality.html#3508" class="Module">hide-funext</a> <a id="3520" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3528" href="Overture.Extensionality.html#3528" class="Function">funext</a> <a id="3535" class="Symbol">:</a> <a id="3537" class="Symbol">∀</a> <a id="3539" href="Overture.Extensionality.html#3539" class="Bound">𝓤</a> <a id="3541" href="Overture.Extensionality.html#3541" class="Bound">𝓦</a>  <a id="3544" class="Symbol">→</a> <a id="3546" href="Overture.Extensionality.html#3539" class="Bound">𝓤</a> <a id="3548" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3550" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3552" href="Overture.Extensionality.html#3541" class="Bound">𝓦</a> <a id="3554" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3556" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3559" href="Overture.Extensionality.html#3528" class="Function">funext</a> <a id="3566" href="Overture.Extensionality.html#3566" class="Bound">𝓤</a> <a id="3568" href="Overture.Extensionality.html#3568" class="Bound">𝓦</a> <a id="3570" class="Symbol">=</a> <a id="3572" class="Symbol">{</a><a id="3573" href="Overture.Extensionality.html#3573" class="Bound">A</a> <a id="3575" class="Symbol">:</a> <a id="3577" href="Overture.Extensionality.html#3566" class="Bound">𝓤</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a> <a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">{</a><a id="3584" href="Overture.Extensionality.html#3584" class="Bound">B</a> <a id="3586" class="Symbol">:</a> <a id="3588" href="Overture.Extensionality.html#3568" class="Bound">𝓦</a> <a id="3590" href="Universes.html#403" class="Function Operator">̇</a> <a id="3592" class="Symbol">}</a> <a id="3594" class="Symbol">{</a><a id="3595" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3597" href="Overture.Extensionality.html#3597" class="Bound">g</a> <a id="3599" class="Symbol">:</a> <a id="3601" href="Overture.Extensionality.html#3573" class="Bound">A</a> <a id="3603" class="Symbol">→</a> <a id="3605" href="Overture.Extensionality.html#3584" class="Bound">B</a><a id="3606" class="Symbol">}</a> <a id="3608" class="Symbol">→</a> <a id="3610" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3612" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3614" href="Overture.Extensionality.html#3597" class="Bound">g</a> <a id="3616" class="Symbol">→</a> <a id="3618" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3620" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3622" href="Overture.Extensionality.html#3597" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3733" href="Overture.Extensionality.html#3733" class="Function">dfunext</a> <a id="3741" class="Symbol">:</a> <a id="3743" class="Symbol">∀</a> <a id="3745" href="Overture.Extensionality.html#3745" class="Bound">𝓤</a> <a id="3747" href="Overture.Extensionality.html#3747" class="Bound">𝓦</a> <a id="3749" class="Symbol">→</a> <a id="3751" href="Overture.Extensionality.html#3745" class="Bound">𝓤</a> <a id="3753" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3755" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3757" href="Overture.Extensionality.html#3747" class="Bound">𝓦</a> <a id="3759" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3761" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3764" href="Overture.Extensionality.html#3733" class="Function">dfunext</a> <a id="3772" href="Overture.Extensionality.html#3772" class="Bound">𝓤</a> <a id="3774" href="Overture.Extensionality.html#3774" class="Bound">𝓦</a> <a id="3776" class="Symbol">=</a> <a id="3778" class="Symbol">{</a><a id="3779" href="Overture.Extensionality.html#3779" class="Bound">A</a> <a id="3781" class="Symbol">:</a> <a id="3783" href="Overture.Extensionality.html#3772" class="Bound">𝓤</a> <a id="3785" href="Universes.html#403" class="Function Operator">̇</a> <a id="3787" class="Symbol">}{</a><a id="3789" href="Overture.Extensionality.html#3789" class="Bound">B</a> <a id="3791" class="Symbol">:</a> <a id="3793" href="Overture.Extensionality.html#3779" class="Bound">A</a> <a id="3795" class="Symbol">→</a> <a id="3797" href="Overture.Extensionality.html#3774" class="Bound">𝓦</a> <a id="3799" href="Universes.html#403" class="Function Operator">̇</a> <a id="3801" class="Symbol">}{</a><a id="3803" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3805" href="Overture.Extensionality.html#3805" class="Bound">g</a> <a id="3807" class="Symbol">:</a> <a id="3809" class="Symbol">∀(</a><a id="3811" href="Overture.Extensionality.html#3811" class="Bound">x</a> <a id="3813" class="Symbol">:</a> <a id="3815" href="Overture.Extensionality.html#3779" class="Bound">A</a><a id="3816" class="Symbol">)</a> <a id="3818" class="Symbol">→</a> <a id="3820" href="Overture.Extensionality.html#3789" class="Bound">B</a> <a id="3822" href="Overture.Extensionality.html#3811" class="Bound">x</a><a id="3823" class="Symbol">}</a> <a id="3825" class="Symbol">→</a>  <a id="3828" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3830" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3832" href="Overture.Extensionality.html#3805" class="Bound">g</a>  <a id="3835" class="Symbol">→</a>  <a id="3838" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3840" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3842" href="Overture.Extensionality.html#3805" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="4628" class="Keyword">open</a> <a id="4633" class="Keyword">import</a> <a id="4640" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="4667" class="Keyword">using</a> <a id="4673" class="Symbol">(</a><a id="4674" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="4680" class="Symbol">;</a> <a id="4682" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="4689" class="Symbol">)</a> <a id="4691" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.  Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Escardó denote this universe by 𝓤ω (which is an alias for Agda's `Setω` universe).<sup>[3](Overture.Extensionality.html#fn3)</sup> The types `global-funext` and `global-dfunext` defined in the [Type Topology][] library are the following.

<pre class="Agda">

<a id="5518" class="Keyword">module</a> <a id="hide-global-funext"></a><a id="5525" href="Overture.Extensionality.html#5525" class="Module">hide-global-funext</a> <a id="5544" class="Keyword">where</a>

 <a id="hide-global-funext.global-funext"></a><a id="5552" href="Overture.Extensionality.html#5552" class="Function">global-funext</a> <a id="5566" class="Symbol">:</a> <a id="5568" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5572" href="Overture.Extensionality.html#5552" class="Function">global-funext</a> <a id="5586" class="Symbol">=</a> <a id="5588" class="Symbol">∀</a>  <a id="5591" class="Symbol">{</a><a id="5592" href="Overture.Extensionality.html#5592" class="Bound">𝓤</a> <a id="5594" href="Overture.Extensionality.html#5594" class="Bound">𝓥</a><a id="5595" class="Symbol">}</a> <a id="5597" class="Symbol">→</a> <a id="5599" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a> <a id="5606" href="Overture.Extensionality.html#5592" class="Bound">𝓤</a> <a id="5608" href="Overture.Extensionality.html#5594" class="Bound">𝓥</a>

 <a id="hide-global-funext.global-dfunext"></a><a id="5612" href="Overture.Extensionality.html#5612" class="Function">global-dfunext</a> <a id="5627" class="Symbol">:</a> <a id="5629" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5633" href="Overture.Extensionality.html#5612" class="Function">global-dfunext</a> <a id="5648" class="Symbol">=</a> <a id="5650" class="Symbol">∀</a> <a id="5652" class="Symbol">{</a><a id="5653" href="Overture.Extensionality.html#5653" class="Bound">𝓤</a> <a id="5655" href="Overture.Extensionality.html#5655" class="Bound">𝓥</a><a id="5656" class="Symbol">}</a> <a id="5658" class="Symbol">→</a> <a id="5660" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a> <a id="5668" href="Overture.Extensionality.html#5653" class="Bound">𝓤</a> <a id="5670" href="Overture.Extensionality.html#5655" class="Bound">𝓥</a>

</pre>


**ATTENTION!** (backward incompatibility)  
We have decided to remove from the latest version of the [UALib][] all instances of global function extensionality and limit ourselves to local applications of the principle.  This has the advantage of making transparent precisely how and where the library depends on function extensionality.  (It also prepares the way for moving to a univalence-based version of the library that we plan to undertake very soon.)  The price we pay for this precision is a library that is littered with many function extensionality postulates. We will try to clean this up in the near future (but ultimately we will probably remove all of these postulates in favor of *univalence*).



The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="extfun"></a><a id="6481" href="Overture.Extensionality.html#6481" class="Function">extfun</a> <a id="6488" class="Symbol">:</a> <a id="6490" class="Symbol">{</a><a id="6491" href="Overture.Extensionality.html#6491" class="Bound">A</a> <a id="6493" class="Symbol">:</a> <a id="6495" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6497" href="Universes.html#403" class="Function Operator">̇</a><a id="6498" class="Symbol">}{</a><a id="6500" href="Overture.Extensionality.html#6500" class="Bound">B</a> <a id="6502" class="Symbol">:</a> <a id="6504" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6506" href="Universes.html#403" class="Function Operator">̇</a><a id="6507" class="Symbol">}{</a><a id="6509" href="Overture.Extensionality.html#6509" class="Bound">f</a> <a id="6511" href="Overture.Extensionality.html#6511" class="Bound">g</a> <a id="6513" class="Symbol">:</a> <a id="6515" href="Overture.Extensionality.html#6491" class="Bound">A</a> <a id="6517" class="Symbol">→</a> <a id="6519" href="Overture.Extensionality.html#6500" class="Bound">B</a><a id="6520" class="Symbol">}</a> <a id="6522" class="Symbol">→</a> <a id="6524" href="Overture.Extensionality.html#6509" class="Bound">f</a> <a id="6526" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6528" href="Overture.Extensionality.html#6511" class="Bound">g</a>  <a id="6531" class="Symbol">→</a>  <a id="6534" href="Overture.Extensionality.html#6509" class="Bound">f</a> <a id="6536" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6538" href="Overture.Extensionality.html#6511" class="Bound">g</a>
<a id="6540" href="Overture.Extensionality.html#6481" class="Function">extfun</a> <a id="6547" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6552" class="Symbol">_</a> <a id="6554" class="Symbol">=</a> <a id="6556" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6682" href="Overture.Extensionality.html#6682" class="Function">extdfun</a> <a id="6690" class="Symbol">:</a> <a id="6692" class="Symbol">{</a><a id="6693" href="Overture.Extensionality.html#6693" class="Bound">A</a> <a id="6695" class="Symbol">:</a> <a id="6697" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6699" href="Universes.html#403" class="Function Operator">̇</a> <a id="6701" class="Symbol">}{</a><a id="6703" href="Overture.Extensionality.html#6703" class="Bound">B</a> <a id="6705" class="Symbol">:</a> <a id="6707" href="Overture.Extensionality.html#6693" class="Bound">A</a> <a id="6709" class="Symbol">→</a> <a id="6711" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6713" href="Universes.html#403" class="Function Operator">̇</a> <a id="6715" class="Symbol">}(</a><a id="6717" href="Overture.Extensionality.html#6717" class="Bound">f</a> <a id="6719" href="Overture.Extensionality.html#6719" class="Bound">g</a> <a id="6721" class="Symbol">:</a> <a id="6723" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6725" href="Overture.Extensionality.html#6703" class="Bound">B</a><a id="6726" class="Symbol">)</a> <a id="6728" class="Symbol">→</a> <a id="6730" href="Overture.Extensionality.html#6717" class="Bound">f</a> <a id="6732" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6734" href="Overture.Extensionality.html#6719" class="Bound">g</a> <a id="6736" class="Symbol">→</a> <a id="6738" href="Overture.Extensionality.html#6717" class="Bound">f</a> <a id="6740" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6742" href="Overture.Extensionality.html#6719" class="Bound">g</a>
<a id="6744" href="Overture.Extensionality.html#6682" class="Function">extdfun</a> <a id="6752" class="Symbol">_</a> <a id="6754" class="Symbol">_</a> <a id="6756" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6761" class="Symbol">_</a> <a id="6763" class="Symbol">=</a> <a id="6765" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.

In the definition of `funext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `funext` is an assertion (which may or may not hold). In the definition of `extfun`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `extfun` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8657" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8664" href="Overture.Extensionality.html#8664" class="Module">hide-tt-defs</a> <a id="8677" class="Symbol">{</a><a id="8678" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8680" class="Symbol">:</a> <a id="8682" href="Universes.html#205" class="Postulate">Universe</a><a id="8690" class="Symbol">}</a> <a id="8692" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8700" href="Overture.Extensionality.html#8700" class="Function">is-center</a> <a id="8710" class="Symbol">:</a> <a id="8712" class="Symbol">(</a><a id="8713" href="Overture.Extensionality.html#8713" class="Bound">A</a> <a id="8715" class="Symbol">:</a> <a id="8717" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8719" href="Universes.html#403" class="Function Operator">̇</a> <a id="8721" class="Symbol">)</a> <a id="8723" class="Symbol">→</a> <a id="8725" href="Overture.Extensionality.html#8713" class="Bound">A</a> <a id="8727" class="Symbol">→</a> <a id="8729" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8731" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8734" href="Overture.Extensionality.html#8700" class="Function">is-center</a> <a id="8744" href="Overture.Extensionality.html#8744" class="Bound">A</a> <a id="8746" href="Overture.Extensionality.html#8746" class="Bound">c</a> <a id="8748" class="Symbol">=</a> <a id="8750" class="Symbol">(</a><a id="8751" href="Overture.Extensionality.html#8751" class="Bound">x</a> <a id="8753" class="Symbol">:</a> <a id="8755" href="Overture.Extensionality.html#8744" class="Bound">A</a><a id="8756" class="Symbol">)</a> <a id="8758" class="Symbol">→</a> <a id="8760" href="Overture.Extensionality.html#8746" class="Bound">c</a> <a id="8762" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8764" href="Overture.Extensionality.html#8751" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8768" href="Overture.Extensionality.html#8768" class="Function">is-singleton</a> <a id="8781" class="Symbol">:</a> <a id="8783" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8785" href="Universes.html#403" class="Function Operator">̇</a> <a id="8787" class="Symbol">→</a> <a id="8789" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8791" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8794" href="Overture.Extensionality.html#8768" class="Function">is-singleton</a> <a id="8807" href="Overture.Extensionality.html#8807" class="Bound">A</a> <a id="8809" class="Symbol">=</a> <a id="8811" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8813" href="Overture.Extensionality.html#8813" class="Bound">c</a> <a id="8815" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8817" href="Overture.Extensionality.html#8807" class="Bound">A</a> <a id="8819" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8821" href="Overture.Extensionality.html#8700" class="Function">is-center</a> <a id="8831" href="Overture.Extensionality.html#8807" class="Bound">A</a> <a id="8833" href="Overture.Extensionality.html#8813" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8837" href="Overture.Extensionality.html#8837" class="Function">is-subsingleton</a> <a id="8853" class="Symbol">:</a> <a id="8855" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8857" href="Universes.html#403" class="Function Operator">̇</a> <a id="8859" class="Symbol">→</a> <a id="8861" href="Overture.Extensionality.html#8678" class="Bound">𝓤</a> <a id="8863" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8866" href="Overture.Extensionality.html#8837" class="Function">is-subsingleton</a> <a id="8882" href="Overture.Extensionality.html#8882" class="Bound">A</a> <a id="8884" class="Symbol">=</a> <a id="8886" class="Symbol">(</a><a id="8887" href="Overture.Extensionality.html#8887" class="Bound">x</a> <a id="8889" href="Overture.Extensionality.html#8889" class="Bound">y</a> <a id="8891" class="Symbol">:</a> <a id="8893" href="Overture.Extensionality.html#8882" class="Bound">A</a><a id="8894" class="Symbol">)</a> <a id="8896" class="Symbol">→</a> <a id="8898" href="Overture.Extensionality.html#8887" class="Bound">x</a> <a id="8900" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8902" href="Overture.Extensionality.html#8889" class="Bound">y</a>

</pre>

We import the original definitions of the last three types as follows. (The [first footnote](Overture.Equality.html#fn1) of [Overture.Equality][] explains why we both define and import certain types.)

<pre class="Agda">

<a id="9133" class="Keyword">open</a> <a id="9138" class="Keyword">import</a> <a id="9145" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9158" class="Keyword">using</a> <a id="9164" class="Symbol">(</a><a id="9165" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9174" class="Symbol">;</a> <a id="9176" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9188" class="Symbol">;</a> <a id="9190" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9205" class="Symbol">)</a> <a id="9207" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9624" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9631" href="Overture.Extensionality.html#9631" class="Module">hide-tt-defs&#39;</a> <a id="9645" class="Symbol">{</a><a id="9646" href="Overture.Extensionality.html#9646" class="Bound">𝓤</a> <a id="9648" href="Overture.Extensionality.html#9648" class="Bound">𝓦</a> <a id="9650" class="Symbol">:</a> <a id="9652" href="Universes.html#205" class="Postulate">Universe</a><a id="9660" class="Symbol">}</a> <a id="9662" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9670" href="Overture.Extensionality.html#9670" class="Function">fiber</a> <a id="9676" class="Symbol">:</a> <a id="9678" class="Symbol">{</a><a id="9679" href="Overture.Extensionality.html#9679" class="Bound">A</a> <a id="9681" class="Symbol">:</a> <a id="9683" href="Overture.Extensionality.html#9646" class="Bound">𝓤</a> <a id="9685" href="Universes.html#403" class="Function Operator">̇</a> <a id="9687" class="Symbol">}</a> <a id="9689" class="Symbol">{</a><a id="9690" href="Overture.Extensionality.html#9690" class="Bound">B</a> <a id="9692" class="Symbol">:</a> <a id="9694" href="Overture.Extensionality.html#9648" class="Bound">𝓦</a> <a id="9696" href="Universes.html#403" class="Function Operator">̇</a> <a id="9698" class="Symbol">}</a> <a id="9700" class="Symbol">(</a><a id="9701" href="Overture.Extensionality.html#9701" class="Bound">f</a> <a id="9703" class="Symbol">:</a> <a id="9705" href="Overture.Extensionality.html#9679" class="Bound">A</a> <a id="9707" class="Symbol">→</a> <a id="9709" href="Overture.Extensionality.html#9690" class="Bound">B</a><a id="9710" class="Symbol">)</a> <a id="9712" class="Symbol">→</a> <a id="9714" href="Overture.Extensionality.html#9690" class="Bound">B</a> <a id="9716" class="Symbol">→</a> <a id="9718" href="Overture.Extensionality.html#9646" class="Bound">𝓤</a> <a id="9720" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9722" href="Overture.Extensionality.html#9648" class="Bound">𝓦</a> <a id="9724" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9727" href="Overture.Extensionality.html#9670" class="Function">fiber</a> <a id="9733" class="Symbol">{</a><a id="9734" href="Overture.Extensionality.html#9734" class="Bound">A</a><a id="9735" class="Symbol">}</a> <a id="9737" href="Overture.Extensionality.html#9737" class="Bound">f</a> <a id="9739" href="Overture.Extensionality.html#9739" class="Bound">y</a> <a id="9741" class="Symbol">=</a> <a id="9743" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9745" href="Overture.Extensionality.html#9745" class="Bound">x</a> <a id="9747" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9749" href="Overture.Extensionality.html#9734" class="Bound">A</a> <a id="9751" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9753" href="Overture.Extensionality.html#9737" class="Bound">f</a> <a id="9755" href="Overture.Extensionality.html#9745" class="Bound">x</a> <a id="9757" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="9759" href="Overture.Extensionality.html#9739" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9865" href="Overture.Extensionality.html#9865" class="Function">is-equiv</a> <a id="9874" class="Symbol">:</a> <a id="9876" class="Symbol">{</a><a id="9877" href="Overture.Extensionality.html#9877" class="Bound">A</a> <a id="9879" class="Symbol">:</a> <a id="9881" href="Overture.Extensionality.html#9646" class="Bound">𝓤</a> <a id="9883" href="Universes.html#403" class="Function Operator">̇</a> <a id="9885" class="Symbol">}</a> <a id="9887" class="Symbol">{</a><a id="9888" href="Overture.Extensionality.html#9888" class="Bound">B</a> <a id="9890" class="Symbol">:</a> <a id="9892" href="Overture.Extensionality.html#9648" class="Bound">𝓦</a> <a id="9894" href="Universes.html#403" class="Function Operator">̇</a> <a id="9896" class="Symbol">}</a> <a id="9898" class="Symbol">→</a> <a id="9900" class="Symbol">(</a><a id="9901" href="Overture.Extensionality.html#9877" class="Bound">A</a> <a id="9903" class="Symbol">→</a> <a id="9905" href="Overture.Extensionality.html#9888" class="Bound">B</a><a id="9906" class="Symbol">)</a> <a id="9908" class="Symbol">→</a> <a id="9910" href="Overture.Extensionality.html#9646" class="Bound">𝓤</a> <a id="9912" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9914" href="Overture.Extensionality.html#9648" class="Bound">𝓦</a> <a id="9916" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9919" href="Overture.Extensionality.html#9865" class="Function">is-equiv</a> <a id="9928" href="Overture.Extensionality.html#9928" class="Bound">f</a> <a id="9930" class="Symbol">=</a> <a id="9932" class="Symbol">∀</a> <a id="9934" href="Overture.Extensionality.html#9934" class="Bound">y</a> <a id="9936" class="Symbol">→</a> <a id="9938" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9951" class="Symbol">(</a><a id="9952" href="Overture.Extensionality.html#9670" class="Function">fiber</a> <a id="9958" href="Overture.Extensionality.html#9928" class="Bound">f</a> <a id="9960" href="Overture.Extensionality.html#9934" class="Bound">y</a><a id="9961" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="10168" class="Keyword">open</a> <a id="10173" class="Keyword">import</a> <a id="10180" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10197" class="Keyword">using</a> <a id="10203" class="Symbol">(</a><a id="10204" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10209" class="Symbol">;</a> <a id="10211" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10219" class="Symbol">)</a> <a id="10221" class="Keyword">public</a>

<a id="10229" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10236" href="Overture.Extensionality.html#10236" class="Module">hide-hfunext</a> <a id="10249" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10257" href="Overture.Extensionality.html#10257" class="Function">hfunext</a> <a id="10265" class="Symbol">:</a>  <a id="10268" class="Symbol">∀</a> <a id="10270" href="Overture.Extensionality.html#10270" class="Bound">𝓤</a> <a id="10272" href="Overture.Extensionality.html#10272" class="Bound">𝓦</a> <a id="10274" class="Symbol">→</a> <a id="10276" class="Symbol">(</a><a id="10277" href="Overture.Extensionality.html#10270" class="Bound">𝓤</a> <a id="10279" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10281" href="Overture.Extensionality.html#10272" class="Bound">𝓦</a><a id="10282" class="Symbol">)</a><a id="10283" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="10285" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10288" href="Overture.Extensionality.html#10257" class="Function">hfunext</a> <a id="10296" href="Overture.Extensionality.html#10296" class="Bound">𝓤</a> <a id="10298" href="Overture.Extensionality.html#10298" class="Bound">𝓦</a> <a id="10300" class="Symbol">=</a> <a id="10302" class="Symbol">{</a><a id="10303" href="Overture.Extensionality.html#10303" class="Bound">A</a> <a id="10305" class="Symbol">:</a> <a id="10307" href="Overture.Extensionality.html#10296" class="Bound">𝓤</a> <a id="10309" href="Universes.html#403" class="Function Operator">̇</a><a id="10310" class="Symbol">}{</a><a id="10312" href="Overture.Extensionality.html#10312" class="Bound">B</a> <a id="10314" class="Symbol">:</a> <a id="10316" href="Overture.Extensionality.html#10303" class="Bound">A</a> <a id="10318" class="Symbol">→</a> <a id="10320" href="Overture.Extensionality.html#10298" class="Bound">𝓦</a> <a id="10322" href="Universes.html#403" class="Function Operator">̇</a><a id="10323" class="Symbol">}</a> <a id="10325" class="Symbol">(</a><a id="10326" href="Overture.Extensionality.html#10326" class="Bound">f</a> <a id="10328" href="Overture.Extensionality.html#10328" class="Bound">g</a> <a id="10330" class="Symbol">:</a> <a id="10332" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10334" href="Overture.Extensionality.html#10312" class="Bound">B</a><a id="10335" class="Symbol">)</a> <a id="10337" class="Symbol">→</a> <a id="10339" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10348" class="Symbol">(</a><a id="10349" href="Overture.Extensionality.html#6682" class="Function">extdfun</a> <a id="10357" href="Overture.Extensionality.html#10326" class="Bound">f</a> <a id="10359" href="Overture.Extensionality.html#10328" class="Bound">g</a><a id="10360" class="Symbol">)</a>

<a id="10363" class="Keyword">open</a> <a id="10368" class="Keyword">import</a> <a id="10375" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10402" class="Keyword">using</a> <a id="10408" class="Symbol">(</a><a id="10409" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10416" class="Symbol">)</a> <a id="10418" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

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
