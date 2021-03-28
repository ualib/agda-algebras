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

The natural notion of function equality, which is often called *point-wise equality*, is defined as follows: `∀ x → f x ≡ g x`.  Here is how this notion is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="2851" class="Keyword">module</a> <a id="hide-∼"></a><a id="2858" href="Overture.Extensionality.html#2858" class="Module">hide-∼</a> <a id="2865" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2873" href="Overture.Extensionality.html#2873" class="Function Operator">_∼_</a> <a id="2877" class="Symbol">:</a> <a id="2879" class="Symbol">{</a><a id="2880" href="Overture.Extensionality.html#2880" class="Bound">A</a> <a id="2882" class="Symbol">:</a> <a id="2884" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2886" href="Universes.html#403" class="Function Operator">̇</a> <a id="2888" class="Symbol">}</a> <a id="2890" class="Symbol">{</a><a id="2891" href="Overture.Extensionality.html#2891" class="Bound">B</a> <a id="2893" class="Symbol">:</a> <a id="2895" href="Overture.Extensionality.html#2880" class="Bound">A</a> <a id="2897" class="Symbol">→</a> <a id="2899" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2901" href="Universes.html#403" class="Function Operator">̇</a> <a id="2903" class="Symbol">}</a> <a id="2905" class="Symbol">→</a> <a id="2907" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2909" href="Overture.Extensionality.html#2891" class="Bound">B</a> <a id="2911" class="Symbol">→</a> <a id="2913" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2915" href="Overture.Extensionality.html#2891" class="Bound">B</a> <a id="2917" class="Symbol">→</a> <a id="2919" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2921" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2923" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2925" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2928" href="Overture.Extensionality.html#2928" class="Bound">f</a> <a id="2930" href="Overture.Extensionality.html#2873" class="Function Operator">∼</a> <a id="2932" href="Overture.Extensionality.html#2932" class="Bound">g</a> <a id="2934" class="Symbol">=</a> <a id="2936" class="Symbol">∀</a> <a id="2938" href="Overture.Extensionality.html#2938" class="Bound">x</a> <a id="2940" class="Symbol">→</a> <a id="2942" href="Overture.Extensionality.html#2928" class="Bound">f</a> <a id="2944" href="Overture.Extensionality.html#2938" class="Bound">x</a> <a id="2946" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="2948" href="Overture.Extensionality.html#2932" class="Bound">g</a> <a id="2950" href="Overture.Extensionality.html#2938" class="Bound">x</a>

 <a id="2954" class="Keyword">infix</a> <a id="2960" class="Number">0</a> <a id="2962" href="Overture.Extensionality.html#2873" class="Function Operator">_∼_</a>

<a id="2967" class="Keyword">open</a> <a id="2972" class="Keyword">import</a> <a id="2979" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="3006" class="Keyword">using</a> <a id="3012" class="Symbol">(</a><a id="3013" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3016" class="Symbol">)</a> <a id="3018" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, and import the original definition below.)

<pre class="Agda">

<a id="3485" class="Keyword">module</a> <a id="hide-funext"></a><a id="3492" href="Overture.Extensionality.html#3492" class="Module">hide-funext</a> <a id="3504" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3512" href="Overture.Extensionality.html#3512" class="Function">funext</a> <a id="3519" class="Symbol">:</a> <a id="3521" class="Symbol">∀</a> <a id="3523" href="Overture.Extensionality.html#3523" class="Bound">𝓤</a> <a id="3525" href="Overture.Extensionality.html#3525" class="Bound">𝓦</a>  <a id="3528" class="Symbol">→</a> <a id="3530" href="Overture.Extensionality.html#3523" class="Bound">𝓤</a> <a id="3532" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3534" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3536" href="Overture.Extensionality.html#3525" class="Bound">𝓦</a> <a id="3538" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3540" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3543" href="Overture.Extensionality.html#3512" class="Function">funext</a> <a id="3550" href="Overture.Extensionality.html#3550" class="Bound">𝓤</a> <a id="3552" href="Overture.Extensionality.html#3552" class="Bound">𝓦</a> <a id="3554" class="Symbol">=</a> <a id="3556" class="Symbol">{</a><a id="3557" href="Overture.Extensionality.html#3557" class="Bound">A</a> <a id="3559" class="Symbol">:</a> <a id="3561" href="Overture.Extensionality.html#3550" class="Bound">𝓤</a> <a id="3563" href="Universes.html#403" class="Function Operator">̇</a> <a id="3565" class="Symbol">}</a> <a id="3567" class="Symbol">{</a><a id="3568" href="Overture.Extensionality.html#3568" class="Bound">B</a> <a id="3570" class="Symbol">:</a> <a id="3572" href="Overture.Extensionality.html#3552" class="Bound">𝓦</a> <a id="3574" href="Universes.html#403" class="Function Operator">̇</a> <a id="3576" class="Symbol">}</a> <a id="3578" class="Symbol">{</a><a id="3579" href="Overture.Extensionality.html#3579" class="Bound">f</a> <a id="3581" href="Overture.Extensionality.html#3581" class="Bound">g</a> <a id="3583" class="Symbol">:</a> <a id="3585" href="Overture.Extensionality.html#3557" class="Bound">A</a> <a id="3587" class="Symbol">→</a> <a id="3589" href="Overture.Extensionality.html#3568" class="Bound">B</a><a id="3590" class="Symbol">}</a> <a id="3592" class="Symbol">→</a> <a id="3594" href="Overture.Extensionality.html#3579" class="Bound">f</a> <a id="3596" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3598" href="Overture.Extensionality.html#3581" class="Bound">g</a> <a id="3600" class="Symbol">→</a> <a id="3602" href="Overture.Extensionality.html#3579" class="Bound">f</a> <a id="3604" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3606" href="Overture.Extensionality.html#3581" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3717" href="Overture.Extensionality.html#3717" class="Function">dfunext</a> <a id="3725" class="Symbol">:</a> <a id="3727" class="Symbol">∀</a> <a id="3729" href="Overture.Extensionality.html#3729" class="Bound">𝓤</a> <a id="3731" href="Overture.Extensionality.html#3731" class="Bound">𝓦</a> <a id="3733" class="Symbol">→</a> <a id="3735" href="Overture.Extensionality.html#3729" class="Bound">𝓤</a> <a id="3737" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3739" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3741" href="Overture.Extensionality.html#3731" class="Bound">𝓦</a> <a id="3743" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3745" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3748" href="Overture.Extensionality.html#3717" class="Function">dfunext</a> <a id="3756" href="Overture.Extensionality.html#3756" class="Bound">𝓤</a> <a id="3758" href="Overture.Extensionality.html#3758" class="Bound">𝓦</a> <a id="3760" class="Symbol">=</a> <a id="3762" class="Symbol">{</a><a id="3763" href="Overture.Extensionality.html#3763" class="Bound">A</a> <a id="3765" class="Symbol">:</a> <a id="3767" href="Overture.Extensionality.html#3756" class="Bound">𝓤</a> <a id="3769" href="Universes.html#403" class="Function Operator">̇</a> <a id="3771" class="Symbol">}{</a><a id="3773" href="Overture.Extensionality.html#3773" class="Bound">B</a> <a id="3775" class="Symbol">:</a> <a id="3777" href="Overture.Extensionality.html#3763" class="Bound">A</a> <a id="3779" class="Symbol">→</a> <a id="3781" href="Overture.Extensionality.html#3758" class="Bound">𝓦</a> <a id="3783" href="Universes.html#403" class="Function Operator">̇</a> <a id="3785" class="Symbol">}{</a><a id="3787" href="Overture.Extensionality.html#3787" class="Bound">f</a> <a id="3789" href="Overture.Extensionality.html#3789" class="Bound">g</a> <a id="3791" class="Symbol">:</a> <a id="3793" class="Symbol">∀(</a><a id="3795" href="Overture.Extensionality.html#3795" class="Bound">x</a> <a id="3797" class="Symbol">:</a> <a id="3799" href="Overture.Extensionality.html#3763" class="Bound">A</a><a id="3800" class="Symbol">)</a> <a id="3802" class="Symbol">→</a> <a id="3804" href="Overture.Extensionality.html#3773" class="Bound">B</a> <a id="3806" href="Overture.Extensionality.html#3795" class="Bound">x</a><a id="3807" class="Symbol">}</a> <a id="3809" class="Symbol">→</a>  <a id="3812" href="Overture.Extensionality.html#3787" class="Bound">f</a> <a id="3814" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3816" href="Overture.Extensionality.html#3789" class="Bound">g</a>  <a id="3819" class="Symbol">→</a>  <a id="3822" href="Overture.Extensionality.html#3787" class="Bound">f</a> <a id="3824" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="3826" href="Overture.Extensionality.html#3789" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5235" href="Overture.Extensionality.html#5235" class="Function">global-funext</a> <a id="5249" class="Symbol">:</a> <a id="5251" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5255" href="Overture.Extensionality.html#5235" class="Function">global-funext</a> <a id="5269" class="Symbol">=</a> <a id="5271" class="Symbol">∀</a>  <a id="5274" class="Symbol">{</a><a id="5275" href="Overture.Extensionality.html#5275" class="Bound">𝓤</a> <a id="5277" href="Overture.Extensionality.html#5277" class="Bound">𝓥</a><a id="5278" class="Symbol">}</a> <a id="5280" class="Symbol">→</a> <a id="5282" href="Overture.Extensionality.html#3512" class="Function">funext</a> <a id="5289" href="Overture.Extensionality.html#5275" class="Bound">𝓤</a> <a id="5291" href="Overture.Extensionality.html#5277" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5295" href="Overture.Extensionality.html#5295" class="Function">global-dfunext</a> <a id="5310" class="Symbol">:</a> <a id="5312" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5316" href="Overture.Extensionality.html#5295" class="Function">global-dfunext</a> <a id="5331" class="Symbol">=</a> <a id="5333" class="Symbol">∀</a> <a id="5335" class="Symbol">{</a><a id="5336" href="Overture.Extensionality.html#5336" class="Bound">𝓤</a> <a id="5338" href="Overture.Extensionality.html#5338" class="Bound">𝓥</a><a id="5339" class="Symbol">}</a> <a id="5341" class="Symbol">→</a> <a id="5343" href="Overture.Extensionality.html#3717" class="Function">dfunext</a> <a id="5351" href="Overture.Extensionality.html#5336" class="Bound">𝓤</a> <a id="5353" href="Overture.Extensionality.html#5338" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Overture.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5649" class="Keyword">open</a> <a id="5654" class="Keyword">import</a> <a id="5661" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5688" class="Keyword">using</a> <a id="5694" class="Symbol">(</a><a id="5695" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5701" class="Symbol">;</a> <a id="5703" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5710" class="Symbol">)</a> <a id="5712" class="Keyword">public</a>
<a id="5719" class="Keyword">open</a> <a id="5724" class="Keyword">import</a> <a id="5731" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5757" class="Keyword">using</a> <a id="5763" class="Symbol">(</a><a id="5764" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5778" class="Symbol">)</a> <a id="5780" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6057" class="Keyword">open</a> <a id="6062" class="Keyword">import</a> <a id="6069" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6078" class="Keyword">using</a> <a id="6084" class="Symbol">(</a><a id="6085" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6088" class="Symbol">)</a> <a id="6090" class="Keyword">public</a>

<a id="extfun"></a><a id="6098" href="Overture.Extensionality.html#6098" class="Function">extfun</a> <a id="6105" class="Symbol">:</a> <a id="6107" class="Symbol">{</a><a id="6108" href="Overture.Extensionality.html#6108" class="Bound">A</a> <a id="6110" class="Symbol">:</a> <a id="6112" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6114" href="Universes.html#403" class="Function Operator">̇</a><a id="6115" class="Symbol">}{</a><a id="6117" href="Overture.Extensionality.html#6117" class="Bound">B</a> <a id="6119" class="Symbol">:</a> <a id="6121" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6123" href="Universes.html#403" class="Function Operator">̇</a><a id="6124" class="Symbol">}{</a><a id="6126" href="Overture.Extensionality.html#6126" class="Bound">f</a> <a id="6128" href="Overture.Extensionality.html#6128" class="Bound">g</a> <a id="6130" class="Symbol">:</a> <a id="6132" href="Overture.Extensionality.html#6108" class="Bound">A</a> <a id="6134" class="Symbol">→</a> <a id="6136" href="Overture.Extensionality.html#6117" class="Bound">B</a><a id="6137" class="Symbol">}</a> <a id="6139" class="Symbol">→</a> <a id="6141" href="Overture.Extensionality.html#6126" class="Bound">f</a> <a id="6143" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="6145" href="Overture.Extensionality.html#6128" class="Bound">g</a>  <a id="6148" class="Symbol">→</a>  <a id="6151" href="Overture.Extensionality.html#6126" class="Bound">f</a> <a id="6153" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6155" href="Overture.Extensionality.html#6128" class="Bound">g</a>
<a id="6157" href="Overture.Extensionality.html#6098" class="Function">extfun</a> <a id="6164" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6169" class="Symbol">_</a> <a id="6171" class="Symbol">=</a> <a id="6173" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6299" href="Overture.Extensionality.html#6299" class="Function">extdfun</a> <a id="6307" class="Symbol">:</a> <a id="6309" class="Symbol">{</a><a id="6310" href="Overture.Extensionality.html#6310" class="Bound">A</a> <a id="6312" class="Symbol">:</a> <a id="6314" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6316" href="Universes.html#403" class="Function Operator">̇</a> <a id="6318" class="Symbol">}{</a><a id="6320" href="Overture.Extensionality.html#6320" class="Bound">B</a> <a id="6322" class="Symbol">:</a> <a id="6324" href="Overture.Extensionality.html#6310" class="Bound">A</a> <a id="6326" class="Symbol">→</a> <a id="6328" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6330" href="Universes.html#403" class="Function Operator">̇</a> <a id="6332" class="Symbol">}(</a><a id="6334" href="Overture.Extensionality.html#6334" class="Bound">f</a> <a id="6336" href="Overture.Extensionality.html#6336" class="Bound">g</a> <a id="6338" class="Symbol">:</a> <a id="6340" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6342" href="Overture.Extensionality.html#6320" class="Bound">B</a><a id="6343" class="Symbol">)</a> <a id="6345" class="Symbol">→</a> <a id="6347" href="Overture.Extensionality.html#6334" class="Bound">f</a> <a id="6349" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="6351" href="Overture.Extensionality.html#6336" class="Bound">g</a> <a id="6353" class="Symbol">→</a> <a id="6355" href="Overture.Extensionality.html#6334" class="Bound">f</a> <a id="6357" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6359" href="Overture.Extensionality.html#6336" class="Bound">g</a>
<a id="6361" href="Overture.Extensionality.html#6299" class="Function">extdfun</a> <a id="6369" class="Symbol">_</a> <a id="6371" class="Symbol">_</a> <a id="6373" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6378" class="Symbol">_</a> <a id="6380" class="Symbol">=</a> <a id="6382" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8243" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8250" href="Overture.Extensionality.html#8250" class="Module">hide-tt-defs</a> <a id="8263" class="Symbol">{</a><a id="8264" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8266" class="Symbol">:</a> <a id="8268" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8276" class="Symbol">}</a> <a id="8278" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8286" href="Overture.Extensionality.html#8286" class="Function">is-center</a> <a id="8296" class="Symbol">:</a> <a id="8298" class="Symbol">(</a><a id="8299" href="Overture.Extensionality.html#8299" class="Bound">A</a> <a id="8301" class="Symbol">:</a> <a id="8303" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8305" href="Universes.html#403" class="Function Operator">̇</a> <a id="8307" class="Symbol">)</a> <a id="8309" class="Symbol">→</a> <a id="8311" href="Overture.Extensionality.html#8299" class="Bound">A</a> <a id="8313" class="Symbol">→</a> <a id="8315" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8317" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8320" href="Overture.Extensionality.html#8286" class="Function">is-center</a> <a id="8330" href="Overture.Extensionality.html#8330" class="Bound">A</a> <a id="8332" href="Overture.Extensionality.html#8332" class="Bound">c</a> <a id="8334" class="Symbol">=</a> <a id="8336" class="Symbol">(</a><a id="8337" href="Overture.Extensionality.html#8337" class="Bound">x</a> <a id="8339" class="Symbol">:</a> <a id="8341" href="Overture.Extensionality.html#8330" class="Bound">A</a><a id="8342" class="Symbol">)</a> <a id="8344" class="Symbol">→</a> <a id="8346" href="Overture.Extensionality.html#8332" class="Bound">c</a> <a id="8348" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="8350" href="Overture.Extensionality.html#8337" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8354" href="Overture.Extensionality.html#8354" class="Function">is-singleton</a> <a id="8367" class="Symbol">:</a> <a id="8369" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8371" href="Universes.html#403" class="Function Operator">̇</a> <a id="8373" class="Symbol">→</a> <a id="8375" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8377" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8380" href="Overture.Extensionality.html#8354" class="Function">is-singleton</a> <a id="8393" href="Overture.Extensionality.html#8393" class="Bound">A</a> <a id="8395" class="Symbol">=</a> <a id="8397" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8399" href="Overture.Extensionality.html#8399" class="Bound">c</a> <a id="8401" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8403" href="Overture.Extensionality.html#8393" class="Bound">A</a> <a id="8405" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8407" href="Overture.Extensionality.html#8286" class="Function">is-center</a> <a id="8417" href="Overture.Extensionality.html#8393" class="Bound">A</a> <a id="8419" href="Overture.Extensionality.html#8399" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8423" href="Overture.Extensionality.html#8423" class="Function">is-subsingleton</a> <a id="8439" class="Symbol">:</a> <a id="8441" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8443" href="Universes.html#403" class="Function Operator">̇</a> <a id="8445" class="Symbol">→</a> <a id="8447" href="Overture.Extensionality.html#8264" class="Bound">𝓤</a> <a id="8449" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8452" href="Overture.Extensionality.html#8423" class="Function">is-subsingleton</a> <a id="8468" href="Overture.Extensionality.html#8468" class="Bound">A</a> <a id="8470" class="Symbol">=</a> <a id="8472" class="Symbol">(</a><a id="8473" href="Overture.Extensionality.html#8473" class="Bound">x</a> <a id="8475" href="Overture.Extensionality.html#8475" class="Bound">y</a> <a id="8477" class="Symbol">:</a> <a id="8479" href="Overture.Extensionality.html#8468" class="Bound">A</a><a id="8480" class="Symbol">)</a> <a id="8482" class="Symbol">→</a> <a id="8484" href="Overture.Extensionality.html#8473" class="Bound">x</a> <a id="8486" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="8488" href="Overture.Extensionality.html#8475" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Overture.Equality.html#fn1) of the [Overture.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8783" class="Keyword">open</a> <a id="8788" class="Keyword">import</a> <a id="8795" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8808" class="Keyword">using</a> <a id="8814" class="Symbol">(</a><a id="8815" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8824" class="Symbol">;</a> <a id="8826" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8838" class="Symbol">;</a> <a id="8840" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8855" class="Symbol">)</a> <a id="8857" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9274" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9281" href="Overture.Extensionality.html#9281" class="Module">hide-tt-defs&#39;</a> <a id="9295" class="Symbol">{</a><a id="9296" href="Overture.Extensionality.html#9296" class="Bound">𝓤</a> <a id="9298" href="Overture.Extensionality.html#9298" class="Bound">𝓦</a> <a id="9300" class="Symbol">:</a> <a id="9302" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9310" class="Symbol">}</a> <a id="9312" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9320" href="Overture.Extensionality.html#9320" class="Function">fiber</a> <a id="9326" class="Symbol">:</a> <a id="9328" class="Symbol">{</a><a id="9329" href="Overture.Extensionality.html#9329" class="Bound">A</a> <a id="9331" class="Symbol">:</a> <a id="9333" href="Overture.Extensionality.html#9296" class="Bound">𝓤</a> <a id="9335" href="Universes.html#403" class="Function Operator">̇</a> <a id="9337" class="Symbol">}</a> <a id="9339" class="Symbol">{</a><a id="9340" href="Overture.Extensionality.html#9340" class="Bound">B</a> <a id="9342" class="Symbol">:</a> <a id="9344" href="Overture.Extensionality.html#9298" class="Bound">𝓦</a> <a id="9346" href="Universes.html#403" class="Function Operator">̇</a> <a id="9348" class="Symbol">}</a> <a id="9350" class="Symbol">(</a><a id="9351" href="Overture.Extensionality.html#9351" class="Bound">f</a> <a id="9353" class="Symbol">:</a> <a id="9355" href="Overture.Extensionality.html#9329" class="Bound">A</a> <a id="9357" class="Symbol">→</a> <a id="9359" href="Overture.Extensionality.html#9340" class="Bound">B</a><a id="9360" class="Symbol">)</a> <a id="9362" class="Symbol">→</a> <a id="9364" href="Overture.Extensionality.html#9340" class="Bound">B</a> <a id="9366" class="Symbol">→</a> <a id="9368" href="Overture.Extensionality.html#9296" class="Bound">𝓤</a> <a id="9370" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9372" href="Overture.Extensionality.html#9298" class="Bound">𝓦</a> <a id="9374" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9377" href="Overture.Extensionality.html#9320" class="Function">fiber</a> <a id="9383" class="Symbol">{</a><a id="9384" href="Overture.Extensionality.html#9384" class="Bound">A</a><a id="9385" class="Symbol">}</a> <a id="9387" href="Overture.Extensionality.html#9387" class="Bound">f</a> <a id="9389" href="Overture.Extensionality.html#9389" class="Bound">y</a> <a id="9391" class="Symbol">=</a> <a id="9393" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9395" href="Overture.Extensionality.html#9395" class="Bound">x</a> <a id="9397" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9399" href="Overture.Extensionality.html#9384" class="Bound">A</a> <a id="9401" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9403" href="Overture.Extensionality.html#9387" class="Bound">f</a> <a id="9405" href="Overture.Extensionality.html#9395" class="Bound">x</a> <a id="9407" href="Overture.Equality.html#2388" class="Datatype Operator">≡</a> <a id="9409" href="Overture.Extensionality.html#9389" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9515" href="Overture.Extensionality.html#9515" class="Function">is-equiv</a> <a id="9524" class="Symbol">:</a> <a id="9526" class="Symbol">{</a><a id="9527" href="Overture.Extensionality.html#9527" class="Bound">A</a> <a id="9529" class="Symbol">:</a> <a id="9531" href="Overture.Extensionality.html#9296" class="Bound">𝓤</a> <a id="9533" href="Universes.html#403" class="Function Operator">̇</a> <a id="9535" class="Symbol">}</a> <a id="9537" class="Symbol">{</a><a id="9538" href="Overture.Extensionality.html#9538" class="Bound">B</a> <a id="9540" class="Symbol">:</a> <a id="9542" href="Overture.Extensionality.html#9298" class="Bound">𝓦</a> <a id="9544" href="Universes.html#403" class="Function Operator">̇</a> <a id="9546" class="Symbol">}</a> <a id="9548" class="Symbol">→</a> <a id="9550" class="Symbol">(</a><a id="9551" href="Overture.Extensionality.html#9527" class="Bound">A</a> <a id="9553" class="Symbol">→</a> <a id="9555" href="Overture.Extensionality.html#9538" class="Bound">B</a><a id="9556" class="Symbol">)</a> <a id="9558" class="Symbol">→</a> <a id="9560" href="Overture.Extensionality.html#9296" class="Bound">𝓤</a> <a id="9562" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9564" href="Overture.Extensionality.html#9298" class="Bound">𝓦</a> <a id="9566" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9569" href="Overture.Extensionality.html#9515" class="Function">is-equiv</a> <a id="9578" href="Overture.Extensionality.html#9578" class="Bound">f</a> <a id="9580" class="Symbol">=</a> <a id="9582" class="Symbol">∀</a> <a id="9584" href="Overture.Extensionality.html#9584" class="Bound">y</a> <a id="9586" class="Symbol">→</a> <a id="9588" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9601" class="Symbol">(</a><a id="9602" href="Overture.Extensionality.html#9320" class="Function">fiber</a> <a id="9608" href="Overture.Extensionality.html#9578" class="Bound">f</a> <a id="9610" href="Overture.Extensionality.html#9584" class="Bound">y</a><a id="9611" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="9818" class="Keyword">open</a> <a id="9823" class="Keyword">import</a> <a id="9830" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9847" class="Keyword">using</a> <a id="9853" class="Symbol">(</a><a id="9854" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9859" class="Symbol">;</a> <a id="9861" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9869" class="Symbol">)</a> <a id="9871" class="Keyword">public</a>

<a id="9879" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9886" href="Overture.Extensionality.html#9886" class="Module">hide-hfunext</a> <a id="9899" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9907" href="Overture.Extensionality.html#9907" class="Function">hfunext</a> <a id="9915" class="Symbol">:</a>  <a id="9918" class="Symbol">∀</a> <a id="9920" href="Overture.Extensionality.html#9920" class="Bound">𝓤</a> <a id="9922" href="Overture.Extensionality.html#9922" class="Bound">𝓦</a> <a id="9924" class="Symbol">→</a> <a id="9926" class="Symbol">(</a><a id="9927" href="Overture.Extensionality.html#9920" class="Bound">𝓤</a> <a id="9929" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9931" href="Overture.Extensionality.html#9922" class="Bound">𝓦</a><a id="9932" class="Symbol">)</a><a id="9933" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="9935" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9938" href="Overture.Extensionality.html#9907" class="Function">hfunext</a> <a id="9946" href="Overture.Extensionality.html#9946" class="Bound">𝓤</a> <a id="9948" href="Overture.Extensionality.html#9948" class="Bound">𝓦</a> <a id="9950" class="Symbol">=</a> <a id="9952" class="Symbol">{</a><a id="9953" href="Overture.Extensionality.html#9953" class="Bound">A</a> <a id="9955" class="Symbol">:</a> <a id="9957" href="Overture.Extensionality.html#9946" class="Bound">𝓤</a> <a id="9959" href="Universes.html#403" class="Function Operator">̇</a><a id="9960" class="Symbol">}{</a><a id="9962" href="Overture.Extensionality.html#9962" class="Bound">B</a> <a id="9964" class="Symbol">:</a> <a id="9966" href="Overture.Extensionality.html#9953" class="Bound">A</a> <a id="9968" class="Symbol">→</a> <a id="9970" href="Overture.Extensionality.html#9948" class="Bound">𝓦</a> <a id="9972" href="Universes.html#403" class="Function Operator">̇</a><a id="9973" class="Symbol">}</a> <a id="9975" class="Symbol">(</a><a id="9976" href="Overture.Extensionality.html#9976" class="Bound">f</a> <a id="9978" href="Overture.Extensionality.html#9978" class="Bound">g</a> <a id="9980" class="Symbol">:</a> <a id="9982" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9984" href="Overture.Extensionality.html#9962" class="Bound">B</a><a id="9985" class="Symbol">)</a> <a id="9987" class="Symbol">→</a> <a id="9989" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="9998" class="Symbol">(</a><a id="9999" href="Overture.Extensionality.html#6299" class="Function">extdfun</a> <a id="10007" href="Overture.Extensionality.html#9976" class="Bound">f</a> <a id="10009" href="Overture.Extensionality.html#9978" class="Bound">g</a><a id="10010" class="Symbol">)</a>
<a id="10012" class="Keyword">open</a> <a id="10017" class="Keyword">import</a> <a id="10024" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10052" class="Keyword">using</a> <a id="10058" class="Symbol">(</a><a id="10059" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10066" class="Symbol">)</a> <a id="10068" class="Keyword">public</a>

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
