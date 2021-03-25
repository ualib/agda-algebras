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
 <a id="2928" href="Overture.Extensionality.html#2928" class="Bound">f</a> <a id="2930" href="Overture.Extensionality.html#2873" class="Function Operator">∼</a> <a id="2932" href="Overture.Extensionality.html#2932" class="Bound">g</a> <a id="2934" class="Symbol">=</a> <a id="2936" class="Symbol">∀</a> <a id="2938" href="Overture.Extensionality.html#2938" class="Bound">x</a> <a id="2940" class="Symbol">→</a> <a id="2942" href="Overture.Extensionality.html#2928" class="Bound">f</a> <a id="2944" href="Overture.Extensionality.html#2938" class="Bound">x</a> <a id="2946" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="2948" href="Overture.Extensionality.html#2932" class="Bound">g</a> <a id="2950" href="Overture.Extensionality.html#2938" class="Bound">x</a>

 <a id="2954" class="Keyword">infix</a> <a id="2960" class="Number">0</a> <a id="2962" href="Overture.Extensionality.html#2873" class="Function Operator">_∼_</a>

<a id="2967" class="Keyword">open</a> <a id="2972" class="Keyword">import</a> <a id="2979" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="3006" class="Keyword">using</a> <a id="3012" class="Symbol">(</a><a id="3013" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3016" class="Symbol">)</a> <a id="3018" class="Keyword">public</a>

</pre>

*Function extensionality* is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

<a id="3447" class="Keyword">module</a> <a id="hide-funext"></a><a id="3454" href="Overture.Extensionality.html#3454" class="Module">hide-funext</a> <a id="3466" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3474" href="Overture.Extensionality.html#3474" class="Function">funext</a> <a id="3481" class="Symbol">:</a> <a id="3483" class="Symbol">∀</a> <a id="3485" href="Overture.Extensionality.html#3485" class="Bound">𝓤</a> <a id="3487" href="Overture.Extensionality.html#3487" class="Bound">𝓦</a>  <a id="3490" class="Symbol">→</a> <a id="3492" href="Overture.Extensionality.html#3485" class="Bound">𝓤</a> <a id="3494" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3496" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3498" href="Overture.Extensionality.html#3487" class="Bound">𝓦</a> <a id="3500" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3502" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3505" href="Overture.Extensionality.html#3474" class="Function">funext</a> <a id="3512" href="Overture.Extensionality.html#3512" class="Bound">𝓤</a> <a id="3514" href="Overture.Extensionality.html#3514" class="Bound">𝓦</a> <a id="3516" class="Symbol">=</a> <a id="3518" class="Symbol">{</a><a id="3519" href="Overture.Extensionality.html#3519" class="Bound">A</a> <a id="3521" class="Symbol">:</a> <a id="3523" href="Overture.Extensionality.html#3512" class="Bound">𝓤</a> <a id="3525" href="Universes.html#403" class="Function Operator">̇</a> <a id="3527" class="Symbol">}</a> <a id="3529" class="Symbol">{</a><a id="3530" href="Overture.Extensionality.html#3530" class="Bound">B</a> <a id="3532" class="Symbol">:</a> <a id="3534" href="Overture.Extensionality.html#3514" class="Bound">𝓦</a> <a id="3536" href="Universes.html#403" class="Function Operator">̇</a> <a id="3538" class="Symbol">}</a> <a id="3540" class="Symbol">{</a><a id="3541" href="Overture.Extensionality.html#3541" class="Bound">f</a> <a id="3543" href="Overture.Extensionality.html#3543" class="Bound">g</a> <a id="3545" class="Symbol">:</a> <a id="3547" href="Overture.Extensionality.html#3519" class="Bound">A</a> <a id="3549" class="Symbol">→</a> <a id="3551" href="Overture.Extensionality.html#3530" class="Bound">B</a><a id="3552" class="Symbol">}</a> <a id="3554" class="Symbol">→</a> <a id="3556" href="Overture.Extensionality.html#3541" class="Bound">f</a> <a id="3558" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3560" href="Overture.Extensionality.html#3543" class="Bound">g</a> <a id="3562" class="Symbol">→</a> <a id="3564" href="Overture.Extensionality.html#3541" class="Bound">f</a> <a id="3566" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="3568" href="Overture.Extensionality.html#3543" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3679" href="Overture.Extensionality.html#3679" class="Function">dfunext</a> <a id="3687" class="Symbol">:</a> <a id="3689" class="Symbol">∀</a> <a id="3691" href="Overture.Extensionality.html#3691" class="Bound">𝓤</a> <a id="3693" href="Overture.Extensionality.html#3693" class="Bound">𝓦</a> <a id="3695" class="Symbol">→</a> <a id="3697" href="Overture.Extensionality.html#3691" class="Bound">𝓤</a> <a id="3699" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3701" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3703" href="Overture.Extensionality.html#3693" class="Bound">𝓦</a> <a id="3705" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3707" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3710" href="Overture.Extensionality.html#3679" class="Function">dfunext</a> <a id="3718" href="Overture.Extensionality.html#3718" class="Bound">𝓤</a> <a id="3720" href="Overture.Extensionality.html#3720" class="Bound">𝓦</a> <a id="3722" class="Symbol">=</a> <a id="3724" class="Symbol">{</a><a id="3725" href="Overture.Extensionality.html#3725" class="Bound">A</a> <a id="3727" class="Symbol">:</a> <a id="3729" href="Overture.Extensionality.html#3718" class="Bound">𝓤</a> <a id="3731" href="Universes.html#403" class="Function Operator">̇</a> <a id="3733" class="Symbol">}{</a><a id="3735" href="Overture.Extensionality.html#3735" class="Bound">B</a> <a id="3737" class="Symbol">:</a> <a id="3739" href="Overture.Extensionality.html#3725" class="Bound">A</a> <a id="3741" class="Symbol">→</a> <a id="3743" href="Overture.Extensionality.html#3720" class="Bound">𝓦</a> <a id="3745" href="Universes.html#403" class="Function Operator">̇</a> <a id="3747" class="Symbol">}{</a><a id="3749" href="Overture.Extensionality.html#3749" class="Bound">f</a> <a id="3751" href="Overture.Extensionality.html#3751" class="Bound">g</a> <a id="3753" class="Symbol">:</a> <a id="3755" class="Symbol">∀(</a><a id="3757" href="Overture.Extensionality.html#3757" class="Bound">x</a> <a id="3759" class="Symbol">:</a> <a id="3761" href="Overture.Extensionality.html#3725" class="Bound">A</a><a id="3762" class="Symbol">)</a> <a id="3764" class="Symbol">→</a> <a id="3766" href="Overture.Extensionality.html#3735" class="Bound">B</a> <a id="3768" href="Overture.Extensionality.html#3757" class="Bound">x</a><a id="3769" class="Symbol">}</a> <a id="3771" class="Symbol">→</a>  <a id="3774" href="Overture.Extensionality.html#3749" class="Bound">f</a> <a id="3776" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3778" href="Overture.Extensionality.html#3751" class="Bound">g</a>  <a id="3781" class="Symbol">→</a>  <a id="3784" href="Overture.Extensionality.html#3749" class="Bound">f</a> <a id="3786" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="3788" href="Overture.Extensionality.html#3751" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5197" href="Overture.Extensionality.html#5197" class="Function">global-funext</a> <a id="5211" class="Symbol">:</a> <a id="5213" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5217" href="Overture.Extensionality.html#5197" class="Function">global-funext</a> <a id="5231" class="Symbol">=</a> <a id="5233" class="Symbol">∀</a>  <a id="5236" class="Symbol">{</a><a id="5237" href="Overture.Extensionality.html#5237" class="Bound">𝓤</a> <a id="5239" href="Overture.Extensionality.html#5239" class="Bound">𝓥</a><a id="5240" class="Symbol">}</a> <a id="5242" class="Symbol">→</a> <a id="5244" href="Overture.Extensionality.html#3474" class="Function">funext</a> <a id="5251" href="Overture.Extensionality.html#5237" class="Bound">𝓤</a> <a id="5253" href="Overture.Extensionality.html#5239" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5257" href="Overture.Extensionality.html#5257" class="Function">global-dfunext</a> <a id="5272" class="Symbol">:</a> <a id="5274" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5278" href="Overture.Extensionality.html#5257" class="Function">global-dfunext</a> <a id="5293" class="Symbol">=</a> <a id="5295" class="Symbol">∀</a> <a id="5297" class="Symbol">{</a><a id="5298" href="Overture.Extensionality.html#5298" class="Bound">𝓤</a> <a id="5300" href="Overture.Extensionality.html#5300" class="Bound">𝓥</a><a id="5301" class="Symbol">}</a> <a id="5303" class="Symbol">→</a> <a id="5305" href="Overture.Extensionality.html#3679" class="Function">dfunext</a> <a id="5313" href="Overture.Extensionality.html#5298" class="Bound">𝓤</a> <a id="5315" href="Overture.Extensionality.html#5300" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Overture.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5611" class="Keyword">open</a> <a id="5616" class="Keyword">import</a> <a id="5623" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5650" class="Keyword">using</a> <a id="5656" class="Symbol">(</a><a id="5657" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5663" class="Symbol">;</a> <a id="5665" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5672" class="Symbol">)</a> <a id="5674" class="Keyword">public</a>
<a id="5681" class="Keyword">open</a> <a id="5686" class="Keyword">import</a> <a id="5693" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5719" class="Keyword">using</a> <a id="5725" class="Symbol">(</a><a id="5726" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5740" class="Symbol">)</a> <a id="5742" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6019" class="Keyword">open</a> <a id="6024" class="Keyword">import</a> <a id="6031" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6040" class="Keyword">using</a> <a id="6046" class="Symbol">(</a><a id="6047" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6050" class="Symbol">)</a> <a id="6052" class="Keyword">public</a>

<a id="extfun"></a><a id="6060" href="Overture.Extensionality.html#6060" class="Function">extfun</a> <a id="6067" class="Symbol">:</a> <a id="6069" class="Symbol">{</a><a id="6070" href="Overture.Extensionality.html#6070" class="Bound">A</a> <a id="6072" class="Symbol">:</a> <a id="6074" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6076" href="Universes.html#403" class="Function Operator">̇</a><a id="6077" class="Symbol">}{</a><a id="6079" href="Overture.Extensionality.html#6079" class="Bound">B</a> <a id="6081" class="Symbol">:</a> <a id="6083" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6085" href="Universes.html#403" class="Function Operator">̇</a><a id="6086" class="Symbol">}{</a><a id="6088" href="Overture.Extensionality.html#6088" class="Bound">f</a> <a id="6090" href="Overture.Extensionality.html#6090" class="Bound">g</a> <a id="6092" class="Symbol">:</a> <a id="6094" href="Overture.Extensionality.html#6070" class="Bound">A</a> <a id="6096" class="Symbol">→</a> <a id="6098" href="Overture.Extensionality.html#6079" class="Bound">B</a><a id="6099" class="Symbol">}</a> <a id="6101" class="Symbol">→</a> <a id="6103" href="Overture.Extensionality.html#6088" class="Bound">f</a> <a id="6105" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="6107" href="Overture.Extensionality.html#6090" class="Bound">g</a>  <a id="6110" class="Symbol">→</a>  <a id="6113" href="Overture.Extensionality.html#6088" class="Bound">f</a> <a id="6115" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6117" href="Overture.Extensionality.html#6090" class="Bound">g</a>
<a id="6119" href="Overture.Extensionality.html#6060" class="Function">extfun</a> <a id="6126" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6131" class="Symbol">_</a> <a id="6133" class="Symbol">=</a> <a id="6135" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6261" href="Overture.Extensionality.html#6261" class="Function">extdfun</a> <a id="6269" class="Symbol">:</a> <a id="6271" class="Symbol">{</a><a id="6272" href="Overture.Extensionality.html#6272" class="Bound">A</a> <a id="6274" class="Symbol">:</a> <a id="6276" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6278" href="Universes.html#403" class="Function Operator">̇</a> <a id="6280" class="Symbol">}{</a><a id="6282" href="Overture.Extensionality.html#6282" class="Bound">B</a> <a id="6284" class="Symbol">:</a> <a id="6286" href="Overture.Extensionality.html#6272" class="Bound">A</a> <a id="6288" class="Symbol">→</a> <a id="6290" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6292" href="Universes.html#403" class="Function Operator">̇</a> <a id="6294" class="Symbol">}(</a><a id="6296" href="Overture.Extensionality.html#6296" class="Bound">f</a> <a id="6298" href="Overture.Extensionality.html#6298" class="Bound">g</a> <a id="6300" class="Symbol">:</a> <a id="6302" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6304" href="Overture.Extensionality.html#6282" class="Bound">B</a><a id="6305" class="Symbol">)</a> <a id="6307" class="Symbol">→</a> <a id="6309" href="Overture.Extensionality.html#6296" class="Bound">f</a> <a id="6311" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="6313" href="Overture.Extensionality.html#6298" class="Bound">g</a> <a id="6315" class="Symbol">→</a> <a id="6317" href="Overture.Extensionality.html#6296" class="Bound">f</a> <a id="6319" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6321" href="Overture.Extensionality.html#6298" class="Bound">g</a>
<a id="6323" href="Overture.Extensionality.html#6261" class="Function">extdfun</a> <a id="6331" class="Symbol">_</a> <a id="6333" class="Symbol">_</a> <a id="6335" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6340" class="Symbol">_</a> <a id="6342" class="Symbol">=</a> <a id="6344" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8205" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8212" href="Overture.Extensionality.html#8212" class="Module">hide-tt-defs</a> <a id="8225" class="Symbol">{</a><a id="8226" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8228" class="Symbol">:</a> <a id="8230" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8238" class="Symbol">}</a> <a id="8240" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8248" href="Overture.Extensionality.html#8248" class="Function">is-center</a> <a id="8258" class="Symbol">:</a> <a id="8260" class="Symbol">(</a><a id="8261" href="Overture.Extensionality.html#8261" class="Bound">A</a> <a id="8263" class="Symbol">:</a> <a id="8265" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8267" href="Universes.html#403" class="Function Operator">̇</a> <a id="8269" class="Symbol">)</a> <a id="8271" class="Symbol">→</a> <a id="8273" href="Overture.Extensionality.html#8261" class="Bound">A</a> <a id="8275" class="Symbol">→</a> <a id="8277" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8279" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8282" href="Overture.Extensionality.html#8248" class="Function">is-center</a> <a id="8292" href="Overture.Extensionality.html#8292" class="Bound">A</a> <a id="8294" href="Overture.Extensionality.html#8294" class="Bound">c</a> <a id="8296" class="Symbol">=</a> <a id="8298" class="Symbol">(</a><a id="8299" href="Overture.Extensionality.html#8299" class="Bound">x</a> <a id="8301" class="Symbol">:</a> <a id="8303" href="Overture.Extensionality.html#8292" class="Bound">A</a><a id="8304" class="Symbol">)</a> <a id="8306" class="Symbol">→</a> <a id="8308" href="Overture.Extensionality.html#8294" class="Bound">c</a> <a id="8310" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="8312" href="Overture.Extensionality.html#8299" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8316" href="Overture.Extensionality.html#8316" class="Function">is-singleton</a> <a id="8329" class="Symbol">:</a> <a id="8331" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8333" href="Universes.html#403" class="Function Operator">̇</a> <a id="8335" class="Symbol">→</a> <a id="8337" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8339" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8342" href="Overture.Extensionality.html#8316" class="Function">is-singleton</a> <a id="8355" href="Overture.Extensionality.html#8355" class="Bound">A</a> <a id="8357" class="Symbol">=</a> <a id="8359" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8361" href="Overture.Extensionality.html#8361" class="Bound">c</a> <a id="8363" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8365" href="Overture.Extensionality.html#8355" class="Bound">A</a> <a id="8367" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8369" href="Overture.Extensionality.html#8248" class="Function">is-center</a> <a id="8379" href="Overture.Extensionality.html#8355" class="Bound">A</a> <a id="8381" href="Overture.Extensionality.html#8361" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8385" href="Overture.Extensionality.html#8385" class="Function">is-subsingleton</a> <a id="8401" class="Symbol">:</a> <a id="8403" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8405" href="Universes.html#403" class="Function Operator">̇</a> <a id="8407" class="Symbol">→</a> <a id="8409" href="Overture.Extensionality.html#8226" class="Bound">𝓤</a> <a id="8411" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8414" href="Overture.Extensionality.html#8385" class="Function">is-subsingleton</a> <a id="8430" href="Overture.Extensionality.html#8430" class="Bound">A</a> <a id="8432" class="Symbol">=</a> <a id="8434" class="Symbol">(</a><a id="8435" href="Overture.Extensionality.html#8435" class="Bound">x</a> <a id="8437" href="Overture.Extensionality.html#8437" class="Bound">y</a> <a id="8439" class="Symbol">:</a> <a id="8441" href="Overture.Extensionality.html#8430" class="Bound">A</a><a id="8442" class="Symbol">)</a> <a id="8444" class="Symbol">→</a> <a id="8446" href="Overture.Extensionality.html#8435" class="Bound">x</a> <a id="8448" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="8450" href="Overture.Extensionality.html#8437" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Overture.Equality.html#fn1) of the [Overture.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8745" class="Keyword">open</a> <a id="8750" class="Keyword">import</a> <a id="8757" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8770" class="Keyword">using</a> <a id="8776" class="Symbol">(</a><a id="8777" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8786" class="Symbol">;</a> <a id="8788" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8800" class="Symbol">;</a> <a id="8802" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8817" class="Symbol">)</a> <a id="8819" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9236" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9243" href="Overture.Extensionality.html#9243" class="Module">hide-tt-defs&#39;</a> <a id="9257" class="Symbol">{</a><a id="9258" href="Overture.Extensionality.html#9258" class="Bound">𝓤</a> <a id="9260" href="Overture.Extensionality.html#9260" class="Bound">𝓦</a> <a id="9262" class="Symbol">:</a> <a id="9264" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9272" class="Symbol">}</a> <a id="9274" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9282" href="Overture.Extensionality.html#9282" class="Function">fiber</a> <a id="9288" class="Symbol">:</a> <a id="9290" class="Symbol">{</a><a id="9291" href="Overture.Extensionality.html#9291" class="Bound">A</a> <a id="9293" class="Symbol">:</a> <a id="9295" href="Overture.Extensionality.html#9258" class="Bound">𝓤</a> <a id="9297" href="Universes.html#403" class="Function Operator">̇</a> <a id="9299" class="Symbol">}</a> <a id="9301" class="Symbol">{</a><a id="9302" href="Overture.Extensionality.html#9302" class="Bound">B</a> <a id="9304" class="Symbol">:</a> <a id="9306" href="Overture.Extensionality.html#9260" class="Bound">𝓦</a> <a id="9308" href="Universes.html#403" class="Function Operator">̇</a> <a id="9310" class="Symbol">}</a> <a id="9312" class="Symbol">(</a><a id="9313" href="Overture.Extensionality.html#9313" class="Bound">f</a> <a id="9315" class="Symbol">:</a> <a id="9317" href="Overture.Extensionality.html#9291" class="Bound">A</a> <a id="9319" class="Symbol">→</a> <a id="9321" href="Overture.Extensionality.html#9302" class="Bound">B</a><a id="9322" class="Symbol">)</a> <a id="9324" class="Symbol">→</a> <a id="9326" href="Overture.Extensionality.html#9302" class="Bound">B</a> <a id="9328" class="Symbol">→</a> <a id="9330" href="Overture.Extensionality.html#9258" class="Bound">𝓤</a> <a id="9332" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9334" href="Overture.Extensionality.html#9260" class="Bound">𝓦</a> <a id="9336" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9339" href="Overture.Extensionality.html#9282" class="Function">fiber</a> <a id="9345" class="Symbol">{</a><a id="9346" href="Overture.Extensionality.html#9346" class="Bound">A</a><a id="9347" class="Symbol">}</a> <a id="9349" href="Overture.Extensionality.html#9349" class="Bound">f</a> <a id="9351" href="Overture.Extensionality.html#9351" class="Bound">y</a> <a id="9353" class="Symbol">=</a> <a id="9355" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9357" href="Overture.Extensionality.html#9357" class="Bound">x</a> <a id="9359" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9361" href="Overture.Extensionality.html#9346" class="Bound">A</a> <a id="9363" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9365" href="Overture.Extensionality.html#9349" class="Bound">f</a> <a id="9367" href="Overture.Extensionality.html#9357" class="Bound">x</a> <a id="9369" href="Overture.Equality.html#2389" class="Datatype Operator">≡</a> <a id="9371" href="Overture.Extensionality.html#9351" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9477" href="Overture.Extensionality.html#9477" class="Function">is-equiv</a> <a id="9486" class="Symbol">:</a> <a id="9488" class="Symbol">{</a><a id="9489" href="Overture.Extensionality.html#9489" class="Bound">A</a> <a id="9491" class="Symbol">:</a> <a id="9493" href="Overture.Extensionality.html#9258" class="Bound">𝓤</a> <a id="9495" href="Universes.html#403" class="Function Operator">̇</a> <a id="9497" class="Symbol">}</a> <a id="9499" class="Symbol">{</a><a id="9500" href="Overture.Extensionality.html#9500" class="Bound">B</a> <a id="9502" class="Symbol">:</a> <a id="9504" href="Overture.Extensionality.html#9260" class="Bound">𝓦</a> <a id="9506" href="Universes.html#403" class="Function Operator">̇</a> <a id="9508" class="Symbol">}</a> <a id="9510" class="Symbol">→</a> <a id="9512" class="Symbol">(</a><a id="9513" href="Overture.Extensionality.html#9489" class="Bound">A</a> <a id="9515" class="Symbol">→</a> <a id="9517" href="Overture.Extensionality.html#9500" class="Bound">B</a><a id="9518" class="Symbol">)</a> <a id="9520" class="Symbol">→</a> <a id="9522" href="Overture.Extensionality.html#9258" class="Bound">𝓤</a> <a id="9524" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9526" href="Overture.Extensionality.html#9260" class="Bound">𝓦</a> <a id="9528" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9531" href="Overture.Extensionality.html#9477" class="Function">is-equiv</a> <a id="9540" href="Overture.Extensionality.html#9540" class="Bound">f</a> <a id="9542" class="Symbol">=</a> <a id="9544" class="Symbol">∀</a> <a id="9546" href="Overture.Extensionality.html#9546" class="Bound">y</a> <a id="9548" class="Symbol">→</a> <a id="9550" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9563" class="Symbol">(</a><a id="9564" href="Overture.Extensionality.html#9282" class="Function">fiber</a> <a id="9570" href="Overture.Extensionality.html#9540" class="Bound">f</a> <a id="9572" href="Overture.Extensionality.html#9546" class="Bound">y</a><a id="9573" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="9780" class="Keyword">open</a> <a id="9785" class="Keyword">import</a> <a id="9792" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9809" class="Keyword">using</a> <a id="9815" class="Symbol">(</a><a id="9816" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9821" class="Symbol">;</a> <a id="9823" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9831" class="Symbol">)</a> <a id="9833" class="Keyword">public</a>

<a id="9841" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9848" href="Overture.Extensionality.html#9848" class="Module">hide-hfunext</a> <a id="9861" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9869" href="Overture.Extensionality.html#9869" class="Function">hfunext</a> <a id="9877" class="Symbol">:</a>  <a id="9880" class="Symbol">∀</a> <a id="9882" href="Overture.Extensionality.html#9882" class="Bound">𝓤</a> <a id="9884" href="Overture.Extensionality.html#9884" class="Bound">𝓦</a> <a id="9886" class="Symbol">→</a> <a id="9888" class="Symbol">(</a><a id="9889" href="Overture.Extensionality.html#9882" class="Bound">𝓤</a> <a id="9891" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9893" href="Overture.Extensionality.html#9884" class="Bound">𝓦</a><a id="9894" class="Symbol">)</a><a id="9895" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="9897" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9900" href="Overture.Extensionality.html#9869" class="Function">hfunext</a> <a id="9908" href="Overture.Extensionality.html#9908" class="Bound">𝓤</a> <a id="9910" href="Overture.Extensionality.html#9910" class="Bound">𝓦</a> <a id="9912" class="Symbol">=</a> <a id="9914" class="Symbol">{</a><a id="9915" href="Overture.Extensionality.html#9915" class="Bound">A</a> <a id="9917" class="Symbol">:</a> <a id="9919" href="Overture.Extensionality.html#9908" class="Bound">𝓤</a> <a id="9921" href="Universes.html#403" class="Function Operator">̇</a><a id="9922" class="Symbol">}{</a><a id="9924" href="Overture.Extensionality.html#9924" class="Bound">B</a> <a id="9926" class="Symbol">:</a> <a id="9928" href="Overture.Extensionality.html#9915" class="Bound">A</a> <a id="9930" class="Symbol">→</a> <a id="9932" href="Overture.Extensionality.html#9910" class="Bound">𝓦</a> <a id="9934" href="Universes.html#403" class="Function Operator">̇</a><a id="9935" class="Symbol">}</a> <a id="9937" class="Symbol">(</a><a id="9938" href="Overture.Extensionality.html#9938" class="Bound">f</a> <a id="9940" href="Overture.Extensionality.html#9940" class="Bound">g</a> <a id="9942" class="Symbol">:</a> <a id="9944" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9946" href="Overture.Extensionality.html#9924" class="Bound">B</a><a id="9947" class="Symbol">)</a> <a id="9949" class="Symbol">→</a> <a id="9951" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="9960" class="Symbol">(</a><a id="9961" href="Overture.Extensionality.html#6261" class="Function">extdfun</a> <a id="9969" href="Overture.Extensionality.html#9938" class="Bound">f</a> <a id="9971" href="Overture.Extensionality.html#9940" class="Bound">g</a><a id="9972" class="Symbol">)</a>
<a id="9974" class="Keyword">open</a> <a id="9979" class="Keyword">import</a> <a id="9986" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10014" class="Keyword">using</a> <a id="10020" class="Symbol">(</a><a id="10021" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10028" class="Symbol">)</a> <a id="10030" class="Keyword">public</a>

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
