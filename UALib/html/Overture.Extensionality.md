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

<a id="2851" class="Keyword">module</a> <a id="hide-∼"></a><a id="2858" href="Overture.Extensionality.html#2858" class="Module">hide-∼</a> <a id="2865" class="Symbol">{</a><a id="2866" href="Overture.Extensionality.html#2866" class="Bound">𝓤</a> <a id="2868" href="Overture.Extensionality.html#2868" class="Bound">𝓦</a> <a id="2870" class="Symbol">:</a> <a id="2872" href="Universes.html#205" class="Postulate">Universe</a><a id="2880" class="Symbol">}</a> <a id="2882" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2890" href="Overture.Extensionality.html#2890" class="Function Operator">_∼_</a> <a id="2894" class="Symbol">:</a> <a id="2896" class="Symbol">{</a><a id="2897" href="Overture.Extensionality.html#2897" class="Bound">A</a> <a id="2899" class="Symbol">:</a> <a id="2901" href="Overture.Extensionality.html#2866" class="Bound">𝓤</a> <a id="2903" href="Universes.html#403" class="Function Operator">̇</a> <a id="2905" class="Symbol">}</a> <a id="2907" class="Symbol">{</a><a id="2908" href="Overture.Extensionality.html#2908" class="Bound">B</a> <a id="2910" class="Symbol">:</a> <a id="2912" href="Overture.Extensionality.html#2897" class="Bound">A</a> <a id="2914" class="Symbol">→</a> <a id="2916" href="Overture.Extensionality.html#2868" class="Bound">𝓦</a> <a id="2918" href="Universes.html#403" class="Function Operator">̇</a> <a id="2920" class="Symbol">}</a> <a id="2922" class="Symbol">→</a> <a id="2924" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2926" href="Overture.Extensionality.html#2908" class="Bound">B</a> <a id="2928" class="Symbol">→</a> <a id="2930" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2932" href="Overture.Extensionality.html#2908" class="Bound">B</a> <a id="2934" class="Symbol">→</a> <a id="2936" href="Overture.Extensionality.html#2866" class="Bound">𝓤</a> <a id="2938" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2940" href="Overture.Extensionality.html#2868" class="Bound">𝓦</a> <a id="2942" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2945" href="Overture.Extensionality.html#2945" class="Bound">f</a> <a id="2947" href="Overture.Extensionality.html#2890" class="Function Operator">∼</a> <a id="2949" href="Overture.Extensionality.html#2949" class="Bound">g</a> <a id="2951" class="Symbol">=</a> <a id="2953" class="Symbol">∀</a> <a id="2955" href="Overture.Extensionality.html#2955" class="Bound">x</a> <a id="2957" class="Symbol">→</a> <a id="2959" href="Overture.Extensionality.html#2945" class="Bound">f</a> <a id="2961" href="Overture.Extensionality.html#2955" class="Bound">x</a> <a id="2963" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="2965" href="Overture.Extensionality.html#2949" class="Bound">g</a> <a id="2967" href="Overture.Extensionality.html#2955" class="Bound">x</a>

 <a id="2971" class="Keyword">infix</a> <a id="2977" class="Number">0</a> <a id="2979" href="Overture.Extensionality.html#2890" class="Function Operator">_∼_</a>

<a id="2984" class="Keyword">open</a> <a id="2989" class="Keyword">import</a> <a id="2996" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="3023" class="Keyword">using</a> <a id="3029" class="Symbol">(</a><a id="3030" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3033" class="Symbol">)</a> <a id="3035" class="Keyword">public</a>

</pre>

*Function extensionality* is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

<a id="3464" class="Keyword">module</a> <a id="hide-funext"></a><a id="3471" href="Overture.Extensionality.html#3471" class="Module">hide-funext</a> <a id="3483" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3491" href="Overture.Extensionality.html#3491" class="Function">funext</a> <a id="3498" class="Symbol">:</a> <a id="3500" class="Symbol">∀</a> <a id="3502" href="Overture.Extensionality.html#3502" class="Bound">𝓤</a> <a id="3504" href="Overture.Extensionality.html#3504" class="Bound">𝓦</a>  <a id="3507" class="Symbol">→</a> <a id="3509" href="Overture.Extensionality.html#3502" class="Bound">𝓤</a> <a id="3511" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3513" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3515" href="Overture.Extensionality.html#3504" class="Bound">𝓦</a> <a id="3517" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3519" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3522" href="Overture.Extensionality.html#3491" class="Function">funext</a> <a id="3529" href="Overture.Extensionality.html#3529" class="Bound">𝓤</a> <a id="3531" href="Overture.Extensionality.html#3531" class="Bound">𝓦</a> <a id="3533" class="Symbol">=</a> <a id="3535" class="Symbol">{</a><a id="3536" href="Overture.Extensionality.html#3536" class="Bound">A</a> <a id="3538" class="Symbol">:</a> <a id="3540" href="Overture.Extensionality.html#3529" class="Bound">𝓤</a> <a id="3542" href="Universes.html#403" class="Function Operator">̇</a> <a id="3544" class="Symbol">}</a> <a id="3546" class="Symbol">{</a><a id="3547" href="Overture.Extensionality.html#3547" class="Bound">B</a> <a id="3549" class="Symbol">:</a> <a id="3551" href="Overture.Extensionality.html#3531" class="Bound">𝓦</a> <a id="3553" href="Universes.html#403" class="Function Operator">̇</a> <a id="3555" class="Symbol">}</a> <a id="3557" class="Symbol">{</a><a id="3558" href="Overture.Extensionality.html#3558" class="Bound">f</a> <a id="3560" href="Overture.Extensionality.html#3560" class="Bound">g</a> <a id="3562" class="Symbol">:</a> <a id="3564" href="Overture.Extensionality.html#3536" class="Bound">A</a> <a id="3566" class="Symbol">→</a> <a id="3568" href="Overture.Extensionality.html#3547" class="Bound">B</a><a id="3569" class="Symbol">}</a> <a id="3571" class="Symbol">→</a> <a id="3573" href="Overture.Extensionality.html#3558" class="Bound">f</a> <a id="3575" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3577" href="Overture.Extensionality.html#3560" class="Bound">g</a> <a id="3579" class="Symbol">→</a> <a id="3581" href="Overture.Extensionality.html#3558" class="Bound">f</a> <a id="3583" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3585" href="Overture.Extensionality.html#3560" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3696" href="Overture.Extensionality.html#3696" class="Function">dfunext</a> <a id="3704" class="Symbol">:</a> <a id="3706" class="Symbol">∀</a> <a id="3708" href="Overture.Extensionality.html#3708" class="Bound">𝓤</a> <a id="3710" href="Overture.Extensionality.html#3710" class="Bound">𝓦</a> <a id="3712" class="Symbol">→</a> <a id="3714" href="Overture.Extensionality.html#3708" class="Bound">𝓤</a> <a id="3716" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3718" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3720" href="Overture.Extensionality.html#3710" class="Bound">𝓦</a> <a id="3722" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3724" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3727" href="Overture.Extensionality.html#3696" class="Function">dfunext</a> <a id="3735" href="Overture.Extensionality.html#3735" class="Bound">𝓤</a> <a id="3737" href="Overture.Extensionality.html#3737" class="Bound">𝓦</a> <a id="3739" class="Symbol">=</a> <a id="3741" class="Symbol">{</a><a id="3742" href="Overture.Extensionality.html#3742" class="Bound">A</a> <a id="3744" class="Symbol">:</a> <a id="3746" href="Overture.Extensionality.html#3735" class="Bound">𝓤</a> <a id="3748" href="Universes.html#403" class="Function Operator">̇</a> <a id="3750" class="Symbol">}{</a><a id="3752" href="Overture.Extensionality.html#3752" class="Bound">B</a> <a id="3754" class="Symbol">:</a> <a id="3756" href="Overture.Extensionality.html#3742" class="Bound">A</a> <a id="3758" class="Symbol">→</a> <a id="3760" href="Overture.Extensionality.html#3737" class="Bound">𝓦</a> <a id="3762" href="Universes.html#403" class="Function Operator">̇</a> <a id="3764" class="Symbol">}{</a><a id="3766" href="Overture.Extensionality.html#3766" class="Bound">f</a> <a id="3768" href="Overture.Extensionality.html#3768" class="Bound">g</a> <a id="3770" class="Symbol">:</a> <a id="3772" class="Symbol">∀(</a><a id="3774" href="Overture.Extensionality.html#3774" class="Bound">x</a> <a id="3776" class="Symbol">:</a> <a id="3778" href="Overture.Extensionality.html#3742" class="Bound">A</a><a id="3779" class="Symbol">)</a> <a id="3781" class="Symbol">→</a> <a id="3783" href="Overture.Extensionality.html#3752" class="Bound">B</a> <a id="3785" href="Overture.Extensionality.html#3774" class="Bound">x</a><a id="3786" class="Symbol">}</a> <a id="3788" class="Symbol">→</a>  <a id="3791" href="Overture.Extensionality.html#3766" class="Bound">f</a> <a id="3793" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3795" href="Overture.Extensionality.html#3768" class="Bound">g</a>  <a id="3798" class="Symbol">→</a>  <a id="3801" href="Overture.Extensionality.html#3766" class="Bound">f</a> <a id="3803" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3805" href="Overture.Extensionality.html#3768" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5214" href="Overture.Extensionality.html#5214" class="Function">global-funext</a> <a id="5228" class="Symbol">:</a> <a id="5230" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5234" href="Overture.Extensionality.html#5214" class="Function">global-funext</a> <a id="5248" class="Symbol">=</a> <a id="5250" class="Symbol">∀</a>  <a id="5253" class="Symbol">{</a><a id="5254" href="Overture.Extensionality.html#5254" class="Bound">𝓤</a> <a id="5256" href="Overture.Extensionality.html#5256" class="Bound">𝓥</a><a id="5257" class="Symbol">}</a> <a id="5259" class="Symbol">→</a> <a id="5261" href="Overture.Extensionality.html#3491" class="Function">funext</a> <a id="5268" href="Overture.Extensionality.html#5254" class="Bound">𝓤</a> <a id="5270" href="Overture.Extensionality.html#5256" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5274" href="Overture.Extensionality.html#5274" class="Function">global-dfunext</a> <a id="5289" class="Symbol">:</a> <a id="5291" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5295" href="Overture.Extensionality.html#5274" class="Function">global-dfunext</a> <a id="5310" class="Symbol">=</a> <a id="5312" class="Symbol">∀</a> <a id="5314" class="Symbol">{</a><a id="5315" href="Overture.Extensionality.html#5315" class="Bound">𝓤</a> <a id="5317" href="Overture.Extensionality.html#5317" class="Bound">𝓥</a><a id="5318" class="Symbol">}</a> <a id="5320" class="Symbol">→</a> <a id="5322" href="Overture.Extensionality.html#3696" class="Function">dfunext</a> <a id="5330" href="Overture.Extensionality.html#5315" class="Bound">𝓤</a> <a id="5332" href="Overture.Extensionality.html#5317" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Overture.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5628" class="Keyword">open</a> <a id="5633" class="Keyword">import</a> <a id="5640" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5667" class="Keyword">using</a> <a id="5673" class="Symbol">(</a><a id="5674" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5680" class="Symbol">;</a> <a id="5682" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5689" class="Symbol">)</a> <a id="5691" class="Keyword">public</a>
<a id="5698" class="Keyword">open</a> <a id="5703" class="Keyword">import</a> <a id="5710" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5736" class="Keyword">using</a> <a id="5742" class="Symbol">(</a><a id="5743" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5757" class="Symbol">)</a> <a id="5759" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6036" class="Keyword">open</a> <a id="6041" class="Keyword">import</a> <a id="6048" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6057" class="Keyword">using</a> <a id="6063" class="Symbol">(</a><a id="6064" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6067" class="Symbol">)</a> <a id="6069" class="Keyword">public</a>

<a id="6077" class="Keyword">module</a> <a id="6084" href="Overture.Extensionality.html#6084" class="Module">_</a> <a id="6086" class="Symbol">{</a><a id="6087" href="Overture.Extensionality.html#6087" class="Bound">𝓤</a> <a id="6089" href="Overture.Extensionality.html#6089" class="Bound">𝓦</a> <a id="6091" class="Symbol">:</a> <a id="6093" href="Universes.html#205" class="Postulate">Universe</a><a id="6101" class="Symbol">}</a> <a id="6103" class="Keyword">where</a>

 <a id="6111" href="Overture.Extensionality.html#6111" class="Function">extfun</a> <a id="6118" class="Symbol">:</a> <a id="6120" class="Symbol">{</a><a id="6121" href="Overture.Extensionality.html#6121" class="Bound">A</a> <a id="6123" class="Symbol">:</a> <a id="6125" href="Overture.Extensionality.html#6087" class="Bound">𝓤</a> <a id="6127" href="Universes.html#403" class="Function Operator">̇</a><a id="6128" class="Symbol">}{</a><a id="6130" href="Overture.Extensionality.html#6130" class="Bound">B</a> <a id="6132" class="Symbol">:</a> <a id="6134" href="Overture.Extensionality.html#6089" class="Bound">𝓦</a> <a id="6136" href="Universes.html#403" class="Function Operator">̇</a><a id="6137" class="Symbol">}{</a><a id="6139" href="Overture.Extensionality.html#6139" class="Bound">f</a> <a id="6141" href="Overture.Extensionality.html#6141" class="Bound">g</a> <a id="6143" class="Symbol">:</a> <a id="6145" href="Overture.Extensionality.html#6121" class="Bound">A</a> <a id="6147" class="Symbol">→</a> <a id="6149" href="Overture.Extensionality.html#6130" class="Bound">B</a><a id="6150" class="Symbol">}</a> <a id="6152" class="Symbol">→</a> <a id="6154" href="Overture.Extensionality.html#6139" class="Bound">f</a> <a id="6156" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6158" href="Overture.Extensionality.html#6141" class="Bound">g</a>  <a id="6161" class="Symbol">→</a>  <a id="6164" href="Overture.Extensionality.html#6139" class="Bound">f</a> <a id="6166" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6168" href="Overture.Extensionality.html#6141" class="Bound">g</a>
 <a id="6171" href="Overture.Extensionality.html#6111" class="Function">extfun</a> <a id="6178" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6183" class="Symbol">_</a> <a id="6185" class="Symbol">=</a> <a id="6187" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

 <a id="6314" href="Overture.Extensionality.html#6314" class="Function">extdfun</a> <a id="6322" class="Symbol">:</a> <a id="6324" class="Symbol">{</a><a id="6325" href="Overture.Extensionality.html#6325" class="Bound">A</a> <a id="6327" class="Symbol">:</a> <a id="6329" href="Overture.Extensionality.html#6087" class="Bound">𝓤</a> <a id="6331" href="Universes.html#403" class="Function Operator">̇</a> <a id="6333" class="Symbol">}{</a><a id="6335" href="Overture.Extensionality.html#6335" class="Bound">B</a> <a id="6337" class="Symbol">:</a> <a id="6339" href="Overture.Extensionality.html#6325" class="Bound">A</a> <a id="6341" class="Symbol">→</a> <a id="6343" href="Overture.Extensionality.html#6089" class="Bound">𝓦</a> <a id="6345" href="Universes.html#403" class="Function Operator">̇</a> <a id="6347" class="Symbol">}(</a><a id="6349" href="Overture.Extensionality.html#6349" class="Bound">f</a> <a id="6351" href="Overture.Extensionality.html#6351" class="Bound">g</a> <a id="6353" class="Symbol">:</a> <a id="6355" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6357" href="Overture.Extensionality.html#6335" class="Bound">B</a><a id="6358" class="Symbol">)</a> <a id="6360" class="Symbol">→</a> <a id="6362" href="Overture.Extensionality.html#6349" class="Bound">f</a> <a id="6364" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6366" href="Overture.Extensionality.html#6351" class="Bound">g</a> <a id="6368" class="Symbol">→</a> <a id="6370" href="Overture.Extensionality.html#6349" class="Bound">f</a> <a id="6372" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6374" href="Overture.Extensionality.html#6351" class="Bound">g</a>
 <a id="6377" href="Overture.Extensionality.html#6314" class="Function">extdfun</a> <a id="6385" class="Symbol">_</a> <a id="6387" class="Symbol">_</a> <a id="6389" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6394" class="Symbol">_</a> <a id="6396" class="Symbol">=</a> <a id="6398" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8259" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8266" href="Overture.Extensionality.html#8266" class="Module">hide-tt-defs</a> <a id="8279" class="Symbol">{</a><a id="8280" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8282" class="Symbol">:</a> <a id="8284" href="Universes.html#205" class="Postulate">Universe</a><a id="8292" class="Symbol">}</a> <a id="8294" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8302" href="Overture.Extensionality.html#8302" class="Function">is-center</a> <a id="8312" class="Symbol">:</a> <a id="8314" class="Symbol">(</a><a id="8315" href="Overture.Extensionality.html#8315" class="Bound">A</a> <a id="8317" class="Symbol">:</a> <a id="8319" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8321" href="Universes.html#403" class="Function Operator">̇</a> <a id="8323" class="Symbol">)</a> <a id="8325" class="Symbol">→</a> <a id="8327" href="Overture.Extensionality.html#8315" class="Bound">A</a> <a id="8329" class="Symbol">→</a> <a id="8331" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8333" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8336" href="Overture.Extensionality.html#8302" class="Function">is-center</a> <a id="8346" href="Overture.Extensionality.html#8346" class="Bound">A</a> <a id="8348" href="Overture.Extensionality.html#8348" class="Bound">c</a> <a id="8350" class="Symbol">=</a> <a id="8352" class="Symbol">(</a><a id="8353" href="Overture.Extensionality.html#8353" class="Bound">x</a> <a id="8355" class="Symbol">:</a> <a id="8357" href="Overture.Extensionality.html#8346" class="Bound">A</a><a id="8358" class="Symbol">)</a> <a id="8360" class="Symbol">→</a> <a id="8362" href="Overture.Extensionality.html#8348" class="Bound">c</a> <a id="8364" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8366" href="Overture.Extensionality.html#8353" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8370" href="Overture.Extensionality.html#8370" class="Function">is-singleton</a> <a id="8383" class="Symbol">:</a> <a id="8385" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8387" href="Universes.html#403" class="Function Operator">̇</a> <a id="8389" class="Symbol">→</a> <a id="8391" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8393" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8396" href="Overture.Extensionality.html#8370" class="Function">is-singleton</a> <a id="8409" href="Overture.Extensionality.html#8409" class="Bound">A</a> <a id="8411" class="Symbol">=</a> <a id="8413" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8415" href="Overture.Extensionality.html#8415" class="Bound">c</a> <a id="8417" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8419" href="Overture.Extensionality.html#8409" class="Bound">A</a> <a id="8421" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8423" href="Overture.Extensionality.html#8302" class="Function">is-center</a> <a id="8433" href="Overture.Extensionality.html#8409" class="Bound">A</a> <a id="8435" href="Overture.Extensionality.html#8415" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8439" href="Overture.Extensionality.html#8439" class="Function">is-subsingleton</a> <a id="8455" class="Symbol">:</a> <a id="8457" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8459" href="Universes.html#403" class="Function Operator">̇</a> <a id="8461" class="Symbol">→</a> <a id="8463" href="Overture.Extensionality.html#8280" class="Bound">𝓤</a> <a id="8465" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8468" href="Overture.Extensionality.html#8439" class="Function">is-subsingleton</a> <a id="8484" href="Overture.Extensionality.html#8484" class="Bound">A</a> <a id="8486" class="Symbol">=</a> <a id="8488" class="Symbol">(</a><a id="8489" href="Overture.Extensionality.html#8489" class="Bound">x</a> <a id="8491" href="Overture.Extensionality.html#8491" class="Bound">y</a> <a id="8493" class="Symbol">:</a> <a id="8495" href="Overture.Extensionality.html#8484" class="Bound">A</a><a id="8496" class="Symbol">)</a> <a id="8498" class="Symbol">→</a> <a id="8500" href="Overture.Extensionality.html#8489" class="Bound">x</a> <a id="8502" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8504" href="Overture.Extensionality.html#8491" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Overture.Equality.html#fn1) of the [Overture.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8799" class="Keyword">open</a> <a id="8804" class="Keyword">import</a> <a id="8811" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8824" class="Keyword">using</a> <a id="8830" class="Symbol">(</a><a id="8831" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8840" class="Symbol">;</a> <a id="8842" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8854" class="Symbol">;</a> <a id="8856" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8871" class="Symbol">)</a> <a id="8873" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9290" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9297" href="Overture.Extensionality.html#9297" class="Module">hide-tt-defs&#39;</a> <a id="9311" class="Symbol">{</a><a id="9312" href="Overture.Extensionality.html#9312" class="Bound">𝓤</a> <a id="9314" href="Overture.Extensionality.html#9314" class="Bound">𝓦</a> <a id="9316" class="Symbol">:</a> <a id="9318" href="Universes.html#205" class="Postulate">Universe</a><a id="9326" class="Symbol">}</a> <a id="9328" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9336" href="Overture.Extensionality.html#9336" class="Function">fiber</a> <a id="9342" class="Symbol">:</a> <a id="9344" class="Symbol">{</a><a id="9345" href="Overture.Extensionality.html#9345" class="Bound">A</a> <a id="9347" class="Symbol">:</a> <a id="9349" href="Overture.Extensionality.html#9312" class="Bound">𝓤</a> <a id="9351" href="Universes.html#403" class="Function Operator">̇</a> <a id="9353" class="Symbol">}</a> <a id="9355" class="Symbol">{</a><a id="9356" href="Overture.Extensionality.html#9356" class="Bound">B</a> <a id="9358" class="Symbol">:</a> <a id="9360" href="Overture.Extensionality.html#9314" class="Bound">𝓦</a> <a id="9362" href="Universes.html#403" class="Function Operator">̇</a> <a id="9364" class="Symbol">}</a> <a id="9366" class="Symbol">(</a><a id="9367" href="Overture.Extensionality.html#9367" class="Bound">f</a> <a id="9369" class="Symbol">:</a> <a id="9371" href="Overture.Extensionality.html#9345" class="Bound">A</a> <a id="9373" class="Symbol">→</a> <a id="9375" href="Overture.Extensionality.html#9356" class="Bound">B</a><a id="9376" class="Symbol">)</a> <a id="9378" class="Symbol">→</a> <a id="9380" href="Overture.Extensionality.html#9356" class="Bound">B</a> <a id="9382" class="Symbol">→</a> <a id="9384" href="Overture.Extensionality.html#9312" class="Bound">𝓤</a> <a id="9386" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9388" href="Overture.Extensionality.html#9314" class="Bound">𝓦</a> <a id="9390" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9393" href="Overture.Extensionality.html#9336" class="Function">fiber</a> <a id="9399" class="Symbol">{</a><a id="9400" href="Overture.Extensionality.html#9400" class="Bound">A</a><a id="9401" class="Symbol">}</a> <a id="9403" href="Overture.Extensionality.html#9403" class="Bound">f</a> <a id="9405" href="Overture.Extensionality.html#9405" class="Bound">y</a> <a id="9407" class="Symbol">=</a> <a id="9409" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9411" href="Overture.Extensionality.html#9411" class="Bound">x</a> <a id="9413" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9415" href="Overture.Extensionality.html#9400" class="Bound">A</a> <a id="9417" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9419" href="Overture.Extensionality.html#9403" class="Bound">f</a> <a id="9421" href="Overture.Extensionality.html#9411" class="Bound">x</a> <a id="9423" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="9425" href="Overture.Extensionality.html#9405" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9531" href="Overture.Extensionality.html#9531" class="Function">is-equiv</a> <a id="9540" class="Symbol">:</a> <a id="9542" class="Symbol">{</a><a id="9543" href="Overture.Extensionality.html#9543" class="Bound">A</a> <a id="9545" class="Symbol">:</a> <a id="9547" href="Overture.Extensionality.html#9312" class="Bound">𝓤</a> <a id="9549" href="Universes.html#403" class="Function Operator">̇</a> <a id="9551" class="Symbol">}</a> <a id="9553" class="Symbol">{</a><a id="9554" href="Overture.Extensionality.html#9554" class="Bound">B</a> <a id="9556" class="Symbol">:</a> <a id="9558" href="Overture.Extensionality.html#9314" class="Bound">𝓦</a> <a id="9560" href="Universes.html#403" class="Function Operator">̇</a> <a id="9562" class="Symbol">}</a> <a id="9564" class="Symbol">→</a> <a id="9566" class="Symbol">(</a><a id="9567" href="Overture.Extensionality.html#9543" class="Bound">A</a> <a id="9569" class="Symbol">→</a> <a id="9571" href="Overture.Extensionality.html#9554" class="Bound">B</a><a id="9572" class="Symbol">)</a> <a id="9574" class="Symbol">→</a> <a id="9576" href="Overture.Extensionality.html#9312" class="Bound">𝓤</a> <a id="9578" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9580" href="Overture.Extensionality.html#9314" class="Bound">𝓦</a> <a id="9582" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9585" href="Overture.Extensionality.html#9531" class="Function">is-equiv</a> <a id="9594" href="Overture.Extensionality.html#9594" class="Bound">f</a> <a id="9596" class="Symbol">=</a> <a id="9598" class="Symbol">∀</a> <a id="9600" href="Overture.Extensionality.html#9600" class="Bound">y</a> <a id="9602" class="Symbol">→</a> <a id="9604" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9617" class="Symbol">(</a><a id="9618" href="Overture.Extensionality.html#9336" class="Function">fiber</a> <a id="9624" href="Overture.Extensionality.html#9594" class="Bound">f</a> <a id="9626" href="Overture.Extensionality.html#9600" class="Bound">y</a><a id="9627" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="9834" class="Keyword">open</a> <a id="9839" class="Keyword">import</a> <a id="9846" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9863" class="Keyword">using</a> <a id="9869" class="Symbol">(</a><a id="9870" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9875" class="Symbol">;</a> <a id="9877" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9885" class="Symbol">)</a> <a id="9887" class="Keyword">public</a>

<a id="9895" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9902" href="Overture.Extensionality.html#9902" class="Module">hide-hfunext</a> <a id="9915" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9923" href="Overture.Extensionality.html#9923" class="Function">hfunext</a> <a id="9931" class="Symbol">:</a>  <a id="9934" class="Symbol">∀</a> <a id="9936" href="Overture.Extensionality.html#9936" class="Bound">𝓤</a> <a id="9938" href="Overture.Extensionality.html#9938" class="Bound">𝓦</a> <a id="9940" class="Symbol">→</a> <a id="9942" class="Symbol">(</a><a id="9943" href="Overture.Extensionality.html#9936" class="Bound">𝓤</a> <a id="9945" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9947" href="Overture.Extensionality.html#9938" class="Bound">𝓦</a><a id="9948" class="Symbol">)</a><a id="9949" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9951" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9954" href="Overture.Extensionality.html#9923" class="Function">hfunext</a> <a id="9962" href="Overture.Extensionality.html#9962" class="Bound">𝓤</a> <a id="9964" href="Overture.Extensionality.html#9964" class="Bound">𝓦</a> <a id="9966" class="Symbol">=</a> <a id="9968" class="Symbol">{</a><a id="9969" href="Overture.Extensionality.html#9969" class="Bound">A</a> <a id="9971" class="Symbol">:</a> <a id="9973" href="Overture.Extensionality.html#9962" class="Bound">𝓤</a> <a id="9975" href="Universes.html#403" class="Function Operator">̇</a><a id="9976" class="Symbol">}{</a><a id="9978" href="Overture.Extensionality.html#9978" class="Bound">B</a> <a id="9980" class="Symbol">:</a> <a id="9982" href="Overture.Extensionality.html#9969" class="Bound">A</a> <a id="9984" class="Symbol">→</a> <a id="9986" href="Overture.Extensionality.html#9964" class="Bound">𝓦</a> <a id="9988" href="Universes.html#403" class="Function Operator">̇</a><a id="9989" class="Symbol">}</a> <a id="9991" class="Symbol">(</a><a id="9992" href="Overture.Extensionality.html#9992" class="Bound">f</a> <a id="9994" href="Overture.Extensionality.html#9994" class="Bound">g</a> <a id="9996" class="Symbol">:</a> <a id="9998" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10000" href="Overture.Extensionality.html#9978" class="Bound">B</a><a id="10001" class="Symbol">)</a> <a id="10003" class="Symbol">→</a> <a id="10005" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10014" class="Symbol">(</a><a id="10015" href="Overture.Extensionality.html#6314" class="Function">extdfun</a> <a id="10023" href="Overture.Extensionality.html#9992" class="Bound">f</a> <a id="10025" href="Overture.Extensionality.html#9994" class="Bound">g</a><a id="10026" class="Symbol">)</a>
<a id="10028" class="Keyword">open</a> <a id="10033" class="Keyword">import</a> <a id="10040" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10068" class="Keyword">using</a> <a id="10074" class="Symbol">(</a><a id="10075" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10082" class="Symbol">)</a> <a id="10084" class="Keyword">public</a>

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
