---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="325" class="Symbol">{-#</a> <a id="329" class="Keyword">OPTIONS</a> <a id="337" class="Pragma">--without-K</a> <a id="349" class="Pragma">--exact-split</a> <a id="363" class="Pragma">--safe</a> <a id="370" class="Symbol">#-}</a>

<a id="375" class="Keyword">module</a> <a id="382" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="405" class="Keyword">where</a>

<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="441" class="Keyword">public</a>

</pre>

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  If you're already familiar with function extensionality, you may want to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose f and g are defined on A = ℤ (the integers) as follows: f x := x + 2 and g x := ((2 * x) - 8)/2 + 6.  Would you say that f and g are equal?

If you know a little bit of basic algebra, then you probably can't resist the urge to reduce g to the form x + 2 and proclaim that f and g are, indeed, equal.  And you would be right, at least in middle school, and the discussion would end there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions f and g above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves, at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions f and g both of which take a list as input and produce as output a correctly sorted version of that list?  Are the functions the same?  What if f were defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while g used [quick sort](https://en.wikipedia.org/wiki/Quicksort).  I think most of us would then agree that such f and g are not equal.

In each of the examples above, it is common to say that the two functions f and g are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same (external) output when given the same input, but f and g not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their (internal) definitions differ.

In this module, we describe types (many of which were already defined by Martín Escardó in his [Type Topology][] library) that manifest this notion of *extensional equality of functions*, or *function extensionality*.

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

The natural notion of function equality, which is often called *point-wise equality*, is defined as follows: `∀ x → f x ≡ g x`.  Here is how this notion is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="2956" class="Keyword">module</a> <a id="hide-funext"></a><a id="2963" href="Prelude.Extensionality.html#2963" class="Module">hide-funext</a> <a id="2975" class="Keyword">where</a>

 <a id="hide-funext._∼_"></a><a id="2983" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a> <a id="2987" class="Symbol">:</a> <a id="2989" class="Symbol">{</a><a id="2990" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="2992" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="2994" class="Symbol">:</a> <a id="2996" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3004" class="Symbol">}{</a><a id="3006" href="Prelude.Extensionality.html#3006" class="Bound">A</a> <a id="3008" class="Symbol">:</a> <a id="3010" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="3012" href="Universes.html#403" class="Function Operator">̇</a> <a id="3014" class="Symbol">}</a> <a id="3016" class="Symbol">{</a><a id="3017" href="Prelude.Extensionality.html#3017" class="Bound">B</a> <a id="3019" class="Symbol">:</a> <a id="3021" href="Prelude.Extensionality.html#3006" class="Bound">A</a> <a id="3023" class="Symbol">→</a> <a id="3025" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="3027" href="Universes.html#403" class="Function Operator">̇</a> <a id="3029" class="Symbol">}</a> <a id="3031" class="Symbol">→</a> <a id="3033" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3035" href="Prelude.Extensionality.html#3017" class="Bound">B</a> <a id="3037" class="Symbol">→</a> <a id="3039" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3041" href="Prelude.Extensionality.html#3017" class="Bound">B</a> <a id="3043" class="Symbol">→</a> <a id="3045" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="3047" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3049" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="3051" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3054" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3056" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3058" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3060" class="Symbol">=</a> <a id="3062" class="Symbol">∀</a> <a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3066" class="Symbol">→</a> <a id="3068" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3070" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3072" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3074" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3076" href="Prelude.Extensionality.html#3064" class="Bound">x</a>

 <a id="3080" class="Keyword">infix</a> <a id="3086" class="Number">0</a> <a id="3088" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a>

</pre>

*Function extensionality* is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3515" href="Prelude.Extensionality.html#3515" class="Function">funext</a> <a id="3522" class="Symbol">:</a> <a id="3524" class="Symbol">∀</a> <a id="3526" href="Prelude.Extensionality.html#3526" class="Bound">𝓤</a> <a id="3528" href="Prelude.Extensionality.html#3528" class="Bound">𝓦</a>  <a id="3531" class="Symbol">→</a> <a id="3533" href="Prelude.Extensionality.html#3526" class="Bound">𝓤</a> <a id="3535" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3537" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3539" href="Prelude.Extensionality.html#3528" class="Bound">𝓦</a> <a id="3541" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3543" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3546" href="Prelude.Extensionality.html#3515" class="Function">funext</a> <a id="3553" href="Prelude.Extensionality.html#3553" class="Bound">𝓤</a> <a id="3555" href="Prelude.Extensionality.html#3555" class="Bound">𝓦</a> <a id="3557" class="Symbol">=</a> <a id="3559" class="Symbol">{</a><a id="3560" href="Prelude.Extensionality.html#3560" class="Bound">A</a> <a id="3562" class="Symbol">:</a> <a id="3564" href="Prelude.Extensionality.html#3553" class="Bound">𝓤</a> <a id="3566" href="Universes.html#403" class="Function Operator">̇</a> <a id="3568" class="Symbol">}</a> <a id="3570" class="Symbol">{</a><a id="3571" href="Prelude.Extensionality.html#3571" class="Bound">B</a> <a id="3573" class="Symbol">:</a> <a id="3575" href="Prelude.Extensionality.html#3555" class="Bound">𝓦</a> <a id="3577" href="Universes.html#403" class="Function Operator">̇</a> <a id="3579" class="Symbol">}</a> <a id="3581" class="Symbol">{</a><a id="3582" href="Prelude.Extensionality.html#3582" class="Bound">f</a> <a id="3584" href="Prelude.Extensionality.html#3584" class="Bound">g</a> <a id="3586" class="Symbol">:</a> <a id="3588" href="Prelude.Extensionality.html#3560" class="Bound">A</a> <a id="3590" class="Symbol">→</a> <a id="3592" href="Prelude.Extensionality.html#3571" class="Bound">B</a><a id="3593" class="Symbol">}</a> <a id="3595" class="Symbol">→</a> <a id="3597" href="Prelude.Extensionality.html#3582" class="Bound">f</a> <a id="3599" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3601" href="Prelude.Extensionality.html#3584" class="Bound">g</a> <a id="3603" class="Symbol">→</a> <a id="3605" href="Prelude.Extensionality.html#3582" class="Bound">f</a> <a id="3607" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3609" href="Prelude.Extensionality.html#3584" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3720" href="Prelude.Extensionality.html#3720" class="Function">dfunext</a> <a id="3728" class="Symbol">:</a> <a id="3730" class="Symbol">∀</a> <a id="3732" href="Prelude.Extensionality.html#3732" class="Bound">𝓤</a> <a id="3734" href="Prelude.Extensionality.html#3734" class="Bound">𝓦</a> <a id="3736" class="Symbol">→</a> <a id="3738" href="Prelude.Extensionality.html#3732" class="Bound">𝓤</a> <a id="3740" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3742" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3744" href="Prelude.Extensionality.html#3734" class="Bound">𝓦</a> <a id="3746" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3748" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3751" href="Prelude.Extensionality.html#3720" class="Function">dfunext</a> <a id="3759" href="Prelude.Extensionality.html#3759" class="Bound">𝓤</a> <a id="3761" href="Prelude.Extensionality.html#3761" class="Bound">𝓦</a> <a id="3763" class="Symbol">=</a> <a id="3765" class="Symbol">{</a><a id="3766" href="Prelude.Extensionality.html#3766" class="Bound">A</a> <a id="3768" class="Symbol">:</a> <a id="3770" href="Prelude.Extensionality.html#3759" class="Bound">𝓤</a> <a id="3772" href="Universes.html#403" class="Function Operator">̇</a> <a id="3774" class="Symbol">}{</a><a id="3776" href="Prelude.Extensionality.html#3776" class="Bound">B</a> <a id="3778" class="Symbol">:</a> <a id="3780" href="Prelude.Extensionality.html#3766" class="Bound">A</a> <a id="3782" class="Symbol">→</a> <a id="3784" href="Prelude.Extensionality.html#3761" class="Bound">𝓦</a> <a id="3786" href="Universes.html#403" class="Function Operator">̇</a> <a id="3788" class="Symbol">}{</a><a id="3790" href="Prelude.Extensionality.html#3790" class="Bound">f</a> <a id="3792" href="Prelude.Extensionality.html#3792" class="Bound">g</a> <a id="3794" class="Symbol">:</a> <a id="3796" class="Symbol">∀(</a><a id="3798" href="Prelude.Extensionality.html#3798" class="Bound">x</a> <a id="3800" class="Symbol">:</a> <a id="3802" href="Prelude.Extensionality.html#3766" class="Bound">A</a><a id="3803" class="Symbol">)</a> <a id="3805" class="Symbol">→</a> <a id="3807" href="Prelude.Extensionality.html#3776" class="Bound">B</a> <a id="3809" href="Prelude.Extensionality.html#3798" class="Bound">x</a><a id="3810" class="Symbol">}</a> <a id="3812" class="Symbol">→</a>  <a id="3815" href="Prelude.Extensionality.html#3790" class="Bound">f</a> <a id="3817" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3819" href="Prelude.Extensionality.html#3792" class="Bound">g</a>  <a id="3822" class="Symbol">→</a>  <a id="3825" href="Prelude.Extensionality.html#3790" class="Bound">f</a> <a id="3827" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3829" href="Prelude.Extensionality.html#3792" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called "pointwise equality of functions" is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following (which is pointed out to us by <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó in his notes</a>), *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5189" href="Prelude.Extensionality.html#5189" class="Function">global-funext</a> <a id="5203" class="Symbol">:</a> <a id="5205" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5209" href="Prelude.Extensionality.html#5189" class="Function">global-funext</a> <a id="5223" class="Symbol">=</a> <a id="5225" class="Symbol">∀</a>  <a id="5228" class="Symbol">{</a><a id="5229" href="Prelude.Extensionality.html#5229" class="Bound">𝓤</a> <a id="5231" href="Prelude.Extensionality.html#5231" class="Bound">𝓥</a><a id="5232" class="Symbol">}</a> <a id="5234" class="Symbol">→</a> <a id="5236" href="Prelude.Extensionality.html#3515" class="Function">funext</a> <a id="5243" href="Prelude.Extensionality.html#5229" class="Bound">𝓤</a> <a id="5245" href="Prelude.Extensionality.html#5231" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5249" href="Prelude.Extensionality.html#5249" class="Function">global-dfunext</a> <a id="5264" class="Symbol">:</a> <a id="5266" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5270" href="Prelude.Extensionality.html#5249" class="Function">global-dfunext</a> <a id="5285" class="Symbol">=</a> <a id="5287" class="Symbol">∀</a> <a id="5289" class="Symbol">{</a><a id="5290" href="Prelude.Extensionality.html#5290" class="Bound">𝓤</a> <a id="5292" href="Prelude.Extensionality.html#5292" class="Bound">𝓥</a><a id="5293" class="Symbol">}</a> <a id="5295" class="Symbol">→</a> <a id="5297" href="Prelude.Extensionality.html#3720" class="Function">dfunext</a> <a id="5305" href="Prelude.Extensionality.html#5290" class="Bound">𝓤</a> <a id="5307" href="Prelude.Extensionality.html#5292" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5602" class="Keyword">open</a> <a id="5607" class="Keyword">import</a> <a id="5614" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5641" class="Keyword">using</a> <a id="5647" class="Symbol">(</a><a id="5648" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5651" class="Symbol">;</a> <a id="5653" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5659" class="Symbol">;</a> <a id="5661" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5668" class="Symbol">)</a> <a id="5670" class="Keyword">public</a>
<a id="5677" class="Keyword">open</a> <a id="5682" class="Keyword">import</a> <a id="5689" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5715" class="Keyword">using</a> <a id="5721" class="Symbol">(</a><a id="5722" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5736" class="Symbol">)</a> <a id="5738" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6015" class="Keyword">open</a> <a id="6020" class="Keyword">import</a> <a id="6027" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6036" class="Keyword">using</a> <a id="6042" class="Symbol">(</a><a id="6043" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6046" class="Symbol">)</a> <a id="6048" class="Keyword">public</a>

<a id="6056" class="Keyword">module</a> <a id="6063" href="Prelude.Extensionality.html#6063" class="Module">_</a> <a id="6065" class="Symbol">{</a><a id="6066" href="Prelude.Extensionality.html#6066" class="Bound">𝓤</a> <a id="6068" href="Prelude.Extensionality.html#6068" class="Bound">𝓦</a> <a id="6070" class="Symbol">:</a> <a id="6072" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6080" class="Symbol">}</a> <a id="6082" class="Keyword">where</a>

 <a id="6090" href="Prelude.Extensionality.html#6090" class="Function">extfun</a> <a id="6097" class="Symbol">:</a> <a id="6099" class="Symbol">{</a><a id="6100" href="Prelude.Extensionality.html#6100" class="Bound">A</a> <a id="6102" class="Symbol">:</a> <a id="6104" href="Prelude.Extensionality.html#6066" class="Bound">𝓤</a> <a id="6106" href="Universes.html#403" class="Function Operator">̇</a><a id="6107" class="Symbol">}{</a><a id="6109" href="Prelude.Extensionality.html#6109" class="Bound">B</a> <a id="6111" class="Symbol">:</a> <a id="6113" href="Prelude.Extensionality.html#6068" class="Bound">𝓦</a> <a id="6115" href="Universes.html#403" class="Function Operator">̇</a><a id="6116" class="Symbol">}{</a><a id="6118" href="Prelude.Extensionality.html#6118" class="Bound">f</a> <a id="6120" href="Prelude.Extensionality.html#6120" class="Bound">g</a> <a id="6122" class="Symbol">:</a> <a id="6124" href="Prelude.Extensionality.html#6100" class="Bound">A</a> <a id="6126" class="Symbol">→</a> <a id="6128" href="Prelude.Extensionality.html#6109" class="Bound">B</a><a id="6129" class="Symbol">}</a> <a id="6131" class="Symbol">→</a> <a id="6133" href="Prelude.Extensionality.html#6118" class="Bound">f</a> <a id="6135" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6137" href="Prelude.Extensionality.html#6120" class="Bound">g</a>  <a id="6140" class="Symbol">→</a>  <a id="6143" href="Prelude.Extensionality.html#6118" class="Bound">f</a> <a id="6145" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6147" href="Prelude.Extensionality.html#6120" class="Bound">g</a>
 <a id="6150" href="Prelude.Extensionality.html#6090" class="Function">extfun</a> <a id="6157" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6162" class="Symbol">_</a> <a id="6164" class="Symbol">=</a> <a id="6166" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6292" href="Prelude.Extensionality.html#6292" class="Function">extdfun</a> <a id="6300" class="Symbol">:</a> <a id="6302" class="Symbol">{</a><a id="6303" href="Prelude.Extensionality.html#6303" class="Bound">A</a> <a id="6305" class="Symbol">:</a> <a id="6307" href="Prelude.Extensionality.html#6066" class="Bound">𝓤</a> <a id="6309" href="Universes.html#403" class="Function Operator">̇</a> <a id="6311" class="Symbol">}{</a><a id="6313" href="Prelude.Extensionality.html#6313" class="Bound">B</a> <a id="6315" class="Symbol">:</a> <a id="6317" href="Prelude.Extensionality.html#6303" class="Bound">A</a> <a id="6319" class="Symbol">→</a> <a id="6321" href="Prelude.Extensionality.html#6068" class="Bound">𝓦</a> <a id="6323" href="Universes.html#403" class="Function Operator">̇</a> <a id="6325" class="Symbol">}(</a><a id="6327" href="Prelude.Extensionality.html#6327" class="Bound">f</a> <a id="6329" href="Prelude.Extensionality.html#6329" class="Bound">g</a> <a id="6331" class="Symbol">:</a> <a id="6333" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6335" href="Prelude.Extensionality.html#6313" class="Bound">B</a><a id="6336" class="Symbol">)</a> <a id="6338" class="Symbol">→</a> <a id="6340" href="Prelude.Extensionality.html#6327" class="Bound">f</a> <a id="6342" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6344" href="Prelude.Extensionality.html#6329" class="Bound">g</a> <a id="6346" class="Symbol">→</a> <a id="6348" href="Prelude.Extensionality.html#6327" class="Bound">f</a> <a id="6350" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6352" href="Prelude.Extensionality.html#6329" class="Bound">g</a>
 <a id="6355" href="Prelude.Extensionality.html#6292" class="Function">extdfun</a> <a id="6363" class="Symbol">_</a> <a id="6365" class="Symbol">_</a> <a id="6367" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6372" class="Symbol">_</a> <a id="6374" class="Symbol">=</a> <a id="6376" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8237" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8244" href="Prelude.Extensionality.html#8244" class="Module">hide-tt-defs</a> <a id="8257" class="Symbol">{</a><a id="8258" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8260" class="Symbol">:</a> <a id="8262" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8270" class="Symbol">}</a> <a id="8272" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8280" href="Prelude.Extensionality.html#8280" class="Function">is-center</a> <a id="8290" class="Symbol">:</a> <a id="8292" class="Symbol">(</a><a id="8293" href="Prelude.Extensionality.html#8293" class="Bound">A</a> <a id="8295" class="Symbol">:</a> <a id="8297" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8299" href="Universes.html#403" class="Function Operator">̇</a> <a id="8301" class="Symbol">)</a> <a id="8303" class="Symbol">→</a> <a id="8305" href="Prelude.Extensionality.html#8293" class="Bound">A</a> <a id="8307" class="Symbol">→</a> <a id="8309" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8311" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8314" href="Prelude.Extensionality.html#8280" class="Function">is-center</a> <a id="8324" href="Prelude.Extensionality.html#8324" class="Bound">A</a> <a id="8326" href="Prelude.Extensionality.html#8326" class="Bound">c</a> <a id="8328" class="Symbol">=</a> <a id="8330" class="Symbol">(</a><a id="8331" href="Prelude.Extensionality.html#8331" class="Bound">x</a> <a id="8333" class="Symbol">:</a> <a id="8335" href="Prelude.Extensionality.html#8324" class="Bound">A</a><a id="8336" class="Symbol">)</a> <a id="8338" class="Symbol">→</a> <a id="8340" href="Prelude.Extensionality.html#8326" class="Bound">c</a> <a id="8342" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8344" href="Prelude.Extensionality.html#8331" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8348" href="Prelude.Extensionality.html#8348" class="Function">is-singleton</a> <a id="8361" class="Symbol">:</a> <a id="8363" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8365" href="Universes.html#403" class="Function Operator">̇</a> <a id="8367" class="Symbol">→</a> <a id="8369" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8371" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8374" href="Prelude.Extensionality.html#8348" class="Function">is-singleton</a> <a id="8387" href="Prelude.Extensionality.html#8387" class="Bound">A</a> <a id="8389" class="Symbol">=</a> <a id="8391" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8393" href="Prelude.Extensionality.html#8393" class="Bound">c</a> <a id="8395" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8397" href="Prelude.Extensionality.html#8387" class="Bound">A</a> <a id="8399" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8401" href="Prelude.Extensionality.html#8280" class="Function">is-center</a> <a id="8411" href="Prelude.Extensionality.html#8387" class="Bound">A</a> <a id="8413" href="Prelude.Extensionality.html#8393" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8417" href="Prelude.Extensionality.html#8417" class="Function">is-subsingleton</a> <a id="8433" class="Symbol">:</a> <a id="8435" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8437" href="Universes.html#403" class="Function Operator">̇</a> <a id="8439" class="Symbol">→</a> <a id="8441" href="Prelude.Extensionality.html#8258" class="Bound">𝓤</a> <a id="8443" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8446" href="Prelude.Extensionality.html#8417" class="Function">is-subsingleton</a> <a id="8462" href="Prelude.Extensionality.html#8462" class="Bound">A</a> <a id="8464" class="Symbol">=</a> <a id="8466" class="Symbol">(</a><a id="8467" href="Prelude.Extensionality.html#8467" class="Bound">x</a> <a id="8469" href="Prelude.Extensionality.html#8469" class="Bound">y</a> <a id="8471" class="Symbol">:</a> <a id="8473" href="Prelude.Extensionality.html#8462" class="Bound">A</a><a id="8474" class="Symbol">)</a> <a id="8476" class="Symbol">→</a> <a id="8478" href="Prelude.Extensionality.html#8467" class="Bound">x</a> <a id="8480" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8482" href="Prelude.Extensionality.html#8469" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8775" class="Keyword">open</a> <a id="8780" class="Keyword">import</a> <a id="8787" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8800" class="Keyword">using</a> <a id="8806" class="Symbol">(</a><a id="8807" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8816" class="Symbol">;</a> <a id="8818" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8830" class="Symbol">;</a> <a id="8832" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8847" class="Symbol">)</a> <a id="8849" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9266" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9273" href="Prelude.Extensionality.html#9273" class="Module">hide-tt-defs&#39;</a> <a id="9287" class="Symbol">{</a><a id="9288" href="Prelude.Extensionality.html#9288" class="Bound">𝓤</a> <a id="9290" href="Prelude.Extensionality.html#9290" class="Bound">𝓦</a> <a id="9292" class="Symbol">:</a> <a id="9294" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9302" class="Symbol">}</a> <a id="9304" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9312" href="Prelude.Extensionality.html#9312" class="Function">fiber</a> <a id="9318" class="Symbol">:</a> <a id="9320" class="Symbol">{</a><a id="9321" href="Prelude.Extensionality.html#9321" class="Bound">A</a> <a id="9323" class="Symbol">:</a> <a id="9325" href="Prelude.Extensionality.html#9288" class="Bound">𝓤</a> <a id="9327" href="Universes.html#403" class="Function Operator">̇</a> <a id="9329" class="Symbol">}</a> <a id="9331" class="Symbol">{</a><a id="9332" href="Prelude.Extensionality.html#9332" class="Bound">B</a> <a id="9334" class="Symbol">:</a> <a id="9336" href="Prelude.Extensionality.html#9290" class="Bound">𝓦</a> <a id="9338" href="Universes.html#403" class="Function Operator">̇</a> <a id="9340" class="Symbol">}</a> <a id="9342" class="Symbol">(</a><a id="9343" href="Prelude.Extensionality.html#9343" class="Bound">f</a> <a id="9345" class="Symbol">:</a> <a id="9347" href="Prelude.Extensionality.html#9321" class="Bound">A</a> <a id="9349" class="Symbol">→</a> <a id="9351" href="Prelude.Extensionality.html#9332" class="Bound">B</a><a id="9352" class="Symbol">)</a> <a id="9354" class="Symbol">→</a> <a id="9356" href="Prelude.Extensionality.html#9332" class="Bound">B</a> <a id="9358" class="Symbol">→</a> <a id="9360" href="Prelude.Extensionality.html#9288" class="Bound">𝓤</a> <a id="9362" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9364" href="Prelude.Extensionality.html#9290" class="Bound">𝓦</a> <a id="9366" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9369" href="Prelude.Extensionality.html#9312" class="Function">fiber</a> <a id="9375" class="Symbol">{</a><a id="9376" href="Prelude.Extensionality.html#9376" class="Bound">A</a><a id="9377" class="Symbol">}</a> <a id="9379" href="Prelude.Extensionality.html#9379" class="Bound">f</a> <a id="9381" href="Prelude.Extensionality.html#9381" class="Bound">y</a> <a id="9383" class="Symbol">=</a> <a id="9385" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9387" href="Prelude.Extensionality.html#9387" class="Bound">x</a> <a id="9389" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9391" href="Prelude.Extensionality.html#9376" class="Bound">A</a> <a id="9393" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9395" href="Prelude.Extensionality.html#9379" class="Bound">f</a> <a id="9397" href="Prelude.Extensionality.html#9387" class="Bound">x</a> <a id="9399" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="9401" href="Prelude.Extensionality.html#9381" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9507" href="Prelude.Extensionality.html#9507" class="Function">is-equiv</a> <a id="9516" class="Symbol">:</a> <a id="9518" class="Symbol">{</a><a id="9519" href="Prelude.Extensionality.html#9519" class="Bound">A</a> <a id="9521" class="Symbol">:</a> <a id="9523" href="Prelude.Extensionality.html#9288" class="Bound">𝓤</a> <a id="9525" href="Universes.html#403" class="Function Operator">̇</a> <a id="9527" class="Symbol">}</a> <a id="9529" class="Symbol">{</a><a id="9530" href="Prelude.Extensionality.html#9530" class="Bound">B</a> <a id="9532" class="Symbol">:</a> <a id="9534" href="Prelude.Extensionality.html#9290" class="Bound">𝓦</a> <a id="9536" href="Universes.html#403" class="Function Operator">̇</a> <a id="9538" class="Symbol">}</a> <a id="9540" class="Symbol">→</a> <a id="9542" class="Symbol">(</a><a id="9543" href="Prelude.Extensionality.html#9519" class="Bound">A</a> <a id="9545" class="Symbol">→</a> <a id="9547" href="Prelude.Extensionality.html#9530" class="Bound">B</a><a id="9548" class="Symbol">)</a> <a id="9550" class="Symbol">→</a> <a id="9552" href="Prelude.Extensionality.html#9288" class="Bound">𝓤</a> <a id="9554" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9556" href="Prelude.Extensionality.html#9290" class="Bound">𝓦</a> <a id="9558" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9561" href="Prelude.Extensionality.html#9507" class="Function">is-equiv</a> <a id="9570" href="Prelude.Extensionality.html#9570" class="Bound">f</a> <a id="9572" class="Symbol">=</a> <a id="9574" class="Symbol">∀</a> <a id="9576" href="Prelude.Extensionality.html#9576" class="Bound">y</a> <a id="9578" class="Symbol">→</a> <a id="9580" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9593" class="Symbol">(</a><a id="9594" href="Prelude.Extensionality.html#9312" class="Function">fiber</a> <a id="9600" href="Prelude.Extensionality.html#9570" class="Bound">f</a> <a id="9602" href="Prelude.Extensionality.html#9576" class="Bound">y</a><a id="9603" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="9809" class="Keyword">open</a> <a id="9814" class="Keyword">import</a> <a id="9821" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9838" class="Keyword">using</a> <a id="9844" class="Symbol">(</a><a id="9845" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9850" class="Symbol">;</a> <a id="9852" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9860" class="Symbol">)</a> <a id="9862" class="Keyword">public</a>

<a id="9870" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9877" href="Prelude.Extensionality.html#9877" class="Module">hide-hfunext</a> <a id="9890" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9898" href="Prelude.Extensionality.html#9898" class="Function">hfunext</a> <a id="9906" class="Symbol">:</a> <a id="9908" class="Symbol">(</a><a id="9909" href="Prelude.Extensionality.html#9909" class="Bound">𝓤</a> <a id="9911" href="Prelude.Extensionality.html#9911" class="Bound">𝓦</a> <a id="9913" class="Symbol">:</a> <a id="9915" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9923" class="Symbol">)</a> <a id="9925" class="Symbol">→</a> <a id="9927" class="Symbol">(</a><a id="9928" href="Prelude.Extensionality.html#9909" class="Bound">𝓤</a> <a id="9930" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9932" href="Prelude.Extensionality.html#9911" class="Bound">𝓦</a><a id="9933" class="Symbol">)</a><a id="9934" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="9936" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9939" href="Prelude.Extensionality.html#9898" class="Function">hfunext</a> <a id="9947" href="Prelude.Extensionality.html#9947" class="Bound">𝓤</a> <a id="9949" href="Prelude.Extensionality.html#9949" class="Bound">𝓦</a> <a id="9951" class="Symbol">=</a> <a id="9953" class="Symbol">{</a><a id="9954" href="Prelude.Extensionality.html#9954" class="Bound">A</a> <a id="9956" class="Symbol">:</a> <a id="9958" href="Prelude.Extensionality.html#9947" class="Bound">𝓤</a> <a id="9960" href="Universes.html#403" class="Function Operator">̇</a><a id="9961" class="Symbol">}{</a><a id="9963" href="Prelude.Extensionality.html#9963" class="Bound">B</a> <a id="9965" class="Symbol">:</a> <a id="9967" href="Prelude.Extensionality.html#9954" class="Bound">A</a> <a id="9969" class="Symbol">→</a> <a id="9971" href="Prelude.Extensionality.html#9949" class="Bound">𝓦</a> <a id="9973" href="Universes.html#403" class="Function Operator">̇</a><a id="9974" class="Symbol">}</a> <a id="9976" class="Symbol">(</a><a id="9977" href="Prelude.Extensionality.html#9977" class="Bound">f</a> <a id="9979" href="Prelude.Extensionality.html#9979" class="Bound">g</a> <a id="9981" class="Symbol">:</a> <a id="9983" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9985" href="Prelude.Extensionality.html#9963" class="Bound">B</a><a id="9986" class="Symbol">)</a> <a id="9988" class="Symbol">→</a> <a id="9990" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="9999" class="Symbol">(</a><a id="10000" href="Prelude.Extensionality.html#6292" class="Function">extdfun</a> <a id="10008" href="Prelude.Extensionality.html#9977" class="Bound">f</a> <a id="10010" href="Prelude.Extensionality.html#9979" class="Bound">g</a><a id="10011" class="Symbol">)</a>
<a id="10013" class="Keyword">open</a> <a id="10018" class="Keyword">import</a> <a id="10025" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10053" class="Keyword">using</a> <a id="10059" class="Symbol">(</a><a id="10060" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10067" class="Symbol">)</a> <a id="10069" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>2</sup> <span class="footnote" id="fn2"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>3</sup><span class="footnote" id="fn3">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

<p></p>
<p></p>


[← Prelude.Equality](Prelude.Equality.html)
<span style="float:right;">[Prelude.Inverses →](Prelude.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
