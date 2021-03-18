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

What does it mean to say that two functions `f g : X → Y` are equal?

Suppose f and g are defined on X = ℤ (the integers) as follows: f x := x + 2 and g x := ((2 * x) - 8)/2 + 6.  Would you say that f and g are equal?

If you know a little bit of basic algebra, then you probably can't resist the urge to reduce g to the form x + 2 and proclaim that f and g are, indeed, equal.  And you would be right, at least in middle school, and the discussion would end there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions f and g above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves, at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions f and g both of which take a list as input and produce as output a correctly sorted version of that list?  Are the functions the same?  What if f were defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while g used [quick sort](https://en.wikipedia.org/wiki/Quicksort).  I think most of us would then agree that such f and g are not equal.

In each of the examples above, it is common to say that the two functions f and g are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same (external) output when given the same input, but f and g not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their (internal) definitions differ.

In this module, we describe types (many of which were already defined by Martín Escardó in his [Type Topology][] library) that manifest this notion of *extensional equality of functions*, or *function extensionality*.

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

The natural notion of function equality, which is often called *point-wise equality*, is defined as follows: `∀ x → f x ≡ g x`.  Here is how this notion is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="2956" class="Keyword">module</a> <a id="hide-funext"></a><a id="2963" href="Prelude.Extensionality.html#2963" class="Module">hide-funext</a> <a id="2975" class="Keyword">where</a>

 <a id="hide-funext._∼_"></a><a id="2983" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a> <a id="2987" class="Symbol">:</a> <a id="2989" class="Symbol">{</a><a id="2990" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="2992" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="2994" class="Symbol">:</a> <a id="2996" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3004" class="Symbol">}{</a><a id="3006" href="Prelude.Extensionality.html#3006" class="Bound">X</a> <a id="3008" class="Symbol">:</a> <a id="3010" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="3012" href="Universes.html#403" class="Function Operator">̇</a> <a id="3014" class="Symbol">}</a> <a id="3016" class="Symbol">{</a><a id="3017" href="Prelude.Extensionality.html#3017" class="Bound">A</a> <a id="3019" class="Symbol">:</a> <a id="3021" href="Prelude.Extensionality.html#3006" class="Bound">X</a> <a id="3023" class="Symbol">→</a> <a id="3025" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="3027" href="Universes.html#403" class="Function Operator">̇</a> <a id="3029" class="Symbol">}</a> <a id="3031" class="Symbol">→</a> <a id="3033" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3035" href="Prelude.Extensionality.html#3017" class="Bound">A</a> <a id="3037" class="Symbol">→</a> <a id="3039" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3041" href="Prelude.Extensionality.html#3017" class="Bound">A</a> <a id="3043" class="Symbol">→</a> <a id="3045" href="Prelude.Extensionality.html#2990" class="Bound">𝓤</a> <a id="3047" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3049" href="Prelude.Extensionality.html#2992" class="Bound">𝓥</a> <a id="3051" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3054" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3056" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3058" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3060" class="Symbol">=</a> <a id="3062" class="Symbol">∀</a> <a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3066" class="Symbol">→</a> <a id="3068" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3070" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3072" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="3074" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3076" href="Prelude.Extensionality.html#3064" class="Bound">x</a>

 <a id="3080" class="Keyword">infix</a> <a id="3086" class="Number">0</a> <a id="3088" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a>

</pre>

**Function extensionality** is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3517" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3524" class="Symbol">:</a> <a id="3526" class="Symbol">∀</a> <a id="3528" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3530" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a>  <a id="3533" class="Symbol">→</a> <a id="3535" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3537" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3539" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3541" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a> <a id="3543" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3545" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3548" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3555" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3557" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3559" class="Symbol">=</a> <a id="3561" class="Symbol">{</a><a id="3562" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3564" class="Symbol">:</a> <a id="3566" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3568" href="Universes.html#403" class="Function Operator">̇</a> <a id="3570" class="Symbol">}</a> <a id="3572" class="Symbol">{</a><a id="3573" href="Prelude.Extensionality.html#3573" class="Bound">B</a> <a id="3575" class="Symbol">:</a> <a id="3577" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a> <a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">{</a><a id="3584" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3586" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3588" class="Symbol">:</a> <a id="3590" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3592" class="Symbol">→</a> <a id="3594" href="Prelude.Extensionality.html#3573" class="Bound">B</a><a id="3595" class="Symbol">}</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3601" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3603" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3605" class="Symbol">→</a> <a id="3607" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3609" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="3611" href="Prelude.Extensionality.html#3586" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3722" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3730" class="Symbol">:</a> <a id="3732" class="Symbol">∀</a> <a id="3734" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3736" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3738" class="Symbol">→</a> <a id="3740" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3742" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3744" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3746" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3748" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3750" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3753" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3761" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3763" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3765" class="Symbol">=</a> <a id="3767" class="Symbol">{</a><a id="3768" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3770" class="Symbol">:</a> <a id="3772" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3774" href="Universes.html#403" class="Function Operator">̇</a> <a id="3776" class="Symbol">}{</a><a id="3778" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3780" class="Symbol">:</a> <a id="3782" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3784" class="Symbol">→</a> <a id="3786" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3788" href="Universes.html#403" class="Function Operator">̇</a> <a id="3790" class="Symbol">}{</a><a id="3792" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3794" href="Prelude.Extensionality.html#3794" class="Bound">g</a> <a id="3796" class="Symbol">:</a> <a id="3798" class="Symbol">∀(</a><a id="3800" href="Prelude.Extensionality.html#3800" class="Bound">x</a> <a id="3802" class="Symbol">:</a> <a id="3804" href="Prelude.Extensionality.html#3768" class="Bound">A</a><a id="3805" class="Symbol">)</a> <a id="3807" class="Symbol">→</a> <a id="3809" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3811" href="Prelude.Extensionality.html#3800" class="Bound">x</a><a id="3812" class="Symbol">}</a> <a id="3814" class="Symbol">→</a>  <a id="3817" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3819" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3821" href="Prelude.Extensionality.html#3794" class="Bound">g</a>  <a id="3824" class="Symbol">→</a>  <a id="3827" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3829" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="3831" href="Prelude.Extensionality.html#3794" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called "pointwise equality of functions" is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following (which is pointed out to us by <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó in his notes</a>), *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="4969" href="Prelude.Extensionality.html#4969" class="Function">global-funext</a> <a id="4983" class="Symbol">:</a> <a id="4985" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4989" href="Prelude.Extensionality.html#4969" class="Function">global-funext</a> <a id="5003" class="Symbol">=</a> <a id="5005" class="Symbol">∀</a>  <a id="5008" class="Symbol">{</a><a id="5009" href="Prelude.Extensionality.html#5009" class="Bound">𝓤</a> <a id="5011" href="Prelude.Extensionality.html#5011" class="Bound">𝓥</a><a id="5012" class="Symbol">}</a> <a id="5014" class="Symbol">→</a> <a id="5016" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="5023" href="Prelude.Extensionality.html#5009" class="Bound">𝓤</a> <a id="5025" href="Prelude.Extensionality.html#5011" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5029" href="Prelude.Extensionality.html#5029" class="Function">global-dfunext</a> <a id="5044" class="Symbol">:</a> <a id="5046" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5050" href="Prelude.Extensionality.html#5029" class="Function">global-dfunext</a> <a id="5065" class="Symbol">=</a> <a id="5067" class="Symbol">∀</a> <a id="5069" class="Symbol">{</a><a id="5070" href="Prelude.Extensionality.html#5070" class="Bound">𝓤</a> <a id="5072" href="Prelude.Extensionality.html#5072" class="Bound">𝓥</a><a id="5073" class="Symbol">}</a> <a id="5075" class="Symbol">→</a> <a id="5077" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="5085" href="Prelude.Extensionality.html#5070" class="Bound">𝓤</a> <a id="5087" href="Prelude.Extensionality.html#5072" class="Bound">𝓥</a>

</pre>

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5547" class="Keyword">open</a> <a id="5552" class="Keyword">import</a> <a id="5559" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5586" class="Keyword">using</a> <a id="5592" class="Symbol">(</a><a id="5593" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5596" class="Symbol">;</a> <a id="5598" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5604" class="Symbol">;</a> <a id="5606" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5613" class="Symbol">)</a> <a id="5615" class="Keyword">public</a>
<a id="5622" class="Keyword">open</a> <a id="5627" class="Keyword">import</a> <a id="5634" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5660" class="Keyword">using</a> <a id="5666" class="Symbol">(</a><a id="5667" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5681" class="Symbol">)</a> <a id="5683" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="6012" class="Keyword">open</a> <a id="6017" class="Keyword">import</a> <a id="6024" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6033" class="Keyword">using</a> <a id="6039" class="Symbol">(</a><a id="6040" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6043" class="Symbol">)</a> <a id="6045" class="Keyword">public</a>

<a id="6053" class="Keyword">module</a> <a id="6060" href="Prelude.Extensionality.html#6060" class="Module">_</a> <a id="6062" class="Symbol">{</a><a id="6063" href="Prelude.Extensionality.html#6063" class="Bound">𝓤</a> <a id="6065" href="Prelude.Extensionality.html#6065" class="Bound">𝓦</a> <a id="6067" class="Symbol">:</a> <a id="6069" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6077" class="Symbol">}</a> <a id="6079" class="Keyword">where</a>

 <a id="6087" href="Prelude.Extensionality.html#6087" class="Function">extfun</a> <a id="6094" class="Symbol">:</a> <a id="6096" class="Symbol">{</a><a id="6097" href="Prelude.Extensionality.html#6097" class="Bound">A</a> <a id="6099" class="Symbol">:</a> <a id="6101" href="Prelude.Extensionality.html#6063" class="Bound">𝓤</a> <a id="6103" href="Universes.html#403" class="Function Operator">̇</a><a id="6104" class="Symbol">}{</a><a id="6106" href="Prelude.Extensionality.html#6106" class="Bound">B</a> <a id="6108" class="Symbol">:</a> <a id="6110" href="Prelude.Extensionality.html#6065" class="Bound">𝓦</a> <a id="6112" href="Universes.html#403" class="Function Operator">̇</a><a id="6113" class="Symbol">}{</a><a id="6115" href="Prelude.Extensionality.html#6115" class="Bound">f</a> <a id="6117" href="Prelude.Extensionality.html#6117" class="Bound">g</a> <a id="6119" class="Symbol">:</a> <a id="6121" href="Prelude.Extensionality.html#6097" class="Bound">A</a> <a id="6123" class="Symbol">→</a> <a id="6125" href="Prelude.Extensionality.html#6106" class="Bound">B</a><a id="6126" class="Symbol">}</a> <a id="6128" class="Symbol">→</a> <a id="6130" href="Prelude.Extensionality.html#6115" class="Bound">f</a> <a id="6132" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="6134" href="Prelude.Extensionality.html#6117" class="Bound">g</a>  <a id="6137" class="Symbol">→</a>  <a id="6140" href="Prelude.Extensionality.html#6115" class="Bound">f</a> <a id="6142" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6144" href="Prelude.Extensionality.html#6117" class="Bound">g</a>
 <a id="6147" href="Prelude.Extensionality.html#6087" class="Function">extfun</a> <a id="6154" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6159" class="Symbol">_</a> <a id="6161" class="Symbol">=</a> <a id="6163" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6289" href="Prelude.Extensionality.html#6289" class="Function">extdfun</a> <a id="6297" class="Symbol">:</a> <a id="6299" class="Symbol">{</a><a id="6300" href="Prelude.Extensionality.html#6300" class="Bound">A</a> <a id="6302" class="Symbol">:</a> <a id="6304" href="Prelude.Extensionality.html#6063" class="Bound">𝓤</a> <a id="6306" href="Universes.html#403" class="Function Operator">̇</a> <a id="6308" class="Symbol">}{</a><a id="6310" href="Prelude.Extensionality.html#6310" class="Bound">B</a> <a id="6312" class="Symbol">:</a> <a id="6314" href="Prelude.Extensionality.html#6300" class="Bound">A</a> <a id="6316" class="Symbol">→</a> <a id="6318" href="Prelude.Extensionality.html#6065" class="Bound">𝓦</a> <a id="6320" href="Universes.html#403" class="Function Operator">̇</a> <a id="6322" class="Symbol">}(</a><a id="6324" href="Prelude.Extensionality.html#6324" class="Bound">f</a> <a id="6326" href="Prelude.Extensionality.html#6326" class="Bound">g</a> <a id="6328" class="Symbol">:</a> <a id="6330" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6332" href="Prelude.Extensionality.html#6310" class="Bound">B</a><a id="6333" class="Symbol">)</a> <a id="6335" class="Symbol">→</a> <a id="6337" href="Prelude.Extensionality.html#6324" class="Bound">f</a> <a id="6339" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="6341" href="Prelude.Extensionality.html#6326" class="Bound">g</a> <a id="6343" class="Symbol">→</a> <a id="6345" href="Prelude.Extensionality.html#6324" class="Bound">f</a> <a id="6347" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6349" href="Prelude.Extensionality.html#6326" class="Bound">g</a>
 <a id="6352" href="Prelude.Extensionality.html#6289" class="Function">extdfun</a> <a id="6360" class="Symbol">_</a> <a id="6362" class="Symbol">_</a> <a id="6364" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6369" class="Symbol">_</a> <a id="6371" class="Symbol">=</a> <a id="6373" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to assume we have a proof for this type. That is, we could postulate that function extensionality holds and assume we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8691" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8698" href="Prelude.Extensionality.html#8698" class="Module">hide-tt-defs</a> <a id="8711" class="Symbol">{</a><a id="8712" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8714" class="Symbol">:</a> <a id="8716" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8724" class="Symbol">}</a> <a id="8726" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8734" href="Prelude.Extensionality.html#8734" class="Function">is-center</a> <a id="8744" class="Symbol">:</a> <a id="8746" class="Symbol">(</a><a id="8747" href="Prelude.Extensionality.html#8747" class="Bound">X</a> <a id="8749" class="Symbol">:</a> <a id="8751" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8753" href="Universes.html#403" class="Function Operator">̇</a> <a id="8755" class="Symbol">)</a> <a id="8757" class="Symbol">→</a> <a id="8759" href="Prelude.Extensionality.html#8747" class="Bound">X</a> <a id="8761" class="Symbol">→</a> <a id="8763" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8765" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8768" href="Prelude.Extensionality.html#8734" class="Function">is-center</a> <a id="8778" href="Prelude.Extensionality.html#8778" class="Bound">X</a> <a id="8780" href="Prelude.Extensionality.html#8780" class="Bound">c</a> <a id="8782" class="Symbol">=</a> <a id="8784" class="Symbol">(</a><a id="8785" href="Prelude.Extensionality.html#8785" class="Bound">x</a> <a id="8787" class="Symbol">:</a> <a id="8789" href="Prelude.Extensionality.html#8778" class="Bound">X</a><a id="8790" class="Symbol">)</a> <a id="8792" class="Symbol">→</a> <a id="8794" href="Prelude.Extensionality.html#8780" class="Bound">c</a> <a id="8796" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="8798" href="Prelude.Extensionality.html#8785" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8802" href="Prelude.Extensionality.html#8802" class="Function">is-singleton</a> <a id="8815" class="Symbol">:</a> <a id="8817" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8819" href="Universes.html#403" class="Function Operator">̇</a> <a id="8821" class="Symbol">→</a> <a id="8823" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8825" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8828" href="Prelude.Extensionality.html#8802" class="Function">is-singleton</a> <a id="8841" href="Prelude.Extensionality.html#8841" class="Bound">X</a> <a id="8843" class="Symbol">=</a> <a id="8845" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8847" href="Prelude.Extensionality.html#8847" class="Bound">c</a> <a id="8849" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8851" href="Prelude.Extensionality.html#8841" class="Bound">X</a> <a id="8853" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8855" href="Prelude.Extensionality.html#8734" class="Function">is-center</a> <a id="8865" href="Prelude.Extensionality.html#8841" class="Bound">X</a> <a id="8867" href="Prelude.Extensionality.html#8847" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8871" href="Prelude.Extensionality.html#8871" class="Function">is-subsingleton</a> <a id="8887" class="Symbol">:</a> <a id="8889" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8891" href="Universes.html#403" class="Function Operator">̇</a> <a id="8893" class="Symbol">→</a> <a id="8895" href="Prelude.Extensionality.html#8712" class="Bound">𝓤</a> <a id="8897" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8900" href="Prelude.Extensionality.html#8871" class="Function">is-subsingleton</a> <a id="8916" href="Prelude.Extensionality.html#8916" class="Bound">X</a> <a id="8918" class="Symbol">=</a> <a id="8920" class="Symbol">(</a><a id="8921" href="Prelude.Extensionality.html#8921" class="Bound">x</a> <a id="8923" href="Prelude.Extensionality.html#8923" class="Bound">y</a> <a id="8925" class="Symbol">:</a> <a id="8927" href="Prelude.Extensionality.html#8916" class="Bound">X</a><a id="8928" class="Symbol">)</a> <a id="8930" class="Symbol">→</a> <a id="8932" href="Prelude.Extensionality.html#8921" class="Bound">x</a> <a id="8934" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="8936" href="Prelude.Extensionality.html#8923" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9229" class="Keyword">open</a> <a id="9234" class="Keyword">import</a> <a id="9241" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9254" class="Keyword">using</a> <a id="9260" class="Symbol">(</a><a id="9261" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9270" class="Symbol">;</a> <a id="9272" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9284" class="Symbol">;</a> <a id="9286" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9301" class="Symbol">)</a> <a id="9303" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="10142" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="10149" href="Prelude.Extensionality.html#10149" class="Module">hide-tt-defs&#39;</a> <a id="10163" class="Symbol">{</a><a id="10164" href="Prelude.Extensionality.html#10164" class="Bound">𝓤</a> <a id="10166" href="Prelude.Extensionality.html#10166" class="Bound">𝓦</a> <a id="10168" class="Symbol">:</a> <a id="10170" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10178" class="Symbol">}</a> <a id="10180" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="10188" href="Prelude.Extensionality.html#10188" class="Function">fiber</a> <a id="10194" class="Symbol">:</a> <a id="10196" class="Symbol">{</a><a id="10197" href="Prelude.Extensionality.html#10197" class="Bound">X</a> <a id="10199" class="Symbol">:</a> <a id="10201" href="Prelude.Extensionality.html#10164" class="Bound">𝓤</a> <a id="10203" href="Universes.html#403" class="Function Operator">̇</a> <a id="10205" class="Symbol">}</a> <a id="10207" class="Symbol">{</a><a id="10208" href="Prelude.Extensionality.html#10208" class="Bound">Y</a> <a id="10210" class="Symbol">:</a> <a id="10212" href="Prelude.Extensionality.html#10166" class="Bound">𝓦</a> <a id="10214" href="Universes.html#403" class="Function Operator">̇</a> <a id="10216" class="Symbol">}</a> <a id="10218" class="Symbol">(</a><a id="10219" href="Prelude.Extensionality.html#10219" class="Bound">f</a> <a id="10221" class="Symbol">:</a> <a id="10223" href="Prelude.Extensionality.html#10197" class="Bound">X</a> <a id="10225" class="Symbol">→</a> <a id="10227" href="Prelude.Extensionality.html#10208" class="Bound">Y</a><a id="10228" class="Symbol">)</a> <a id="10230" class="Symbol">→</a> <a id="10232" href="Prelude.Extensionality.html#10208" class="Bound">Y</a> <a id="10234" class="Symbol">→</a> <a id="10236" href="Prelude.Extensionality.html#10164" class="Bound">𝓤</a> <a id="10238" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10240" href="Prelude.Extensionality.html#10166" class="Bound">𝓦</a> <a id="10242" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10245" href="Prelude.Extensionality.html#10188" class="Function">fiber</a> <a id="10251" class="Symbol">{</a><a id="10252" href="Prelude.Extensionality.html#10252" class="Bound">X</a><a id="10253" class="Symbol">}</a> <a id="10255" href="Prelude.Extensionality.html#10255" class="Bound">f</a> <a id="10257" href="Prelude.Extensionality.html#10257" class="Bound">y</a> <a id="10259" class="Symbol">=</a> <a id="10261" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="10263" href="Prelude.Extensionality.html#10263" class="Bound">x</a> <a id="10265" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="10267" href="Prelude.Extensionality.html#10252" class="Bound">X</a> <a id="10269" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="10271" href="Prelude.Extensionality.html#10255" class="Bound">f</a> <a id="10273" href="Prelude.Extensionality.html#10263" class="Bound">x</a> <a id="10275" href="Prelude.Equality.html#1364" class="Datatype Operator">≡</a> <a id="10277" href="Prelude.Extensionality.html#10257" class="Bound">y</a>

</pre>

A function is called an **equivalence** if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="10385" href="Prelude.Extensionality.html#10385" class="Function">is-equiv</a> <a id="10394" class="Symbol">:</a> <a id="10396" class="Symbol">{</a><a id="10397" href="Prelude.Extensionality.html#10397" class="Bound">X</a> <a id="10399" class="Symbol">:</a> <a id="10401" href="Prelude.Extensionality.html#10164" class="Bound">𝓤</a> <a id="10403" href="Universes.html#403" class="Function Operator">̇</a> <a id="10405" class="Symbol">}</a> <a id="10407" class="Symbol">{</a><a id="10408" href="Prelude.Extensionality.html#10408" class="Bound">Y</a> <a id="10410" class="Symbol">:</a> <a id="10412" href="Prelude.Extensionality.html#10166" class="Bound">𝓦</a> <a id="10414" href="Universes.html#403" class="Function Operator">̇</a> <a id="10416" class="Symbol">}</a> <a id="10418" class="Symbol">→</a> <a id="10420" class="Symbol">(</a><a id="10421" href="Prelude.Extensionality.html#10397" class="Bound">X</a> <a id="10423" class="Symbol">→</a> <a id="10425" href="Prelude.Extensionality.html#10408" class="Bound">Y</a><a id="10426" class="Symbol">)</a> <a id="10428" class="Symbol">→</a> <a id="10430" href="Prelude.Extensionality.html#10164" class="Bound">𝓤</a> <a id="10432" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10434" href="Prelude.Extensionality.html#10166" class="Bound">𝓦</a> <a id="10436" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10439" href="Prelude.Extensionality.html#10385" class="Function">is-equiv</a> <a id="10448" href="Prelude.Extensionality.html#10448" class="Bound">f</a> <a id="10450" class="Symbol">=</a> <a id="10452" class="Symbol">∀</a> <a id="10454" href="Prelude.Extensionality.html#10454" class="Bound">y</a> <a id="10456" class="Symbol">→</a> <a id="10458" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="10471" class="Symbol">(</a><a id="10472" href="Prelude.Extensionality.html#10188" class="Function">fiber</a> <a id="10478" href="Prelude.Extensionality.html#10448" class="Bound">f</a> <a id="10480" href="Prelude.Extensionality.html#10454" class="Bound">y</a><a id="10481" class="Symbol">)</a>

</pre>

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>  We will precede its definition with a public import statement so that the types we described above, originally defined in the Type Topology][], will be available throughout the remainder of the [UALib][].

<pre class="Agda">

<a id="10890" class="Keyword">open</a> <a id="10895" class="Keyword">import</a> <a id="10902" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10919" class="Keyword">using</a> <a id="10925" class="Symbol">(</a><a id="10926" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10931" class="Symbol">;</a> <a id="10933" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10941" class="Symbol">)</a> <a id="10943" class="Keyword">public</a>

<a id="10951" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10958" href="Prelude.Extensionality.html#10958" class="Module">hide-hfunext</a> <a id="10971" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10979" href="Prelude.Extensionality.html#10979" class="Function">hfunext</a> <a id="10987" class="Symbol">:</a> <a id="10989" class="Symbol">(</a><a id="10990" href="Prelude.Extensionality.html#10990" class="Bound">𝓤</a> <a id="10992" href="Prelude.Extensionality.html#10992" class="Bound">𝓦</a> <a id="10994" class="Symbol">:</a> <a id="10996" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="11004" class="Symbol">)</a> <a id="11006" class="Symbol">→</a> <a id="11008" class="Symbol">(</a><a id="11009" href="Prelude.Extensionality.html#10990" class="Bound">𝓤</a> <a id="11011" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11013" href="Prelude.Extensionality.html#10992" class="Bound">𝓦</a><a id="11014" class="Symbol">)</a><a id="11015" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="11017" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11020" href="Prelude.Extensionality.html#10979" class="Function">hfunext</a> <a id="11028" href="Prelude.Extensionality.html#11028" class="Bound">𝓤</a> <a id="11030" href="Prelude.Extensionality.html#11030" class="Bound">𝓦</a> <a id="11032" class="Symbol">=</a> <a id="11034" class="Symbol">{</a><a id="11035" href="Prelude.Extensionality.html#11035" class="Bound">A</a> <a id="11037" class="Symbol">:</a> <a id="11039" href="Prelude.Extensionality.html#11028" class="Bound">𝓤</a> <a id="11041" href="Universes.html#403" class="Function Operator">̇</a><a id="11042" class="Symbol">}{</a><a id="11044" href="Prelude.Extensionality.html#11044" class="Bound">B</a> <a id="11046" class="Symbol">:</a> <a id="11048" href="Prelude.Extensionality.html#11035" class="Bound">A</a> <a id="11050" class="Symbol">→</a> <a id="11052" href="Prelude.Extensionality.html#11030" class="Bound">𝓦</a> <a id="11054" href="Universes.html#403" class="Function Operator">̇</a><a id="11055" class="Symbol">}</a> <a id="11057" class="Symbol">(</a><a id="11058" href="Prelude.Extensionality.html#11058" class="Bound">f</a> <a id="11060" href="Prelude.Extensionality.html#11060" class="Bound">g</a> <a id="11062" class="Symbol">:</a> <a id="11064" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="11066" href="Prelude.Extensionality.html#11044" class="Bound">B</a><a id="11067" class="Symbol">)</a> <a id="11069" class="Symbol">→</a> <a id="11071" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="11080" class="Symbol">(</a><a id="11081" href="Prelude.Extensionality.html#6289" class="Function">extdfun</a> <a id="11089" href="Prelude.Extensionality.html#11058" class="Bound">f</a> <a id="11091" href="Prelude.Extensionality.html#11060" class="Bound">g</a><a id="11092" class="Symbol">)</a>
<a id="11094" class="Keyword">open</a> <a id="11099" class="Keyword">import</a> <a id="11106" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="11134" class="Keyword">using</a> <a id="11140" class="Symbol">(</a><a id="11141" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="11148" class="Symbol">)</a> <a id="11150" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>2</sup> <span class="footnote" id="fn2"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>3</sup><span class="footnote" id="fn3"> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library.</span>

<sup>4</sup><span class="footnote" id="fn4">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

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
