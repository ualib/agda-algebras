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
 <a id="3054" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3056" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3058" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3060" class="Symbol">=</a> <a id="3062" class="Symbol">∀</a> <a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3066" class="Symbol">→</a> <a id="3068" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3070" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3072" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="3074" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3076" href="Prelude.Extensionality.html#3064" class="Bound">x</a>

 <a id="3080" class="Keyword">infix</a> <a id="3086" class="Number">0</a> <a id="3088" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a>

</pre>

**Function extensionality** is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3517" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3524" class="Symbol">:</a> <a id="3526" class="Symbol">∀</a> <a id="3528" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3530" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a>  <a id="3533" class="Symbol">→</a> <a id="3535" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3537" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3539" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3541" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a> <a id="3543" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3545" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3548" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3555" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3557" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3559" class="Symbol">=</a> <a id="3561" class="Symbol">{</a><a id="3562" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3564" class="Symbol">:</a> <a id="3566" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3568" href="Universes.html#403" class="Function Operator">̇</a> <a id="3570" class="Symbol">}</a> <a id="3572" class="Symbol">{</a><a id="3573" href="Prelude.Extensionality.html#3573" class="Bound">B</a> <a id="3575" class="Symbol">:</a> <a id="3577" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a> <a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">{</a><a id="3584" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3586" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3588" class="Symbol">:</a> <a id="3590" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3592" class="Symbol">→</a> <a id="3594" href="Prelude.Extensionality.html#3573" class="Bound">B</a><a id="3595" class="Symbol">}</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3601" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3603" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3605" class="Symbol">→</a> <a id="3607" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3609" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="3611" href="Prelude.Extensionality.html#3586" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3722" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3730" class="Symbol">:</a> <a id="3732" class="Symbol">∀</a> <a id="3734" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3736" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3738" class="Symbol">→</a> <a id="3740" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3742" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3744" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3746" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3748" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3750" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3753" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3761" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3763" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3765" class="Symbol">=</a> <a id="3767" class="Symbol">{</a><a id="3768" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3770" class="Symbol">:</a> <a id="3772" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3774" href="Universes.html#403" class="Function Operator">̇</a> <a id="3776" class="Symbol">}{</a><a id="3778" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3780" class="Symbol">:</a> <a id="3782" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3784" class="Symbol">→</a> <a id="3786" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3788" href="Universes.html#403" class="Function Operator">̇</a> <a id="3790" class="Symbol">}{</a><a id="3792" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3794" href="Prelude.Extensionality.html#3794" class="Bound">g</a> <a id="3796" class="Symbol">:</a> <a id="3798" class="Symbol">∀(</a><a id="3800" href="Prelude.Extensionality.html#3800" class="Bound">x</a> <a id="3802" class="Symbol">:</a> <a id="3804" href="Prelude.Extensionality.html#3768" class="Bound">A</a><a id="3805" class="Symbol">)</a> <a id="3807" class="Symbol">→</a> <a id="3809" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3811" href="Prelude.Extensionality.html#3800" class="Bound">x</a><a id="3812" class="Symbol">}</a> <a id="3814" class="Symbol">→</a>  <a id="3817" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3819" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3821" href="Prelude.Extensionality.html#3794" class="Bound">g</a>  <a id="3824" class="Symbol">→</a>  <a id="3827" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3829" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="3831" href="Prelude.Extensionality.html#3794" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called "pointwise equality of functions" is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following (which is pointed out to us by <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó in his notes</a>), *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5191" href="Prelude.Extensionality.html#5191" class="Function">global-funext</a> <a id="5205" class="Symbol">:</a> <a id="5207" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5211" href="Prelude.Extensionality.html#5191" class="Function">global-funext</a> <a id="5225" class="Symbol">=</a> <a id="5227" class="Symbol">∀</a>  <a id="5230" class="Symbol">{</a><a id="5231" href="Prelude.Extensionality.html#5231" class="Bound">𝓤</a> <a id="5233" href="Prelude.Extensionality.html#5233" class="Bound">𝓥</a><a id="5234" class="Symbol">}</a> <a id="5236" class="Symbol">→</a> <a id="5238" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="5245" href="Prelude.Extensionality.html#5231" class="Bound">𝓤</a> <a id="5247" href="Prelude.Extensionality.html#5233" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5251" href="Prelude.Extensionality.html#5251" class="Function">global-dfunext</a> <a id="5266" class="Symbol">:</a> <a id="5268" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5272" href="Prelude.Extensionality.html#5251" class="Function">global-dfunext</a> <a id="5287" class="Symbol">=</a> <a id="5289" class="Symbol">∀</a> <a id="5291" class="Symbol">{</a><a id="5292" href="Prelude.Extensionality.html#5292" class="Bound">𝓤</a> <a id="5294" href="Prelude.Extensionality.html#5294" class="Bound">𝓥</a><a id="5295" class="Symbol">}</a> <a id="5297" class="Symbol">→</a> <a id="5299" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="5307" href="Prelude.Extensionality.html#5292" class="Bound">𝓤</a> <a id="5309" href="Prelude.Extensionality.html#5294" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5604" class="Keyword">open</a> <a id="5609" class="Keyword">import</a> <a id="5616" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5643" class="Keyword">using</a> <a id="5649" class="Symbol">(</a><a id="5650" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5653" class="Symbol">;</a> <a id="5655" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5661" class="Symbol">;</a> <a id="5663" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5670" class="Symbol">)</a> <a id="5672" class="Keyword">public</a>
<a id="5679" class="Keyword">open</a> <a id="5684" class="Keyword">import</a> <a id="5691" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5717" class="Keyword">using</a> <a id="5723" class="Symbol">(</a><a id="5724" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5738" class="Symbol">)</a> <a id="5740" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="6069" class="Keyword">open</a> <a id="6074" class="Keyword">import</a> <a id="6081" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6090" class="Keyword">using</a> <a id="6096" class="Symbol">(</a><a id="6097" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6100" class="Symbol">)</a> <a id="6102" class="Keyword">public</a>

<a id="6110" class="Keyword">module</a> <a id="6117" href="Prelude.Extensionality.html#6117" class="Module">_</a> <a id="6119" class="Symbol">{</a><a id="6120" href="Prelude.Extensionality.html#6120" class="Bound">𝓤</a> <a id="6122" href="Prelude.Extensionality.html#6122" class="Bound">𝓦</a> <a id="6124" class="Symbol">:</a> <a id="6126" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6134" class="Symbol">}</a> <a id="6136" class="Keyword">where</a>

 <a id="6144" href="Prelude.Extensionality.html#6144" class="Function">extfun</a> <a id="6151" class="Symbol">:</a> <a id="6153" class="Symbol">{</a><a id="6154" href="Prelude.Extensionality.html#6154" class="Bound">A</a> <a id="6156" class="Symbol">:</a> <a id="6158" href="Prelude.Extensionality.html#6120" class="Bound">𝓤</a> <a id="6160" href="Universes.html#403" class="Function Operator">̇</a><a id="6161" class="Symbol">}{</a><a id="6163" href="Prelude.Extensionality.html#6163" class="Bound">B</a> <a id="6165" class="Symbol">:</a> <a id="6167" href="Prelude.Extensionality.html#6122" class="Bound">𝓦</a> <a id="6169" href="Universes.html#403" class="Function Operator">̇</a><a id="6170" class="Symbol">}{</a><a id="6172" href="Prelude.Extensionality.html#6172" class="Bound">f</a> <a id="6174" href="Prelude.Extensionality.html#6174" class="Bound">g</a> <a id="6176" class="Symbol">:</a> <a id="6178" href="Prelude.Extensionality.html#6154" class="Bound">A</a> <a id="6180" class="Symbol">→</a> <a id="6182" href="Prelude.Extensionality.html#6163" class="Bound">B</a><a id="6183" class="Symbol">}</a> <a id="6185" class="Symbol">→</a> <a id="6187" href="Prelude.Extensionality.html#6172" class="Bound">f</a> <a id="6189" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="6191" href="Prelude.Extensionality.html#6174" class="Bound">g</a>  <a id="6194" class="Symbol">→</a>  <a id="6197" href="Prelude.Extensionality.html#6172" class="Bound">f</a> <a id="6199" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6201" href="Prelude.Extensionality.html#6174" class="Bound">g</a>
 <a id="6204" href="Prelude.Extensionality.html#6144" class="Function">extfun</a> <a id="6211" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6216" class="Symbol">_</a> <a id="6218" class="Symbol">=</a> <a id="6220" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6346" href="Prelude.Extensionality.html#6346" class="Function">extdfun</a> <a id="6354" class="Symbol">:</a> <a id="6356" class="Symbol">{</a><a id="6357" href="Prelude.Extensionality.html#6357" class="Bound">A</a> <a id="6359" class="Symbol">:</a> <a id="6361" href="Prelude.Extensionality.html#6120" class="Bound">𝓤</a> <a id="6363" href="Universes.html#403" class="Function Operator">̇</a> <a id="6365" class="Symbol">}{</a><a id="6367" href="Prelude.Extensionality.html#6367" class="Bound">B</a> <a id="6369" class="Symbol">:</a> <a id="6371" href="Prelude.Extensionality.html#6357" class="Bound">A</a> <a id="6373" class="Symbol">→</a> <a id="6375" href="Prelude.Extensionality.html#6122" class="Bound">𝓦</a> <a id="6377" href="Universes.html#403" class="Function Operator">̇</a> <a id="6379" class="Symbol">}(</a><a id="6381" href="Prelude.Extensionality.html#6381" class="Bound">f</a> <a id="6383" href="Prelude.Extensionality.html#6383" class="Bound">g</a> <a id="6385" class="Symbol">:</a> <a id="6387" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6389" href="Prelude.Extensionality.html#6367" class="Bound">B</a><a id="6390" class="Symbol">)</a> <a id="6392" class="Symbol">→</a> <a id="6394" href="Prelude.Extensionality.html#6381" class="Bound">f</a> <a id="6396" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="6398" href="Prelude.Extensionality.html#6383" class="Bound">g</a> <a id="6400" class="Symbol">→</a> <a id="6402" href="Prelude.Extensionality.html#6381" class="Bound">f</a> <a id="6404" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6406" href="Prelude.Extensionality.html#6383" class="Bound">g</a>
 <a id="6409" href="Prelude.Extensionality.html#6346" class="Function">extdfun</a> <a id="6417" class="Symbol">_</a> <a id="6419" class="Symbol">_</a> <a id="6421" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6426" class="Symbol">_</a> <a id="6428" class="Symbol">=</a> <a id="6430" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to assume we have a proof for this type. That is, we could postulate that function extensionality holds and assume we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8520" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8527" href="Prelude.Extensionality.html#8527" class="Module">hide-tt-defs</a> <a id="8540" class="Symbol">{</a><a id="8541" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8543" class="Symbol">:</a> <a id="8545" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8553" class="Symbol">}</a> <a id="8555" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8563" href="Prelude.Extensionality.html#8563" class="Function">is-center</a> <a id="8573" class="Symbol">:</a> <a id="8575" class="Symbol">(</a><a id="8576" href="Prelude.Extensionality.html#8576" class="Bound">X</a> <a id="8578" class="Symbol">:</a> <a id="8580" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8582" href="Universes.html#403" class="Function Operator">̇</a> <a id="8584" class="Symbol">)</a> <a id="8586" class="Symbol">→</a> <a id="8588" href="Prelude.Extensionality.html#8576" class="Bound">X</a> <a id="8590" class="Symbol">→</a> <a id="8592" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8594" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8597" href="Prelude.Extensionality.html#8563" class="Function">is-center</a> <a id="8607" href="Prelude.Extensionality.html#8607" class="Bound">X</a> <a id="8609" href="Prelude.Extensionality.html#8609" class="Bound">c</a> <a id="8611" class="Symbol">=</a> <a id="8613" class="Symbol">(</a><a id="8614" href="Prelude.Extensionality.html#8614" class="Bound">x</a> <a id="8616" class="Symbol">:</a> <a id="8618" href="Prelude.Extensionality.html#8607" class="Bound">X</a><a id="8619" class="Symbol">)</a> <a id="8621" class="Symbol">→</a> <a id="8623" href="Prelude.Extensionality.html#8609" class="Bound">c</a> <a id="8625" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8627" href="Prelude.Extensionality.html#8614" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8631" href="Prelude.Extensionality.html#8631" class="Function">is-singleton</a> <a id="8644" class="Symbol">:</a> <a id="8646" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8648" href="Universes.html#403" class="Function Operator">̇</a> <a id="8650" class="Symbol">→</a> <a id="8652" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8654" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8657" href="Prelude.Extensionality.html#8631" class="Function">is-singleton</a> <a id="8670" href="Prelude.Extensionality.html#8670" class="Bound">X</a> <a id="8672" class="Symbol">=</a> <a id="8674" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8676" href="Prelude.Extensionality.html#8676" class="Bound">c</a> <a id="8678" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8680" href="Prelude.Extensionality.html#8670" class="Bound">X</a> <a id="8682" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8684" href="Prelude.Extensionality.html#8563" class="Function">is-center</a> <a id="8694" href="Prelude.Extensionality.html#8670" class="Bound">X</a> <a id="8696" href="Prelude.Extensionality.html#8676" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8700" href="Prelude.Extensionality.html#8700" class="Function">is-subsingleton</a> <a id="8716" class="Symbol">:</a> <a id="8718" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8720" href="Universes.html#403" class="Function Operator">̇</a> <a id="8722" class="Symbol">→</a> <a id="8724" href="Prelude.Extensionality.html#8541" class="Bound">𝓤</a> <a id="8726" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8729" href="Prelude.Extensionality.html#8700" class="Function">is-subsingleton</a> <a id="8745" href="Prelude.Extensionality.html#8745" class="Bound">X</a> <a id="8747" class="Symbol">=</a> <a id="8749" class="Symbol">(</a><a id="8750" href="Prelude.Extensionality.html#8750" class="Bound">x</a> <a id="8752" href="Prelude.Extensionality.html#8752" class="Bound">y</a> <a id="8754" class="Symbol">:</a> <a id="8756" href="Prelude.Extensionality.html#8745" class="Bound">X</a><a id="8757" class="Symbol">)</a> <a id="8759" class="Symbol">→</a> <a id="8761" href="Prelude.Extensionality.html#8750" class="Bound">x</a> <a id="8763" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8765" href="Prelude.Extensionality.html#8752" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9058" class="Keyword">open</a> <a id="9063" class="Keyword">import</a> <a id="9070" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9083" class="Keyword">using</a> <a id="9089" class="Symbol">(</a><a id="9090" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9099" class="Symbol">;</a> <a id="9101" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9113" class="Symbol">;</a> <a id="9115" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9130" class="Symbol">)</a> <a id="9132" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9549" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9556" href="Prelude.Extensionality.html#9556" class="Module">hide-tt-defs&#39;</a> <a id="9570" class="Symbol">{</a><a id="9571" href="Prelude.Extensionality.html#9571" class="Bound">𝓤</a> <a id="9573" href="Prelude.Extensionality.html#9573" class="Bound">𝓦</a> <a id="9575" class="Symbol">:</a> <a id="9577" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9585" class="Symbol">}</a> <a id="9587" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9595" href="Prelude.Extensionality.html#9595" class="Function">fiber</a> <a id="9601" class="Symbol">:</a> <a id="9603" class="Symbol">{</a><a id="9604" href="Prelude.Extensionality.html#9604" class="Bound">X</a> <a id="9606" class="Symbol">:</a> <a id="9608" href="Prelude.Extensionality.html#9571" class="Bound">𝓤</a> <a id="9610" href="Universes.html#403" class="Function Operator">̇</a> <a id="9612" class="Symbol">}</a> <a id="9614" class="Symbol">{</a><a id="9615" href="Prelude.Extensionality.html#9615" class="Bound">Y</a> <a id="9617" class="Symbol">:</a> <a id="9619" href="Prelude.Extensionality.html#9573" class="Bound">𝓦</a> <a id="9621" href="Universes.html#403" class="Function Operator">̇</a> <a id="9623" class="Symbol">}</a> <a id="9625" class="Symbol">(</a><a id="9626" href="Prelude.Extensionality.html#9626" class="Bound">f</a> <a id="9628" class="Symbol">:</a> <a id="9630" href="Prelude.Extensionality.html#9604" class="Bound">X</a> <a id="9632" class="Symbol">→</a> <a id="9634" href="Prelude.Extensionality.html#9615" class="Bound">Y</a><a id="9635" class="Symbol">)</a> <a id="9637" class="Symbol">→</a> <a id="9639" href="Prelude.Extensionality.html#9615" class="Bound">Y</a> <a id="9641" class="Symbol">→</a> <a id="9643" href="Prelude.Extensionality.html#9571" class="Bound">𝓤</a> <a id="9645" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9647" href="Prelude.Extensionality.html#9573" class="Bound">𝓦</a> <a id="9649" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9652" href="Prelude.Extensionality.html#9595" class="Function">fiber</a> <a id="9658" class="Symbol">{</a><a id="9659" href="Prelude.Extensionality.html#9659" class="Bound">X</a><a id="9660" class="Symbol">}</a> <a id="9662" href="Prelude.Extensionality.html#9662" class="Bound">f</a> <a id="9664" href="Prelude.Extensionality.html#9664" class="Bound">y</a> <a id="9666" class="Symbol">=</a> <a id="9668" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9670" href="Prelude.Extensionality.html#9670" class="Bound">x</a> <a id="9672" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9674" href="Prelude.Extensionality.html#9659" class="Bound">X</a> <a id="9676" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9678" href="Prelude.Extensionality.html#9662" class="Bound">f</a> <a id="9680" href="Prelude.Extensionality.html#9670" class="Bound">x</a> <a id="9682" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="9684" href="Prelude.Extensionality.html#9664" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9790" href="Prelude.Extensionality.html#9790" class="Function">is-equiv</a> <a id="9799" class="Symbol">:</a> <a id="9801" class="Symbol">{</a><a id="9802" href="Prelude.Extensionality.html#9802" class="Bound">X</a> <a id="9804" class="Symbol">:</a> <a id="9806" href="Prelude.Extensionality.html#9571" class="Bound">𝓤</a> <a id="9808" href="Universes.html#403" class="Function Operator">̇</a> <a id="9810" class="Symbol">}</a> <a id="9812" class="Symbol">{</a><a id="9813" href="Prelude.Extensionality.html#9813" class="Bound">Y</a> <a id="9815" class="Symbol">:</a> <a id="9817" href="Prelude.Extensionality.html#9573" class="Bound">𝓦</a> <a id="9819" href="Universes.html#403" class="Function Operator">̇</a> <a id="9821" class="Symbol">}</a> <a id="9823" class="Symbol">→</a> <a id="9825" class="Symbol">(</a><a id="9826" href="Prelude.Extensionality.html#9802" class="Bound">X</a> <a id="9828" class="Symbol">→</a> <a id="9830" href="Prelude.Extensionality.html#9813" class="Bound">Y</a><a id="9831" class="Symbol">)</a> <a id="9833" class="Symbol">→</a> <a id="9835" href="Prelude.Extensionality.html#9571" class="Bound">𝓤</a> <a id="9837" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9839" href="Prelude.Extensionality.html#9573" class="Bound">𝓦</a> <a id="9841" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9844" href="Prelude.Extensionality.html#9790" class="Function">is-equiv</a> <a id="9853" href="Prelude.Extensionality.html#9853" class="Bound">f</a> <a id="9855" class="Symbol">=</a> <a id="9857" class="Symbol">∀</a> <a id="9859" href="Prelude.Extensionality.html#9859" class="Bound">y</a> <a id="9861" class="Symbol">→</a> <a id="9863" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9876" class="Symbol">(</a><a id="9877" href="Prelude.Extensionality.html#9595" class="Function">fiber</a> <a id="9883" href="Prelude.Extensionality.html#9853" class="Bound">f</a> <a id="9885" href="Prelude.Extensionality.html#9859" class="Bound">y</a><a id="9886" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="10092" class="Keyword">open</a> <a id="10097" class="Keyword">import</a> <a id="10104" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10121" class="Keyword">using</a> <a id="10127" class="Symbol">(</a><a id="10128" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10133" class="Symbol">;</a> <a id="10135" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10143" class="Symbol">)</a> <a id="10145" class="Keyword">public</a>

<a id="10153" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10160" href="Prelude.Extensionality.html#10160" class="Module">hide-hfunext</a> <a id="10173" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10181" href="Prelude.Extensionality.html#10181" class="Function">hfunext</a> <a id="10189" class="Symbol">:</a> <a id="10191" class="Symbol">(</a><a id="10192" href="Prelude.Extensionality.html#10192" class="Bound">𝓤</a> <a id="10194" href="Prelude.Extensionality.html#10194" class="Bound">𝓦</a> <a id="10196" class="Symbol">:</a> <a id="10198" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10206" class="Symbol">)</a> <a id="10208" class="Symbol">→</a> <a id="10210" class="Symbol">(</a><a id="10211" href="Prelude.Extensionality.html#10192" class="Bound">𝓤</a> <a id="10213" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10215" href="Prelude.Extensionality.html#10194" class="Bound">𝓦</a><a id="10216" class="Symbol">)</a><a id="10217" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10219" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10222" href="Prelude.Extensionality.html#10181" class="Function">hfunext</a> <a id="10230" href="Prelude.Extensionality.html#10230" class="Bound">𝓤</a> <a id="10232" href="Prelude.Extensionality.html#10232" class="Bound">𝓦</a> <a id="10234" class="Symbol">=</a> <a id="10236" class="Symbol">{</a><a id="10237" href="Prelude.Extensionality.html#10237" class="Bound">A</a> <a id="10239" class="Symbol">:</a> <a id="10241" href="Prelude.Extensionality.html#10230" class="Bound">𝓤</a> <a id="10243" href="Universes.html#403" class="Function Operator">̇</a><a id="10244" class="Symbol">}{</a><a id="10246" href="Prelude.Extensionality.html#10246" class="Bound">B</a> <a id="10248" class="Symbol">:</a> <a id="10250" href="Prelude.Extensionality.html#10237" class="Bound">A</a> <a id="10252" class="Symbol">→</a> <a id="10254" href="Prelude.Extensionality.html#10232" class="Bound">𝓦</a> <a id="10256" href="Universes.html#403" class="Function Operator">̇</a><a id="10257" class="Symbol">}</a> <a id="10259" class="Symbol">(</a><a id="10260" href="Prelude.Extensionality.html#10260" class="Bound">f</a> <a id="10262" href="Prelude.Extensionality.html#10262" class="Bound">g</a> <a id="10264" class="Symbol">:</a> <a id="10266" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10268" href="Prelude.Extensionality.html#10246" class="Bound">B</a><a id="10269" class="Symbol">)</a> <a id="10271" class="Symbol">→</a> <a id="10273" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10282" class="Symbol">(</a><a id="10283" href="Prelude.Extensionality.html#6346" class="Function">extdfun</a> <a id="10291" href="Prelude.Extensionality.html#10260" class="Bound">f</a> <a id="10293" href="Prelude.Extensionality.html#10262" class="Bound">g</a><a id="10294" class="Symbol">)</a>
<a id="10296" class="Keyword">open</a> <a id="10301" class="Keyword">import</a> <a id="10308" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10336" class="Keyword">using</a> <a id="10342" class="Symbol">(</a><a id="10343" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10350" class="Symbol">)</a> <a id="10352" class="Keyword">public</a>

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
