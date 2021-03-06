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
 <a id="3054" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3056" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3058" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3060" class="Symbol">=</a> <a id="3062" class="Symbol">∀</a> <a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3066" class="Symbol">→</a> <a id="3068" href="Prelude.Extensionality.html#3054" class="Bound">f</a> <a id="3070" href="Prelude.Extensionality.html#3064" class="Bound">x</a> <a id="3072" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3074" href="Prelude.Extensionality.html#3058" class="Bound">g</a> <a id="3076" href="Prelude.Extensionality.html#3064" class="Bound">x</a>

 <a id="3080" class="Keyword">infix</a> <a id="3086" class="Number">0</a> <a id="3088" href="Prelude.Extensionality.html#2983" class="Function Operator">_∼_</a>

</pre>

**Function extensionality** is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3517" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3524" class="Symbol">:</a> <a id="3526" class="Symbol">∀</a> <a id="3528" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3530" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a>  <a id="3533" class="Symbol">→</a> <a id="3535" href="Prelude.Extensionality.html#3528" class="Bound">𝓤</a> <a id="3537" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3539" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3541" href="Prelude.Extensionality.html#3530" class="Bound">𝓦</a> <a id="3543" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3545" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3548" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="3555" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3557" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3559" class="Symbol">=</a> <a id="3561" class="Symbol">{</a><a id="3562" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3564" class="Symbol">:</a> <a id="3566" href="Prelude.Extensionality.html#3555" class="Bound">𝓤</a> <a id="3568" href="Universes.html#403" class="Function Operator">̇</a> <a id="3570" class="Symbol">}</a> <a id="3572" class="Symbol">{</a><a id="3573" href="Prelude.Extensionality.html#3573" class="Bound">B</a> <a id="3575" class="Symbol">:</a> <a id="3577" href="Prelude.Extensionality.html#3557" class="Bound">𝓦</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a> <a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">{</a><a id="3584" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3586" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3588" class="Symbol">:</a> <a id="3590" href="Prelude.Extensionality.html#3562" class="Bound">A</a> <a id="3592" class="Symbol">→</a> <a id="3594" href="Prelude.Extensionality.html#3573" class="Bound">B</a><a id="3595" class="Symbol">}</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3601" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3603" href="Prelude.Extensionality.html#3586" class="Bound">g</a> <a id="3605" class="Symbol">→</a> <a id="3607" href="Prelude.Extensionality.html#3584" class="Bound">f</a> <a id="3609" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3611" href="Prelude.Extensionality.html#3586" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3722" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3730" class="Symbol">:</a> <a id="3732" class="Symbol">∀</a> <a id="3734" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3736" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3738" class="Symbol">→</a> <a id="3740" href="Prelude.Extensionality.html#3734" class="Bound">𝓤</a> <a id="3742" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3744" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3746" href="Prelude.Extensionality.html#3736" class="Bound">𝓦</a> <a id="3748" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3750" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3753" href="Prelude.Extensionality.html#3722" class="Function">dfunext</a> <a id="3761" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3763" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3765" class="Symbol">=</a> <a id="3767" class="Symbol">{</a><a id="3768" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3770" class="Symbol">:</a> <a id="3772" href="Prelude.Extensionality.html#3761" class="Bound">𝓤</a> <a id="3774" href="Universes.html#403" class="Function Operator">̇</a> <a id="3776" class="Symbol">}{</a><a id="3778" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3780" class="Symbol">:</a> <a id="3782" href="Prelude.Extensionality.html#3768" class="Bound">A</a> <a id="3784" class="Symbol">→</a> <a id="3786" href="Prelude.Extensionality.html#3763" class="Bound">𝓦</a> <a id="3788" href="Universes.html#403" class="Function Operator">̇</a> <a id="3790" class="Symbol">}{</a><a id="3792" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3794" href="Prelude.Extensionality.html#3794" class="Bound">g</a> <a id="3796" class="Symbol">:</a> <a id="3798" class="Symbol">∀(</a><a id="3800" href="Prelude.Extensionality.html#3800" class="Bound">x</a> <a id="3802" class="Symbol">:</a> <a id="3804" href="Prelude.Extensionality.html#3768" class="Bound">A</a><a id="3805" class="Symbol">)</a> <a id="3807" class="Symbol">→</a> <a id="3809" href="Prelude.Extensionality.html#3778" class="Bound">B</a> <a id="3811" href="Prelude.Extensionality.html#3800" class="Bound">x</a><a id="3812" class="Symbol">}</a> <a id="3814" class="Symbol">→</a>  <a id="3817" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3819" href="Prelude.Extensionality.html#2983" class="Function Operator">∼</a> <a id="3821" href="Prelude.Extensionality.html#3794" class="Bound">g</a>  <a id="3824" class="Symbol">→</a>  <a id="3827" href="Prelude.Extensionality.html#3792" class="Bound">f</a> <a id="3829" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3831" href="Prelude.Extensionality.html#3794" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called "pointwise equality of functions" is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following (which is pointed out to us by <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó in his notes</a>), *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="4969" href="Prelude.Extensionality.html#4969" class="Function">global-funext</a> <a id="4983" class="Symbol">:</a> <a id="4985" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4989" href="Prelude.Extensionality.html#4969" class="Function">global-funext</a> <a id="5003" class="Symbol">=</a> <a id="5005" class="Symbol">∀</a>  <a id="5008" class="Symbol">{</a><a id="5009" href="Prelude.Extensionality.html#5009" class="Bound">𝓤</a> <a id="5011" href="Prelude.Extensionality.html#5011" class="Bound">𝓥</a><a id="5012" class="Symbol">}</a> <a id="5014" class="Symbol">→</a> <a id="5016" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="5023" href="Prelude.Extensionality.html#5009" class="Bound">𝓤</a> <a id="5025" href="Prelude.Extensionality.html#5011" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5029" href="Prelude.Extensionality.html#5029" class="Function">global-dfunext</a> <a id="5044" class="Symbol">:</a> <a id="5046" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5050" href="Prelude.Extensionality.html#5029" class="Function">global-dfunext</a> <a id="5065" class="Symbol">=</a> <a id="5067" class="Symbol">∀</a> <a id="5069" class="Symbol">{</a><a id="5070" href="Prelude.Extensionality.html#5070" class="Bound">𝓤</a> <a id="5072" href="Prelude.Extensionality.html#5072" class="Bound">𝓥</a><a id="5073" class="Symbol">}</a> <a id="5075" class="Symbol">→</a> <a id="5077" href="Prelude.Extensionality.html#3517" class="Function">funext</a> <a id="5084" href="Prelude.Extensionality.html#5070" class="Bound">𝓤</a> <a id="5086" href="Prelude.Extensionality.html#5072" class="Bound">𝓥</a>

</pre>

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5546" class="Keyword">open</a> <a id="5551" class="Keyword">import</a> <a id="5558" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5585" class="Keyword">using</a> <a id="5591" class="Symbol">(</a><a id="5592" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5595" class="Symbol">;</a> <a id="5597" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5603" class="Symbol">;</a> <a id="5605" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5612" class="Symbol">)</a> <a id="5614" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5943" class="Keyword">open</a> <a id="5948" class="Keyword">import</a> <a id="5955" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5964" class="Keyword">using</a> <a id="5970" class="Symbol">(</a><a id="5971" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5974" class="Symbol">)</a> <a id="5976" class="Keyword">public</a>

<a id="5984" class="Keyword">module</a> <a id="5991" href="Prelude.Extensionality.html#5991" class="Module">_</a> <a id="5993" class="Symbol">{</a><a id="5994" href="Prelude.Extensionality.html#5994" class="Bound">𝓤</a> <a id="5996" href="Prelude.Extensionality.html#5996" class="Bound">𝓦</a> <a id="5998" class="Symbol">:</a> <a id="6000" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6008" class="Symbol">}</a> <a id="6010" class="Keyword">where</a>

 <a id="6018" href="Prelude.Extensionality.html#6018" class="Function">extfun</a> <a id="6025" class="Symbol">:</a> <a id="6027" class="Symbol">{</a><a id="6028" href="Prelude.Extensionality.html#6028" class="Bound">A</a> <a id="6030" class="Symbol">:</a> <a id="6032" href="Prelude.Extensionality.html#5994" class="Bound">𝓤</a> <a id="6034" href="Universes.html#403" class="Function Operator">̇</a><a id="6035" class="Symbol">}{</a><a id="6037" href="Prelude.Extensionality.html#6037" class="Bound">B</a> <a id="6039" class="Symbol">:</a> <a id="6041" href="Prelude.Extensionality.html#5996" class="Bound">𝓦</a> <a id="6043" href="Universes.html#403" class="Function Operator">̇</a><a id="6044" class="Symbol">}{</a><a id="6046" href="Prelude.Extensionality.html#6046" class="Bound">f</a> <a id="6048" href="Prelude.Extensionality.html#6048" class="Bound">g</a> <a id="6050" class="Symbol">:</a> <a id="6052" href="Prelude.Extensionality.html#6028" class="Bound">A</a> <a id="6054" class="Symbol">→</a> <a id="6056" href="Prelude.Extensionality.html#6037" class="Bound">B</a><a id="6057" class="Symbol">}</a> <a id="6059" class="Symbol">→</a> <a id="6061" href="Prelude.Extensionality.html#6046" class="Bound">f</a> <a id="6063" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="6065" href="Prelude.Extensionality.html#6048" class="Bound">g</a>  <a id="6068" class="Symbol">→</a>  <a id="6071" href="Prelude.Extensionality.html#6046" class="Bound">f</a> <a id="6073" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6075" href="Prelude.Extensionality.html#6048" class="Bound">g</a>
 <a id="6078" href="Prelude.Extensionality.html#6018" class="Function">extfun</a> <a id="6085" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6090" class="Symbol">_</a> <a id="6092" class="Symbol">=</a> <a id="6094" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

 <a id="6179" href="Prelude.Extensionality.html#6179" class="Function">extdfun</a> <a id="6187" class="Symbol">:</a> <a id="6189" class="Symbol">{</a><a id="6190" href="Prelude.Extensionality.html#6190" class="Bound">A</a> <a id="6192" class="Symbol">:</a> <a id="6194" href="Prelude.Extensionality.html#5994" class="Bound">𝓤</a> <a id="6196" href="Universes.html#403" class="Function Operator">̇</a> <a id="6198" class="Symbol">}{</a><a id="6200" href="Prelude.Extensionality.html#6200" class="Bound">B</a> <a id="6202" class="Symbol">:</a> <a id="6204" href="Prelude.Extensionality.html#6190" class="Bound">A</a> <a id="6206" class="Symbol">→</a> <a id="6208" href="Prelude.Extensionality.html#5996" class="Bound">𝓦</a> <a id="6210" href="Universes.html#403" class="Function Operator">̇</a> <a id="6212" class="Symbol">}(</a><a id="6214" href="Prelude.Extensionality.html#6214" class="Bound">f</a> <a id="6216" href="Prelude.Extensionality.html#6216" class="Bound">g</a> <a id="6218" class="Symbol">:</a> <a id="6220" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6222" href="Prelude.Extensionality.html#6200" class="Bound">B</a><a id="6223" class="Symbol">)</a> <a id="6225" class="Symbol">→</a> <a id="6227" href="Prelude.Extensionality.html#6214" class="Bound">f</a> <a id="6229" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="6231" href="Prelude.Extensionality.html#6216" class="Bound">g</a> <a id="6233" class="Symbol">→</a> <a id="6235" href="Prelude.Extensionality.html#6214" class="Bound">f</a> <a id="6237" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6239" href="Prelude.Extensionality.html#6216" class="Bound">g</a>
 <a id="6242" href="Prelude.Extensionality.html#6179" class="Function">extdfun</a> <a id="6250" class="Symbol">_</a> <a id="6252" class="Symbol">_</a> <a id="6254" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6259" class="Symbol">_</a> <a id="6261" class="Symbol">=</a> <a id="6263" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8165" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8172" href="Prelude.Extensionality.html#8172" class="Module">hide-tt-defs</a> <a id="8185" class="Symbol">{</a><a id="8186" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8188" class="Symbol">:</a> <a id="8190" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8198" class="Symbol">}</a> <a id="8200" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8208" href="Prelude.Extensionality.html#8208" class="Function">is-center</a> <a id="8218" class="Symbol">:</a> <a id="8220" class="Symbol">(</a><a id="8221" href="Prelude.Extensionality.html#8221" class="Bound">X</a> <a id="8223" class="Symbol">:</a> <a id="8225" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8227" href="Universes.html#403" class="Function Operator">̇</a> <a id="8229" class="Symbol">)</a> <a id="8231" class="Symbol">→</a> <a id="8233" href="Prelude.Extensionality.html#8221" class="Bound">X</a> <a id="8235" class="Symbol">→</a> <a id="8237" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8239" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8242" href="Prelude.Extensionality.html#8208" class="Function">is-center</a> <a id="8252" href="Prelude.Extensionality.html#8252" class="Bound">X</a> <a id="8254" href="Prelude.Extensionality.html#8254" class="Bound">c</a> <a id="8256" class="Symbol">=</a> <a id="8258" class="Symbol">(</a><a id="8259" href="Prelude.Extensionality.html#8259" class="Bound">x</a> <a id="8261" class="Symbol">:</a> <a id="8263" href="Prelude.Extensionality.html#8252" class="Bound">X</a><a id="8264" class="Symbol">)</a> <a id="8266" class="Symbol">→</a> <a id="8268" href="Prelude.Extensionality.html#8254" class="Bound">c</a> <a id="8270" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8272" href="Prelude.Extensionality.html#8259" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8276" href="Prelude.Extensionality.html#8276" class="Function">is-singleton</a> <a id="8289" class="Symbol">:</a> <a id="8291" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8293" href="Universes.html#403" class="Function Operator">̇</a> <a id="8295" class="Symbol">→</a> <a id="8297" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8299" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8302" href="Prelude.Extensionality.html#8276" class="Function">is-singleton</a> <a id="8315" href="Prelude.Extensionality.html#8315" class="Bound">X</a> <a id="8317" class="Symbol">=</a> <a id="8319" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8321" href="Prelude.Extensionality.html#8321" class="Bound">c</a> <a id="8323" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8325" href="Prelude.Extensionality.html#8315" class="Bound">X</a> <a id="8327" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8329" href="Prelude.Extensionality.html#8208" class="Function">is-center</a> <a id="8339" href="Prelude.Extensionality.html#8315" class="Bound">X</a> <a id="8341" href="Prelude.Extensionality.html#8321" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8345" href="Prelude.Extensionality.html#8345" class="Function">is-subsingleton</a> <a id="8361" class="Symbol">:</a> <a id="8363" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8365" href="Universes.html#403" class="Function Operator">̇</a> <a id="8367" class="Symbol">→</a> <a id="8369" href="Prelude.Extensionality.html#8186" class="Bound">𝓤</a> <a id="8371" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8374" href="Prelude.Extensionality.html#8345" class="Function">is-subsingleton</a> <a id="8390" href="Prelude.Extensionality.html#8390" class="Bound">X</a> <a id="8392" class="Symbol">=</a> <a id="8394" class="Symbol">(</a><a id="8395" href="Prelude.Extensionality.html#8395" class="Bound">x</a> <a id="8397" href="Prelude.Extensionality.html#8397" class="Bound">y</a> <a id="8399" class="Symbol">:</a> <a id="8401" href="Prelude.Extensionality.html#8390" class="Bound">X</a><a id="8402" class="Symbol">)</a> <a id="8404" class="Symbol">→</a> <a id="8406" href="Prelude.Extensionality.html#8395" class="Bound">x</a> <a id="8408" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8410" href="Prelude.Extensionality.html#8397" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8703" class="Keyword">open</a> <a id="8708" class="Keyword">import</a> <a id="8715" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8728" class="Keyword">using</a> <a id="8734" class="Symbol">(</a><a id="8735" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8744" class="Symbol">;</a> <a id="8746" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8758" class="Symbol">;</a> <a id="8760" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8775" class="Symbol">)</a> <a id="8777" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9616" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9623" href="Prelude.Extensionality.html#9623" class="Module">hide-tt-defs&#39;</a> <a id="9637" class="Symbol">{</a><a id="9638" href="Prelude.Extensionality.html#9638" class="Bound">𝓤</a> <a id="9640" href="Prelude.Extensionality.html#9640" class="Bound">𝓦</a> <a id="9642" class="Symbol">:</a> <a id="9644" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9652" class="Symbol">}</a> <a id="9654" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9662" href="Prelude.Extensionality.html#9662" class="Function">fiber</a> <a id="9668" class="Symbol">:</a> <a id="9670" class="Symbol">{</a><a id="9671" href="Prelude.Extensionality.html#9671" class="Bound">X</a> <a id="9673" class="Symbol">:</a> <a id="9675" href="Prelude.Extensionality.html#9638" class="Bound">𝓤</a> <a id="9677" href="Universes.html#403" class="Function Operator">̇</a> <a id="9679" class="Symbol">}</a> <a id="9681" class="Symbol">{</a><a id="9682" href="Prelude.Extensionality.html#9682" class="Bound">Y</a> <a id="9684" class="Symbol">:</a> <a id="9686" href="Prelude.Extensionality.html#9640" class="Bound">𝓦</a> <a id="9688" href="Universes.html#403" class="Function Operator">̇</a> <a id="9690" class="Symbol">}</a> <a id="9692" class="Symbol">(</a><a id="9693" href="Prelude.Extensionality.html#9693" class="Bound">f</a> <a id="9695" class="Symbol">:</a> <a id="9697" href="Prelude.Extensionality.html#9671" class="Bound">X</a> <a id="9699" class="Symbol">→</a> <a id="9701" href="Prelude.Extensionality.html#9682" class="Bound">Y</a><a id="9702" class="Symbol">)</a> <a id="9704" class="Symbol">→</a> <a id="9706" href="Prelude.Extensionality.html#9682" class="Bound">Y</a> <a id="9708" class="Symbol">→</a> <a id="9710" href="Prelude.Extensionality.html#9638" class="Bound">𝓤</a> <a id="9712" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9714" href="Prelude.Extensionality.html#9640" class="Bound">𝓦</a> <a id="9716" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9719" href="Prelude.Extensionality.html#9662" class="Function">fiber</a> <a id="9725" class="Symbol">{</a><a id="9726" href="Prelude.Extensionality.html#9726" class="Bound">X</a><a id="9727" class="Symbol">}</a> <a id="9729" href="Prelude.Extensionality.html#9729" class="Bound">f</a> <a id="9731" href="Prelude.Extensionality.html#9731" class="Bound">y</a> <a id="9733" class="Symbol">=</a> <a id="9735" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9737" href="Prelude.Extensionality.html#9737" class="Bound">x</a> <a id="9739" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9741" href="Prelude.Extensionality.html#9726" class="Bound">X</a> <a id="9743" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9745" href="Prelude.Extensionality.html#9729" class="Bound">f</a> <a id="9747" href="Prelude.Extensionality.html#9737" class="Bound">x</a> <a id="9749" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="9751" href="Prelude.Extensionality.html#9731" class="Bound">y</a>

</pre>

A function is called an **equivalence** if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9859" href="Prelude.Extensionality.html#9859" class="Function">is-equiv</a> <a id="9868" class="Symbol">:</a> <a id="9870" class="Symbol">{</a><a id="9871" href="Prelude.Extensionality.html#9871" class="Bound">X</a> <a id="9873" class="Symbol">:</a> <a id="9875" href="Prelude.Extensionality.html#9638" class="Bound">𝓤</a> <a id="9877" href="Universes.html#403" class="Function Operator">̇</a> <a id="9879" class="Symbol">}</a> <a id="9881" class="Symbol">{</a><a id="9882" href="Prelude.Extensionality.html#9882" class="Bound">Y</a> <a id="9884" class="Symbol">:</a> <a id="9886" href="Prelude.Extensionality.html#9640" class="Bound">𝓦</a> <a id="9888" href="Universes.html#403" class="Function Operator">̇</a> <a id="9890" class="Symbol">}</a> <a id="9892" class="Symbol">→</a> <a id="9894" class="Symbol">(</a><a id="9895" href="Prelude.Extensionality.html#9871" class="Bound">X</a> <a id="9897" class="Symbol">→</a> <a id="9899" href="Prelude.Extensionality.html#9882" class="Bound">Y</a><a id="9900" class="Symbol">)</a> <a id="9902" class="Symbol">→</a> <a id="9904" href="Prelude.Extensionality.html#9638" class="Bound">𝓤</a> <a id="9906" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9908" href="Prelude.Extensionality.html#9640" class="Bound">𝓦</a> <a id="9910" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9913" href="Prelude.Extensionality.html#9859" class="Function">is-equiv</a> <a id="9922" href="Prelude.Extensionality.html#9922" class="Bound">f</a> <a id="9924" class="Symbol">=</a> <a id="9926" class="Symbol">∀</a> <a id="9928" href="Prelude.Extensionality.html#9928" class="Bound">y</a> <a id="9930" class="Symbol">→</a> <a id="9932" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9945" class="Symbol">(</a><a id="9946" href="Prelude.Extensionality.html#9662" class="Function">fiber</a> <a id="9952" href="Prelude.Extensionality.html#9922" class="Bound">f</a> <a id="9954" href="Prelude.Extensionality.html#9928" class="Bound">y</a><a id="9955" class="Symbol">)</a>

</pre>

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>  We will precede its definition with a public import statement so that the types we described above, originally defined in the Type Topology][], will be available throughout the remainder of the [UALib][].

<pre class="Agda">

<a id="10364" class="Keyword">open</a> <a id="10369" class="Keyword">import</a> <a id="10376" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10393" class="Keyword">using</a> <a id="10399" class="Symbol">(</a><a id="10400" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10405" class="Symbol">;</a> <a id="10407" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10415" class="Symbol">)</a> <a id="10417" class="Keyword">public</a>

<a id="10425" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10432" href="Prelude.Extensionality.html#10432" class="Module">hide-hfunext</a> <a id="10445" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10453" href="Prelude.Extensionality.html#10453" class="Function">hfunext</a> <a id="10461" class="Symbol">:</a> <a id="10463" class="Symbol">(</a><a id="10464" href="Prelude.Extensionality.html#10464" class="Bound">𝓤</a> <a id="10466" href="Prelude.Extensionality.html#10466" class="Bound">𝓦</a> <a id="10468" class="Symbol">:</a> <a id="10470" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10478" class="Symbol">)</a> <a id="10480" class="Symbol">→</a> <a id="10482" class="Symbol">(</a><a id="10483" href="Prelude.Extensionality.html#10464" class="Bound">𝓤</a> <a id="10485" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10487" href="Prelude.Extensionality.html#10466" class="Bound">𝓦</a><a id="10488" class="Symbol">)</a><a id="10489" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10491" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10494" href="Prelude.Extensionality.html#10453" class="Function">hfunext</a> <a id="10502" href="Prelude.Extensionality.html#10502" class="Bound">𝓤</a> <a id="10504" href="Prelude.Extensionality.html#10504" class="Bound">𝓦</a> <a id="10506" class="Symbol">=</a> <a id="10508" class="Symbol">{</a><a id="10509" href="Prelude.Extensionality.html#10509" class="Bound">A</a> <a id="10511" class="Symbol">:</a> <a id="10513" href="Prelude.Extensionality.html#10502" class="Bound">𝓤</a> <a id="10515" href="Universes.html#403" class="Function Operator">̇</a><a id="10516" class="Symbol">}{</a><a id="10518" href="Prelude.Extensionality.html#10518" class="Bound">B</a> <a id="10520" class="Symbol">:</a> <a id="10522" href="Prelude.Extensionality.html#10509" class="Bound">A</a> <a id="10524" class="Symbol">→</a> <a id="10526" href="Prelude.Extensionality.html#10504" class="Bound">𝓦</a> <a id="10528" href="Universes.html#403" class="Function Operator">̇</a><a id="10529" class="Symbol">}</a> <a id="10531" class="Symbol">(</a><a id="10532" href="Prelude.Extensionality.html#10532" class="Bound">f</a> <a id="10534" href="Prelude.Extensionality.html#10534" class="Bound">g</a> <a id="10536" class="Symbol">:</a> <a id="10538" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10540" href="Prelude.Extensionality.html#10518" class="Bound">B</a><a id="10541" class="Symbol">)</a> <a id="10543" class="Symbol">→</a> <a id="10545" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10554" class="Symbol">(</a><a id="10555" href="Prelude.Extensionality.html#6179" class="Function">extdfun</a> <a id="10563" href="Prelude.Extensionality.html#10532" class="Bound">f</a> <a id="10565" href="Prelude.Extensionality.html#10534" class="Bound">g</a><a id="10566" class="Symbol">)</a>
<a id="10568" class="Keyword">open</a> <a id="10573" class="Keyword">import</a> <a id="10580" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10607" class="Keyword">using</a> <a id="10613" class="Symbol">(</a><a id="10614" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10621" class="Symbol">)</a> <a id="10623" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>2</sup> <span class="footnote" id="fn2"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>3</sup><span class="footnote" id="fn3"> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library. We initially proved this lemma with a simple invocation of `𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁`, but discovered that this proof leads to an `efunext` type that doesn't play well with other definitions in the [Type Topology][] library (e.g., `NatΠ-is-embedding`).</span>

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
