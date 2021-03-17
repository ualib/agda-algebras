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
 <a id="6078" href="Prelude.Extensionality.html#6018" class="Function">extfun</a> <a id="6085" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6090" class="Symbol">_</a> <a id="6092" class="Symbol">=</a> <a id="6094" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6220" href="Prelude.Extensionality.html#6220" class="Function">extdfun</a> <a id="6228" class="Symbol">:</a> <a id="6230" class="Symbol">{</a><a id="6231" href="Prelude.Extensionality.html#6231" class="Bound">A</a> <a id="6233" class="Symbol">:</a> <a id="6235" href="Prelude.Extensionality.html#5994" class="Bound">𝓤</a> <a id="6237" href="Universes.html#403" class="Function Operator">̇</a> <a id="6239" class="Symbol">}{</a><a id="6241" href="Prelude.Extensionality.html#6241" class="Bound">B</a> <a id="6243" class="Symbol">:</a> <a id="6245" href="Prelude.Extensionality.html#6231" class="Bound">A</a> <a id="6247" class="Symbol">→</a> <a id="6249" href="Prelude.Extensionality.html#5996" class="Bound">𝓦</a> <a id="6251" href="Universes.html#403" class="Function Operator">̇</a> <a id="6253" class="Symbol">}(</a><a id="6255" href="Prelude.Extensionality.html#6255" class="Bound">f</a> <a id="6257" href="Prelude.Extensionality.html#6257" class="Bound">g</a> <a id="6259" class="Symbol">:</a> <a id="6261" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6263" href="Prelude.Extensionality.html#6241" class="Bound">B</a><a id="6264" class="Symbol">)</a> <a id="6266" class="Symbol">→</a> <a id="6268" href="Prelude.Extensionality.html#6255" class="Bound">f</a> <a id="6270" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="6272" href="Prelude.Extensionality.html#6257" class="Bound">g</a> <a id="6274" class="Symbol">→</a> <a id="6276" href="Prelude.Extensionality.html#6255" class="Bound">f</a> <a id="6278" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6280" href="Prelude.Extensionality.html#6257" class="Bound">g</a>
 <a id="6283" href="Prelude.Extensionality.html#6220" class="Function">extdfun</a> <a id="6291" class="Symbol">_</a> <a id="6293" class="Symbol">_</a> <a id="6295" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6300" class="Symbol">_</a> <a id="6302" class="Symbol">=</a> <a id="6304" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to assume we have a proof for this type. That is, we could postulate that function extensionality holds and assume we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8622" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8629" href="Prelude.Extensionality.html#8629" class="Module">hide-tt-defs</a> <a id="8642" class="Symbol">{</a><a id="8643" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8645" class="Symbol">:</a> <a id="8647" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8655" class="Symbol">}</a> <a id="8657" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8665" href="Prelude.Extensionality.html#8665" class="Function">is-center</a> <a id="8675" class="Symbol">:</a> <a id="8677" class="Symbol">(</a><a id="8678" href="Prelude.Extensionality.html#8678" class="Bound">X</a> <a id="8680" class="Symbol">:</a> <a id="8682" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8684" href="Universes.html#403" class="Function Operator">̇</a> <a id="8686" class="Symbol">)</a> <a id="8688" class="Symbol">→</a> <a id="8690" href="Prelude.Extensionality.html#8678" class="Bound">X</a> <a id="8692" class="Symbol">→</a> <a id="8694" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8696" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8699" href="Prelude.Extensionality.html#8665" class="Function">is-center</a> <a id="8709" href="Prelude.Extensionality.html#8709" class="Bound">X</a> <a id="8711" href="Prelude.Extensionality.html#8711" class="Bound">c</a> <a id="8713" class="Symbol">=</a> <a id="8715" class="Symbol">(</a><a id="8716" href="Prelude.Extensionality.html#8716" class="Bound">x</a> <a id="8718" class="Symbol">:</a> <a id="8720" href="Prelude.Extensionality.html#8709" class="Bound">X</a><a id="8721" class="Symbol">)</a> <a id="8723" class="Symbol">→</a> <a id="8725" href="Prelude.Extensionality.html#8711" class="Bound">c</a> <a id="8727" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8729" href="Prelude.Extensionality.html#8716" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8733" href="Prelude.Extensionality.html#8733" class="Function">is-singleton</a> <a id="8746" class="Symbol">:</a> <a id="8748" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8750" href="Universes.html#403" class="Function Operator">̇</a> <a id="8752" class="Symbol">→</a> <a id="8754" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8756" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8759" href="Prelude.Extensionality.html#8733" class="Function">is-singleton</a> <a id="8772" href="Prelude.Extensionality.html#8772" class="Bound">X</a> <a id="8774" class="Symbol">=</a> <a id="8776" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8778" href="Prelude.Extensionality.html#8778" class="Bound">c</a> <a id="8780" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8782" href="Prelude.Extensionality.html#8772" class="Bound">X</a> <a id="8784" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8786" href="Prelude.Extensionality.html#8665" class="Function">is-center</a> <a id="8796" href="Prelude.Extensionality.html#8772" class="Bound">X</a> <a id="8798" href="Prelude.Extensionality.html#8778" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8802" href="Prelude.Extensionality.html#8802" class="Function">is-subsingleton</a> <a id="8818" class="Symbol">:</a> <a id="8820" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8822" href="Universes.html#403" class="Function Operator">̇</a> <a id="8824" class="Symbol">→</a> <a id="8826" href="Prelude.Extensionality.html#8643" class="Bound">𝓤</a> <a id="8828" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8831" href="Prelude.Extensionality.html#8802" class="Function">is-subsingleton</a> <a id="8847" href="Prelude.Extensionality.html#8847" class="Bound">X</a> <a id="8849" class="Symbol">=</a> <a id="8851" class="Symbol">(</a><a id="8852" href="Prelude.Extensionality.html#8852" class="Bound">x</a> <a id="8854" href="Prelude.Extensionality.html#8854" class="Bound">y</a> <a id="8856" class="Symbol">:</a> <a id="8858" href="Prelude.Extensionality.html#8847" class="Bound">X</a><a id="8859" class="Symbol">)</a> <a id="8861" class="Symbol">→</a> <a id="8863" href="Prelude.Extensionality.html#8852" class="Bound">x</a> <a id="8865" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8867" href="Prelude.Extensionality.html#8854" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9160" class="Keyword">open</a> <a id="9165" class="Keyword">import</a> <a id="9172" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9185" class="Keyword">using</a> <a id="9191" class="Symbol">(</a><a id="9192" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9201" class="Symbol">;</a> <a id="9203" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9215" class="Symbol">;</a> <a id="9217" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9232" class="Symbol">)</a> <a id="9234" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="10073" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="10080" href="Prelude.Extensionality.html#10080" class="Module">hide-tt-defs&#39;</a> <a id="10094" class="Symbol">{</a><a id="10095" href="Prelude.Extensionality.html#10095" class="Bound">𝓤</a> <a id="10097" href="Prelude.Extensionality.html#10097" class="Bound">𝓦</a> <a id="10099" class="Symbol">:</a> <a id="10101" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10109" class="Symbol">}</a> <a id="10111" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="10119" href="Prelude.Extensionality.html#10119" class="Function">fiber</a> <a id="10125" class="Symbol">:</a> <a id="10127" class="Symbol">{</a><a id="10128" href="Prelude.Extensionality.html#10128" class="Bound">X</a> <a id="10130" class="Symbol">:</a> <a id="10132" href="Prelude.Extensionality.html#10095" class="Bound">𝓤</a> <a id="10134" href="Universes.html#403" class="Function Operator">̇</a> <a id="10136" class="Symbol">}</a> <a id="10138" class="Symbol">{</a><a id="10139" href="Prelude.Extensionality.html#10139" class="Bound">Y</a> <a id="10141" class="Symbol">:</a> <a id="10143" href="Prelude.Extensionality.html#10097" class="Bound">𝓦</a> <a id="10145" href="Universes.html#403" class="Function Operator">̇</a> <a id="10147" class="Symbol">}</a> <a id="10149" class="Symbol">(</a><a id="10150" href="Prelude.Extensionality.html#10150" class="Bound">f</a> <a id="10152" class="Symbol">:</a> <a id="10154" href="Prelude.Extensionality.html#10128" class="Bound">X</a> <a id="10156" class="Symbol">→</a> <a id="10158" href="Prelude.Extensionality.html#10139" class="Bound">Y</a><a id="10159" class="Symbol">)</a> <a id="10161" class="Symbol">→</a> <a id="10163" href="Prelude.Extensionality.html#10139" class="Bound">Y</a> <a id="10165" class="Symbol">→</a> <a id="10167" href="Prelude.Extensionality.html#10095" class="Bound">𝓤</a> <a id="10169" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10171" href="Prelude.Extensionality.html#10097" class="Bound">𝓦</a> <a id="10173" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10176" href="Prelude.Extensionality.html#10119" class="Function">fiber</a> <a id="10182" class="Symbol">{</a><a id="10183" href="Prelude.Extensionality.html#10183" class="Bound">X</a><a id="10184" class="Symbol">}</a> <a id="10186" href="Prelude.Extensionality.html#10186" class="Bound">f</a> <a id="10188" href="Prelude.Extensionality.html#10188" class="Bound">y</a> <a id="10190" class="Symbol">=</a> <a id="10192" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="10194" href="Prelude.Extensionality.html#10194" class="Bound">x</a> <a id="10196" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="10198" href="Prelude.Extensionality.html#10183" class="Bound">X</a> <a id="10200" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="10202" href="Prelude.Extensionality.html#10186" class="Bound">f</a> <a id="10204" href="Prelude.Extensionality.html#10194" class="Bound">x</a> <a id="10206" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="10208" href="Prelude.Extensionality.html#10188" class="Bound">y</a>

</pre>

A function is called an **equivalence** if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="10316" href="Prelude.Extensionality.html#10316" class="Function">is-equiv</a> <a id="10325" class="Symbol">:</a> <a id="10327" class="Symbol">{</a><a id="10328" href="Prelude.Extensionality.html#10328" class="Bound">X</a> <a id="10330" class="Symbol">:</a> <a id="10332" href="Prelude.Extensionality.html#10095" class="Bound">𝓤</a> <a id="10334" href="Universes.html#403" class="Function Operator">̇</a> <a id="10336" class="Symbol">}</a> <a id="10338" class="Symbol">{</a><a id="10339" href="Prelude.Extensionality.html#10339" class="Bound">Y</a> <a id="10341" class="Symbol">:</a> <a id="10343" href="Prelude.Extensionality.html#10097" class="Bound">𝓦</a> <a id="10345" href="Universes.html#403" class="Function Operator">̇</a> <a id="10347" class="Symbol">}</a> <a id="10349" class="Symbol">→</a> <a id="10351" class="Symbol">(</a><a id="10352" href="Prelude.Extensionality.html#10328" class="Bound">X</a> <a id="10354" class="Symbol">→</a> <a id="10356" href="Prelude.Extensionality.html#10339" class="Bound">Y</a><a id="10357" class="Symbol">)</a> <a id="10359" class="Symbol">→</a> <a id="10361" href="Prelude.Extensionality.html#10095" class="Bound">𝓤</a> <a id="10363" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10365" href="Prelude.Extensionality.html#10097" class="Bound">𝓦</a> <a id="10367" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10370" href="Prelude.Extensionality.html#10316" class="Function">is-equiv</a> <a id="10379" href="Prelude.Extensionality.html#10379" class="Bound">f</a> <a id="10381" class="Symbol">=</a> <a id="10383" class="Symbol">∀</a> <a id="10385" href="Prelude.Extensionality.html#10385" class="Bound">y</a> <a id="10387" class="Symbol">→</a> <a id="10389" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="10402" class="Symbol">(</a><a id="10403" href="Prelude.Extensionality.html#10119" class="Function">fiber</a> <a id="10409" href="Prelude.Extensionality.html#10379" class="Bound">f</a> <a id="10411" href="Prelude.Extensionality.html#10385" class="Bound">y</a><a id="10412" class="Symbol">)</a>

</pre>

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>  We will precede its definition with a public import statement so that the types we described above, originally defined in the Type Topology][], will be available throughout the remainder of the [UALib][].

<pre class="Agda">

<a id="10821" class="Keyword">open</a> <a id="10826" class="Keyword">import</a> <a id="10833" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10850" class="Keyword">using</a> <a id="10856" class="Symbol">(</a><a id="10857" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10862" class="Symbol">;</a> <a id="10864" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10872" class="Symbol">)</a> <a id="10874" class="Keyword">public</a>

<a id="10882" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10889" href="Prelude.Extensionality.html#10889" class="Module">hide-hfunext</a> <a id="10902" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10910" href="Prelude.Extensionality.html#10910" class="Function">hfunext</a> <a id="10918" class="Symbol">:</a> <a id="10920" class="Symbol">(</a><a id="10921" href="Prelude.Extensionality.html#10921" class="Bound">𝓤</a> <a id="10923" href="Prelude.Extensionality.html#10923" class="Bound">𝓦</a> <a id="10925" class="Symbol">:</a> <a id="10927" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10935" class="Symbol">)</a> <a id="10937" class="Symbol">→</a> <a id="10939" class="Symbol">(</a><a id="10940" href="Prelude.Extensionality.html#10921" class="Bound">𝓤</a> <a id="10942" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10944" href="Prelude.Extensionality.html#10923" class="Bound">𝓦</a><a id="10945" class="Symbol">)</a><a id="10946" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10948" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10951" href="Prelude.Extensionality.html#10910" class="Function">hfunext</a> <a id="10959" href="Prelude.Extensionality.html#10959" class="Bound">𝓤</a> <a id="10961" href="Prelude.Extensionality.html#10961" class="Bound">𝓦</a> <a id="10963" class="Symbol">=</a> <a id="10965" class="Symbol">{</a><a id="10966" href="Prelude.Extensionality.html#10966" class="Bound">A</a> <a id="10968" class="Symbol">:</a> <a id="10970" href="Prelude.Extensionality.html#10959" class="Bound">𝓤</a> <a id="10972" href="Universes.html#403" class="Function Operator">̇</a><a id="10973" class="Symbol">}{</a><a id="10975" href="Prelude.Extensionality.html#10975" class="Bound">B</a> <a id="10977" class="Symbol">:</a> <a id="10979" href="Prelude.Extensionality.html#10966" class="Bound">A</a> <a id="10981" class="Symbol">→</a> <a id="10983" href="Prelude.Extensionality.html#10961" class="Bound">𝓦</a> <a id="10985" href="Universes.html#403" class="Function Operator">̇</a><a id="10986" class="Symbol">}</a> <a id="10988" class="Symbol">(</a><a id="10989" href="Prelude.Extensionality.html#10989" class="Bound">f</a> <a id="10991" href="Prelude.Extensionality.html#10991" class="Bound">g</a> <a id="10993" class="Symbol">:</a> <a id="10995" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10997" href="Prelude.Extensionality.html#10975" class="Bound">B</a><a id="10998" class="Symbol">)</a> <a id="11000" class="Symbol">→</a> <a id="11002" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="11011" class="Symbol">(</a><a id="11012" href="Prelude.Extensionality.html#6220" class="Function">extdfun</a> <a id="11020" href="Prelude.Extensionality.html#10989" class="Bound">f</a> <a id="11022" href="Prelude.Extensionality.html#10991" class="Bound">g</a><a id="11023" class="Symbol">)</a>
<a id="11025" class="Keyword">open</a> <a id="11030" class="Keyword">import</a> <a id="11037" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="11064" class="Keyword">using</a> <a id="11070" class="Symbol">(</a><a id="11071" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="11078" class="Symbol">)</a> <a id="11080" class="Keyword">public</a>

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
