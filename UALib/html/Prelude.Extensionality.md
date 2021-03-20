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




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="6067" class="Keyword">open</a> <a id="6072" class="Keyword">import</a> <a id="6079" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6088" class="Keyword">using</a> <a id="6094" class="Symbol">(</a><a id="6095" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6098" class="Symbol">)</a> <a id="6100" class="Keyword">public</a>

<a id="6108" class="Keyword">module</a> <a id="6115" href="Prelude.Extensionality.html#6115" class="Module">_</a> <a id="6117" class="Symbol">{</a><a id="6118" href="Prelude.Extensionality.html#6118" class="Bound">𝓤</a> <a id="6120" href="Prelude.Extensionality.html#6120" class="Bound">𝓦</a> <a id="6122" class="Symbol">:</a> <a id="6124" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6132" class="Symbol">}</a> <a id="6134" class="Keyword">where</a>

 <a id="6142" href="Prelude.Extensionality.html#6142" class="Function">extfun</a> <a id="6149" class="Symbol">:</a> <a id="6151" class="Symbol">{</a><a id="6152" href="Prelude.Extensionality.html#6152" class="Bound">A</a> <a id="6154" class="Symbol">:</a> <a id="6156" href="Prelude.Extensionality.html#6118" class="Bound">𝓤</a> <a id="6158" href="Universes.html#403" class="Function Operator">̇</a><a id="6159" class="Symbol">}{</a><a id="6161" href="Prelude.Extensionality.html#6161" class="Bound">B</a> <a id="6163" class="Symbol">:</a> <a id="6165" href="Prelude.Extensionality.html#6120" class="Bound">𝓦</a> <a id="6167" href="Universes.html#403" class="Function Operator">̇</a><a id="6168" class="Symbol">}{</a><a id="6170" href="Prelude.Extensionality.html#6170" class="Bound">f</a> <a id="6172" href="Prelude.Extensionality.html#6172" class="Bound">g</a> <a id="6174" class="Symbol">:</a> <a id="6176" href="Prelude.Extensionality.html#6152" class="Bound">A</a> <a id="6178" class="Symbol">→</a> <a id="6180" href="Prelude.Extensionality.html#6161" class="Bound">B</a><a id="6181" class="Symbol">}</a> <a id="6183" class="Symbol">→</a> <a id="6185" href="Prelude.Extensionality.html#6170" class="Bound">f</a> <a id="6187" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6189" href="Prelude.Extensionality.html#6172" class="Bound">g</a>  <a id="6192" class="Symbol">→</a>  <a id="6195" href="Prelude.Extensionality.html#6170" class="Bound">f</a> <a id="6197" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6199" href="Prelude.Extensionality.html#6172" class="Bound">g</a>
 <a id="6202" href="Prelude.Extensionality.html#6142" class="Function">extfun</a> <a id="6209" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6214" class="Symbol">_</a> <a id="6216" class="Symbol">=</a> <a id="6218" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6344" href="Prelude.Extensionality.html#6344" class="Function">extdfun</a> <a id="6352" class="Symbol">:</a> <a id="6354" class="Symbol">{</a><a id="6355" href="Prelude.Extensionality.html#6355" class="Bound">A</a> <a id="6357" class="Symbol">:</a> <a id="6359" href="Prelude.Extensionality.html#6118" class="Bound">𝓤</a> <a id="6361" href="Universes.html#403" class="Function Operator">̇</a> <a id="6363" class="Symbol">}{</a><a id="6365" href="Prelude.Extensionality.html#6365" class="Bound">B</a> <a id="6367" class="Symbol">:</a> <a id="6369" href="Prelude.Extensionality.html#6355" class="Bound">A</a> <a id="6371" class="Symbol">→</a> <a id="6373" href="Prelude.Extensionality.html#6120" class="Bound">𝓦</a> <a id="6375" href="Universes.html#403" class="Function Operator">̇</a> <a id="6377" class="Symbol">}(</a><a id="6379" href="Prelude.Extensionality.html#6379" class="Bound">f</a> <a id="6381" href="Prelude.Extensionality.html#6381" class="Bound">g</a> <a id="6383" class="Symbol">:</a> <a id="6385" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6387" href="Prelude.Extensionality.html#6365" class="Bound">B</a><a id="6388" class="Symbol">)</a> <a id="6390" class="Symbol">→</a> <a id="6392" href="Prelude.Extensionality.html#6379" class="Bound">f</a> <a id="6394" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6396" href="Prelude.Extensionality.html#6381" class="Bound">g</a> <a id="6398" class="Symbol">→</a> <a id="6400" href="Prelude.Extensionality.html#6379" class="Bound">f</a> <a id="6402" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6404" href="Prelude.Extensionality.html#6381" class="Bound">g</a>
 <a id="6407" href="Prelude.Extensionality.html#6344" class="Function">extdfun</a> <a id="6415" class="Symbol">_</a> <a id="6417" class="Symbol">_</a> <a id="6419" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6424" class="Symbol">_</a> <a id="6426" class="Symbol">=</a> <a id="6428" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to assume we have a proof for this type. That is, we could postulate that function extensionality holds and assume we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8518" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8525" href="Prelude.Extensionality.html#8525" class="Module">hide-tt-defs</a> <a id="8538" class="Symbol">{</a><a id="8539" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8541" class="Symbol">:</a> <a id="8543" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8551" class="Symbol">}</a> <a id="8553" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8561" href="Prelude.Extensionality.html#8561" class="Function">is-center</a> <a id="8571" class="Symbol">:</a> <a id="8573" class="Symbol">(</a><a id="8574" href="Prelude.Extensionality.html#8574" class="Bound">A</a> <a id="8576" class="Symbol">:</a> <a id="8578" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8580" href="Universes.html#403" class="Function Operator">̇</a> <a id="8582" class="Symbol">)</a> <a id="8584" class="Symbol">→</a> <a id="8586" href="Prelude.Extensionality.html#8574" class="Bound">A</a> <a id="8588" class="Symbol">→</a> <a id="8590" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8592" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8595" href="Prelude.Extensionality.html#8561" class="Function">is-center</a> <a id="8605" href="Prelude.Extensionality.html#8605" class="Bound">A</a> <a id="8607" href="Prelude.Extensionality.html#8607" class="Bound">c</a> <a id="8609" class="Symbol">=</a> <a id="8611" class="Symbol">(</a><a id="8612" href="Prelude.Extensionality.html#8612" class="Bound">x</a> <a id="8614" class="Symbol">:</a> <a id="8616" href="Prelude.Extensionality.html#8605" class="Bound">A</a><a id="8617" class="Symbol">)</a> <a id="8619" class="Symbol">→</a> <a id="8621" href="Prelude.Extensionality.html#8607" class="Bound">c</a> <a id="8623" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8625" href="Prelude.Extensionality.html#8612" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8629" href="Prelude.Extensionality.html#8629" class="Function">is-singleton</a> <a id="8642" class="Symbol">:</a> <a id="8644" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8646" href="Universes.html#403" class="Function Operator">̇</a> <a id="8648" class="Symbol">→</a> <a id="8650" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8652" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8655" href="Prelude.Extensionality.html#8629" class="Function">is-singleton</a> <a id="8668" href="Prelude.Extensionality.html#8668" class="Bound">A</a> <a id="8670" class="Symbol">=</a> <a id="8672" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8674" href="Prelude.Extensionality.html#8674" class="Bound">c</a> <a id="8676" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8678" href="Prelude.Extensionality.html#8668" class="Bound">A</a> <a id="8680" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8682" href="Prelude.Extensionality.html#8561" class="Function">is-center</a> <a id="8692" href="Prelude.Extensionality.html#8668" class="Bound">A</a> <a id="8694" href="Prelude.Extensionality.html#8674" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8698" href="Prelude.Extensionality.html#8698" class="Function">is-subsingleton</a> <a id="8714" class="Symbol">:</a> <a id="8716" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8718" href="Universes.html#403" class="Function Operator">̇</a> <a id="8720" class="Symbol">→</a> <a id="8722" href="Prelude.Extensionality.html#8539" class="Bound">𝓤</a> <a id="8724" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8727" href="Prelude.Extensionality.html#8698" class="Function">is-subsingleton</a> <a id="8743" href="Prelude.Extensionality.html#8743" class="Bound">A</a> <a id="8745" class="Symbol">=</a> <a id="8747" class="Symbol">(</a><a id="8748" href="Prelude.Extensionality.html#8748" class="Bound">x</a> <a id="8750" href="Prelude.Extensionality.html#8750" class="Bound">y</a> <a id="8752" class="Symbol">:</a> <a id="8754" href="Prelude.Extensionality.html#8743" class="Bound">A</a><a id="8755" class="Symbol">)</a> <a id="8757" class="Symbol">→</a> <a id="8759" href="Prelude.Extensionality.html#8748" class="Bound">x</a> <a id="8761" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8763" href="Prelude.Extensionality.html#8750" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9056" class="Keyword">open</a> <a id="9061" class="Keyword">import</a> <a id="9068" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9081" class="Keyword">using</a> <a id="9087" class="Symbol">(</a><a id="9088" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9097" class="Symbol">;</a> <a id="9099" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9111" class="Symbol">;</a> <a id="9113" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9128" class="Symbol">)</a> <a id="9130" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9547" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9554" href="Prelude.Extensionality.html#9554" class="Module">hide-tt-defs&#39;</a> <a id="9568" class="Symbol">{</a><a id="9569" href="Prelude.Extensionality.html#9569" class="Bound">𝓤</a> <a id="9571" href="Prelude.Extensionality.html#9571" class="Bound">𝓦</a> <a id="9573" class="Symbol">:</a> <a id="9575" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9583" class="Symbol">}</a> <a id="9585" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9593" href="Prelude.Extensionality.html#9593" class="Function">fiber</a> <a id="9599" class="Symbol">:</a> <a id="9601" class="Symbol">{</a><a id="9602" href="Prelude.Extensionality.html#9602" class="Bound">A</a> <a id="9604" class="Symbol">:</a> <a id="9606" href="Prelude.Extensionality.html#9569" class="Bound">𝓤</a> <a id="9608" href="Universes.html#403" class="Function Operator">̇</a> <a id="9610" class="Symbol">}</a> <a id="9612" class="Symbol">{</a><a id="9613" href="Prelude.Extensionality.html#9613" class="Bound">B</a> <a id="9615" class="Symbol">:</a> <a id="9617" href="Prelude.Extensionality.html#9571" class="Bound">𝓦</a> <a id="9619" href="Universes.html#403" class="Function Operator">̇</a> <a id="9621" class="Symbol">}</a> <a id="9623" class="Symbol">(</a><a id="9624" href="Prelude.Extensionality.html#9624" class="Bound">f</a> <a id="9626" class="Symbol">:</a> <a id="9628" href="Prelude.Extensionality.html#9602" class="Bound">A</a> <a id="9630" class="Symbol">→</a> <a id="9632" href="Prelude.Extensionality.html#9613" class="Bound">B</a><a id="9633" class="Symbol">)</a> <a id="9635" class="Symbol">→</a> <a id="9637" href="Prelude.Extensionality.html#9613" class="Bound">B</a> <a id="9639" class="Symbol">→</a> <a id="9641" href="Prelude.Extensionality.html#9569" class="Bound">𝓤</a> <a id="9643" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9645" href="Prelude.Extensionality.html#9571" class="Bound">𝓦</a> <a id="9647" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9650" href="Prelude.Extensionality.html#9593" class="Function">fiber</a> <a id="9656" class="Symbol">{</a><a id="9657" href="Prelude.Extensionality.html#9657" class="Bound">A</a><a id="9658" class="Symbol">}</a> <a id="9660" href="Prelude.Extensionality.html#9660" class="Bound">f</a> <a id="9662" href="Prelude.Extensionality.html#9662" class="Bound">y</a> <a id="9664" class="Symbol">=</a> <a id="9666" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9668" href="Prelude.Extensionality.html#9668" class="Bound">x</a> <a id="9670" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9672" href="Prelude.Extensionality.html#9657" class="Bound">A</a> <a id="9674" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9676" href="Prelude.Extensionality.html#9660" class="Bound">f</a> <a id="9678" href="Prelude.Extensionality.html#9668" class="Bound">x</a> <a id="9680" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="9682" href="Prelude.Extensionality.html#9662" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9788" href="Prelude.Extensionality.html#9788" class="Function">is-equiv</a> <a id="9797" class="Symbol">:</a> <a id="9799" class="Symbol">{</a><a id="9800" href="Prelude.Extensionality.html#9800" class="Bound">A</a> <a id="9802" class="Symbol">:</a> <a id="9804" href="Prelude.Extensionality.html#9569" class="Bound">𝓤</a> <a id="9806" href="Universes.html#403" class="Function Operator">̇</a> <a id="9808" class="Symbol">}</a> <a id="9810" class="Symbol">{</a><a id="9811" href="Prelude.Extensionality.html#9811" class="Bound">B</a> <a id="9813" class="Symbol">:</a> <a id="9815" href="Prelude.Extensionality.html#9571" class="Bound">𝓦</a> <a id="9817" href="Universes.html#403" class="Function Operator">̇</a> <a id="9819" class="Symbol">}</a> <a id="9821" class="Symbol">→</a> <a id="9823" class="Symbol">(</a><a id="9824" href="Prelude.Extensionality.html#9800" class="Bound">A</a> <a id="9826" class="Symbol">→</a> <a id="9828" href="Prelude.Extensionality.html#9811" class="Bound">B</a><a id="9829" class="Symbol">)</a> <a id="9831" class="Symbol">→</a> <a id="9833" href="Prelude.Extensionality.html#9569" class="Bound">𝓤</a> <a id="9835" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9837" href="Prelude.Extensionality.html#9571" class="Bound">𝓦</a> <a id="9839" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9842" href="Prelude.Extensionality.html#9788" class="Function">is-equiv</a> <a id="9851" href="Prelude.Extensionality.html#9851" class="Bound">f</a> <a id="9853" class="Symbol">=</a> <a id="9855" class="Symbol">∀</a> <a id="9857" href="Prelude.Extensionality.html#9857" class="Bound">y</a> <a id="9859" class="Symbol">→</a> <a id="9861" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9874" class="Symbol">(</a><a id="9875" href="Prelude.Extensionality.html#9593" class="Function">fiber</a> <a id="9881" href="Prelude.Extensionality.html#9851" class="Bound">f</a> <a id="9883" href="Prelude.Extensionality.html#9857" class="Bound">y</a><a id="9884" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="10090" class="Keyword">open</a> <a id="10095" class="Keyword">import</a> <a id="10102" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10119" class="Keyword">using</a> <a id="10125" class="Symbol">(</a><a id="10126" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10131" class="Symbol">;</a> <a id="10133" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10141" class="Symbol">)</a> <a id="10143" class="Keyword">public</a>

<a id="10151" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10158" href="Prelude.Extensionality.html#10158" class="Module">hide-hfunext</a> <a id="10171" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10179" href="Prelude.Extensionality.html#10179" class="Function">hfunext</a> <a id="10187" class="Symbol">:</a> <a id="10189" class="Symbol">(</a><a id="10190" href="Prelude.Extensionality.html#10190" class="Bound">𝓤</a> <a id="10192" href="Prelude.Extensionality.html#10192" class="Bound">𝓦</a> <a id="10194" class="Symbol">:</a> <a id="10196" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10204" class="Symbol">)</a> <a id="10206" class="Symbol">→</a> <a id="10208" class="Symbol">(</a><a id="10209" href="Prelude.Extensionality.html#10190" class="Bound">𝓤</a> <a id="10211" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10213" href="Prelude.Extensionality.html#10192" class="Bound">𝓦</a><a id="10214" class="Symbol">)</a><a id="10215" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10217" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10220" href="Prelude.Extensionality.html#10179" class="Function">hfunext</a> <a id="10228" href="Prelude.Extensionality.html#10228" class="Bound">𝓤</a> <a id="10230" href="Prelude.Extensionality.html#10230" class="Bound">𝓦</a> <a id="10232" class="Symbol">=</a> <a id="10234" class="Symbol">{</a><a id="10235" href="Prelude.Extensionality.html#10235" class="Bound">A</a> <a id="10237" class="Symbol">:</a> <a id="10239" href="Prelude.Extensionality.html#10228" class="Bound">𝓤</a> <a id="10241" href="Universes.html#403" class="Function Operator">̇</a><a id="10242" class="Symbol">}{</a><a id="10244" href="Prelude.Extensionality.html#10244" class="Bound">B</a> <a id="10246" class="Symbol">:</a> <a id="10248" href="Prelude.Extensionality.html#10235" class="Bound">A</a> <a id="10250" class="Symbol">→</a> <a id="10252" href="Prelude.Extensionality.html#10230" class="Bound">𝓦</a> <a id="10254" href="Universes.html#403" class="Function Operator">̇</a><a id="10255" class="Symbol">}</a> <a id="10257" class="Symbol">(</a><a id="10258" href="Prelude.Extensionality.html#10258" class="Bound">f</a> <a id="10260" href="Prelude.Extensionality.html#10260" class="Bound">g</a> <a id="10262" class="Symbol">:</a> <a id="10264" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10266" href="Prelude.Extensionality.html#10244" class="Bound">B</a><a id="10267" class="Symbol">)</a> <a id="10269" class="Symbol">→</a> <a id="10271" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10280" class="Symbol">(</a><a id="10281" href="Prelude.Extensionality.html#6344" class="Function">extdfun</a> <a id="10289" href="Prelude.Extensionality.html#10258" class="Bound">f</a> <a id="10291" href="Prelude.Extensionality.html#10260" class="Bound">g</a><a id="10292" class="Symbol">)</a>
<a id="10294" class="Keyword">open</a> <a id="10299" class="Keyword">import</a> <a id="10306" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10334" class="Keyword">using</a> <a id="10340" class="Symbol">(</a><a id="10341" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10348" class="Symbol">)</a> <a id="10350" class="Keyword">public</a>

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
