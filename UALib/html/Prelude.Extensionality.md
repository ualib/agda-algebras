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

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal." Moreover, if one assumes the [univalence axiom][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).

However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5474" href="Prelude.Extensionality.html#5474" class="Function">global-funext</a> <a id="5488" class="Symbol">:</a> <a id="5490" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5494" href="Prelude.Extensionality.html#5474" class="Function">global-funext</a> <a id="5508" class="Symbol">=</a> <a id="5510" class="Symbol">∀</a>  <a id="5513" class="Symbol">{</a><a id="5514" href="Prelude.Extensionality.html#5514" class="Bound">𝓤</a> <a id="5516" href="Prelude.Extensionality.html#5516" class="Bound">𝓥</a><a id="5517" class="Symbol">}</a> <a id="5519" class="Symbol">→</a> <a id="5521" href="Prelude.Extensionality.html#3515" class="Function">funext</a> <a id="5528" href="Prelude.Extensionality.html#5514" class="Bound">𝓤</a> <a id="5530" href="Prelude.Extensionality.html#5516" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5534" href="Prelude.Extensionality.html#5534" class="Function">global-dfunext</a> <a id="5549" class="Symbol">:</a> <a id="5551" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5555" href="Prelude.Extensionality.html#5534" class="Function">global-dfunext</a> <a id="5570" class="Symbol">=</a> <a id="5572" class="Symbol">∀</a> <a id="5574" class="Symbol">{</a><a id="5575" href="Prelude.Extensionality.html#5575" class="Bound">𝓤</a> <a id="5577" href="Prelude.Extensionality.html#5577" class="Bound">𝓥</a><a id="5578" class="Symbol">}</a> <a id="5580" class="Symbol">→</a> <a id="5582" href="Prelude.Extensionality.html#3720" class="Function">dfunext</a> <a id="5590" href="Prelude.Extensionality.html#5575" class="Bound">𝓤</a> <a id="5592" href="Prelude.Extensionality.html#5577" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5887" class="Keyword">open</a> <a id="5892" class="Keyword">import</a> <a id="5899" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5926" class="Keyword">using</a> <a id="5932" class="Symbol">(</a><a id="5933" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5936" class="Symbol">;</a> <a id="5938" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5944" class="Symbol">;</a> <a id="5946" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5953" class="Symbol">)</a> <a id="5955" class="Keyword">public</a>
<a id="5962" class="Keyword">open</a> <a id="5967" class="Keyword">import</a> <a id="5974" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="6000" class="Keyword">using</a> <a id="6006" class="Symbol">(</a><a id="6007" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6021" class="Symbol">)</a> <a id="6023" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6300" class="Keyword">open</a> <a id="6305" class="Keyword">import</a> <a id="6312" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6321" class="Keyword">using</a> <a id="6327" class="Symbol">(</a><a id="6328" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6331" class="Symbol">)</a> <a id="6333" class="Keyword">public</a>

<a id="6341" class="Keyword">module</a> <a id="6348" href="Prelude.Extensionality.html#6348" class="Module">_</a> <a id="6350" class="Symbol">{</a><a id="6351" href="Prelude.Extensionality.html#6351" class="Bound">𝓤</a> <a id="6353" href="Prelude.Extensionality.html#6353" class="Bound">𝓦</a> <a id="6355" class="Symbol">:</a> <a id="6357" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6365" class="Symbol">}</a> <a id="6367" class="Keyword">where</a>

 <a id="6375" href="Prelude.Extensionality.html#6375" class="Function">extfun</a> <a id="6382" class="Symbol">:</a> <a id="6384" class="Symbol">{</a><a id="6385" href="Prelude.Extensionality.html#6385" class="Bound">A</a> <a id="6387" class="Symbol">:</a> <a id="6389" href="Prelude.Extensionality.html#6351" class="Bound">𝓤</a> <a id="6391" href="Universes.html#403" class="Function Operator">̇</a><a id="6392" class="Symbol">}{</a><a id="6394" href="Prelude.Extensionality.html#6394" class="Bound">B</a> <a id="6396" class="Symbol">:</a> <a id="6398" href="Prelude.Extensionality.html#6353" class="Bound">𝓦</a> <a id="6400" href="Universes.html#403" class="Function Operator">̇</a><a id="6401" class="Symbol">}{</a><a id="6403" href="Prelude.Extensionality.html#6403" class="Bound">f</a> <a id="6405" href="Prelude.Extensionality.html#6405" class="Bound">g</a> <a id="6407" class="Symbol">:</a> <a id="6409" href="Prelude.Extensionality.html#6385" class="Bound">A</a> <a id="6411" class="Symbol">→</a> <a id="6413" href="Prelude.Extensionality.html#6394" class="Bound">B</a><a id="6414" class="Symbol">}</a> <a id="6416" class="Symbol">→</a> <a id="6418" href="Prelude.Extensionality.html#6403" class="Bound">f</a> <a id="6420" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6422" href="Prelude.Extensionality.html#6405" class="Bound">g</a>  <a id="6425" class="Symbol">→</a>  <a id="6428" href="Prelude.Extensionality.html#6403" class="Bound">f</a> <a id="6430" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6432" href="Prelude.Extensionality.html#6405" class="Bound">g</a>
 <a id="6435" href="Prelude.Extensionality.html#6375" class="Function">extfun</a> <a id="6442" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6447" class="Symbol">_</a> <a id="6449" class="Symbol">=</a> <a id="6451" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6577" href="Prelude.Extensionality.html#6577" class="Function">extdfun</a> <a id="6585" class="Symbol">:</a> <a id="6587" class="Symbol">{</a><a id="6588" href="Prelude.Extensionality.html#6588" class="Bound">A</a> <a id="6590" class="Symbol">:</a> <a id="6592" href="Prelude.Extensionality.html#6351" class="Bound">𝓤</a> <a id="6594" href="Universes.html#403" class="Function Operator">̇</a> <a id="6596" class="Symbol">}{</a><a id="6598" href="Prelude.Extensionality.html#6598" class="Bound">B</a> <a id="6600" class="Symbol">:</a> <a id="6602" href="Prelude.Extensionality.html#6588" class="Bound">A</a> <a id="6604" class="Symbol">→</a> <a id="6606" href="Prelude.Extensionality.html#6353" class="Bound">𝓦</a> <a id="6608" href="Universes.html#403" class="Function Operator">̇</a> <a id="6610" class="Symbol">}(</a><a id="6612" href="Prelude.Extensionality.html#6612" class="Bound">f</a> <a id="6614" href="Prelude.Extensionality.html#6614" class="Bound">g</a> <a id="6616" class="Symbol">:</a> <a id="6618" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6620" href="Prelude.Extensionality.html#6598" class="Bound">B</a><a id="6621" class="Symbol">)</a> <a id="6623" class="Symbol">→</a> <a id="6625" href="Prelude.Extensionality.html#6612" class="Bound">f</a> <a id="6627" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6629" href="Prelude.Extensionality.html#6614" class="Bound">g</a> <a id="6631" class="Symbol">→</a> <a id="6633" href="Prelude.Extensionality.html#6612" class="Bound">f</a> <a id="6635" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6637" href="Prelude.Extensionality.html#6614" class="Bound">g</a>
 <a id="6640" href="Prelude.Extensionality.html#6577" class="Function">extdfun</a> <a id="6648" class="Symbol">_</a> <a id="6650" class="Symbol">_</a> <a id="6652" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6657" class="Symbol">_</a> <a id="6659" class="Symbol">=</a> <a id="6661" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8522" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8529" href="Prelude.Extensionality.html#8529" class="Module">hide-tt-defs</a> <a id="8542" class="Symbol">{</a><a id="8543" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8545" class="Symbol">:</a> <a id="8547" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8555" class="Symbol">}</a> <a id="8557" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8565" href="Prelude.Extensionality.html#8565" class="Function">is-center</a> <a id="8575" class="Symbol">:</a> <a id="8577" class="Symbol">(</a><a id="8578" href="Prelude.Extensionality.html#8578" class="Bound">A</a> <a id="8580" class="Symbol">:</a> <a id="8582" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8584" href="Universes.html#403" class="Function Operator">̇</a> <a id="8586" class="Symbol">)</a> <a id="8588" class="Symbol">→</a> <a id="8590" href="Prelude.Extensionality.html#8578" class="Bound">A</a> <a id="8592" class="Symbol">→</a> <a id="8594" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8596" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8599" href="Prelude.Extensionality.html#8565" class="Function">is-center</a> <a id="8609" href="Prelude.Extensionality.html#8609" class="Bound">A</a> <a id="8611" href="Prelude.Extensionality.html#8611" class="Bound">c</a> <a id="8613" class="Symbol">=</a> <a id="8615" class="Symbol">(</a><a id="8616" href="Prelude.Extensionality.html#8616" class="Bound">x</a> <a id="8618" class="Symbol">:</a> <a id="8620" href="Prelude.Extensionality.html#8609" class="Bound">A</a><a id="8621" class="Symbol">)</a> <a id="8623" class="Symbol">→</a> <a id="8625" href="Prelude.Extensionality.html#8611" class="Bound">c</a> <a id="8627" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8629" href="Prelude.Extensionality.html#8616" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8633" href="Prelude.Extensionality.html#8633" class="Function">is-singleton</a> <a id="8646" class="Symbol">:</a> <a id="8648" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8650" href="Universes.html#403" class="Function Operator">̇</a> <a id="8652" class="Symbol">→</a> <a id="8654" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8656" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8659" href="Prelude.Extensionality.html#8633" class="Function">is-singleton</a> <a id="8672" href="Prelude.Extensionality.html#8672" class="Bound">A</a> <a id="8674" class="Symbol">=</a> <a id="8676" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8678" href="Prelude.Extensionality.html#8678" class="Bound">c</a> <a id="8680" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8682" href="Prelude.Extensionality.html#8672" class="Bound">A</a> <a id="8684" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8686" href="Prelude.Extensionality.html#8565" class="Function">is-center</a> <a id="8696" href="Prelude.Extensionality.html#8672" class="Bound">A</a> <a id="8698" href="Prelude.Extensionality.html#8678" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8702" href="Prelude.Extensionality.html#8702" class="Function">is-subsingleton</a> <a id="8718" class="Symbol">:</a> <a id="8720" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8722" href="Universes.html#403" class="Function Operator">̇</a> <a id="8724" class="Symbol">→</a> <a id="8726" href="Prelude.Extensionality.html#8543" class="Bound">𝓤</a> <a id="8728" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8731" href="Prelude.Extensionality.html#8702" class="Function">is-subsingleton</a> <a id="8747" href="Prelude.Extensionality.html#8747" class="Bound">A</a> <a id="8749" class="Symbol">=</a> <a id="8751" class="Symbol">(</a><a id="8752" href="Prelude.Extensionality.html#8752" class="Bound">x</a> <a id="8754" href="Prelude.Extensionality.html#8754" class="Bound">y</a> <a id="8756" class="Symbol">:</a> <a id="8758" href="Prelude.Extensionality.html#8747" class="Bound">A</a><a id="8759" class="Symbol">)</a> <a id="8761" class="Symbol">→</a> <a id="8763" href="Prelude.Extensionality.html#8752" class="Bound">x</a> <a id="8765" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8767" href="Prelude.Extensionality.html#8754" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9060" class="Keyword">open</a> <a id="9065" class="Keyword">import</a> <a id="9072" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9085" class="Keyword">using</a> <a id="9091" class="Symbol">(</a><a id="9092" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9101" class="Symbol">;</a> <a id="9103" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9115" class="Symbol">;</a> <a id="9117" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9132" class="Symbol">)</a> <a id="9134" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9551" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9558" href="Prelude.Extensionality.html#9558" class="Module">hide-tt-defs&#39;</a> <a id="9572" class="Symbol">{</a><a id="9573" href="Prelude.Extensionality.html#9573" class="Bound">𝓤</a> <a id="9575" href="Prelude.Extensionality.html#9575" class="Bound">𝓦</a> <a id="9577" class="Symbol">:</a> <a id="9579" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9587" class="Symbol">}</a> <a id="9589" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9597" href="Prelude.Extensionality.html#9597" class="Function">fiber</a> <a id="9603" class="Symbol">:</a> <a id="9605" class="Symbol">{</a><a id="9606" href="Prelude.Extensionality.html#9606" class="Bound">A</a> <a id="9608" class="Symbol">:</a> <a id="9610" href="Prelude.Extensionality.html#9573" class="Bound">𝓤</a> <a id="9612" href="Universes.html#403" class="Function Operator">̇</a> <a id="9614" class="Symbol">}</a> <a id="9616" class="Symbol">{</a><a id="9617" href="Prelude.Extensionality.html#9617" class="Bound">B</a> <a id="9619" class="Symbol">:</a> <a id="9621" href="Prelude.Extensionality.html#9575" class="Bound">𝓦</a> <a id="9623" href="Universes.html#403" class="Function Operator">̇</a> <a id="9625" class="Symbol">}</a> <a id="9627" class="Symbol">(</a><a id="9628" href="Prelude.Extensionality.html#9628" class="Bound">f</a> <a id="9630" class="Symbol">:</a> <a id="9632" href="Prelude.Extensionality.html#9606" class="Bound">A</a> <a id="9634" class="Symbol">→</a> <a id="9636" href="Prelude.Extensionality.html#9617" class="Bound">B</a><a id="9637" class="Symbol">)</a> <a id="9639" class="Symbol">→</a> <a id="9641" href="Prelude.Extensionality.html#9617" class="Bound">B</a> <a id="9643" class="Symbol">→</a> <a id="9645" href="Prelude.Extensionality.html#9573" class="Bound">𝓤</a> <a id="9647" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9649" href="Prelude.Extensionality.html#9575" class="Bound">𝓦</a> <a id="9651" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9654" href="Prelude.Extensionality.html#9597" class="Function">fiber</a> <a id="9660" class="Symbol">{</a><a id="9661" href="Prelude.Extensionality.html#9661" class="Bound">A</a><a id="9662" class="Symbol">}</a> <a id="9664" href="Prelude.Extensionality.html#9664" class="Bound">f</a> <a id="9666" href="Prelude.Extensionality.html#9666" class="Bound">y</a> <a id="9668" class="Symbol">=</a> <a id="9670" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9672" href="Prelude.Extensionality.html#9672" class="Bound">x</a> <a id="9674" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9676" href="Prelude.Extensionality.html#9661" class="Bound">A</a> <a id="9678" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9680" href="Prelude.Extensionality.html#9664" class="Bound">f</a> <a id="9682" href="Prelude.Extensionality.html#9672" class="Bound">x</a> <a id="9684" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="9686" href="Prelude.Extensionality.html#9666" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9792" href="Prelude.Extensionality.html#9792" class="Function">is-equiv</a> <a id="9801" class="Symbol">:</a> <a id="9803" class="Symbol">{</a><a id="9804" href="Prelude.Extensionality.html#9804" class="Bound">A</a> <a id="9806" class="Symbol">:</a> <a id="9808" href="Prelude.Extensionality.html#9573" class="Bound">𝓤</a> <a id="9810" href="Universes.html#403" class="Function Operator">̇</a> <a id="9812" class="Symbol">}</a> <a id="9814" class="Symbol">{</a><a id="9815" href="Prelude.Extensionality.html#9815" class="Bound">B</a> <a id="9817" class="Symbol">:</a> <a id="9819" href="Prelude.Extensionality.html#9575" class="Bound">𝓦</a> <a id="9821" href="Universes.html#403" class="Function Operator">̇</a> <a id="9823" class="Symbol">}</a> <a id="9825" class="Symbol">→</a> <a id="9827" class="Symbol">(</a><a id="9828" href="Prelude.Extensionality.html#9804" class="Bound">A</a> <a id="9830" class="Symbol">→</a> <a id="9832" href="Prelude.Extensionality.html#9815" class="Bound">B</a><a id="9833" class="Symbol">)</a> <a id="9835" class="Symbol">→</a> <a id="9837" href="Prelude.Extensionality.html#9573" class="Bound">𝓤</a> <a id="9839" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9841" href="Prelude.Extensionality.html#9575" class="Bound">𝓦</a> <a id="9843" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9846" href="Prelude.Extensionality.html#9792" class="Function">is-equiv</a> <a id="9855" href="Prelude.Extensionality.html#9855" class="Bound">f</a> <a id="9857" class="Symbol">=</a> <a id="9859" class="Symbol">∀</a> <a id="9861" href="Prelude.Extensionality.html#9861" class="Bound">y</a> <a id="9863" class="Symbol">→</a> <a id="9865" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9878" class="Symbol">(</a><a id="9879" href="Prelude.Extensionality.html#9597" class="Function">fiber</a> <a id="9885" href="Prelude.Extensionality.html#9855" class="Bound">f</a> <a id="9887" href="Prelude.Extensionality.html#9861" class="Bound">y</a><a id="9888" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="10094" class="Keyword">open</a> <a id="10099" class="Keyword">import</a> <a id="10106" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10123" class="Keyword">using</a> <a id="10129" class="Symbol">(</a><a id="10130" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10135" class="Symbol">;</a> <a id="10137" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10145" class="Symbol">)</a> <a id="10147" class="Keyword">public</a>

<a id="10155" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10162" href="Prelude.Extensionality.html#10162" class="Module">hide-hfunext</a> <a id="10175" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10183" href="Prelude.Extensionality.html#10183" class="Function">hfunext</a> <a id="10191" class="Symbol">:</a> <a id="10193" class="Symbol">(</a><a id="10194" href="Prelude.Extensionality.html#10194" class="Bound">𝓤</a> <a id="10196" href="Prelude.Extensionality.html#10196" class="Bound">𝓦</a> <a id="10198" class="Symbol">:</a> <a id="10200" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10208" class="Symbol">)</a> <a id="10210" class="Symbol">→</a> <a id="10212" class="Symbol">(</a><a id="10213" href="Prelude.Extensionality.html#10194" class="Bound">𝓤</a> <a id="10215" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10217" href="Prelude.Extensionality.html#10196" class="Bound">𝓦</a><a id="10218" class="Symbol">)</a><a id="10219" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10221" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10224" href="Prelude.Extensionality.html#10183" class="Function">hfunext</a> <a id="10232" href="Prelude.Extensionality.html#10232" class="Bound">𝓤</a> <a id="10234" href="Prelude.Extensionality.html#10234" class="Bound">𝓦</a> <a id="10236" class="Symbol">=</a> <a id="10238" class="Symbol">{</a><a id="10239" href="Prelude.Extensionality.html#10239" class="Bound">A</a> <a id="10241" class="Symbol">:</a> <a id="10243" href="Prelude.Extensionality.html#10232" class="Bound">𝓤</a> <a id="10245" href="Universes.html#403" class="Function Operator">̇</a><a id="10246" class="Symbol">}{</a><a id="10248" href="Prelude.Extensionality.html#10248" class="Bound">B</a> <a id="10250" class="Symbol">:</a> <a id="10252" href="Prelude.Extensionality.html#10239" class="Bound">A</a> <a id="10254" class="Symbol">→</a> <a id="10256" href="Prelude.Extensionality.html#10234" class="Bound">𝓦</a> <a id="10258" href="Universes.html#403" class="Function Operator">̇</a><a id="10259" class="Symbol">}</a> <a id="10261" class="Symbol">(</a><a id="10262" href="Prelude.Extensionality.html#10262" class="Bound">f</a> <a id="10264" href="Prelude.Extensionality.html#10264" class="Bound">g</a> <a id="10266" class="Symbol">:</a> <a id="10268" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10270" href="Prelude.Extensionality.html#10248" class="Bound">B</a><a id="10271" class="Symbol">)</a> <a id="10273" class="Symbol">→</a> <a id="10275" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10284" class="Symbol">(</a><a id="10285" href="Prelude.Extensionality.html#6577" class="Function">extdfun</a> <a id="10293" href="Prelude.Extensionality.html#10262" class="Bound">f</a> <a id="10295" href="Prelude.Extensionality.html#10264" class="Bound">g</a><a id="10296" class="Symbol">)</a>
<a id="10298" class="Keyword">open</a> <a id="10303" class="Keyword">import</a> <a id="10310" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10338" class="Keyword">using</a> <a id="10344" class="Symbol">(</a><a id="10345" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10352" class="Symbol">)</a> <a id="10354" class="Keyword">public</a>

</pre>

------------------------------------

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
