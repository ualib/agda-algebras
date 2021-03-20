---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="310" class="Symbol">{-#</a> <a id="314" class="Keyword">OPTIONS</a> <a id="322" class="Pragma">--without-K</a> <a id="334" class="Pragma">--exact-split</a> <a id="348" class="Pragma">--safe</a> <a id="355" class="Symbol">#-}</a>

<a id="360" class="Keyword">module</a> <a id="367" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="390" class="Keyword">where</a>

<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="426" class="Keyword">public</a>

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

<a id="2941" class="Keyword">module</a> <a id="hide-funext"></a><a id="2948" href="Prelude.Extensionality.html#2948" class="Module">hide-funext</a> <a id="2960" class="Keyword">where</a>

 <a id="hide-funext._∼_"></a><a id="2968" href="Prelude.Extensionality.html#2968" class="Function Operator">_∼_</a> <a id="2972" class="Symbol">:</a> <a id="2974" class="Symbol">{</a><a id="2975" href="Prelude.Extensionality.html#2975" class="Bound">𝓤</a> <a id="2977" href="Prelude.Extensionality.html#2977" class="Bound">𝓥</a> <a id="2979" class="Symbol">:</a> <a id="2981" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2989" class="Symbol">}{</a><a id="2991" href="Prelude.Extensionality.html#2991" class="Bound">A</a> <a id="2993" class="Symbol">:</a> <a id="2995" href="Prelude.Extensionality.html#2975" class="Bound">𝓤</a> <a id="2997" href="Universes.html#403" class="Function Operator">̇</a> <a id="2999" class="Symbol">}</a> <a id="3001" class="Symbol">{</a><a id="3002" href="Prelude.Extensionality.html#3002" class="Bound">B</a> <a id="3004" class="Symbol">:</a> <a id="3006" href="Prelude.Extensionality.html#2991" class="Bound">A</a> <a id="3008" class="Symbol">→</a> <a id="3010" href="Prelude.Extensionality.html#2977" class="Bound">𝓥</a> <a id="3012" href="Universes.html#403" class="Function Operator">̇</a> <a id="3014" class="Symbol">}</a> <a id="3016" class="Symbol">→</a> <a id="3018" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3020" href="Prelude.Extensionality.html#3002" class="Bound">B</a> <a id="3022" class="Symbol">→</a> <a id="3024" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3026" href="Prelude.Extensionality.html#3002" class="Bound">B</a> <a id="3028" class="Symbol">→</a> <a id="3030" href="Prelude.Extensionality.html#2975" class="Bound">𝓤</a> <a id="3032" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3034" href="Prelude.Extensionality.html#2977" class="Bound">𝓥</a> <a id="3036" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3039" href="Prelude.Extensionality.html#3039" class="Bound">f</a> <a id="3041" href="Prelude.Extensionality.html#2968" class="Function Operator">∼</a> <a id="3043" href="Prelude.Extensionality.html#3043" class="Bound">g</a> <a id="3045" class="Symbol">=</a> <a id="3047" class="Symbol">∀</a> <a id="3049" href="Prelude.Extensionality.html#3049" class="Bound">x</a> <a id="3051" class="Symbol">→</a> <a id="3053" href="Prelude.Extensionality.html#3039" class="Bound">f</a> <a id="3055" href="Prelude.Extensionality.html#3049" class="Bound">x</a> <a id="3057" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3059" href="Prelude.Extensionality.html#3043" class="Bound">g</a> <a id="3061" href="Prelude.Extensionality.html#3049" class="Bound">x</a>

 <a id="3065" class="Keyword">infix</a> <a id="3071" class="Number">0</a> <a id="3073" href="Prelude.Extensionality.html#2968" class="Function Operator">_∼_</a>

</pre>

*Function extensionality* is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3500" href="Prelude.Extensionality.html#3500" class="Function">funext</a> <a id="3507" class="Symbol">:</a> <a id="3509" class="Symbol">∀</a> <a id="3511" href="Prelude.Extensionality.html#3511" class="Bound">𝓤</a> <a id="3513" href="Prelude.Extensionality.html#3513" class="Bound">𝓦</a>  <a id="3516" class="Symbol">→</a> <a id="3518" href="Prelude.Extensionality.html#3511" class="Bound">𝓤</a> <a id="3520" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3522" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3524" href="Prelude.Extensionality.html#3513" class="Bound">𝓦</a> <a id="3526" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3528" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3531" href="Prelude.Extensionality.html#3500" class="Function">funext</a> <a id="3538" href="Prelude.Extensionality.html#3538" class="Bound">𝓤</a> <a id="3540" href="Prelude.Extensionality.html#3540" class="Bound">𝓦</a> <a id="3542" class="Symbol">=</a> <a id="3544" class="Symbol">{</a><a id="3545" href="Prelude.Extensionality.html#3545" class="Bound">A</a> <a id="3547" class="Symbol">:</a> <a id="3549" href="Prelude.Extensionality.html#3538" class="Bound">𝓤</a> <a id="3551" href="Universes.html#403" class="Function Operator">̇</a> <a id="3553" class="Symbol">}</a> <a id="3555" class="Symbol">{</a><a id="3556" href="Prelude.Extensionality.html#3556" class="Bound">B</a> <a id="3558" class="Symbol">:</a> <a id="3560" href="Prelude.Extensionality.html#3540" class="Bound">𝓦</a> <a id="3562" href="Universes.html#403" class="Function Operator">̇</a> <a id="3564" class="Symbol">}</a> <a id="3566" class="Symbol">{</a><a id="3567" href="Prelude.Extensionality.html#3567" class="Bound">f</a> <a id="3569" href="Prelude.Extensionality.html#3569" class="Bound">g</a> <a id="3571" class="Symbol">:</a> <a id="3573" href="Prelude.Extensionality.html#3545" class="Bound">A</a> <a id="3575" class="Symbol">→</a> <a id="3577" href="Prelude.Extensionality.html#3556" class="Bound">B</a><a id="3578" class="Symbol">}</a> <a id="3580" class="Symbol">→</a> <a id="3582" href="Prelude.Extensionality.html#3567" class="Bound">f</a> <a id="3584" href="Prelude.Extensionality.html#2968" class="Function Operator">∼</a> <a id="3586" href="Prelude.Extensionality.html#3569" class="Bound">g</a> <a id="3588" class="Symbol">→</a> <a id="3590" href="Prelude.Extensionality.html#3567" class="Bound">f</a> <a id="3592" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3594" href="Prelude.Extensionality.html#3569" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3705" href="Prelude.Extensionality.html#3705" class="Function">dfunext</a> <a id="3713" class="Symbol">:</a> <a id="3715" class="Symbol">∀</a> <a id="3717" href="Prelude.Extensionality.html#3717" class="Bound">𝓤</a> <a id="3719" href="Prelude.Extensionality.html#3719" class="Bound">𝓦</a> <a id="3721" class="Symbol">→</a> <a id="3723" href="Prelude.Extensionality.html#3717" class="Bound">𝓤</a> <a id="3725" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3727" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3729" href="Prelude.Extensionality.html#3719" class="Bound">𝓦</a> <a id="3731" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3733" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3736" href="Prelude.Extensionality.html#3705" class="Function">dfunext</a> <a id="3744" href="Prelude.Extensionality.html#3744" class="Bound">𝓤</a> <a id="3746" href="Prelude.Extensionality.html#3746" class="Bound">𝓦</a> <a id="3748" class="Symbol">=</a> <a id="3750" class="Symbol">{</a><a id="3751" href="Prelude.Extensionality.html#3751" class="Bound">A</a> <a id="3753" class="Symbol">:</a> <a id="3755" href="Prelude.Extensionality.html#3744" class="Bound">𝓤</a> <a id="3757" href="Universes.html#403" class="Function Operator">̇</a> <a id="3759" class="Symbol">}{</a><a id="3761" href="Prelude.Extensionality.html#3761" class="Bound">B</a> <a id="3763" class="Symbol">:</a> <a id="3765" href="Prelude.Extensionality.html#3751" class="Bound">A</a> <a id="3767" class="Symbol">→</a> <a id="3769" href="Prelude.Extensionality.html#3746" class="Bound">𝓦</a> <a id="3771" href="Universes.html#403" class="Function Operator">̇</a> <a id="3773" class="Symbol">}{</a><a id="3775" href="Prelude.Extensionality.html#3775" class="Bound">f</a> <a id="3777" href="Prelude.Extensionality.html#3777" class="Bound">g</a> <a id="3779" class="Symbol">:</a> <a id="3781" class="Symbol">∀(</a><a id="3783" href="Prelude.Extensionality.html#3783" class="Bound">x</a> <a id="3785" class="Symbol">:</a> <a id="3787" href="Prelude.Extensionality.html#3751" class="Bound">A</a><a id="3788" class="Symbol">)</a> <a id="3790" class="Symbol">→</a> <a id="3792" href="Prelude.Extensionality.html#3761" class="Bound">B</a> <a id="3794" href="Prelude.Extensionality.html#3783" class="Bound">x</a><a id="3795" class="Symbol">}</a> <a id="3797" class="Symbol">→</a>  <a id="3800" href="Prelude.Extensionality.html#3775" class="Bound">f</a> <a id="3802" href="Prelude.Extensionality.html#2968" class="Function Operator">∼</a> <a id="3804" href="Prelude.Extensionality.html#3777" class="Bound">g</a>  <a id="3807" class="Symbol">→</a>  <a id="3810" href="Prelude.Extensionality.html#3775" class="Bound">f</a> <a id="3812" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3814" href="Prelude.Extensionality.html#3777" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal." Moreover, if one assumes the [univalence axiom][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).

However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5459" href="Prelude.Extensionality.html#5459" class="Function">global-funext</a> <a id="5473" class="Symbol">:</a> <a id="5475" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5479" href="Prelude.Extensionality.html#5459" class="Function">global-funext</a> <a id="5493" class="Symbol">=</a> <a id="5495" class="Symbol">∀</a>  <a id="5498" class="Symbol">{</a><a id="5499" href="Prelude.Extensionality.html#5499" class="Bound">𝓤</a> <a id="5501" href="Prelude.Extensionality.html#5501" class="Bound">𝓥</a><a id="5502" class="Symbol">}</a> <a id="5504" class="Symbol">→</a> <a id="5506" href="Prelude.Extensionality.html#3500" class="Function">funext</a> <a id="5513" href="Prelude.Extensionality.html#5499" class="Bound">𝓤</a> <a id="5515" href="Prelude.Extensionality.html#5501" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5519" href="Prelude.Extensionality.html#5519" class="Function">global-dfunext</a> <a id="5534" class="Symbol">:</a> <a id="5536" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5540" href="Prelude.Extensionality.html#5519" class="Function">global-dfunext</a> <a id="5555" class="Symbol">=</a> <a id="5557" class="Symbol">∀</a> <a id="5559" class="Symbol">{</a><a id="5560" href="Prelude.Extensionality.html#5560" class="Bound">𝓤</a> <a id="5562" href="Prelude.Extensionality.html#5562" class="Bound">𝓥</a><a id="5563" class="Symbol">}</a> <a id="5565" class="Symbol">→</a> <a id="5567" href="Prelude.Extensionality.html#3705" class="Function">dfunext</a> <a id="5575" href="Prelude.Extensionality.html#5560" class="Bound">𝓤</a> <a id="5577" href="Prelude.Extensionality.html#5562" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5872" class="Keyword">open</a> <a id="5877" class="Keyword">import</a> <a id="5884" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5911" class="Keyword">using</a> <a id="5917" class="Symbol">(</a><a id="5918" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5921" class="Symbol">;</a> <a id="5923" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5929" class="Symbol">;</a> <a id="5931" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5938" class="Symbol">)</a> <a id="5940" class="Keyword">public</a>
<a id="5947" class="Keyword">open</a> <a id="5952" class="Keyword">import</a> <a id="5959" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5985" class="Keyword">using</a> <a id="5991" class="Symbol">(</a><a id="5992" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="6006" class="Symbol">)</a> <a id="6008" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6285" class="Keyword">open</a> <a id="6290" class="Keyword">import</a> <a id="6297" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6306" class="Keyword">using</a> <a id="6312" class="Symbol">(</a><a id="6313" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6316" class="Symbol">)</a> <a id="6318" class="Keyword">public</a>

<a id="6326" class="Keyword">module</a> <a id="6333" href="Prelude.Extensionality.html#6333" class="Module">_</a> <a id="6335" class="Symbol">{</a><a id="6336" href="Prelude.Extensionality.html#6336" class="Bound">𝓤</a> <a id="6338" href="Prelude.Extensionality.html#6338" class="Bound">𝓦</a> <a id="6340" class="Symbol">:</a> <a id="6342" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6350" class="Symbol">}</a> <a id="6352" class="Keyword">where</a>

 <a id="6360" href="Prelude.Extensionality.html#6360" class="Function">extfun</a> <a id="6367" class="Symbol">:</a> <a id="6369" class="Symbol">{</a><a id="6370" href="Prelude.Extensionality.html#6370" class="Bound">A</a> <a id="6372" class="Symbol">:</a> <a id="6374" href="Prelude.Extensionality.html#6336" class="Bound">𝓤</a> <a id="6376" href="Universes.html#403" class="Function Operator">̇</a><a id="6377" class="Symbol">}{</a><a id="6379" href="Prelude.Extensionality.html#6379" class="Bound">B</a> <a id="6381" class="Symbol">:</a> <a id="6383" href="Prelude.Extensionality.html#6338" class="Bound">𝓦</a> <a id="6385" href="Universes.html#403" class="Function Operator">̇</a><a id="6386" class="Symbol">}{</a><a id="6388" href="Prelude.Extensionality.html#6388" class="Bound">f</a> <a id="6390" href="Prelude.Extensionality.html#6390" class="Bound">g</a> <a id="6392" class="Symbol">:</a> <a id="6394" href="Prelude.Extensionality.html#6370" class="Bound">A</a> <a id="6396" class="Symbol">→</a> <a id="6398" href="Prelude.Extensionality.html#6379" class="Bound">B</a><a id="6399" class="Symbol">}</a> <a id="6401" class="Symbol">→</a> <a id="6403" href="Prelude.Extensionality.html#6388" class="Bound">f</a> <a id="6405" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6407" href="Prelude.Extensionality.html#6390" class="Bound">g</a>  <a id="6410" class="Symbol">→</a>  <a id="6413" href="Prelude.Extensionality.html#6388" class="Bound">f</a> <a id="6415" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6417" href="Prelude.Extensionality.html#6390" class="Bound">g</a>
 <a id="6420" href="Prelude.Extensionality.html#6360" class="Function">extfun</a> <a id="6427" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6432" class="Symbol">_</a> <a id="6434" class="Symbol">=</a> <a id="6436" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6562" href="Prelude.Extensionality.html#6562" class="Function">extdfun</a> <a id="6570" class="Symbol">:</a> <a id="6572" class="Symbol">{</a><a id="6573" href="Prelude.Extensionality.html#6573" class="Bound">A</a> <a id="6575" class="Symbol">:</a> <a id="6577" href="Prelude.Extensionality.html#6336" class="Bound">𝓤</a> <a id="6579" href="Universes.html#403" class="Function Operator">̇</a> <a id="6581" class="Symbol">}{</a><a id="6583" href="Prelude.Extensionality.html#6583" class="Bound">B</a> <a id="6585" class="Symbol">:</a> <a id="6587" href="Prelude.Extensionality.html#6573" class="Bound">A</a> <a id="6589" class="Symbol">→</a> <a id="6591" href="Prelude.Extensionality.html#6338" class="Bound">𝓦</a> <a id="6593" href="Universes.html#403" class="Function Operator">̇</a> <a id="6595" class="Symbol">}(</a><a id="6597" href="Prelude.Extensionality.html#6597" class="Bound">f</a> <a id="6599" href="Prelude.Extensionality.html#6599" class="Bound">g</a> <a id="6601" class="Symbol">:</a> <a id="6603" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6605" href="Prelude.Extensionality.html#6583" class="Bound">B</a><a id="6606" class="Symbol">)</a> <a id="6608" class="Symbol">→</a> <a id="6610" href="Prelude.Extensionality.html#6597" class="Bound">f</a> <a id="6612" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6614" href="Prelude.Extensionality.html#6599" class="Bound">g</a> <a id="6616" class="Symbol">→</a> <a id="6618" href="Prelude.Extensionality.html#6597" class="Bound">f</a> <a id="6620" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6622" href="Prelude.Extensionality.html#6599" class="Bound">g</a>
 <a id="6625" href="Prelude.Extensionality.html#6562" class="Function">extdfun</a> <a id="6633" class="Symbol">_</a> <a id="6635" class="Symbol">_</a> <a id="6637" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6642" class="Symbol">_</a> <a id="6644" class="Symbol">=</a> <a id="6646" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8507" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8514" href="Prelude.Extensionality.html#8514" class="Module">hide-tt-defs</a> <a id="8527" class="Symbol">{</a><a id="8528" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8530" class="Symbol">:</a> <a id="8532" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8540" class="Symbol">}</a> <a id="8542" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8550" href="Prelude.Extensionality.html#8550" class="Function">is-center</a> <a id="8560" class="Symbol">:</a> <a id="8562" class="Symbol">(</a><a id="8563" href="Prelude.Extensionality.html#8563" class="Bound">A</a> <a id="8565" class="Symbol">:</a> <a id="8567" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8569" href="Universes.html#403" class="Function Operator">̇</a> <a id="8571" class="Symbol">)</a> <a id="8573" class="Symbol">→</a> <a id="8575" href="Prelude.Extensionality.html#8563" class="Bound">A</a> <a id="8577" class="Symbol">→</a> <a id="8579" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8581" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8584" href="Prelude.Extensionality.html#8550" class="Function">is-center</a> <a id="8594" href="Prelude.Extensionality.html#8594" class="Bound">A</a> <a id="8596" href="Prelude.Extensionality.html#8596" class="Bound">c</a> <a id="8598" class="Symbol">=</a> <a id="8600" class="Symbol">(</a><a id="8601" href="Prelude.Extensionality.html#8601" class="Bound">x</a> <a id="8603" class="Symbol">:</a> <a id="8605" href="Prelude.Extensionality.html#8594" class="Bound">A</a><a id="8606" class="Symbol">)</a> <a id="8608" class="Symbol">→</a> <a id="8610" href="Prelude.Extensionality.html#8596" class="Bound">c</a> <a id="8612" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8614" href="Prelude.Extensionality.html#8601" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8618" href="Prelude.Extensionality.html#8618" class="Function">is-singleton</a> <a id="8631" class="Symbol">:</a> <a id="8633" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8635" href="Universes.html#403" class="Function Operator">̇</a> <a id="8637" class="Symbol">→</a> <a id="8639" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8641" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8644" href="Prelude.Extensionality.html#8618" class="Function">is-singleton</a> <a id="8657" href="Prelude.Extensionality.html#8657" class="Bound">A</a> <a id="8659" class="Symbol">=</a> <a id="8661" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8663" href="Prelude.Extensionality.html#8663" class="Bound">c</a> <a id="8665" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8667" href="Prelude.Extensionality.html#8657" class="Bound">A</a> <a id="8669" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8671" href="Prelude.Extensionality.html#8550" class="Function">is-center</a> <a id="8681" href="Prelude.Extensionality.html#8657" class="Bound">A</a> <a id="8683" href="Prelude.Extensionality.html#8663" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8687" href="Prelude.Extensionality.html#8687" class="Function">is-subsingleton</a> <a id="8703" class="Symbol">:</a> <a id="8705" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8707" href="Universes.html#403" class="Function Operator">̇</a> <a id="8709" class="Symbol">→</a> <a id="8711" href="Prelude.Extensionality.html#8528" class="Bound">𝓤</a> <a id="8713" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8716" href="Prelude.Extensionality.html#8687" class="Function">is-subsingleton</a> <a id="8732" href="Prelude.Extensionality.html#8732" class="Bound">A</a> <a id="8734" class="Symbol">=</a> <a id="8736" class="Symbol">(</a><a id="8737" href="Prelude.Extensionality.html#8737" class="Bound">x</a> <a id="8739" href="Prelude.Extensionality.html#8739" class="Bound">y</a> <a id="8741" class="Symbol">:</a> <a id="8743" href="Prelude.Extensionality.html#8732" class="Bound">A</a><a id="8744" class="Symbol">)</a> <a id="8746" class="Symbol">→</a> <a id="8748" href="Prelude.Extensionality.html#8737" class="Bound">x</a> <a id="8750" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8752" href="Prelude.Extensionality.html#8739" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="9045" class="Keyword">open</a> <a id="9050" class="Keyword">import</a> <a id="9057" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9070" class="Keyword">using</a> <a id="9076" class="Symbol">(</a><a id="9077" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9086" class="Symbol">;</a> <a id="9088" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9100" class="Symbol">;</a> <a id="9102" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9117" class="Symbol">)</a> <a id="9119" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9536" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9543" href="Prelude.Extensionality.html#9543" class="Module">hide-tt-defs&#39;</a> <a id="9557" class="Symbol">{</a><a id="9558" href="Prelude.Extensionality.html#9558" class="Bound">𝓤</a> <a id="9560" href="Prelude.Extensionality.html#9560" class="Bound">𝓦</a> <a id="9562" class="Symbol">:</a> <a id="9564" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9572" class="Symbol">}</a> <a id="9574" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9582" href="Prelude.Extensionality.html#9582" class="Function">fiber</a> <a id="9588" class="Symbol">:</a> <a id="9590" class="Symbol">{</a><a id="9591" href="Prelude.Extensionality.html#9591" class="Bound">A</a> <a id="9593" class="Symbol">:</a> <a id="9595" href="Prelude.Extensionality.html#9558" class="Bound">𝓤</a> <a id="9597" href="Universes.html#403" class="Function Operator">̇</a> <a id="9599" class="Symbol">}</a> <a id="9601" class="Symbol">{</a><a id="9602" href="Prelude.Extensionality.html#9602" class="Bound">B</a> <a id="9604" class="Symbol">:</a> <a id="9606" href="Prelude.Extensionality.html#9560" class="Bound">𝓦</a> <a id="9608" href="Universes.html#403" class="Function Operator">̇</a> <a id="9610" class="Symbol">}</a> <a id="9612" class="Symbol">(</a><a id="9613" href="Prelude.Extensionality.html#9613" class="Bound">f</a> <a id="9615" class="Symbol">:</a> <a id="9617" href="Prelude.Extensionality.html#9591" class="Bound">A</a> <a id="9619" class="Symbol">→</a> <a id="9621" href="Prelude.Extensionality.html#9602" class="Bound">B</a><a id="9622" class="Symbol">)</a> <a id="9624" class="Symbol">→</a> <a id="9626" href="Prelude.Extensionality.html#9602" class="Bound">B</a> <a id="9628" class="Symbol">→</a> <a id="9630" href="Prelude.Extensionality.html#9558" class="Bound">𝓤</a> <a id="9632" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9634" href="Prelude.Extensionality.html#9560" class="Bound">𝓦</a> <a id="9636" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9639" href="Prelude.Extensionality.html#9582" class="Function">fiber</a> <a id="9645" class="Symbol">{</a><a id="9646" href="Prelude.Extensionality.html#9646" class="Bound">A</a><a id="9647" class="Symbol">}</a> <a id="9649" href="Prelude.Extensionality.html#9649" class="Bound">f</a> <a id="9651" href="Prelude.Extensionality.html#9651" class="Bound">y</a> <a id="9653" class="Symbol">=</a> <a id="9655" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9657" href="Prelude.Extensionality.html#9657" class="Bound">x</a> <a id="9659" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9661" href="Prelude.Extensionality.html#9646" class="Bound">A</a> <a id="9663" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9665" href="Prelude.Extensionality.html#9649" class="Bound">f</a> <a id="9667" href="Prelude.Extensionality.html#9657" class="Bound">x</a> <a id="9669" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="9671" href="Prelude.Extensionality.html#9651" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9777" href="Prelude.Extensionality.html#9777" class="Function">is-equiv</a> <a id="9786" class="Symbol">:</a> <a id="9788" class="Symbol">{</a><a id="9789" href="Prelude.Extensionality.html#9789" class="Bound">A</a> <a id="9791" class="Symbol">:</a> <a id="9793" href="Prelude.Extensionality.html#9558" class="Bound">𝓤</a> <a id="9795" href="Universes.html#403" class="Function Operator">̇</a> <a id="9797" class="Symbol">}</a> <a id="9799" class="Symbol">{</a><a id="9800" href="Prelude.Extensionality.html#9800" class="Bound">B</a> <a id="9802" class="Symbol">:</a> <a id="9804" href="Prelude.Extensionality.html#9560" class="Bound">𝓦</a> <a id="9806" href="Universes.html#403" class="Function Operator">̇</a> <a id="9808" class="Symbol">}</a> <a id="9810" class="Symbol">→</a> <a id="9812" class="Symbol">(</a><a id="9813" href="Prelude.Extensionality.html#9789" class="Bound">A</a> <a id="9815" class="Symbol">→</a> <a id="9817" href="Prelude.Extensionality.html#9800" class="Bound">B</a><a id="9818" class="Symbol">)</a> <a id="9820" class="Symbol">→</a> <a id="9822" href="Prelude.Extensionality.html#9558" class="Bound">𝓤</a> <a id="9824" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9826" href="Prelude.Extensionality.html#9560" class="Bound">𝓦</a> <a id="9828" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9831" href="Prelude.Extensionality.html#9777" class="Function">is-equiv</a> <a id="9840" href="Prelude.Extensionality.html#9840" class="Bound">f</a> <a id="9842" class="Symbol">=</a> <a id="9844" class="Symbol">∀</a> <a id="9846" href="Prelude.Extensionality.html#9846" class="Bound">y</a> <a id="9848" class="Symbol">→</a> <a id="9850" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9863" class="Symbol">(</a><a id="9864" href="Prelude.Extensionality.html#9582" class="Function">fiber</a> <a id="9870" href="Prelude.Extensionality.html#9840" class="Bound">f</a> <a id="9872" href="Prelude.Extensionality.html#9846" class="Bound">y</a><a id="9873" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="10079" class="Keyword">open</a> <a id="10084" class="Keyword">import</a> <a id="10091" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10108" class="Keyword">using</a> <a id="10114" class="Symbol">(</a><a id="10115" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10120" class="Symbol">;</a> <a id="10122" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10130" class="Symbol">)</a> <a id="10132" class="Keyword">public</a>

<a id="10140" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10147" href="Prelude.Extensionality.html#10147" class="Module">hide-hfunext</a> <a id="10160" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10168" href="Prelude.Extensionality.html#10168" class="Function">hfunext</a> <a id="10176" class="Symbol">:</a> <a id="10178" class="Symbol">(</a><a id="10179" href="Prelude.Extensionality.html#10179" class="Bound">𝓤</a> <a id="10181" href="Prelude.Extensionality.html#10181" class="Bound">𝓦</a> <a id="10183" class="Symbol">:</a> <a id="10185" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10193" class="Symbol">)</a> <a id="10195" class="Symbol">→</a> <a id="10197" class="Symbol">(</a><a id="10198" href="Prelude.Extensionality.html#10179" class="Bound">𝓤</a> <a id="10200" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10202" href="Prelude.Extensionality.html#10181" class="Bound">𝓦</a><a id="10203" class="Symbol">)</a><a id="10204" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10206" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10209" href="Prelude.Extensionality.html#10168" class="Function">hfunext</a> <a id="10217" href="Prelude.Extensionality.html#10217" class="Bound">𝓤</a> <a id="10219" href="Prelude.Extensionality.html#10219" class="Bound">𝓦</a> <a id="10221" class="Symbol">=</a> <a id="10223" class="Symbol">{</a><a id="10224" href="Prelude.Extensionality.html#10224" class="Bound">A</a> <a id="10226" class="Symbol">:</a> <a id="10228" href="Prelude.Extensionality.html#10217" class="Bound">𝓤</a> <a id="10230" href="Universes.html#403" class="Function Operator">̇</a><a id="10231" class="Symbol">}{</a><a id="10233" href="Prelude.Extensionality.html#10233" class="Bound">B</a> <a id="10235" class="Symbol">:</a> <a id="10237" href="Prelude.Extensionality.html#10224" class="Bound">A</a> <a id="10239" class="Symbol">→</a> <a id="10241" href="Prelude.Extensionality.html#10219" class="Bound">𝓦</a> <a id="10243" href="Universes.html#403" class="Function Operator">̇</a><a id="10244" class="Symbol">}</a> <a id="10246" class="Symbol">(</a><a id="10247" href="Prelude.Extensionality.html#10247" class="Bound">f</a> <a id="10249" href="Prelude.Extensionality.html#10249" class="Bound">g</a> <a id="10251" class="Symbol">:</a> <a id="10253" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10255" href="Prelude.Extensionality.html#10233" class="Bound">B</a><a id="10256" class="Symbol">)</a> <a id="10258" class="Symbol">→</a> <a id="10260" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10269" class="Symbol">(</a><a id="10270" href="Prelude.Extensionality.html#6562" class="Function">extdfun</a> <a id="10278" href="Prelude.Extensionality.html#10247" class="Bound">f</a> <a id="10280" href="Prelude.Extensionality.html#10249" class="Bound">g</a><a id="10281" class="Symbol">)</a>
<a id="10283" class="Keyword">open</a> <a id="10288" class="Keyword">import</a> <a id="10295" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10323" class="Keyword">using</a> <a id="10329" class="Symbol">(</a><a id="10330" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10337" class="Symbol">)</a> <a id="10339" class="Keyword">public</a>

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
