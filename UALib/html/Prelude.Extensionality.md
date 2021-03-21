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

This introduction is intended for novices.  Those already familiar with function extensionality may wish to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose `f` and `g` are defined on `A = ℤ` (the integers) as follows: `f x := x + 2` and `g x := ((2 * x) - 8)/2 + 6`.  Should we call `f` and `g` equal? Are they the "same" function?  What does that even mean?

It's hard to resist the urge to reduce `g` to `x + 2` and proclaim that `f` and `g` are equal. Indeed, this is often an acceptable answer and the discussion normally ends there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions `f` and `g` above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions, `f` and `g`, both of which take a list as argument and produce as output a correctly sorted version of the input list?  Suppose `f` is defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while `g` uses [quick sort](https://en.wikipedia.org/wiki/Quicksort).  Probably few of us would call `f` and `g` the "same" in this case.

In the examples above, it is common to say that the two functions are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same *external* output when given the same input, but they are not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their *internal* definitions differ.

In this module, we describe types that manifest this notion of *extensional equality of functions*, or *function extensionality*.<sup>[1](Prelude.Extensionality.html#fn1)</sup>

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

The natural notion of function equality, which is often called *point-wise equality*, is defined as follows: `∀ x → f x ≡ g x`.  Here is how this notion is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="2858" class="Keyword">module</a> <a id="hide-∼"></a><a id="2865" href="Prelude.Extensionality.html#2865" class="Module">hide-∼</a> <a id="2872" class="Symbol">{</a><a id="2873" href="Prelude.Extensionality.html#2873" class="Bound">𝓤</a> <a id="2875" href="Prelude.Extensionality.html#2875" class="Bound">𝓦</a> <a id="2877" class="Symbol">:</a> <a id="2879" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2887" class="Symbol">}</a> <a id="2889" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2897" href="Prelude.Extensionality.html#2897" class="Function Operator">_∼_</a> <a id="2901" class="Symbol">:</a> <a id="2903" class="Symbol">{</a><a id="2904" href="Prelude.Extensionality.html#2904" class="Bound">A</a> <a id="2906" class="Symbol">:</a> <a id="2908" href="Prelude.Extensionality.html#2873" class="Bound">𝓤</a> <a id="2910" href="Universes.html#403" class="Function Operator">̇</a> <a id="2912" class="Symbol">}</a> <a id="2914" class="Symbol">{</a><a id="2915" href="Prelude.Extensionality.html#2915" class="Bound">B</a> <a id="2917" class="Symbol">:</a> <a id="2919" href="Prelude.Extensionality.html#2904" class="Bound">A</a> <a id="2921" class="Symbol">→</a> <a id="2923" href="Prelude.Extensionality.html#2875" class="Bound">𝓦</a> <a id="2925" href="Universes.html#403" class="Function Operator">̇</a> <a id="2927" class="Symbol">}</a> <a id="2929" class="Symbol">→</a> <a id="2931" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2933" href="Prelude.Extensionality.html#2915" class="Bound">B</a> <a id="2935" class="Symbol">→</a> <a id="2937" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2939" href="Prelude.Extensionality.html#2915" class="Bound">B</a> <a id="2941" class="Symbol">→</a> <a id="2943" href="Prelude.Extensionality.html#2873" class="Bound">𝓤</a> <a id="2945" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2947" href="Prelude.Extensionality.html#2875" class="Bound">𝓦</a> <a id="2949" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2952" href="Prelude.Extensionality.html#2952" class="Bound">f</a> <a id="2954" href="Prelude.Extensionality.html#2897" class="Function Operator">∼</a> <a id="2956" href="Prelude.Extensionality.html#2956" class="Bound">g</a> <a id="2958" class="Symbol">=</a> <a id="2960" class="Symbol">∀</a> <a id="2962" href="Prelude.Extensionality.html#2962" class="Bound">x</a> <a id="2964" class="Symbol">→</a> <a id="2966" href="Prelude.Extensionality.html#2952" class="Bound">f</a> <a id="2968" href="Prelude.Extensionality.html#2962" class="Bound">x</a> <a id="2970" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="2972" href="Prelude.Extensionality.html#2956" class="Bound">g</a> <a id="2974" href="Prelude.Extensionality.html#2962" class="Bound">x</a>

 <a id="2978" class="Keyword">infix</a> <a id="2984" class="Number">0</a> <a id="2986" href="Prelude.Extensionality.html#2897" class="Function Operator">_∼_</a>

<a id="2991" class="Keyword">open</a> <a id="2996" class="Keyword">import</a> <a id="3003" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="3030" class="Keyword">using</a> <a id="3036" class="Symbol">(</a><a id="3037" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3040" class="Symbol">)</a> <a id="3042" class="Keyword">public</a>

</pre>

*Function extensionality* is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

<a id="3471" class="Keyword">module</a> <a id="hide-funext"></a><a id="3478" href="Prelude.Extensionality.html#3478" class="Module">hide-funext</a> <a id="3490" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3498" href="Prelude.Extensionality.html#3498" class="Function">funext</a> <a id="3505" class="Symbol">:</a> <a id="3507" class="Symbol">∀</a> <a id="3509" href="Prelude.Extensionality.html#3509" class="Bound">𝓤</a> <a id="3511" href="Prelude.Extensionality.html#3511" class="Bound">𝓦</a>  <a id="3514" class="Symbol">→</a> <a id="3516" href="Prelude.Extensionality.html#3509" class="Bound">𝓤</a> <a id="3518" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3520" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3522" href="Prelude.Extensionality.html#3511" class="Bound">𝓦</a> <a id="3524" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3526" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3529" href="Prelude.Extensionality.html#3498" class="Function">funext</a> <a id="3536" href="Prelude.Extensionality.html#3536" class="Bound">𝓤</a> <a id="3538" href="Prelude.Extensionality.html#3538" class="Bound">𝓦</a> <a id="3540" class="Symbol">=</a> <a id="3542" class="Symbol">{</a><a id="3543" href="Prelude.Extensionality.html#3543" class="Bound">A</a> <a id="3545" class="Symbol">:</a> <a id="3547" href="Prelude.Extensionality.html#3536" class="Bound">𝓤</a> <a id="3549" href="Universes.html#403" class="Function Operator">̇</a> <a id="3551" class="Symbol">}</a> <a id="3553" class="Symbol">{</a><a id="3554" href="Prelude.Extensionality.html#3554" class="Bound">B</a> <a id="3556" class="Symbol">:</a> <a id="3558" href="Prelude.Extensionality.html#3538" class="Bound">𝓦</a> <a id="3560" href="Universes.html#403" class="Function Operator">̇</a> <a id="3562" class="Symbol">}</a> <a id="3564" class="Symbol">{</a><a id="3565" href="Prelude.Extensionality.html#3565" class="Bound">f</a> <a id="3567" href="Prelude.Extensionality.html#3567" class="Bound">g</a> <a id="3569" class="Symbol">:</a> <a id="3571" href="Prelude.Extensionality.html#3543" class="Bound">A</a> <a id="3573" class="Symbol">→</a> <a id="3575" href="Prelude.Extensionality.html#3554" class="Bound">B</a><a id="3576" class="Symbol">}</a> <a id="3578" class="Symbol">→</a> <a id="3580" href="Prelude.Extensionality.html#3565" class="Bound">f</a> <a id="3582" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3584" href="Prelude.Extensionality.html#3567" class="Bound">g</a> <a id="3586" class="Symbol">→</a> <a id="3588" href="Prelude.Extensionality.html#3565" class="Bound">f</a> <a id="3590" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3592" href="Prelude.Extensionality.html#3567" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3703" href="Prelude.Extensionality.html#3703" class="Function">dfunext</a> <a id="3711" class="Symbol">:</a> <a id="3713" class="Symbol">∀</a> <a id="3715" href="Prelude.Extensionality.html#3715" class="Bound">𝓤</a> <a id="3717" href="Prelude.Extensionality.html#3717" class="Bound">𝓦</a> <a id="3719" class="Symbol">→</a> <a id="3721" href="Prelude.Extensionality.html#3715" class="Bound">𝓤</a> <a id="3723" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3725" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3727" href="Prelude.Extensionality.html#3717" class="Bound">𝓦</a> <a id="3729" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3731" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3734" href="Prelude.Extensionality.html#3703" class="Function">dfunext</a> <a id="3742" href="Prelude.Extensionality.html#3742" class="Bound">𝓤</a> <a id="3744" href="Prelude.Extensionality.html#3744" class="Bound">𝓦</a> <a id="3746" class="Symbol">=</a> <a id="3748" class="Symbol">{</a><a id="3749" href="Prelude.Extensionality.html#3749" class="Bound">A</a> <a id="3751" class="Symbol">:</a> <a id="3753" href="Prelude.Extensionality.html#3742" class="Bound">𝓤</a> <a id="3755" href="Universes.html#403" class="Function Operator">̇</a> <a id="3757" class="Symbol">}{</a><a id="3759" href="Prelude.Extensionality.html#3759" class="Bound">B</a> <a id="3761" class="Symbol">:</a> <a id="3763" href="Prelude.Extensionality.html#3749" class="Bound">A</a> <a id="3765" class="Symbol">→</a> <a id="3767" href="Prelude.Extensionality.html#3744" class="Bound">𝓦</a> <a id="3769" href="Universes.html#403" class="Function Operator">̇</a> <a id="3771" class="Symbol">}{</a><a id="3773" href="Prelude.Extensionality.html#3773" class="Bound">f</a> <a id="3775" href="Prelude.Extensionality.html#3775" class="Bound">g</a> <a id="3777" class="Symbol">:</a> <a id="3779" class="Symbol">∀(</a><a id="3781" href="Prelude.Extensionality.html#3781" class="Bound">x</a> <a id="3783" class="Symbol">:</a> <a id="3785" href="Prelude.Extensionality.html#3749" class="Bound">A</a><a id="3786" class="Symbol">)</a> <a id="3788" class="Symbol">→</a> <a id="3790" href="Prelude.Extensionality.html#3759" class="Bound">B</a> <a id="3792" href="Prelude.Extensionality.html#3781" class="Bound">x</a><a id="3793" class="Symbol">}</a> <a id="3795" class="Symbol">→</a>  <a id="3798" href="Prelude.Extensionality.html#3773" class="Bound">f</a> <a id="3800" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3802" href="Prelude.Extensionality.html#3775" class="Bound">g</a>  <a id="3805" class="Symbol">→</a>  <a id="3808" href="Prelude.Extensionality.html#3773" class="Bound">f</a> <a id="3810" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="3812" href="Prelude.Extensionality.html#3775" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Prelude.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5220" href="Prelude.Extensionality.html#5220" class="Function">global-funext</a> <a id="5234" class="Symbol">:</a> <a id="5236" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5240" href="Prelude.Extensionality.html#5220" class="Function">global-funext</a> <a id="5254" class="Symbol">=</a> <a id="5256" class="Symbol">∀</a>  <a id="5259" class="Symbol">{</a><a id="5260" href="Prelude.Extensionality.html#5260" class="Bound">𝓤</a> <a id="5262" href="Prelude.Extensionality.html#5262" class="Bound">𝓥</a><a id="5263" class="Symbol">}</a> <a id="5265" class="Symbol">→</a> <a id="5267" href="Prelude.Extensionality.html#3498" class="Function">funext</a> <a id="5274" href="Prelude.Extensionality.html#5260" class="Bound">𝓤</a> <a id="5276" href="Prelude.Extensionality.html#5262" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5280" href="Prelude.Extensionality.html#5280" class="Function">global-dfunext</a> <a id="5295" class="Symbol">:</a> <a id="5297" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5301" href="Prelude.Extensionality.html#5280" class="Function">global-dfunext</a> <a id="5316" class="Symbol">=</a> <a id="5318" class="Symbol">∀</a> <a id="5320" class="Symbol">{</a><a id="5321" href="Prelude.Extensionality.html#5321" class="Bound">𝓤</a> <a id="5323" href="Prelude.Extensionality.html#5323" class="Bound">𝓥</a><a id="5324" class="Symbol">}</a> <a id="5326" class="Symbol">→</a> <a id="5328" href="Prelude.Extensionality.html#3703" class="Function">dfunext</a> <a id="5336" href="Prelude.Extensionality.html#5321" class="Bound">𝓤</a> <a id="5338" href="Prelude.Extensionality.html#5323" class="Bound">𝓥</a>

</pre>

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5633" class="Keyword">open</a> <a id="5638" class="Keyword">import</a> <a id="5645" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5672" class="Keyword">using</a> <a id="5678" class="Symbol">(</a><a id="5679" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5685" class="Symbol">;</a> <a id="5687" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5694" class="Symbol">)</a> <a id="5696" class="Keyword">public</a>
<a id="5703" class="Keyword">open</a> <a id="5708" class="Keyword">import</a> <a id="5715" href="MGS-Subsingleton-Theorems.html" class="Module">MGS-Subsingleton-Theorems</a> <a id="5741" class="Keyword">using</a> <a id="5747" class="Symbol">(</a><a id="5748" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="5762" class="Symbol">)</a> <a id="5764" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="6041" class="Keyword">open</a> <a id="6046" class="Keyword">import</a> <a id="6053" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6062" class="Keyword">using</a> <a id="6068" class="Symbol">(</a><a id="6069" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6072" class="Symbol">)</a> <a id="6074" class="Keyword">public</a>

<a id="6082" class="Keyword">module</a> <a id="6089" href="Prelude.Extensionality.html#6089" class="Module">_</a> <a id="6091" class="Symbol">{</a><a id="6092" href="Prelude.Extensionality.html#6092" class="Bound">𝓤</a> <a id="6094" href="Prelude.Extensionality.html#6094" class="Bound">𝓦</a> <a id="6096" class="Symbol">:</a> <a id="6098" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6106" class="Symbol">}</a> <a id="6108" class="Keyword">where</a>

 <a id="6116" href="Prelude.Extensionality.html#6116" class="Function">extfun</a> <a id="6123" class="Symbol">:</a> <a id="6125" class="Symbol">{</a><a id="6126" href="Prelude.Extensionality.html#6126" class="Bound">A</a> <a id="6128" class="Symbol">:</a> <a id="6130" href="Prelude.Extensionality.html#6092" class="Bound">𝓤</a> <a id="6132" href="Universes.html#403" class="Function Operator">̇</a><a id="6133" class="Symbol">}{</a><a id="6135" href="Prelude.Extensionality.html#6135" class="Bound">B</a> <a id="6137" class="Symbol">:</a> <a id="6139" href="Prelude.Extensionality.html#6094" class="Bound">𝓦</a> <a id="6141" href="Universes.html#403" class="Function Operator">̇</a><a id="6142" class="Symbol">}{</a><a id="6144" href="Prelude.Extensionality.html#6144" class="Bound">f</a> <a id="6146" href="Prelude.Extensionality.html#6146" class="Bound">g</a> <a id="6148" class="Symbol">:</a> <a id="6150" href="Prelude.Extensionality.html#6126" class="Bound">A</a> <a id="6152" class="Symbol">→</a> <a id="6154" href="Prelude.Extensionality.html#6135" class="Bound">B</a><a id="6155" class="Symbol">}</a> <a id="6157" class="Symbol">→</a> <a id="6159" href="Prelude.Extensionality.html#6144" class="Bound">f</a> <a id="6161" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6163" href="Prelude.Extensionality.html#6146" class="Bound">g</a>  <a id="6166" class="Symbol">→</a>  <a id="6169" href="Prelude.Extensionality.html#6144" class="Bound">f</a> <a id="6171" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6173" href="Prelude.Extensionality.html#6146" class="Bound">g</a>
 <a id="6176" href="Prelude.Extensionality.html#6116" class="Function">extfun</a> <a id="6183" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6188" class="Symbol">_</a> <a id="6190" class="Symbol">=</a> <a id="6192" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Prelude.equality][]).

<pre class="Agda">

 <a id="6318" href="Prelude.Extensionality.html#6318" class="Function">extdfun</a> <a id="6326" class="Symbol">:</a> <a id="6328" class="Symbol">{</a><a id="6329" href="Prelude.Extensionality.html#6329" class="Bound">A</a> <a id="6331" class="Symbol">:</a> <a id="6333" href="Prelude.Extensionality.html#6092" class="Bound">𝓤</a> <a id="6335" href="Universes.html#403" class="Function Operator">̇</a> <a id="6337" class="Symbol">}{</a><a id="6339" href="Prelude.Extensionality.html#6339" class="Bound">B</a> <a id="6341" class="Symbol">:</a> <a id="6343" href="Prelude.Extensionality.html#6329" class="Bound">A</a> <a id="6345" class="Symbol">→</a> <a id="6347" href="Prelude.Extensionality.html#6094" class="Bound">𝓦</a> <a id="6349" href="Universes.html#403" class="Function Operator">̇</a> <a id="6351" class="Symbol">}(</a><a id="6353" href="Prelude.Extensionality.html#6353" class="Bound">f</a> <a id="6355" href="Prelude.Extensionality.html#6355" class="Bound">g</a> <a id="6357" class="Symbol">:</a> <a id="6359" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6361" href="Prelude.Extensionality.html#6339" class="Bound">B</a><a id="6362" class="Symbol">)</a> <a id="6364" class="Symbol">→</a> <a id="6366" href="Prelude.Extensionality.html#6353" class="Bound">f</a> <a id="6368" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="6370" href="Prelude.Extensionality.html#6355" class="Bound">g</a> <a id="6372" class="Symbol">→</a> <a id="6374" href="Prelude.Extensionality.html#6353" class="Bound">f</a> <a id="6376" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6378" href="Prelude.Extensionality.html#6355" class="Bound">g</a>
 <a id="6381" href="Prelude.Extensionality.html#6318" class="Function">extdfun</a> <a id="6389" class="Symbol">_</a> <a id="6391" class="Symbol">_</a> <a id="6393" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="6398" class="Symbol">_</a> <a id="6400" class="Symbol">=</a> <a id="6402" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.  In the definition of `funext`, the codomain is a generic type (namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `). In the definition of `extfun`, the codomain is an assertion (namely, `f ∼ g`).  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥` (i.e., a proof that point-wise equal functions are equal), but as noted above the existence of such a witness cannot be *proved* in [MLTT][].

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8263" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8270" href="Prelude.Extensionality.html#8270" class="Module">hide-tt-defs</a> <a id="8283" class="Symbol">{</a><a id="8284" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8286" class="Symbol">:</a> <a id="8288" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8296" class="Symbol">}</a> <a id="8298" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8306" href="Prelude.Extensionality.html#8306" class="Function">is-center</a> <a id="8316" class="Symbol">:</a> <a id="8318" class="Symbol">(</a><a id="8319" href="Prelude.Extensionality.html#8319" class="Bound">A</a> <a id="8321" class="Symbol">:</a> <a id="8323" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8325" href="Universes.html#403" class="Function Operator">̇</a> <a id="8327" class="Symbol">)</a> <a id="8329" class="Symbol">→</a> <a id="8331" href="Prelude.Extensionality.html#8319" class="Bound">A</a> <a id="8333" class="Symbol">→</a> <a id="8335" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8337" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8340" href="Prelude.Extensionality.html#8306" class="Function">is-center</a> <a id="8350" href="Prelude.Extensionality.html#8350" class="Bound">A</a> <a id="8352" href="Prelude.Extensionality.html#8352" class="Bound">c</a> <a id="8354" class="Symbol">=</a> <a id="8356" class="Symbol">(</a><a id="8357" href="Prelude.Extensionality.html#8357" class="Bound">x</a> <a id="8359" class="Symbol">:</a> <a id="8361" href="Prelude.Extensionality.html#8350" class="Bound">A</a><a id="8362" class="Symbol">)</a> <a id="8364" class="Symbol">→</a> <a id="8366" href="Prelude.Extensionality.html#8352" class="Bound">c</a> <a id="8368" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8370" href="Prelude.Extensionality.html#8357" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8374" href="Prelude.Extensionality.html#8374" class="Function">is-singleton</a> <a id="8387" class="Symbol">:</a> <a id="8389" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8391" href="Universes.html#403" class="Function Operator">̇</a> <a id="8393" class="Symbol">→</a> <a id="8395" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8397" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8400" href="Prelude.Extensionality.html#8374" class="Function">is-singleton</a> <a id="8413" href="Prelude.Extensionality.html#8413" class="Bound">A</a> <a id="8415" class="Symbol">=</a> <a id="8417" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8419" href="Prelude.Extensionality.html#8419" class="Bound">c</a> <a id="8421" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8423" href="Prelude.Extensionality.html#8413" class="Bound">A</a> <a id="8425" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8427" href="Prelude.Extensionality.html#8306" class="Function">is-center</a> <a id="8437" href="Prelude.Extensionality.html#8413" class="Bound">A</a> <a id="8439" href="Prelude.Extensionality.html#8419" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8443" href="Prelude.Extensionality.html#8443" class="Function">is-subsingleton</a> <a id="8459" class="Symbol">:</a> <a id="8461" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8463" href="Universes.html#403" class="Function Operator">̇</a> <a id="8465" class="Symbol">→</a> <a id="8467" href="Prelude.Extensionality.html#8284" class="Bound">𝓤</a> <a id="8469" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8472" href="Prelude.Extensionality.html#8443" class="Function">is-subsingleton</a> <a id="8488" href="Prelude.Extensionality.html#8488" class="Bound">A</a> <a id="8490" class="Symbol">=</a> <a id="8492" class="Symbol">(</a><a id="8493" href="Prelude.Extensionality.html#8493" class="Bound">x</a> <a id="8495" href="Prelude.Extensionality.html#8495" class="Bound">y</a> <a id="8497" class="Symbol">:</a> <a id="8499" href="Prelude.Extensionality.html#8488" class="Bound">A</a><a id="8500" class="Symbol">)</a> <a id="8502" class="Symbol">→</a> <a id="8504" href="Prelude.Extensionality.html#8493" class="Bound">x</a> <a id="8506" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="8508" href="Prelude.Extensionality.html#8495" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8801" class="Keyword">open</a> <a id="8806" class="Keyword">import</a> <a id="8813" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8826" class="Keyword">using</a> <a id="8832" class="Symbol">(</a><a id="8833" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8842" class="Symbol">;</a> <a id="8844" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8856" class="Symbol">;</a> <a id="8858" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8873" class="Symbol">)</a> <a id="8875" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9292" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9299" href="Prelude.Extensionality.html#9299" class="Module">hide-tt-defs&#39;</a> <a id="9313" class="Symbol">{</a><a id="9314" href="Prelude.Extensionality.html#9314" class="Bound">𝓤</a> <a id="9316" href="Prelude.Extensionality.html#9316" class="Bound">𝓦</a> <a id="9318" class="Symbol">:</a> <a id="9320" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9328" class="Symbol">}</a> <a id="9330" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9338" href="Prelude.Extensionality.html#9338" class="Function">fiber</a> <a id="9344" class="Symbol">:</a> <a id="9346" class="Symbol">{</a><a id="9347" href="Prelude.Extensionality.html#9347" class="Bound">A</a> <a id="9349" class="Symbol">:</a> <a id="9351" href="Prelude.Extensionality.html#9314" class="Bound">𝓤</a> <a id="9353" href="Universes.html#403" class="Function Operator">̇</a> <a id="9355" class="Symbol">}</a> <a id="9357" class="Symbol">{</a><a id="9358" href="Prelude.Extensionality.html#9358" class="Bound">B</a> <a id="9360" class="Symbol">:</a> <a id="9362" href="Prelude.Extensionality.html#9316" class="Bound">𝓦</a> <a id="9364" href="Universes.html#403" class="Function Operator">̇</a> <a id="9366" class="Symbol">}</a> <a id="9368" class="Symbol">(</a><a id="9369" href="Prelude.Extensionality.html#9369" class="Bound">f</a> <a id="9371" class="Symbol">:</a> <a id="9373" href="Prelude.Extensionality.html#9347" class="Bound">A</a> <a id="9375" class="Symbol">→</a> <a id="9377" href="Prelude.Extensionality.html#9358" class="Bound">B</a><a id="9378" class="Symbol">)</a> <a id="9380" class="Symbol">→</a> <a id="9382" href="Prelude.Extensionality.html#9358" class="Bound">B</a> <a id="9384" class="Symbol">→</a> <a id="9386" href="Prelude.Extensionality.html#9314" class="Bound">𝓤</a> <a id="9388" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9390" href="Prelude.Extensionality.html#9316" class="Bound">𝓦</a> <a id="9392" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9395" href="Prelude.Extensionality.html#9338" class="Function">fiber</a> <a id="9401" class="Symbol">{</a><a id="9402" href="Prelude.Extensionality.html#9402" class="Bound">A</a><a id="9403" class="Symbol">}</a> <a id="9405" href="Prelude.Extensionality.html#9405" class="Bound">f</a> <a id="9407" href="Prelude.Extensionality.html#9407" class="Bound">y</a> <a id="9409" class="Symbol">=</a> <a id="9411" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9413" href="Prelude.Extensionality.html#9413" class="Bound">x</a> <a id="9415" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9417" href="Prelude.Extensionality.html#9402" class="Bound">A</a> <a id="9419" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9421" href="Prelude.Extensionality.html#9405" class="Bound">f</a> <a id="9423" href="Prelude.Extensionality.html#9413" class="Bound">x</a> <a id="9425" href="Prelude.Equality.html#2570" class="Datatype Operator">≡</a> <a id="9427" href="Prelude.Extensionality.html#9407" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9533" href="Prelude.Extensionality.html#9533" class="Function">is-equiv</a> <a id="9542" class="Symbol">:</a> <a id="9544" class="Symbol">{</a><a id="9545" href="Prelude.Extensionality.html#9545" class="Bound">A</a> <a id="9547" class="Symbol">:</a> <a id="9549" href="Prelude.Extensionality.html#9314" class="Bound">𝓤</a> <a id="9551" href="Universes.html#403" class="Function Operator">̇</a> <a id="9553" class="Symbol">}</a> <a id="9555" class="Symbol">{</a><a id="9556" href="Prelude.Extensionality.html#9556" class="Bound">B</a> <a id="9558" class="Symbol">:</a> <a id="9560" href="Prelude.Extensionality.html#9316" class="Bound">𝓦</a> <a id="9562" href="Universes.html#403" class="Function Operator">̇</a> <a id="9564" class="Symbol">}</a> <a id="9566" class="Symbol">→</a> <a id="9568" class="Symbol">(</a><a id="9569" href="Prelude.Extensionality.html#9545" class="Bound">A</a> <a id="9571" class="Symbol">→</a> <a id="9573" href="Prelude.Extensionality.html#9556" class="Bound">B</a><a id="9574" class="Symbol">)</a> <a id="9576" class="Symbol">→</a> <a id="9578" href="Prelude.Extensionality.html#9314" class="Bound">𝓤</a> <a id="9580" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9582" href="Prelude.Extensionality.html#9316" class="Bound">𝓦</a> <a id="9584" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9587" href="Prelude.Extensionality.html#9533" class="Function">is-equiv</a> <a id="9596" href="Prelude.Extensionality.html#9596" class="Bound">f</a> <a id="9598" class="Symbol">=</a> <a id="9600" class="Symbol">∀</a> <a id="9602" href="Prelude.Extensionality.html#9602" class="Bound">y</a> <a id="9604" class="Symbol">→</a> <a id="9606" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9619" class="Symbol">(</a><a id="9620" href="Prelude.Extensionality.html#9338" class="Function">fiber</a> <a id="9626" href="Prelude.Extensionality.html#9596" class="Bound">f</a> <a id="9628" href="Prelude.Extensionality.html#9602" class="Bound">y</a><a id="9629" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="9835" class="Keyword">open</a> <a id="9840" class="Keyword">import</a> <a id="9847" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9864" class="Keyword">using</a> <a id="9870" class="Symbol">(</a><a id="9871" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9876" class="Symbol">;</a> <a id="9878" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9886" class="Symbol">)</a> <a id="9888" class="Keyword">public</a>

<a id="9896" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9903" href="Prelude.Extensionality.html#9903" class="Module">hide-hfunext</a> <a id="9916" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9924" href="Prelude.Extensionality.html#9924" class="Function">hfunext</a> <a id="9932" class="Symbol">:</a>  <a id="9935" class="Symbol">∀</a> <a id="9937" href="Prelude.Extensionality.html#9937" class="Bound">𝓤</a> <a id="9939" href="Prelude.Extensionality.html#9939" class="Bound">𝓦</a> <a id="9941" class="Symbol">→</a> <a id="9943" class="Symbol">(</a><a id="9944" href="Prelude.Extensionality.html#9937" class="Bound">𝓤</a> <a id="9946" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9948" href="Prelude.Extensionality.html#9939" class="Bound">𝓦</a><a id="9949" class="Symbol">)</a><a id="9950" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="9952" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9955" href="Prelude.Extensionality.html#9924" class="Function">hfunext</a> <a id="9963" href="Prelude.Extensionality.html#9963" class="Bound">𝓤</a> <a id="9965" href="Prelude.Extensionality.html#9965" class="Bound">𝓦</a> <a id="9967" class="Symbol">=</a> <a id="9969" class="Symbol">{</a><a id="9970" href="Prelude.Extensionality.html#9970" class="Bound">A</a> <a id="9972" class="Symbol">:</a> <a id="9974" href="Prelude.Extensionality.html#9963" class="Bound">𝓤</a> <a id="9976" href="Universes.html#403" class="Function Operator">̇</a><a id="9977" class="Symbol">}{</a><a id="9979" href="Prelude.Extensionality.html#9979" class="Bound">B</a> <a id="9981" class="Symbol">:</a> <a id="9983" href="Prelude.Extensionality.html#9970" class="Bound">A</a> <a id="9985" class="Symbol">→</a> <a id="9987" href="Prelude.Extensionality.html#9965" class="Bound">𝓦</a> <a id="9989" href="Universes.html#403" class="Function Operator">̇</a><a id="9990" class="Symbol">}</a> <a id="9992" class="Symbol">(</a><a id="9993" href="Prelude.Extensionality.html#9993" class="Bound">f</a> <a id="9995" href="Prelude.Extensionality.html#9995" class="Bound">g</a> <a id="9997" class="Symbol">:</a> <a id="9999" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10001" href="Prelude.Extensionality.html#9979" class="Bound">B</a><a id="10002" class="Symbol">)</a> <a id="10004" class="Symbol">→</a> <a id="10006" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10015" class="Symbol">(</a><a id="10016" href="Prelude.Extensionality.html#6318" class="Function">extdfun</a> <a id="10024" href="Prelude.Extensionality.html#9993" class="Bound">f</a> <a id="10026" href="Prelude.Extensionality.html#9995" class="Bound">g</a><a id="10027" class="Symbol">)</a>
<a id="10029" class="Keyword">open</a> <a id="10034" class="Keyword">import</a> <a id="10041" href="MGS-Subsingleton-Truncation.html" class="Module">MGS-Subsingleton-Truncation</a> <a id="10069" class="Keyword">using</a> <a id="10075" class="Symbol">(</a><a id="10076" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10083" class="Symbol">)</a> <a id="10085" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>3</sup> <span class="footnote" id="fn3"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>4</sup><span class="footnote" id="fn4">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

<br>
<br>

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
