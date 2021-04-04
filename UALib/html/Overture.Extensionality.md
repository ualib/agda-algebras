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

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

<pre class="Agda">

<a id="2885" class="Keyword">module</a> <a id="hide-∼"></a><a id="2892" href="Overture.Extensionality.html#2892" class="Module">hide-∼</a> <a id="2899" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2907" href="Overture.Extensionality.html#2907" class="Function Operator">_∼_</a> <a id="2911" class="Symbol">:</a> <a id="2913" class="Symbol">{</a><a id="2914" href="Overture.Extensionality.html#2914" class="Bound">A</a> <a id="2916" class="Symbol">:</a> <a id="2918" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2920" href="Universes.html#403" class="Function Operator">̇</a> <a id="2922" class="Symbol">}</a> <a id="2924" class="Symbol">{</a><a id="2925" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Overture.Extensionality.html#2914" class="Bound">A</a> <a id="2931" class="Symbol">→</a> <a id="2933" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2935" href="Universes.html#403" class="Function Operator">̇</a> <a id="2937" class="Symbol">}</a> <a id="2939" class="Symbol">→</a> <a id="2941" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2943" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2945" class="Symbol">→</a> <a id="2947" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2949" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2951" class="Symbol">→</a> <a id="2953" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2955" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2957" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2959" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2962" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2964" href="Overture.Extensionality.html#2907" class="Function Operator">∼</a> <a id="2966" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2968" class="Symbol">=</a> <a id="2970" class="Symbol">∀</a> <a id="2972" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2974" class="Symbol">→</a> <a id="2976" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2978" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2980" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="2982" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2984" href="Overture.Extensionality.html#2972" class="Bound">x</a>

 <a id="2988" class="Keyword">infix</a> <a id="2994" class="Number">0</a> <a id="2996" href="Overture.Extensionality.html#2907" class="Function Operator">_∼_</a>

<a id="3001" class="Keyword">open</a> <a id="3006" class="Keyword">import</a> <a id="3013" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3022" class="Keyword">using</a> <a id="3028" class="Symbol">(</a><a id="3029" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3032" class="Symbol">)</a> <a id="3034" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, and import the original definition below.)

<pre class="Agda">

<a id="3501" class="Keyword">module</a> <a id="hide-funext"></a><a id="3508" href="Overture.Extensionality.html#3508" class="Module">hide-funext</a> <a id="3520" class="Keyword">where</a>

 <a id="hide-funext.funext"></a><a id="3528" href="Overture.Extensionality.html#3528" class="Function">funext</a> <a id="3535" class="Symbol">:</a> <a id="3537" class="Symbol">∀</a> <a id="3539" href="Overture.Extensionality.html#3539" class="Bound">𝓤</a> <a id="3541" href="Overture.Extensionality.html#3541" class="Bound">𝓦</a>  <a id="3544" class="Symbol">→</a> <a id="3546" href="Overture.Extensionality.html#3539" class="Bound">𝓤</a> <a id="3548" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3550" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3552" href="Overture.Extensionality.html#3541" class="Bound">𝓦</a> <a id="3554" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3556" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3559" href="Overture.Extensionality.html#3528" class="Function">funext</a> <a id="3566" href="Overture.Extensionality.html#3566" class="Bound">𝓤</a> <a id="3568" href="Overture.Extensionality.html#3568" class="Bound">𝓦</a> <a id="3570" class="Symbol">=</a> <a id="3572" class="Symbol">{</a><a id="3573" href="Overture.Extensionality.html#3573" class="Bound">A</a> <a id="3575" class="Symbol">:</a> <a id="3577" href="Overture.Extensionality.html#3566" class="Bound">𝓤</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a> <a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">{</a><a id="3584" href="Overture.Extensionality.html#3584" class="Bound">B</a> <a id="3586" class="Symbol">:</a> <a id="3588" href="Overture.Extensionality.html#3568" class="Bound">𝓦</a> <a id="3590" href="Universes.html#403" class="Function Operator">̇</a> <a id="3592" class="Symbol">}</a> <a id="3594" class="Symbol">{</a><a id="3595" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3597" href="Overture.Extensionality.html#3597" class="Bound">g</a> <a id="3599" class="Symbol">:</a> <a id="3601" href="Overture.Extensionality.html#3573" class="Bound">A</a> <a id="3603" class="Symbol">→</a> <a id="3605" href="Overture.Extensionality.html#3584" class="Bound">B</a><a id="3606" class="Symbol">}</a> <a id="3608" class="Symbol">→</a> <a id="3610" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3612" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3614" href="Overture.Extensionality.html#3597" class="Bound">g</a> <a id="3616" class="Symbol">→</a> <a id="3618" href="Overture.Extensionality.html#3595" class="Bound">f</a> <a id="3620" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3622" href="Overture.Extensionality.html#3597" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="3733" href="Overture.Extensionality.html#3733" class="Function">dfunext</a> <a id="3741" class="Symbol">:</a> <a id="3743" class="Symbol">∀</a> <a id="3745" href="Overture.Extensionality.html#3745" class="Bound">𝓤</a> <a id="3747" href="Overture.Extensionality.html#3747" class="Bound">𝓦</a> <a id="3749" class="Symbol">→</a> <a id="3751" href="Overture.Extensionality.html#3745" class="Bound">𝓤</a> <a id="3753" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3755" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3757" href="Overture.Extensionality.html#3747" class="Bound">𝓦</a> <a id="3759" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3761" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3764" href="Overture.Extensionality.html#3733" class="Function">dfunext</a> <a id="3772" href="Overture.Extensionality.html#3772" class="Bound">𝓤</a> <a id="3774" href="Overture.Extensionality.html#3774" class="Bound">𝓦</a> <a id="3776" class="Symbol">=</a> <a id="3778" class="Symbol">{</a><a id="3779" href="Overture.Extensionality.html#3779" class="Bound">A</a> <a id="3781" class="Symbol">:</a> <a id="3783" href="Overture.Extensionality.html#3772" class="Bound">𝓤</a> <a id="3785" href="Universes.html#403" class="Function Operator">̇</a> <a id="3787" class="Symbol">}{</a><a id="3789" href="Overture.Extensionality.html#3789" class="Bound">B</a> <a id="3791" class="Symbol">:</a> <a id="3793" href="Overture.Extensionality.html#3779" class="Bound">A</a> <a id="3795" class="Symbol">→</a> <a id="3797" href="Overture.Extensionality.html#3774" class="Bound">𝓦</a> <a id="3799" href="Universes.html#403" class="Function Operator">̇</a> <a id="3801" class="Symbol">}{</a><a id="3803" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3805" href="Overture.Extensionality.html#3805" class="Bound">g</a> <a id="3807" class="Symbol">:</a> <a id="3809" class="Symbol">∀(</a><a id="3811" href="Overture.Extensionality.html#3811" class="Bound">x</a> <a id="3813" class="Symbol">:</a> <a id="3815" href="Overture.Extensionality.html#3779" class="Bound">A</a><a id="3816" class="Symbol">)</a> <a id="3818" class="Symbol">→</a> <a id="3820" href="Overture.Extensionality.html#3789" class="Bound">B</a> <a id="3822" href="Overture.Extensionality.html#3811" class="Bound">x</a><a id="3823" class="Symbol">}</a> <a id="3825" class="Symbol">→</a>  <a id="3828" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3830" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3832" href="Overture.Extensionality.html#3805" class="Bound">g</a>  <a id="3835" class="Symbol">→</a>  <a id="3838" href="Overture.Extensionality.html#3803" class="Bound">f</a> <a id="3840" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3842" href="Overture.Extensionality.html#3805" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] used a *global function extensionality principle* extensively. (This asserts that function extensionality holds at all universe levels.) Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe). (For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).



The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="5218" href="Overture.Extensionality.html#5218" class="Function">global-funext</a> <a id="5232" class="Symbol">:</a> <a id="5234" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5238" href="Overture.Extensionality.html#5218" class="Function">global-funext</a> <a id="5252" class="Symbol">=</a> <a id="5254" class="Symbol">∀</a>  <a id="5257" class="Symbol">{</a><a id="5258" href="Overture.Extensionality.html#5258" class="Bound">𝓤</a> <a id="5260" href="Overture.Extensionality.html#5260" class="Bound">𝓥</a><a id="5261" class="Symbol">}</a> <a id="5263" class="Symbol">→</a> <a id="5265" href="Overture.Extensionality.html#3528" class="Function">funext</a> <a id="5272" href="Overture.Extensionality.html#5258" class="Bound">𝓤</a> <a id="5274" href="Overture.Extensionality.html#5260" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="5278" href="Overture.Extensionality.html#5278" class="Function">global-dfunext</a> <a id="5293" class="Symbol">:</a> <a id="5295" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="5299" href="Overture.Extensionality.html#5278" class="Function">global-dfunext</a> <a id="5314" class="Symbol">=</a> <a id="5316" class="Symbol">∀</a> <a id="5318" class="Symbol">{</a><a id="5319" href="Overture.Extensionality.html#5319" class="Bound">𝓤</a> <a id="5321" href="Overture.Extensionality.html#5321" class="Bound">𝓥</a><a id="5322" class="Symbol">}</a> <a id="5324" class="Symbol">→</a> <a id="5326" href="Overture.Extensionality.html#3733" class="Function">dfunext</a> <a id="5334" href="Overture.Extensionality.html#5319" class="Bound">𝓤</a> <a id="5336" href="Overture.Extensionality.html#5321" class="Bound">𝓥</a>

</pre>

We have decided to remove all invokations of global function extensionality in the [UALib][] and instead apply the principle locally when and where needed. The advantage of this is that we can now see precisely how our formalization effort depends on this principle.  (It also prepares the way for moving to a univalence-based approach that we will soon undertake.)  The price we pay for this precision is a code base that is unfortunately littered with many function extensionality postulates.  Hopefully it will be possible to clean this up in the near future.

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[3](Overture.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="6196" class="Keyword">open</a> <a id="6201" class="Keyword">import</a> <a id="6208" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="6235" class="Keyword">using</a> <a id="6241" class="Symbol">(</a><a id="6242" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="6248" class="Symbol">;</a> <a id="6250" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="6257" class="Symbol">)</a> <a id="6259" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next two types define the converse of function extensionality.

<pre class="Agda">

<a id="extfun"></a><a id="6536" href="Overture.Extensionality.html#6536" class="Function">extfun</a> <a id="6543" class="Symbol">:</a> <a id="6545" class="Symbol">{</a><a id="6546" href="Overture.Extensionality.html#6546" class="Bound">A</a> <a id="6548" class="Symbol">:</a> <a id="6550" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6552" href="Universes.html#403" class="Function Operator">̇</a><a id="6553" class="Symbol">}{</a><a id="6555" href="Overture.Extensionality.html#6555" class="Bound">B</a> <a id="6557" class="Symbol">:</a> <a id="6559" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6561" href="Universes.html#403" class="Function Operator">̇</a><a id="6562" class="Symbol">}{</a><a id="6564" href="Overture.Extensionality.html#6564" class="Bound">f</a> <a id="6566" href="Overture.Extensionality.html#6566" class="Bound">g</a> <a id="6568" class="Symbol">:</a> <a id="6570" href="Overture.Extensionality.html#6546" class="Bound">A</a> <a id="6572" class="Symbol">→</a> <a id="6574" href="Overture.Extensionality.html#6555" class="Bound">B</a><a id="6575" class="Symbol">}</a> <a id="6577" class="Symbol">→</a> <a id="6579" href="Overture.Extensionality.html#6564" class="Bound">f</a> <a id="6581" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6583" href="Overture.Extensionality.html#6566" class="Bound">g</a>  <a id="6586" class="Symbol">→</a>  <a id="6589" href="Overture.Extensionality.html#6564" class="Bound">f</a> <a id="6591" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6593" href="Overture.Extensionality.html#6566" class="Bound">g</a>
<a id="6595" href="Overture.Extensionality.html#6536" class="Function">extfun</a> <a id="6602" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6607" class="Symbol">_</a> <a id="6609" class="Symbol">=</a> <a id="6611" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

<pre class="Agda">

<a id="extdfun"></a><a id="6737" href="Overture.Extensionality.html#6737" class="Function">extdfun</a> <a id="6745" class="Symbol">:</a> <a id="6747" class="Symbol">{</a><a id="6748" href="Overture.Extensionality.html#6748" class="Bound">A</a> <a id="6750" class="Symbol">:</a> <a id="6752" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6754" href="Universes.html#403" class="Function Operator">̇</a> <a id="6756" class="Symbol">}{</a><a id="6758" href="Overture.Extensionality.html#6758" class="Bound">B</a> <a id="6760" class="Symbol">:</a> <a id="6762" href="Overture.Extensionality.html#6748" class="Bound">A</a> <a id="6764" class="Symbol">→</a> <a id="6766" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6768" href="Universes.html#403" class="Function Operator">̇</a> <a id="6770" class="Symbol">}(</a><a id="6772" href="Overture.Extensionality.html#6772" class="Bound">f</a> <a id="6774" href="Overture.Extensionality.html#6774" class="Bound">g</a> <a id="6776" class="Symbol">:</a> <a id="6778" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6780" href="Overture.Extensionality.html#6758" class="Bound">B</a><a id="6781" class="Symbol">)</a> <a id="6783" class="Symbol">→</a> <a id="6785" href="Overture.Extensionality.html#6772" class="Bound">f</a> <a id="6787" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="6789" href="Overture.Extensionality.html#6774" class="Bound">g</a> <a id="6791" class="Symbol">→</a> <a id="6793" href="Overture.Extensionality.html#6772" class="Bound">f</a> <a id="6795" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6797" href="Overture.Extensionality.html#6774" class="Bound">g</a>
<a id="6799" href="Overture.Extensionality.html#6737" class="Function">extdfun</a> <a id="6807" class="Symbol">_</a> <a id="6809" class="Symbol">_</a> <a id="6811" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a> <a id="6816" class="Symbol">_</a> <a id="6818" class="Symbol">=</a> <a id="6820" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.

In the definition of `funext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `funext` is an assertion (which may or may not hold). In the definition of `extfun`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `extfun` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="8712" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8719" href="Overture.Extensionality.html#8719" class="Module">hide-tt-defs</a> <a id="8732" class="Symbol">{</a><a id="8733" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8735" class="Symbol">:</a> <a id="8737" href="Universes.html#205" class="Postulate">Universe</a><a id="8745" class="Symbol">}</a> <a id="8747" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8755" href="Overture.Extensionality.html#8755" class="Function">is-center</a> <a id="8765" class="Symbol">:</a> <a id="8767" class="Symbol">(</a><a id="8768" href="Overture.Extensionality.html#8768" class="Bound">A</a> <a id="8770" class="Symbol">:</a> <a id="8772" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8774" href="Universes.html#403" class="Function Operator">̇</a> <a id="8776" class="Symbol">)</a> <a id="8778" class="Symbol">→</a> <a id="8780" href="Overture.Extensionality.html#8768" class="Bound">A</a> <a id="8782" class="Symbol">→</a> <a id="8784" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8786" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8789" href="Overture.Extensionality.html#8755" class="Function">is-center</a> <a id="8799" href="Overture.Extensionality.html#8799" class="Bound">A</a> <a id="8801" href="Overture.Extensionality.html#8801" class="Bound">c</a> <a id="8803" class="Symbol">=</a> <a id="8805" class="Symbol">(</a><a id="8806" href="Overture.Extensionality.html#8806" class="Bound">x</a> <a id="8808" class="Symbol">:</a> <a id="8810" href="Overture.Extensionality.html#8799" class="Bound">A</a><a id="8811" class="Symbol">)</a> <a id="8813" class="Symbol">→</a> <a id="8815" href="Overture.Extensionality.html#8801" class="Bound">c</a> <a id="8817" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8819" href="Overture.Extensionality.html#8806" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8823" href="Overture.Extensionality.html#8823" class="Function">is-singleton</a> <a id="8836" class="Symbol">:</a> <a id="8838" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8840" href="Universes.html#403" class="Function Operator">̇</a> <a id="8842" class="Symbol">→</a> <a id="8844" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8846" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8849" href="Overture.Extensionality.html#8823" class="Function">is-singleton</a> <a id="8862" href="Overture.Extensionality.html#8862" class="Bound">A</a> <a id="8864" class="Symbol">=</a> <a id="8866" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8868" href="Overture.Extensionality.html#8868" class="Bound">c</a> <a id="8870" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8872" href="Overture.Extensionality.html#8862" class="Bound">A</a> <a id="8874" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8876" href="Overture.Extensionality.html#8755" class="Function">is-center</a> <a id="8886" href="Overture.Extensionality.html#8862" class="Bound">A</a> <a id="8888" href="Overture.Extensionality.html#8868" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8892" href="Overture.Extensionality.html#8892" class="Function">is-subsingleton</a> <a id="8908" class="Symbol">:</a> <a id="8910" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8912" href="Universes.html#403" class="Function Operator">̇</a> <a id="8914" class="Symbol">→</a> <a id="8916" href="Overture.Extensionality.html#8733" class="Bound">𝓤</a> <a id="8918" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8921" href="Overture.Extensionality.html#8892" class="Function">is-subsingleton</a> <a id="8937" href="Overture.Extensionality.html#8937" class="Bound">A</a> <a id="8939" class="Symbol">=</a> <a id="8941" class="Symbol">(</a><a id="8942" href="Overture.Extensionality.html#8942" class="Bound">x</a> <a id="8944" href="Overture.Extensionality.html#8944" class="Bound">y</a> <a id="8946" class="Symbol">:</a> <a id="8948" href="Overture.Extensionality.html#8937" class="Bound">A</a><a id="8949" class="Symbol">)</a> <a id="8951" class="Symbol">→</a> <a id="8953" href="Overture.Extensionality.html#8942" class="Bound">x</a> <a id="8955" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="8957" href="Overture.Extensionality.html#8944" class="Bound">y</a>

</pre>

We import the original definitions of the last three types as follows. (The [first footnote](Overture.Equality.html#fn1) of [Overture.Equality][] explains why we both define and import certain types.)

<pre class="Agda">

<a id="9188" class="Keyword">open</a> <a id="9193" class="Keyword">import</a> <a id="9200" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="9213" class="Keyword">using</a> <a id="9219" class="Symbol">(</a><a id="9220" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="9229" class="Symbol">;</a> <a id="9231" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="9243" class="Symbol">;</a> <a id="9245" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="9260" class="Symbol">)</a> <a id="9262" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9679" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9686" href="Overture.Extensionality.html#9686" class="Module">hide-tt-defs&#39;</a> <a id="9700" class="Symbol">{</a><a id="9701" href="Overture.Extensionality.html#9701" class="Bound">𝓤</a> <a id="9703" href="Overture.Extensionality.html#9703" class="Bound">𝓦</a> <a id="9705" class="Symbol">:</a> <a id="9707" href="Universes.html#205" class="Postulate">Universe</a><a id="9715" class="Symbol">}</a> <a id="9717" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9725" href="Overture.Extensionality.html#9725" class="Function">fiber</a> <a id="9731" class="Symbol">:</a> <a id="9733" class="Symbol">{</a><a id="9734" href="Overture.Extensionality.html#9734" class="Bound">A</a> <a id="9736" class="Symbol">:</a> <a id="9738" href="Overture.Extensionality.html#9701" class="Bound">𝓤</a> <a id="9740" href="Universes.html#403" class="Function Operator">̇</a> <a id="9742" class="Symbol">}</a> <a id="9744" class="Symbol">{</a><a id="9745" href="Overture.Extensionality.html#9745" class="Bound">B</a> <a id="9747" class="Symbol">:</a> <a id="9749" href="Overture.Extensionality.html#9703" class="Bound">𝓦</a> <a id="9751" href="Universes.html#403" class="Function Operator">̇</a> <a id="9753" class="Symbol">}</a> <a id="9755" class="Symbol">(</a><a id="9756" href="Overture.Extensionality.html#9756" class="Bound">f</a> <a id="9758" class="Symbol">:</a> <a id="9760" href="Overture.Extensionality.html#9734" class="Bound">A</a> <a id="9762" class="Symbol">→</a> <a id="9764" href="Overture.Extensionality.html#9745" class="Bound">B</a><a id="9765" class="Symbol">)</a> <a id="9767" class="Symbol">→</a> <a id="9769" href="Overture.Extensionality.html#9745" class="Bound">B</a> <a id="9771" class="Symbol">→</a> <a id="9773" href="Overture.Extensionality.html#9701" class="Bound">𝓤</a> <a id="9775" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9777" href="Overture.Extensionality.html#9703" class="Bound">𝓦</a> <a id="9779" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9782" href="Overture.Extensionality.html#9725" class="Function">fiber</a> <a id="9788" class="Symbol">{</a><a id="9789" href="Overture.Extensionality.html#9789" class="Bound">A</a><a id="9790" class="Symbol">}</a> <a id="9792" href="Overture.Extensionality.html#9792" class="Bound">f</a> <a id="9794" href="Overture.Extensionality.html#9794" class="Bound">y</a> <a id="9796" class="Symbol">=</a> <a id="9798" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9800" href="Overture.Extensionality.html#9800" class="Bound">x</a> <a id="9802" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9804" href="Overture.Extensionality.html#9789" class="Bound">A</a> <a id="9806" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9808" href="Overture.Extensionality.html#9792" class="Bound">f</a> <a id="9810" href="Overture.Extensionality.html#9800" class="Bound">x</a> <a id="9812" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="9814" href="Overture.Extensionality.html#9794" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9920" href="Overture.Extensionality.html#9920" class="Function">is-equiv</a> <a id="9929" class="Symbol">:</a> <a id="9931" class="Symbol">{</a><a id="9932" href="Overture.Extensionality.html#9932" class="Bound">A</a> <a id="9934" class="Symbol">:</a> <a id="9936" href="Overture.Extensionality.html#9701" class="Bound">𝓤</a> <a id="9938" href="Universes.html#403" class="Function Operator">̇</a> <a id="9940" class="Symbol">}</a> <a id="9942" class="Symbol">{</a><a id="9943" href="Overture.Extensionality.html#9943" class="Bound">B</a> <a id="9945" class="Symbol">:</a> <a id="9947" href="Overture.Extensionality.html#9703" class="Bound">𝓦</a> <a id="9949" href="Universes.html#403" class="Function Operator">̇</a> <a id="9951" class="Symbol">}</a> <a id="9953" class="Symbol">→</a> <a id="9955" class="Symbol">(</a><a id="9956" href="Overture.Extensionality.html#9932" class="Bound">A</a> <a id="9958" class="Symbol">→</a> <a id="9960" href="Overture.Extensionality.html#9943" class="Bound">B</a><a id="9961" class="Symbol">)</a> <a id="9963" class="Symbol">→</a> <a id="9965" href="Overture.Extensionality.html#9701" class="Bound">𝓤</a> <a id="9967" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9969" href="Overture.Extensionality.html#9703" class="Bound">𝓦</a> <a id="9971" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9974" href="Overture.Extensionality.html#9920" class="Function">is-equiv</a> <a id="9983" href="Overture.Extensionality.html#9983" class="Bound">f</a> <a id="9985" class="Symbol">=</a> <a id="9987" class="Symbol">∀</a> <a id="9989" href="Overture.Extensionality.html#9989" class="Bound">y</a> <a id="9991" class="Symbol">→</a> <a id="9993" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="10006" class="Symbol">(</a><a id="10007" href="Overture.Extensionality.html#9725" class="Function">fiber</a> <a id="10013" href="Overture.Extensionality.html#9983" class="Bound">f</a> <a id="10015" href="Overture.Extensionality.html#9989" class="Bound">y</a><a id="10016" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="10223" class="Keyword">open</a> <a id="10228" class="Keyword">import</a> <a id="10235" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="10252" class="Keyword">using</a> <a id="10258" class="Symbol">(</a><a id="10259" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="10264" class="Symbol">;</a> <a id="10266" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="10274" class="Symbol">)</a> <a id="10276" class="Keyword">public</a>

<a id="10284" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10291" href="Overture.Extensionality.html#10291" class="Module">hide-hfunext</a> <a id="10304" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10312" href="Overture.Extensionality.html#10312" class="Function">hfunext</a> <a id="10320" class="Symbol">:</a>  <a id="10323" class="Symbol">∀</a> <a id="10325" href="Overture.Extensionality.html#10325" class="Bound">𝓤</a> <a id="10327" href="Overture.Extensionality.html#10327" class="Bound">𝓦</a> <a id="10329" class="Symbol">→</a> <a id="10331" class="Symbol">(</a><a id="10332" href="Overture.Extensionality.html#10325" class="Bound">𝓤</a> <a id="10334" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10336" href="Overture.Extensionality.html#10327" class="Bound">𝓦</a><a id="10337" class="Symbol">)</a><a id="10338" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="10340" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10343" href="Overture.Extensionality.html#10312" class="Function">hfunext</a> <a id="10351" href="Overture.Extensionality.html#10351" class="Bound">𝓤</a> <a id="10353" href="Overture.Extensionality.html#10353" class="Bound">𝓦</a> <a id="10355" class="Symbol">=</a> <a id="10357" class="Symbol">{</a><a id="10358" href="Overture.Extensionality.html#10358" class="Bound">A</a> <a id="10360" class="Symbol">:</a> <a id="10362" href="Overture.Extensionality.html#10351" class="Bound">𝓤</a> <a id="10364" href="Universes.html#403" class="Function Operator">̇</a><a id="10365" class="Symbol">}{</a><a id="10367" href="Overture.Extensionality.html#10367" class="Bound">B</a> <a id="10369" class="Symbol">:</a> <a id="10371" href="Overture.Extensionality.html#10358" class="Bound">A</a> <a id="10373" class="Symbol">→</a> <a id="10375" href="Overture.Extensionality.html#10353" class="Bound">𝓦</a> <a id="10377" href="Universes.html#403" class="Function Operator">̇</a><a id="10378" class="Symbol">}</a> <a id="10380" class="Symbol">(</a><a id="10381" href="Overture.Extensionality.html#10381" class="Bound">f</a> <a id="10383" href="Overture.Extensionality.html#10383" class="Bound">g</a> <a id="10385" class="Symbol">:</a> <a id="10387" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10389" href="Overture.Extensionality.html#10367" class="Bound">B</a><a id="10390" class="Symbol">)</a> <a id="10392" class="Symbol">→</a> <a id="10394" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10403" class="Symbol">(</a><a id="10404" href="Overture.Extensionality.html#6737" class="Function">extdfun</a> <a id="10412" href="Overture.Extensionality.html#10381" class="Bound">f</a> <a id="10414" href="Overture.Extensionality.html#10383" class="Bound">g</a><a id="10415" class="Symbol">)</a>

<a id="10418" class="Keyword">open</a> <a id="10423" class="Keyword">import</a> <a id="10430" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10457" class="Keyword">using</a> <a id="10463" class="Symbol">(</a><a id="10464" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10471" class="Symbol">)</a> <a id="10473" class="Keyword">public</a>

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
