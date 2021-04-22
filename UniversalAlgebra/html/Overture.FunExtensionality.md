---
layout: default
title : Overture.FunExtensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [Overture.FunExtensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="306" class="Symbol">{-#</a> <a id="310" class="Keyword">OPTIONS</a> <a id="318" class="Pragma">--without-K</a> <a id="330" class="Pragma">--exact-split</a> <a id="344" class="Pragma">--safe</a> <a id="351" class="Symbol">#-}</a>

<a id="356" class="Keyword">module</a> <a id="363" href="Overture.FunExtensionality.html" class="Module">Overture.FunExtensionality</a> <a id="390" class="Keyword">where</a>

<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="Overture.Equality.html" class="Module">Overture.Equality</a> <a id="427" class="Keyword">public</a>

</pre>

This introduction is intended for novices.  Those already familiar with function extensionality may wish to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose `f` and `g` are defined on `A = ℤ` (the integers) as follows: `f x := x + 2` and `g x := ((2 * x) - 8)/2 + 6`.  Should we call `f` and `g` equal? Are they the "same" function?  What does that even mean?

It's hard to resist the urge to reduce `g` to `x + 2` and proclaim that `f` and `g` are equal. Indeed, this is often an acceptable answer and the discussion normally ends there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions `f` and `g` above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions, `f` and `g`, both of which take a list as argument and produce as output a correctly sorted version of the input list?  Suppose `f` is defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while `g` uses [quick sort](https://en.wikipedia.org/wiki/Quicksort).  Probably few of us would call `f` and `g` the "same" in this case.

In the examples above, it is common to say that the two functions are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same *external* output when given the same input, but they are not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their *internal* definitions differ.

In this module, we describe types that manifest this notion of *extensional equality of functions*, or *function extensionality*.<sup>[1](Overture.Extensionality.html#fn1)</sup>

#### <a id="function-extensionality-types">Function extensionality types</a>

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

<pre class="Agda">

<a id="2808" class="Keyword">module</a> <a id="hide-∼"></a><a id="2815" href="Overture.FunExtensionality.html#2815" class="Module">hide-∼</a> <a id="2822" class="Symbol">{</a><a id="2823" href="Overture.FunExtensionality.html#2823" class="Bound">A</a> <a id="2825" class="Symbol">:</a> <a id="2827" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2829" href="Universes.html#403" class="Function Operator">̇</a> <a id="2831" class="Symbol">}</a> <a id="2833" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2841" href="Overture.FunExtensionality.html#2841" class="Function Operator">_∼_</a> <a id="2845" class="Symbol">:</a> <a id="2847" class="Symbol">{</a><a id="2848" href="Overture.FunExtensionality.html#2848" class="Bound">B</a> <a id="2850" class="Symbol">:</a> <a id="2852" href="Overture.FunExtensionality.html#2823" class="Bound">A</a> <a id="2854" class="Symbol">→</a> <a id="2856" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2858" href="Universes.html#403" class="Function Operator">̇</a> <a id="2860" class="Symbol">}</a> <a id="2862" class="Symbol">→</a> <a id="2864" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2866" href="Overture.FunExtensionality.html#2848" class="Bound">B</a> <a id="2868" class="Symbol">→</a> <a id="2870" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2872" href="Overture.FunExtensionality.html#2848" class="Bound">B</a> <a id="2874" class="Symbol">→</a> <a id="2876" href="Overture.FunExtensionality.html#2827" class="Bound">𝓤</a> <a id="2878" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2880" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2882" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2885" href="Overture.FunExtensionality.html#2885" class="Bound">f</a> <a id="2887" href="Overture.FunExtensionality.html#2841" class="Function Operator">∼</a> <a id="2889" href="Overture.FunExtensionality.html#2889" class="Bound">g</a> <a id="2891" class="Symbol">=</a> <a id="2893" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="2895" href="Overture.FunExtensionality.html#2895" class="Bound">x</a> <a id="2897" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="2899" href="Overture.FunExtensionality.html#2823" class="Bound">A</a> <a id="2901" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="2903" href="Overture.FunExtensionality.html#2885" class="Bound">f</a> <a id="2905" href="Overture.FunExtensionality.html#2895" class="Bound">x</a> <a id="2907" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="2909" href="Overture.FunExtensionality.html#2889" class="Bound">g</a> <a id="2911" href="Overture.FunExtensionality.html#2895" class="Bound">x</a>

 <a id="2915" class="Keyword">infix</a> <a id="2921" class="Number">0</a> <a id="2923" href="Overture.FunExtensionality.html#2841" class="Function Operator">_∼_</a>

<a id="2928" class="Keyword">open</a> <a id="2933" class="Keyword">import</a> <a id="2940" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="2949" class="Keyword">using</a> <a id="2955" class="Symbol">(</a><a id="2956" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="2959" class="Symbol">)</a> <a id="2961" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal; that is, for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In type theory this principle is represented by the types `funext` (for nondependent functions) and `dfunext` (for dependent functions)~(\cite[\S2.9]{HoTT}).  For example, the latter is defined as follows.<sup>[2](Overture.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="3417" class="Keyword">module</a> <a id="hide-funext"></a><a id="3424" href="Overture.FunExtensionality.html#3424" class="Module">hide-funext</a> <a id="3436" class="Keyword">where</a>

 <a id="hide-funext.dfunext"></a><a id="3444" href="Overture.FunExtensionality.html#3444" class="Function">dfunext</a> <a id="3452" class="Symbol">:</a> <a id="3454" class="Symbol">∀</a> <a id="3456" href="Overture.FunExtensionality.html#3456" class="Bound">𝓤</a> <a id="3458" href="Overture.FunExtensionality.html#3458" class="Bound">𝓦</a> <a id="3460" class="Symbol">→</a> <a id="3462" href="Overture.FunExtensionality.html#3456" class="Bound">𝓤</a> <a id="3464" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3466" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3468" href="Overture.FunExtensionality.html#3458" class="Bound">𝓦</a> <a id="3470" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3472" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3475" href="Overture.FunExtensionality.html#3444" class="Function">dfunext</a> <a id="3483" href="Overture.FunExtensionality.html#3483" class="Bound">𝓤</a> <a id="3485" href="Overture.FunExtensionality.html#3485" class="Bound">𝓦</a> <a id="3487" class="Symbol">=</a> <a id="3489" class="Symbol">{</a><a id="3490" href="Overture.FunExtensionality.html#3490" class="Bound">A</a> <a id="3492" class="Symbol">:</a> <a id="3494" href="Overture.FunExtensionality.html#3483" class="Bound">𝓤</a> <a id="3496" href="Universes.html#403" class="Function Operator">̇</a> <a id="3498" class="Symbol">}{</a><a id="3500" href="Overture.FunExtensionality.html#3500" class="Bound">B</a> <a id="3502" class="Symbol">:</a> <a id="3504" href="Overture.FunExtensionality.html#3490" class="Bound">A</a> <a id="3506" class="Symbol">→</a> <a id="3508" href="Overture.FunExtensionality.html#3485" class="Bound">𝓦</a> <a id="3510" href="Universes.html#403" class="Function Operator">̇</a> <a id="3512" class="Symbol">}{</a><a id="3514" href="Overture.FunExtensionality.html#3514" class="Bound">f</a> <a id="3516" href="Overture.FunExtensionality.html#3516" class="Bound">g</a> <a id="3518" class="Symbol">:</a> <a id="3520" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3522" href="Overture.FunExtensionality.html#3522" class="Bound">x</a> <a id="3524" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="3526" href="Overture.FunExtensionality.html#3490" class="Bound">A</a> <a id="3528" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="3530" href="Overture.FunExtensionality.html#3500" class="Bound">B</a> <a id="3532" href="Overture.FunExtensionality.html#3522" class="Bound">x</a><a id="3533" class="Symbol">}</a> <a id="3535" class="Symbol">→</a>  <a id="3538" href="Overture.FunExtensionality.html#3514" class="Bound">f</a> <a id="3540" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3542" href="Overture.FunExtensionality.html#3516" class="Bound">g</a>  <a id="3545" class="Symbol">→</a>  <a id="3548" href="Overture.FunExtensionality.html#3514" class="Bound">f</a> <a id="3550" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3552" href="Overture.FunExtensionality.html#3516" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[3](Overture.Extensionality.html#fn3)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="4338" class="Keyword">open</a> <a id="4343" class="Keyword">import</a> <a id="4350" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="4377" class="Keyword">using</a> <a id="4383" class="Symbol">(</a><a id="4384" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="4390" class="Symbol">;</a> <a id="4392" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="4399" class="Symbol">)</a> <a id="4401" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.



The next type defines the converse of function extensionality (cf. `cong-app` in [Overture.Equality][] and (2.9.2) in the [HoTT Book][]).

<pre class="Agda">

<a id="happly"></a><a id="4748" href="Overture.FunExtensionality.html#4748" class="Function">happly</a> <a id="4755" class="Symbol">:</a> <a id="4757" class="Symbol">{</a><a id="4758" href="Overture.FunExtensionality.html#4758" class="Bound">A</a> <a id="4760" class="Symbol">:</a> <a id="4762" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4764" href="Universes.html#403" class="Function Operator">̇</a> <a id="4766" class="Symbol">}{</a><a id="4768" href="Overture.FunExtensionality.html#4768" class="Bound">B</a> <a id="4770" class="Symbol">:</a> <a id="4772" href="Overture.FunExtensionality.html#4758" class="Bound">A</a> <a id="4774" class="Symbol">→</a> <a id="4776" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4778" href="Universes.html#403" class="Function Operator">̇</a> <a id="4780" class="Symbol">}{</a><a id="4782" href="Overture.FunExtensionality.html#4782" class="Bound">f</a> <a id="4784" href="Overture.FunExtensionality.html#4784" class="Bound">g</a> <a id="4786" class="Symbol">:</a> <a id="4788" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="4790" href="Overture.FunExtensionality.html#4768" class="Bound">B</a><a id="4791" class="Symbol">}</a> <a id="4793" class="Symbol">→</a> <a id="4795" href="Overture.FunExtensionality.html#4782" class="Bound">f</a> <a id="4797" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4799" href="Overture.FunExtensionality.html#4784" class="Bound">g</a> <a id="4801" class="Symbol">→</a> <a id="4803" href="Overture.FunExtensionality.html#4782" class="Bound">f</a> <a id="4805" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="4807" href="Overture.FunExtensionality.html#4784" class="Bound">g</a>
<a id="4809" href="Overture.FunExtensionality.html#4748" class="Function">happly</a> <a id="4816" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4821" class="Symbol">_</a> <a id="4823" class="Symbol">=</a> <a id="4825" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions by comparing the definitions of `dfunext` and `happly`. In the definition of `dfunext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `dfunext` is an assertion (which may or may not hold). In the definition of `happly`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `happly` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `dfunext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : dfunext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">An alternative way to express function extensionality</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

<pre class="Agda">

<a id="6792" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="6799" href="Overture.FunExtensionality.html#6799" class="Module">hide-tt-defs</a> <a id="6812" class="Symbol">{</a><a id="6813" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6815" class="Symbol">:</a> <a id="6817" href="Universes.html#205" class="Postulate">Universe</a><a id="6825" class="Symbol">}</a> <a id="6827" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="6835" href="Overture.FunExtensionality.html#6835" class="Function">is-center</a> <a id="6845" class="Symbol">:</a> <a id="6847" class="Symbol">(</a><a id="6848" href="Overture.FunExtensionality.html#6848" class="Bound">A</a> <a id="6850" class="Symbol">:</a> <a id="6852" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6854" href="Universes.html#403" class="Function Operator">̇</a> <a id="6856" class="Symbol">)</a> <a id="6858" class="Symbol">→</a> <a id="6860" href="Overture.FunExtensionality.html#6848" class="Bound">A</a> <a id="6862" class="Symbol">→</a> <a id="6864" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6866" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6869" href="Overture.FunExtensionality.html#6835" class="Function">is-center</a> <a id="6879" href="Overture.FunExtensionality.html#6879" class="Bound">A</a> <a id="6881" href="Overture.FunExtensionality.html#6881" class="Bound">c</a> <a id="6883" class="Symbol">=</a> <a id="6885" class="Symbol">(</a><a id="6886" href="Overture.FunExtensionality.html#6886" class="Bound">x</a> <a id="6888" class="Symbol">:</a> <a id="6890" href="Overture.FunExtensionality.html#6879" class="Bound">A</a><a id="6891" class="Symbol">)</a> <a id="6893" class="Symbol">→</a> <a id="6895" href="Overture.FunExtensionality.html#6881" class="Bound">c</a> <a id="6897" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="6899" href="Overture.FunExtensionality.html#6886" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="6903" href="Overture.FunExtensionality.html#6903" class="Function">is-singleton</a> <a id="6916" class="Symbol">:</a> <a id="6918" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6920" href="Universes.html#403" class="Function Operator">̇</a> <a id="6922" class="Symbol">→</a> <a id="6924" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6926" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6929" href="Overture.FunExtensionality.html#6903" class="Function">is-singleton</a> <a id="6942" href="Overture.FunExtensionality.html#6942" class="Bound">A</a> <a id="6944" class="Symbol">=</a> <a id="6946" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="6948" href="Overture.FunExtensionality.html#6948" class="Bound">c</a> <a id="6950" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="6952" href="Overture.FunExtensionality.html#6942" class="Bound">A</a> <a id="6954" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="6956" href="Overture.FunExtensionality.html#6835" class="Function">is-center</a> <a id="6966" href="Overture.FunExtensionality.html#6942" class="Bound">A</a> <a id="6968" href="Overture.FunExtensionality.html#6948" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="6972" href="Overture.FunExtensionality.html#6972" class="Function">is-subsingleton</a> <a id="6988" class="Symbol">:</a> <a id="6990" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6992" href="Universes.html#403" class="Function Operator">̇</a> <a id="6994" class="Symbol">→</a> <a id="6996" href="Overture.FunExtensionality.html#6813" class="Bound">𝓤</a> <a id="6998" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7001" href="Overture.FunExtensionality.html#6972" class="Function">is-subsingleton</a> <a id="7017" href="Overture.FunExtensionality.html#7017" class="Bound">A</a> <a id="7019" class="Symbol">=</a> <a id="7021" class="Symbol">(</a><a id="7022" href="Overture.FunExtensionality.html#7022" class="Bound">x</a> <a id="7024" href="Overture.FunExtensionality.html#7024" class="Bound">y</a> <a id="7026" class="Symbol">:</a> <a id="7028" href="Overture.FunExtensionality.html#7017" class="Bound">A</a><a id="7029" class="Symbol">)</a> <a id="7031" class="Symbol">→</a> <a id="7033" href="Overture.FunExtensionality.html#7022" class="Bound">x</a> <a id="7035" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7037" href="Overture.FunExtensionality.html#7024" class="Bound">y</a>

<a id="7040" class="Keyword">open</a> <a id="7045" class="Keyword">import</a> <a id="7052" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="7065" class="Keyword">using</a> <a id="7071" class="Symbol">(</a><a id="7072" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="7081" class="Symbol">;</a> <a id="7083" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7095" class="Symbol">;</a> <a id="7097" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7112" class="Symbol">)</a> <a id="7114" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="7531" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="7538" href="Overture.FunExtensionality.html#7538" class="Module">hide-tt-defs&#39;</a> <a id="7552" class="Symbol">{</a><a id="7553" href="Overture.FunExtensionality.html#7553" class="Bound">𝓤</a> <a id="7555" href="Overture.FunExtensionality.html#7555" class="Bound">𝓦</a> <a id="7557" class="Symbol">:</a> <a id="7559" href="Universes.html#205" class="Postulate">Universe</a><a id="7567" class="Symbol">}</a> <a id="7569" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="7577" href="Overture.FunExtensionality.html#7577" class="Function">fiber</a> <a id="7583" class="Symbol">:</a> <a id="7585" class="Symbol">{</a><a id="7586" href="Overture.FunExtensionality.html#7586" class="Bound">A</a> <a id="7588" class="Symbol">:</a> <a id="7590" href="Overture.FunExtensionality.html#7553" class="Bound">𝓤</a> <a id="7592" href="Universes.html#403" class="Function Operator">̇</a> <a id="7594" class="Symbol">}</a> <a id="7596" class="Symbol">{</a><a id="7597" href="Overture.FunExtensionality.html#7597" class="Bound">B</a> <a id="7599" class="Symbol">:</a> <a id="7601" href="Overture.FunExtensionality.html#7555" class="Bound">𝓦</a> <a id="7603" href="Universes.html#403" class="Function Operator">̇</a> <a id="7605" class="Symbol">}</a> <a id="7607" class="Symbol">(</a><a id="7608" href="Overture.FunExtensionality.html#7608" class="Bound">f</a> <a id="7610" class="Symbol">:</a> <a id="7612" href="Overture.FunExtensionality.html#7586" class="Bound">A</a> <a id="7614" class="Symbol">→</a> <a id="7616" href="Overture.FunExtensionality.html#7597" class="Bound">B</a><a id="7617" class="Symbol">)</a> <a id="7619" class="Symbol">→</a> <a id="7621" href="Overture.FunExtensionality.html#7597" class="Bound">B</a> <a id="7623" class="Symbol">→</a> <a id="7625" href="Overture.FunExtensionality.html#7553" class="Bound">𝓤</a> <a id="7627" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7629" href="Overture.FunExtensionality.html#7555" class="Bound">𝓦</a> <a id="7631" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7634" href="Overture.FunExtensionality.html#7577" class="Function">fiber</a> <a id="7640" class="Symbol">{</a><a id="7641" href="Overture.FunExtensionality.html#7641" class="Bound">A</a><a id="7642" class="Symbol">}</a> <a id="7644" href="Overture.FunExtensionality.html#7644" class="Bound">f</a> <a id="7646" href="Overture.FunExtensionality.html#7646" class="Bound">y</a> <a id="7648" class="Symbol">=</a> <a id="7650" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="7652" href="Overture.FunExtensionality.html#7652" class="Bound">x</a> <a id="7654" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="7656" href="Overture.FunExtensionality.html#7641" class="Bound">A</a> <a id="7658" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="7660" href="Overture.FunExtensionality.html#7644" class="Bound">f</a> <a id="7662" href="Overture.FunExtensionality.html#7652" class="Bound">x</a> <a id="7664" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7666" href="Overture.FunExtensionality.html#7646" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="7772" href="Overture.FunExtensionality.html#7772" class="Function">is-equiv</a> <a id="7781" class="Symbol">:</a> <a id="7783" class="Symbol">{</a><a id="7784" href="Overture.FunExtensionality.html#7784" class="Bound">A</a> <a id="7786" class="Symbol">:</a> <a id="7788" href="Overture.FunExtensionality.html#7553" class="Bound">𝓤</a> <a id="7790" href="Universes.html#403" class="Function Operator">̇</a> <a id="7792" class="Symbol">}</a> <a id="7794" class="Symbol">{</a><a id="7795" href="Overture.FunExtensionality.html#7795" class="Bound">B</a> <a id="7797" class="Symbol">:</a> <a id="7799" href="Overture.FunExtensionality.html#7555" class="Bound">𝓦</a> <a id="7801" href="Universes.html#403" class="Function Operator">̇</a> <a id="7803" class="Symbol">}</a> <a id="7805" class="Symbol">→</a> <a id="7807" class="Symbol">(</a><a id="7808" href="Overture.FunExtensionality.html#7784" class="Bound">A</a> <a id="7810" class="Symbol">→</a> <a id="7812" href="Overture.FunExtensionality.html#7795" class="Bound">B</a><a id="7813" class="Symbol">)</a> <a id="7815" class="Symbol">→</a> <a id="7817" href="Overture.FunExtensionality.html#7553" class="Bound">𝓤</a> <a id="7819" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7821" href="Overture.FunExtensionality.html#7555" class="Bound">𝓦</a> <a id="7823" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7826" href="Overture.FunExtensionality.html#7772" class="Function">is-equiv</a> <a id="7835" href="Overture.FunExtensionality.html#7835" class="Bound">f</a> <a id="7837" class="Symbol">=</a> <a id="7839" class="Symbol">∀</a> <a id="7841" href="Overture.FunExtensionality.html#7841" class="Bound">y</a> <a id="7843" class="Symbol">→</a> <a id="7845" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="7858" class="Symbol">(</a><a id="7859" href="Overture.FunExtensionality.html#7577" class="Function">fiber</a> <a id="7865" href="Overture.FunExtensionality.html#7835" class="Bound">f</a> <a id="7867" href="Overture.FunExtensionality.html#7841" class="Bound">y</a><a id="7868" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.

<pre class="Agda">

<a id="8027" class="Keyword">open</a> <a id="8032" class="Keyword">import</a> <a id="8039" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="8056" class="Keyword">using</a> <a id="8062" class="Symbol">(</a><a id="8063" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8068" class="Symbol">;</a> <a id="8070" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="8078" class="Symbol">)</a> <a id="8080" class="Keyword">public</a>

<a id="8088" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="8095" href="Overture.FunExtensionality.html#8095" class="Module">hide-hfunext</a> <a id="8108" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="8116" href="Overture.FunExtensionality.html#8116" class="Function">hfunext</a> <a id="8124" class="Symbol">:</a>  <a id="8127" class="Symbol">∀</a> <a id="8129" href="Overture.FunExtensionality.html#8129" class="Bound">𝓤</a> <a id="8131" href="Overture.FunExtensionality.html#8131" class="Bound">𝓦</a> <a id="8133" class="Symbol">→</a> <a id="8135" class="Symbol">(</a><a id="8136" href="Overture.FunExtensionality.html#8129" class="Bound">𝓤</a> <a id="8138" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8140" href="Overture.FunExtensionality.html#8131" class="Bound">𝓦</a><a id="8141" class="Symbol">)</a><a id="8142" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8144" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8147" href="Overture.FunExtensionality.html#8116" class="Function">hfunext</a> <a id="8155" href="Overture.FunExtensionality.html#8155" class="Bound">𝓤</a> <a id="8157" href="Overture.FunExtensionality.html#8157" class="Bound">𝓦</a> <a id="8159" class="Symbol">=</a> <a id="8161" class="Symbol">{</a><a id="8162" href="Overture.FunExtensionality.html#8162" class="Bound">A</a> <a id="8164" class="Symbol">:</a> <a id="8166" href="Overture.FunExtensionality.html#8155" class="Bound">𝓤</a> <a id="8168" href="Universes.html#403" class="Function Operator">̇</a><a id="8169" class="Symbol">}{</a><a id="8171" href="Overture.FunExtensionality.html#8171" class="Bound">B</a> <a id="8173" class="Symbol">:</a> <a id="8175" href="Overture.FunExtensionality.html#8162" class="Bound">A</a> <a id="8177" class="Symbol">→</a> <a id="8179" href="Overture.FunExtensionality.html#8157" class="Bound">𝓦</a> <a id="8181" href="Universes.html#403" class="Function Operator">̇</a><a id="8182" class="Symbol">}</a> <a id="8184" class="Symbol">(</a><a id="8185" href="Overture.FunExtensionality.html#8185" class="Bound">f</a> <a id="8187" href="Overture.FunExtensionality.html#8187" class="Bound">g</a> <a id="8189" class="Symbol">:</a> <a id="8191" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8193" href="Overture.FunExtensionality.html#8171" class="Bound">B</a><a id="8194" class="Symbol">)</a> <a id="8196" class="Symbol">→</a> <a id="8198" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="8207" class="Symbol">(</a><a id="8208" href="Overture.FunExtensionality.html#4748" class="Function">happly</a><a id="8214" class="Symbol">{</a><a id="8215" class="Argument">f</a> <a id="8217" class="Symbol">=</a> <a id="8219" href="Overture.FunExtensionality.html#8185" class="Bound">f</a><a id="8220" class="Symbol">}{</a><a id="8222" href="Overture.FunExtensionality.html#8187" class="Bound">g</a><a id="8223" class="Symbol">})</a>

<a id="8227" class="Keyword">open</a> <a id="8232" class="Keyword">import</a> <a id="8239" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="8266" class="Keyword">using</a> <a id="8272" class="Symbol">(</a><a id="8273" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8280" class="Symbol">)</a> <a id="8282" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>


<sup>2</sup> <span class="footnote" id="fn2"> Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an alternative approach to extensionality; e.g., *univalence* and/or Cubical Agda.

<sup>3</sup> <span class="footnote" id="fn3"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>


<br>
<br>

[← Overture.Equality](Overture.Equality.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff

<sup>3</sup> <span class="footnote" id="fn3"> For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
