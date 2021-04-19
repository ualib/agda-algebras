---
layout: default
title : Overture.FunctionExtensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [Overture.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="308" class="Symbol">{-#</a> <a id="312" class="Keyword">OPTIONS</a> <a id="320" class="Pragma">--without-K</a> <a id="332" class="Pragma">--exact-split</a> <a id="346" class="Pragma">--safe</a> <a id="353" class="Symbol">#-}</a>

<a id="358" class="Keyword">module</a> <a id="365" href="Overture.FunExtensionality.html" class="Module">Overture.FunExtensionality</a> <a id="392" class="Keyword">where</a>

<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="Overture.Equality.html" class="Module">Overture.Equality</a> <a id="429" class="Keyword">public</a>

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

#### <a id="function-extensionality-types">Function extensionality types</a>

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

<pre class="Agda">

<a id="2880" class="Keyword">module</a> <a id="hide-∼"></a><a id="2887" href="Overture.FunExtensionality.html#2887" class="Module">hide-∼</a> <a id="2894" class="Symbol">{</a><a id="2895" href="Overture.FunExtensionality.html#2895" class="Bound">A</a> <a id="2897" class="Symbol">:</a> <a id="2899" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2901" href="Universes.html#403" class="Function Operator">̇</a> <a id="2903" class="Symbol">}</a> <a id="2905" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2913" href="Overture.FunExtensionality.html#2913" class="Function Operator">_∼_</a> <a id="2917" class="Symbol">:</a> <a id="2919" class="Symbol">{</a><a id="2920" href="Overture.FunExtensionality.html#2920" class="Bound">B</a> <a id="2922" class="Symbol">:</a> <a id="2924" href="Overture.FunExtensionality.html#2895" class="Bound">A</a> <a id="2926" class="Symbol">→</a> <a id="2928" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2930" href="Universes.html#403" class="Function Operator">̇</a> <a id="2932" class="Symbol">}</a> <a id="2934" class="Symbol">→</a> <a id="2936" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2938" href="Overture.FunExtensionality.html#2920" class="Bound">B</a> <a id="2940" class="Symbol">→</a> <a id="2942" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2944" href="Overture.FunExtensionality.html#2920" class="Bound">B</a> <a id="2946" class="Symbol">→</a> <a id="2948" href="Overture.FunExtensionality.html#2899" class="Bound">𝓤</a> <a id="2950" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2952" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2954" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2957" href="Overture.FunExtensionality.html#2957" class="Bound">f</a> <a id="2959" href="Overture.FunExtensionality.html#2913" class="Function Operator">∼</a> <a id="2961" href="Overture.FunExtensionality.html#2961" class="Bound">g</a> <a id="2963" class="Symbol">=</a> <a id="2965" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="2967" href="Overture.FunExtensionality.html#2967" class="Bound">x</a> <a id="2969" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="2971" href="Overture.FunExtensionality.html#2895" class="Bound">A</a> <a id="2973" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="2975" href="Overture.FunExtensionality.html#2957" class="Bound">f</a> <a id="2977" href="Overture.FunExtensionality.html#2967" class="Bound">x</a> <a id="2979" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="2981" href="Overture.FunExtensionality.html#2961" class="Bound">g</a> <a id="2983" href="Overture.FunExtensionality.html#2967" class="Bound">x</a>

 <a id="2987" class="Keyword">infix</a> <a id="2993" class="Number">0</a> <a id="2995" href="Overture.FunExtensionality.html#2913" class="Function Operator">_∼_</a>

<a id="3000" class="Keyword">open</a> <a id="3005" class="Keyword">import</a> <a id="3012" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3021" class="Keyword">using</a> <a id="3027" class="Symbol">(</a><a id="3028" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3031" class="Symbol">)</a> <a id="3033" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal; that is, for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In type theory this principle is represented by the types `funext` (for nondependent functions) and `dfunext` (for dependent functions)~(\cite[\S2.9]{HoTT}).  For example, the latter is defined as follows.

<pre class="Agda">

<a id="3441" class="Keyword">module</a> <a id="hide-funext"></a><a id="3448" href="Overture.FunExtensionality.html#3448" class="Module">hide-funext</a> <a id="3460" class="Keyword">where</a>

 <a id="hide-funext.dfunext"></a><a id="3468" href="Overture.FunExtensionality.html#3468" class="Function">dfunext</a> <a id="3476" class="Symbol">:</a> <a id="3478" class="Symbol">∀</a> <a id="3480" href="Overture.FunExtensionality.html#3480" class="Bound">𝓤</a> <a id="3482" href="Overture.FunExtensionality.html#3482" class="Bound">𝓦</a> <a id="3484" class="Symbol">→</a> <a id="3486" href="Overture.FunExtensionality.html#3480" class="Bound">𝓤</a> <a id="3488" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3490" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3492" href="Overture.FunExtensionality.html#3482" class="Bound">𝓦</a> <a id="3494" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3496" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3499" href="Overture.FunExtensionality.html#3468" class="Function">dfunext</a> <a id="3507" href="Overture.FunExtensionality.html#3507" class="Bound">𝓤</a> <a id="3509" href="Overture.FunExtensionality.html#3509" class="Bound">𝓦</a> <a id="3511" class="Symbol">=</a> <a id="3513" class="Symbol">{</a><a id="3514" href="Overture.FunExtensionality.html#3514" class="Bound">A</a> <a id="3516" class="Symbol">:</a> <a id="3518" href="Overture.FunExtensionality.html#3507" class="Bound">𝓤</a> <a id="3520" href="Universes.html#403" class="Function Operator">̇</a> <a id="3522" class="Symbol">}{</a><a id="3524" href="Overture.FunExtensionality.html#3524" class="Bound">B</a> <a id="3526" class="Symbol">:</a> <a id="3528" href="Overture.FunExtensionality.html#3514" class="Bound">A</a> <a id="3530" class="Symbol">→</a> <a id="3532" href="Overture.FunExtensionality.html#3509" class="Bound">𝓦</a> <a id="3534" href="Universes.html#403" class="Function Operator">̇</a> <a id="3536" class="Symbol">}{</a><a id="3538" href="Overture.FunExtensionality.html#3538" class="Bound">f</a> <a id="3540" href="Overture.FunExtensionality.html#3540" class="Bound">g</a> <a id="3542" class="Symbol">:</a> <a id="3544" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3546" href="Overture.FunExtensionality.html#3546" class="Bound">x</a> <a id="3548" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="3550" href="Overture.FunExtensionality.html#3514" class="Bound">A</a> <a id="3552" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="3554" href="Overture.FunExtensionality.html#3524" class="Bound">B</a> <a id="3556" href="Overture.FunExtensionality.html#3546" class="Bound">x</a><a id="3557" class="Symbol">}</a> <a id="3559" class="Symbol">→</a>  <a id="3562" href="Overture.FunExtensionality.html#3538" class="Bound">f</a> <a id="3564" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3566" href="Overture.FunExtensionality.html#3540" class="Bound">g</a>  <a id="3569" class="Symbol">→</a>  <a id="3572" href="Overture.FunExtensionality.html#3538" class="Bound">f</a> <a id="3574" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3576" href="Overture.FunExtensionality.html#3540" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="4362" class="Keyword">open</a> <a id="4367" class="Keyword">import</a> <a id="4374" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="4401" class="Keyword">using</a> <a id="4407" class="Symbol">(</a><a id="4408" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="4414" class="Symbol">;</a> <a id="4416" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="4423" class="Symbol">)</a> <a id="4425" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates.<sup>[4](Overture.Extensionality.html#fn4)</sup>

The next type defines the converse of function extensionality (cf. `cong-app` in [Overture.Equality][] and (2.9.2) in the [HoTT Book][]).

<pre class="Agda">

<a id="happly"></a><a id="5463" href="Overture.FunExtensionality.html#5463" class="Function">happly</a> <a id="5470" class="Symbol">:</a> <a id="5472" class="Symbol">{</a><a id="5473" href="Overture.FunExtensionality.html#5473" class="Bound">A</a> <a id="5475" class="Symbol">:</a> <a id="5477" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5479" href="Universes.html#403" class="Function Operator">̇</a> <a id="5481" class="Symbol">}{</a><a id="5483" href="Overture.FunExtensionality.html#5483" class="Bound">B</a> <a id="5485" class="Symbol">:</a> <a id="5487" href="Overture.FunExtensionality.html#5473" class="Bound">A</a> <a id="5489" class="Symbol">→</a> <a id="5491" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5493" href="Universes.html#403" class="Function Operator">̇</a> <a id="5495" class="Symbol">}{</a><a id="5497" href="Overture.FunExtensionality.html#5497" class="Bound">f</a> <a id="5499" href="Overture.FunExtensionality.html#5499" class="Bound">g</a> <a id="5501" class="Symbol">:</a> <a id="5503" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5505" href="Overture.FunExtensionality.html#5483" class="Bound">B</a><a id="5506" class="Symbol">}</a> <a id="5508" class="Symbol">→</a> <a id="5510" href="Overture.FunExtensionality.html#5497" class="Bound">f</a> <a id="5512" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5514" href="Overture.FunExtensionality.html#5499" class="Bound">g</a> <a id="5516" class="Symbol">→</a> <a id="5518" href="Overture.FunExtensionality.html#5497" class="Bound">f</a> <a id="5520" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5522" href="Overture.FunExtensionality.html#5499" class="Bound">g</a>
<a id="5524" href="Overture.FunExtensionality.html#5463" class="Function">happly</a> <a id="5531" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5536" class="Symbol">_</a> <a id="5538" class="Symbol">=</a> <a id="5540" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions by comparing the definitions of `dfunext` and `happly`. In the definition of `dfunext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `dfunext` is an assertion (which may or may not hold). In the definition of `happly`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `happly` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `dfunext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : dfunext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

<pre class="Agda">

<a id="7485" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="7492" href="Overture.FunExtensionality.html#7492" class="Module">hide-tt-defs</a> <a id="7505" class="Symbol">{</a><a id="7506" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7508" class="Symbol">:</a> <a id="7510" href="Universes.html#205" class="Postulate">Universe</a><a id="7518" class="Symbol">}</a> <a id="7520" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="7528" href="Overture.FunExtensionality.html#7528" class="Function">is-center</a> <a id="7538" class="Symbol">:</a> <a id="7540" class="Symbol">(</a><a id="7541" href="Overture.FunExtensionality.html#7541" class="Bound">A</a> <a id="7543" class="Symbol">:</a> <a id="7545" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7547" href="Universes.html#403" class="Function Operator">̇</a> <a id="7549" class="Symbol">)</a> <a id="7551" class="Symbol">→</a> <a id="7553" href="Overture.FunExtensionality.html#7541" class="Bound">A</a> <a id="7555" class="Symbol">→</a> <a id="7557" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7559" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7562" href="Overture.FunExtensionality.html#7528" class="Function">is-center</a> <a id="7572" href="Overture.FunExtensionality.html#7572" class="Bound">A</a> <a id="7574" href="Overture.FunExtensionality.html#7574" class="Bound">c</a> <a id="7576" class="Symbol">=</a> <a id="7578" class="Symbol">(</a><a id="7579" href="Overture.FunExtensionality.html#7579" class="Bound">x</a> <a id="7581" class="Symbol">:</a> <a id="7583" href="Overture.FunExtensionality.html#7572" class="Bound">A</a><a id="7584" class="Symbol">)</a> <a id="7586" class="Symbol">→</a> <a id="7588" href="Overture.FunExtensionality.html#7574" class="Bound">c</a> <a id="7590" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7592" href="Overture.FunExtensionality.html#7579" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="7596" href="Overture.FunExtensionality.html#7596" class="Function">is-singleton</a> <a id="7609" class="Symbol">:</a> <a id="7611" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7613" href="Universes.html#403" class="Function Operator">̇</a> <a id="7615" class="Symbol">→</a> <a id="7617" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7619" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7622" href="Overture.FunExtensionality.html#7596" class="Function">is-singleton</a> <a id="7635" href="Overture.FunExtensionality.html#7635" class="Bound">A</a> <a id="7637" class="Symbol">=</a> <a id="7639" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="7641" href="Overture.FunExtensionality.html#7641" class="Bound">c</a> <a id="7643" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="7645" href="Overture.FunExtensionality.html#7635" class="Bound">A</a> <a id="7647" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="7649" href="Overture.FunExtensionality.html#7528" class="Function">is-center</a> <a id="7659" href="Overture.FunExtensionality.html#7635" class="Bound">A</a> <a id="7661" href="Overture.FunExtensionality.html#7641" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="7665" href="Overture.FunExtensionality.html#7665" class="Function">is-subsingleton</a> <a id="7681" class="Symbol">:</a> <a id="7683" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7685" href="Universes.html#403" class="Function Operator">̇</a> <a id="7687" class="Symbol">→</a> <a id="7689" href="Overture.FunExtensionality.html#7506" class="Bound">𝓤</a> <a id="7691" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7694" href="Overture.FunExtensionality.html#7665" class="Function">is-subsingleton</a> <a id="7710" href="Overture.FunExtensionality.html#7710" class="Bound">A</a> <a id="7712" class="Symbol">=</a> <a id="7714" class="Symbol">(</a><a id="7715" href="Overture.FunExtensionality.html#7715" class="Bound">x</a> <a id="7717" href="Overture.FunExtensionality.html#7717" class="Bound">y</a> <a id="7719" class="Symbol">:</a> <a id="7721" href="Overture.FunExtensionality.html#7710" class="Bound">A</a><a id="7722" class="Symbol">)</a> <a id="7724" class="Symbol">→</a> <a id="7726" href="Overture.FunExtensionality.html#7715" class="Bound">x</a> <a id="7728" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7730" href="Overture.FunExtensionality.html#7717" class="Bound">y</a>

<a id="7733" class="Keyword">open</a> <a id="7738" class="Keyword">import</a> <a id="7745" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="7758" class="Keyword">using</a> <a id="7764" class="Symbol">(</a><a id="7765" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="7774" class="Symbol">;</a> <a id="7776" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7788" class="Symbol">;</a> <a id="7790" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7805" class="Symbol">)</a> <a id="7807" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="8224" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="8231" href="Overture.FunExtensionality.html#8231" class="Module">hide-tt-defs&#39;</a> <a id="8245" class="Symbol">{</a><a id="8246" href="Overture.FunExtensionality.html#8246" class="Bound">𝓤</a> <a id="8248" href="Overture.FunExtensionality.html#8248" class="Bound">𝓦</a> <a id="8250" class="Symbol">:</a> <a id="8252" href="Universes.html#205" class="Postulate">Universe</a><a id="8260" class="Symbol">}</a> <a id="8262" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="8270" href="Overture.FunExtensionality.html#8270" class="Function">fiber</a> <a id="8276" class="Symbol">:</a> <a id="8278" class="Symbol">{</a><a id="8279" href="Overture.FunExtensionality.html#8279" class="Bound">A</a> <a id="8281" class="Symbol">:</a> <a id="8283" href="Overture.FunExtensionality.html#8246" class="Bound">𝓤</a> <a id="8285" href="Universes.html#403" class="Function Operator">̇</a> <a id="8287" class="Symbol">}</a> <a id="8289" class="Symbol">{</a><a id="8290" href="Overture.FunExtensionality.html#8290" class="Bound">B</a> <a id="8292" class="Symbol">:</a> <a id="8294" href="Overture.FunExtensionality.html#8248" class="Bound">𝓦</a> <a id="8296" href="Universes.html#403" class="Function Operator">̇</a> <a id="8298" class="Symbol">}</a> <a id="8300" class="Symbol">(</a><a id="8301" href="Overture.FunExtensionality.html#8301" class="Bound">f</a> <a id="8303" class="Symbol">:</a> <a id="8305" href="Overture.FunExtensionality.html#8279" class="Bound">A</a> <a id="8307" class="Symbol">→</a> <a id="8309" href="Overture.FunExtensionality.html#8290" class="Bound">B</a><a id="8310" class="Symbol">)</a> <a id="8312" class="Symbol">→</a> <a id="8314" href="Overture.FunExtensionality.html#8290" class="Bound">B</a> <a id="8316" class="Symbol">→</a> <a id="8318" href="Overture.FunExtensionality.html#8246" class="Bound">𝓤</a> <a id="8320" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8322" href="Overture.FunExtensionality.html#8248" class="Bound">𝓦</a> <a id="8324" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8327" href="Overture.FunExtensionality.html#8270" class="Function">fiber</a> <a id="8333" class="Symbol">{</a><a id="8334" href="Overture.FunExtensionality.html#8334" class="Bound">A</a><a id="8335" class="Symbol">}</a> <a id="8337" href="Overture.FunExtensionality.html#8337" class="Bound">f</a> <a id="8339" href="Overture.FunExtensionality.html#8339" class="Bound">y</a> <a id="8341" class="Symbol">=</a> <a id="8343" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8345" href="Overture.FunExtensionality.html#8345" class="Bound">x</a> <a id="8347" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8349" href="Overture.FunExtensionality.html#8334" class="Bound">A</a> <a id="8351" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8353" href="Overture.FunExtensionality.html#8337" class="Bound">f</a> <a id="8355" href="Overture.FunExtensionality.html#8345" class="Bound">x</a> <a id="8357" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8359" href="Overture.FunExtensionality.html#8339" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="8465" href="Overture.FunExtensionality.html#8465" class="Function">is-equiv</a> <a id="8474" class="Symbol">:</a> <a id="8476" class="Symbol">{</a><a id="8477" href="Overture.FunExtensionality.html#8477" class="Bound">A</a> <a id="8479" class="Symbol">:</a> <a id="8481" href="Overture.FunExtensionality.html#8246" class="Bound">𝓤</a> <a id="8483" href="Universes.html#403" class="Function Operator">̇</a> <a id="8485" class="Symbol">}</a> <a id="8487" class="Symbol">{</a><a id="8488" href="Overture.FunExtensionality.html#8488" class="Bound">B</a> <a id="8490" class="Symbol">:</a> <a id="8492" href="Overture.FunExtensionality.html#8248" class="Bound">𝓦</a> <a id="8494" href="Universes.html#403" class="Function Operator">̇</a> <a id="8496" class="Symbol">}</a> <a id="8498" class="Symbol">→</a> <a id="8500" class="Symbol">(</a><a id="8501" href="Overture.FunExtensionality.html#8477" class="Bound">A</a> <a id="8503" class="Symbol">→</a> <a id="8505" href="Overture.FunExtensionality.html#8488" class="Bound">B</a><a id="8506" class="Symbol">)</a> <a id="8508" class="Symbol">→</a> <a id="8510" href="Overture.FunExtensionality.html#8246" class="Bound">𝓤</a> <a id="8512" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8514" href="Overture.FunExtensionality.html#8248" class="Bound">𝓦</a> <a id="8516" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8519" href="Overture.FunExtensionality.html#8465" class="Function">is-equiv</a> <a id="8528" href="Overture.FunExtensionality.html#8528" class="Bound">f</a> <a id="8530" class="Symbol">=</a> <a id="8532" class="Symbol">∀</a> <a id="8534" href="Overture.FunExtensionality.html#8534" class="Bound">y</a> <a id="8536" class="Symbol">→</a> <a id="8538" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="8551" class="Symbol">(</a><a id="8552" href="Overture.FunExtensionality.html#8270" class="Function">fiber</a> <a id="8558" href="Overture.FunExtensionality.html#8528" class="Bound">f</a> <a id="8560" href="Overture.FunExtensionality.html#8534" class="Bound">y</a><a id="8561" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.

<pre class="Agda">

<a id="8720" class="Keyword">open</a> <a id="8725" class="Keyword">import</a> <a id="8732" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="8749" class="Keyword">using</a> <a id="8755" class="Symbol">(</a><a id="8756" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8761" class="Symbol">;</a> <a id="8763" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="8771" class="Symbol">)</a> <a id="8773" class="Keyword">public</a>

<a id="8781" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="8788" href="Overture.FunExtensionality.html#8788" class="Module">hide-hfunext</a> <a id="8801" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="8809" href="Overture.FunExtensionality.html#8809" class="Function">hfunext</a> <a id="8817" class="Symbol">:</a>  <a id="8820" class="Symbol">∀</a> <a id="8822" href="Overture.FunExtensionality.html#8822" class="Bound">𝓤</a> <a id="8824" href="Overture.FunExtensionality.html#8824" class="Bound">𝓦</a> <a id="8826" class="Symbol">→</a> <a id="8828" class="Symbol">(</a><a id="8829" href="Overture.FunExtensionality.html#8822" class="Bound">𝓤</a> <a id="8831" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8833" href="Overture.FunExtensionality.html#8824" class="Bound">𝓦</a><a id="8834" class="Symbol">)</a><a id="8835" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8837" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8840" href="Overture.FunExtensionality.html#8809" class="Function">hfunext</a> <a id="8848" href="Overture.FunExtensionality.html#8848" class="Bound">𝓤</a> <a id="8850" href="Overture.FunExtensionality.html#8850" class="Bound">𝓦</a> <a id="8852" class="Symbol">=</a> <a id="8854" class="Symbol">{</a><a id="8855" href="Overture.FunExtensionality.html#8855" class="Bound">A</a> <a id="8857" class="Symbol">:</a> <a id="8859" href="Overture.FunExtensionality.html#8848" class="Bound">𝓤</a> <a id="8861" href="Universes.html#403" class="Function Operator">̇</a><a id="8862" class="Symbol">}{</a><a id="8864" href="Overture.FunExtensionality.html#8864" class="Bound">B</a> <a id="8866" class="Symbol">:</a> <a id="8868" href="Overture.FunExtensionality.html#8855" class="Bound">A</a> <a id="8870" class="Symbol">→</a> <a id="8872" href="Overture.FunExtensionality.html#8850" class="Bound">𝓦</a> <a id="8874" href="Universes.html#403" class="Function Operator">̇</a><a id="8875" class="Symbol">}</a> <a id="8877" class="Symbol">(</a><a id="8878" href="Overture.FunExtensionality.html#8878" class="Bound">f</a> <a id="8880" href="Overture.FunExtensionality.html#8880" class="Bound">g</a> <a id="8882" class="Symbol">:</a> <a id="8884" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8886" href="Overture.FunExtensionality.html#8864" class="Bound">B</a><a id="8887" class="Symbol">)</a> <a id="8889" class="Symbol">→</a> <a id="8891" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="8900" class="Symbol">(</a><a id="8901" href="Overture.FunExtensionality.html#5463" class="Function">happly</a><a id="8907" class="Symbol">{</a><a id="8908" class="Argument">f</a> <a id="8910" class="Symbol">=</a> <a id="8912" href="Overture.FunExtensionality.html#8878" class="Bound">f</a><a id="8913" class="Symbol">}{</a><a id="8915" href="Overture.FunExtensionality.html#8880" class="Bound">g</a><a id="8916" class="Symbol">})</a>

<a id="8920" class="Keyword">open</a> <a id="8925" class="Keyword">import</a> <a id="8932" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="8959" class="Keyword">using</a> <a id="8965" class="Symbol">(</a><a id="8966" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8973" class="Symbol">)</a> <a id="8975" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>

<sup>3</sup> <span class="footnote" id="fn3"> For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).

<sup>4</sup><span class="footnote" id="fn4">Eventually we will probably remove these postulates in favor of an alternative approach to extensionality; e.g., *univalence* and/or Cubical Agda.
</span>

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
