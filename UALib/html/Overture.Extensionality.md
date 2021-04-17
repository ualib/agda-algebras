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

<a id="2885" class="Keyword">module</a> <a id="hide-∼"></a><a id="2892" href="Overture.Extensionality.html#2892" class="Module">hide-∼</a> <a id="2899" class="Symbol">{</a><a id="2900" href="Overture.Extensionality.html#2900" class="Bound">A</a> <a id="2902" class="Symbol">:</a> <a id="2904" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2906" href="Universes.html#403" class="Function Operator">̇</a> <a id="2908" class="Symbol">}</a> <a id="2910" class="Keyword">where</a>

 <a id="hide-∼._∼_"></a><a id="2918" href="Overture.Extensionality.html#2918" class="Function Operator">_∼_</a> <a id="2922" class="Symbol">:</a> <a id="2924" class="Symbol">{</a><a id="2925" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Overture.Extensionality.html#2900" class="Bound">A</a> <a id="2931" class="Symbol">→</a> <a id="2933" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2935" href="Universes.html#403" class="Function Operator">̇</a> <a id="2937" class="Symbol">}</a> <a id="2939" class="Symbol">→</a> <a id="2941" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2943" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2945" class="Symbol">→</a> <a id="2947" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="2949" href="Overture.Extensionality.html#2925" class="Bound">B</a> <a id="2951" class="Symbol">→</a> <a id="2953" href="Overture.Extensionality.html#2904" class="Bound">𝓤</a> <a id="2955" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2957" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="2959" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2962" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2964" href="Overture.Extensionality.html#2918" class="Function Operator">∼</a> <a id="2966" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2968" class="Symbol">=</a> <a id="2970" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="2972" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2974" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="2976" href="Overture.Extensionality.html#2900" class="Bound">A</a> <a id="2978" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="2980" href="Overture.Extensionality.html#2962" class="Bound">f</a> <a id="2982" href="Overture.Extensionality.html#2972" class="Bound">x</a> <a id="2984" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="2986" href="Overture.Extensionality.html#2966" class="Bound">g</a> <a id="2988" href="Overture.Extensionality.html#2972" class="Bound">x</a>

 <a id="2992" class="Keyword">infix</a> <a id="2998" class="Number">0</a> <a id="3000" href="Overture.Extensionality.html#2918" class="Function Operator">_∼_</a>

<a id="3005" class="Keyword">open</a> <a id="3010" class="Keyword">import</a> <a id="3017" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3026" class="Keyword">using</a> <a id="3032" class="Symbol">(</a><a id="3033" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="3036" class="Symbol">)</a> <a id="3038" class="Keyword">public</a>

</pre>

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal; that is, for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In type theory this principle is represented by the types `funext` (for nondependent functions) and `dfunext` (for dependent functions)~(\cite[\S2.9]{HoTT}).  For example, the latter is defined as follows.

<pre class="Agda">

<a id="3446" class="Keyword">module</a> <a id="hide-funext"></a><a id="3453" href="Overture.Extensionality.html#3453" class="Module">hide-funext</a> <a id="3465" class="Keyword">where</a>

 <a id="hide-funext.dfunext"></a><a id="3473" href="Overture.Extensionality.html#3473" class="Function">dfunext</a> <a id="3481" class="Symbol">:</a> <a id="3483" class="Symbol">∀</a> <a id="3485" href="Overture.Extensionality.html#3485" class="Bound">𝓤</a> <a id="3487" href="Overture.Extensionality.html#3487" class="Bound">𝓦</a> <a id="3489" class="Symbol">→</a> <a id="3491" href="Overture.Extensionality.html#3485" class="Bound">𝓤</a> <a id="3493" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3495" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3497" href="Overture.Extensionality.html#3487" class="Bound">𝓦</a> <a id="3499" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3501" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3504" href="Overture.Extensionality.html#3473" class="Function">dfunext</a> <a id="3512" href="Overture.Extensionality.html#3512" class="Bound">𝓤</a> <a id="3514" href="Overture.Extensionality.html#3514" class="Bound">𝓦</a> <a id="3516" class="Symbol">=</a> <a id="3518" class="Symbol">{</a><a id="3519" href="Overture.Extensionality.html#3519" class="Bound">A</a> <a id="3521" class="Symbol">:</a> <a id="3523" href="Overture.Extensionality.html#3512" class="Bound">𝓤</a> <a id="3525" href="Universes.html#403" class="Function Operator">̇</a> <a id="3527" class="Symbol">}{</a><a id="3529" href="Overture.Extensionality.html#3529" class="Bound">B</a> <a id="3531" class="Symbol">:</a> <a id="3533" href="Overture.Extensionality.html#3519" class="Bound">A</a> <a id="3535" class="Symbol">→</a> <a id="3537" href="Overture.Extensionality.html#3514" class="Bound">𝓦</a> <a id="3539" href="Universes.html#403" class="Function Operator">̇</a> <a id="3541" class="Symbol">}{</a><a id="3543" href="Overture.Extensionality.html#3543" class="Bound">f</a> <a id="3545" href="Overture.Extensionality.html#3545" class="Bound">g</a> <a id="3547" class="Symbol">:</a> <a id="3549" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3551" href="Overture.Extensionality.html#3551" class="Bound">x</a> <a id="3553" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="3555" href="Overture.Extensionality.html#3519" class="Bound">A</a> <a id="3557" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="3559" href="Overture.Extensionality.html#3529" class="Bound">B</a> <a id="3561" href="Overture.Extensionality.html#3551" class="Bound">x</a><a id="3562" class="Symbol">}</a> <a id="3564" class="Symbol">→</a>  <a id="3567" href="Overture.Extensionality.html#3543" class="Bound">f</a> <a id="3569" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3571" href="Overture.Extensionality.html#3545" class="Bound">g</a>  <a id="3574" class="Symbol">→</a>  <a id="3577" href="Overture.Extensionality.html#3543" class="Bound">f</a> <a id="3579" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3581" href="Overture.Extensionality.html#3545" class="Bound">g</a>

</pre>

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="4367" class="Keyword">open</a> <a id="4372" class="Keyword">import</a> <a id="4379" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="4406" class="Keyword">using</a> <a id="4412" class="Symbol">(</a><a id="4413" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="4419" class="Symbol">;</a> <a id="4421" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="4428" class="Symbol">)</a> <a id="4430" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates.<sup>[4](Overture.Extensionality.html#fn4)</sup>

The next type defines the converse of function extensionality (cf. `cong-app` in [Overture.Equality][] and (2.9.2) in the [HoTT Book][]).

<pre class="Agda">

<a id="happly"></a><a id="5468" href="Overture.Extensionality.html#5468" class="Function">happly</a> <a id="5475" class="Symbol">:</a> <a id="5477" class="Symbol">{</a><a id="5478" href="Overture.Extensionality.html#5478" class="Bound">A</a> <a id="5480" class="Symbol">:</a> <a id="5482" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5484" href="Universes.html#403" class="Function Operator">̇</a> <a id="5486" class="Symbol">}{</a><a id="5488" href="Overture.Extensionality.html#5488" class="Bound">B</a> <a id="5490" class="Symbol">:</a> <a id="5492" href="Overture.Extensionality.html#5478" class="Bound">A</a> <a id="5494" class="Symbol">→</a> <a id="5496" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5498" href="Universes.html#403" class="Function Operator">̇</a> <a id="5500" class="Symbol">}{</a><a id="5502" href="Overture.Extensionality.html#5502" class="Bound">f</a> <a id="5504" href="Overture.Extensionality.html#5504" class="Bound">g</a> <a id="5506" class="Symbol">:</a> <a id="5508" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5510" href="Overture.Extensionality.html#5488" class="Bound">B</a><a id="5511" class="Symbol">}</a> <a id="5513" class="Symbol">→</a> <a id="5515" href="Overture.Extensionality.html#5502" class="Bound">f</a> <a id="5517" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5519" href="Overture.Extensionality.html#5504" class="Bound">g</a> <a id="5521" class="Symbol">→</a> <a id="5523" href="Overture.Extensionality.html#5502" class="Bound">f</a> <a id="5525" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5527" href="Overture.Extensionality.html#5504" class="Bound">g</a>
<a id="5529" href="Overture.Extensionality.html#5468" class="Function">happly</a> <a id="5536" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5541" class="Symbol">_</a> <a id="5543" class="Symbol">=</a> <a id="5545" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions by comparing the definitions of `dfunext` and `happly`. In the definition of `dfunext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `dfunext` is an assertion (which may or may not hold). In the definition of `happly`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `happly` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `dfunext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : dfunext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

<pre class="Agda">

<a id="7490" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="7497" href="Overture.Extensionality.html#7497" class="Module">hide-tt-defs</a> <a id="7510" class="Symbol">{</a><a id="7511" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7513" class="Symbol">:</a> <a id="7515" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7523" class="Symbol">}</a> <a id="7525" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="7533" href="Overture.Extensionality.html#7533" class="Function">is-center</a> <a id="7543" class="Symbol">:</a> <a id="7545" class="Symbol">(</a><a id="7546" href="Overture.Extensionality.html#7546" class="Bound">A</a> <a id="7548" class="Symbol">:</a> <a id="7550" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7552" href="Universes.html#403" class="Function Operator">̇</a> <a id="7554" class="Symbol">)</a> <a id="7556" class="Symbol">→</a> <a id="7558" href="Overture.Extensionality.html#7546" class="Bound">A</a> <a id="7560" class="Symbol">→</a> <a id="7562" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7564" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7567" href="Overture.Extensionality.html#7533" class="Function">is-center</a> <a id="7577" href="Overture.Extensionality.html#7577" class="Bound">A</a> <a id="7579" href="Overture.Extensionality.html#7579" class="Bound">c</a> <a id="7581" class="Symbol">=</a> <a id="7583" class="Symbol">(</a><a id="7584" href="Overture.Extensionality.html#7584" class="Bound">x</a> <a id="7586" class="Symbol">:</a> <a id="7588" href="Overture.Extensionality.html#7577" class="Bound">A</a><a id="7589" class="Symbol">)</a> <a id="7591" class="Symbol">→</a> <a id="7593" href="Overture.Extensionality.html#7579" class="Bound">c</a> <a id="7595" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7597" href="Overture.Extensionality.html#7584" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="7601" href="Overture.Extensionality.html#7601" class="Function">is-singleton</a> <a id="7614" class="Symbol">:</a> <a id="7616" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7618" href="Universes.html#403" class="Function Operator">̇</a> <a id="7620" class="Symbol">→</a> <a id="7622" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7624" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7627" href="Overture.Extensionality.html#7601" class="Function">is-singleton</a> <a id="7640" href="Overture.Extensionality.html#7640" class="Bound">A</a> <a id="7642" class="Symbol">=</a> <a id="7644" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="7646" href="Overture.Extensionality.html#7646" class="Bound">c</a> <a id="7648" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="7650" href="Overture.Extensionality.html#7640" class="Bound">A</a> <a id="7652" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="7654" href="Overture.Extensionality.html#7533" class="Function">is-center</a> <a id="7664" href="Overture.Extensionality.html#7640" class="Bound">A</a> <a id="7666" href="Overture.Extensionality.html#7646" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="7670" href="Overture.Extensionality.html#7670" class="Function">is-subsingleton</a> <a id="7686" class="Symbol">:</a> <a id="7688" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7690" href="Universes.html#403" class="Function Operator">̇</a> <a id="7692" class="Symbol">→</a> <a id="7694" href="Overture.Extensionality.html#7511" class="Bound">𝓤</a> <a id="7696" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7699" href="Overture.Extensionality.html#7670" class="Function">is-subsingleton</a> <a id="7715" href="Overture.Extensionality.html#7715" class="Bound">A</a> <a id="7717" class="Symbol">=</a> <a id="7719" class="Symbol">(</a><a id="7720" href="Overture.Extensionality.html#7720" class="Bound">x</a> <a id="7722" href="Overture.Extensionality.html#7722" class="Bound">y</a> <a id="7724" class="Symbol">:</a> <a id="7726" href="Overture.Extensionality.html#7715" class="Bound">A</a><a id="7727" class="Symbol">)</a> <a id="7729" class="Symbol">→</a> <a id="7731" href="Overture.Extensionality.html#7720" class="Bound">x</a> <a id="7733" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="7735" href="Overture.Extensionality.html#7722" class="Bound">y</a>

<a id="7738" class="Keyword">open</a> <a id="7743" class="Keyword">import</a> <a id="7750" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="7763" class="Keyword">using</a> <a id="7769" class="Symbol">(</a><a id="7770" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="7779" class="Symbol">;</a> <a id="7781" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="7793" class="Symbol">;</a> <a id="7795" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="7810" class="Symbol">)</a> <a id="7812" class="Keyword">public</a>

</pre>


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="8229" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="8236" href="Overture.Extensionality.html#8236" class="Module">hide-tt-defs&#39;</a> <a id="8250" class="Symbol">{</a><a id="8251" href="Overture.Extensionality.html#8251" class="Bound">𝓤</a> <a id="8253" href="Overture.Extensionality.html#8253" class="Bound">𝓦</a> <a id="8255" class="Symbol">:</a> <a id="8257" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8265" class="Symbol">}</a> <a id="8267" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="8275" href="Overture.Extensionality.html#8275" class="Function">fiber</a> <a id="8281" class="Symbol">:</a> <a id="8283" class="Symbol">{</a><a id="8284" href="Overture.Extensionality.html#8284" class="Bound">A</a> <a id="8286" class="Symbol">:</a> <a id="8288" href="Overture.Extensionality.html#8251" class="Bound">𝓤</a> <a id="8290" href="Universes.html#403" class="Function Operator">̇</a> <a id="8292" class="Symbol">}</a> <a id="8294" class="Symbol">{</a><a id="8295" href="Overture.Extensionality.html#8295" class="Bound">B</a> <a id="8297" class="Symbol">:</a> <a id="8299" href="Overture.Extensionality.html#8253" class="Bound">𝓦</a> <a id="8301" href="Universes.html#403" class="Function Operator">̇</a> <a id="8303" class="Symbol">}</a> <a id="8305" class="Symbol">(</a><a id="8306" href="Overture.Extensionality.html#8306" class="Bound">f</a> <a id="8308" class="Symbol">:</a> <a id="8310" href="Overture.Extensionality.html#8284" class="Bound">A</a> <a id="8312" class="Symbol">→</a> <a id="8314" href="Overture.Extensionality.html#8295" class="Bound">B</a><a id="8315" class="Symbol">)</a> <a id="8317" class="Symbol">→</a> <a id="8319" href="Overture.Extensionality.html#8295" class="Bound">B</a> <a id="8321" class="Symbol">→</a> <a id="8323" href="Overture.Extensionality.html#8251" class="Bound">𝓤</a> <a id="8325" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8327" href="Overture.Extensionality.html#8253" class="Bound">𝓦</a> <a id="8329" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8332" href="Overture.Extensionality.html#8275" class="Function">fiber</a> <a id="8338" class="Symbol">{</a><a id="8339" href="Overture.Extensionality.html#8339" class="Bound">A</a><a id="8340" class="Symbol">}</a> <a id="8342" href="Overture.Extensionality.html#8342" class="Bound">f</a> <a id="8344" href="Overture.Extensionality.html#8344" class="Bound">y</a> <a id="8346" class="Symbol">=</a> <a id="8348" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8350" href="Overture.Extensionality.html#8350" class="Bound">x</a> <a id="8352" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8354" href="Overture.Extensionality.html#8339" class="Bound">A</a> <a id="8356" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8358" href="Overture.Extensionality.html#8342" class="Bound">f</a> <a id="8360" href="Overture.Extensionality.html#8350" class="Bound">x</a> <a id="8362" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8364" href="Overture.Extensionality.html#8344" class="Bound">y</a>

</pre>

A function is called an *equivalence* if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="8470" href="Overture.Extensionality.html#8470" class="Function">is-equiv</a> <a id="8479" class="Symbol">:</a> <a id="8481" class="Symbol">{</a><a id="8482" href="Overture.Extensionality.html#8482" class="Bound">A</a> <a id="8484" class="Symbol">:</a> <a id="8486" href="Overture.Extensionality.html#8251" class="Bound">𝓤</a> <a id="8488" href="Universes.html#403" class="Function Operator">̇</a> <a id="8490" class="Symbol">}</a> <a id="8492" class="Symbol">{</a><a id="8493" href="Overture.Extensionality.html#8493" class="Bound">B</a> <a id="8495" class="Symbol">:</a> <a id="8497" href="Overture.Extensionality.html#8253" class="Bound">𝓦</a> <a id="8499" href="Universes.html#403" class="Function Operator">̇</a> <a id="8501" class="Symbol">}</a> <a id="8503" class="Symbol">→</a> <a id="8505" class="Symbol">(</a><a id="8506" href="Overture.Extensionality.html#8482" class="Bound">A</a> <a id="8508" class="Symbol">→</a> <a id="8510" href="Overture.Extensionality.html#8493" class="Bound">B</a><a id="8511" class="Symbol">)</a> <a id="8513" class="Symbol">→</a> <a id="8515" href="Overture.Extensionality.html#8251" class="Bound">𝓤</a> <a id="8517" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8519" href="Overture.Extensionality.html#8253" class="Bound">𝓦</a> <a id="8521" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8524" href="Overture.Extensionality.html#8470" class="Function">is-equiv</a> <a id="8533" href="Overture.Extensionality.html#8533" class="Bound">f</a> <a id="8535" class="Symbol">=</a> <a id="8537" class="Symbol">∀</a> <a id="8539" href="Overture.Extensionality.html#8539" class="Bound">y</a> <a id="8541" class="Symbol">→</a> <a id="8543" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="8556" class="Symbol">(</a><a id="8557" href="Overture.Extensionality.html#8275" class="Function">fiber</a> <a id="8563" href="Overture.Extensionality.html#8533" class="Bound">f</a> <a id="8565" href="Overture.Extensionality.html#8539" class="Bound">y</a><a id="8566" class="Symbol">)</a>

</pre>

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.

<pre class="Agda">

<a id="8725" class="Keyword">open</a> <a id="8730" class="Keyword">import</a> <a id="8737" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="8754" class="Keyword">using</a> <a id="8760" class="Symbol">(</a><a id="8761" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="8766" class="Symbol">;</a> <a id="8768" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="8776" class="Symbol">)</a> <a id="8778" class="Keyword">public</a>

<a id="8786" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="8793" href="Overture.Extensionality.html#8793" class="Module">hide-hfunext</a> <a id="8806" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="8814" href="Overture.Extensionality.html#8814" class="Function">hfunext</a> <a id="8822" class="Symbol">:</a>  <a id="8825" class="Symbol">∀</a> <a id="8827" href="Overture.Extensionality.html#8827" class="Bound">𝓤</a> <a id="8829" href="Overture.Extensionality.html#8829" class="Bound">𝓦</a> <a id="8831" class="Symbol">→</a> <a id="8833" class="Symbol">(</a><a id="8834" href="Overture.Extensionality.html#8827" class="Bound">𝓤</a> <a id="8836" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8838" href="Overture.Extensionality.html#8829" class="Bound">𝓦</a><a id="8839" class="Symbol">)</a><a id="8840" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="8842" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8845" href="Overture.Extensionality.html#8814" class="Function">hfunext</a> <a id="8853" href="Overture.Extensionality.html#8853" class="Bound">𝓤</a> <a id="8855" href="Overture.Extensionality.html#8855" class="Bound">𝓦</a> <a id="8857" class="Symbol">=</a> <a id="8859" class="Symbol">{</a><a id="8860" href="Overture.Extensionality.html#8860" class="Bound">A</a> <a id="8862" class="Symbol">:</a> <a id="8864" href="Overture.Extensionality.html#8853" class="Bound">𝓤</a> <a id="8866" href="Universes.html#403" class="Function Operator">̇</a><a id="8867" class="Symbol">}{</a><a id="8869" href="Overture.Extensionality.html#8869" class="Bound">B</a> <a id="8871" class="Symbol">:</a> <a id="8873" href="Overture.Extensionality.html#8860" class="Bound">A</a> <a id="8875" class="Symbol">→</a> <a id="8877" href="Overture.Extensionality.html#8855" class="Bound">𝓦</a> <a id="8879" href="Universes.html#403" class="Function Operator">̇</a><a id="8880" class="Symbol">}</a> <a id="8882" class="Symbol">(</a><a id="8883" href="Overture.Extensionality.html#8883" class="Bound">f</a> <a id="8885" href="Overture.Extensionality.html#8885" class="Bound">g</a> <a id="8887" class="Symbol">:</a> <a id="8889" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8891" href="Overture.Extensionality.html#8869" class="Bound">B</a><a id="8892" class="Symbol">)</a> <a id="8894" class="Symbol">→</a> <a id="8896" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="8905" class="Symbol">(</a><a id="8906" href="Overture.Extensionality.html#5468" class="Function">happly</a><a id="8912" class="Symbol">{</a><a id="8913" class="Argument">f</a> <a id="8915" class="Symbol">=</a> <a id="8917" href="Overture.Extensionality.html#8883" class="Bound">f</a><a id="8918" class="Symbol">}{</a><a id="8920" href="Overture.Extensionality.html#8885" class="Bound">g</a><a id="8921" class="Symbol">})</a>

<a id="8925" class="Keyword">open</a> <a id="8930" class="Keyword">import</a> <a id="8937" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="8964" class="Keyword">using</a> <a id="8970" class="Symbol">(</a><a id="8971" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8978" class="Symbol">)</a> <a id="8980" class="Keyword">public</a>

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
