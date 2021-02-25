---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  If you're already familiar with function extensionality, you may want to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : X → Y` are equal?

Suppose f and g are defined on X = ℤ (the integers) as follows: f x := x + 2 and g x := ((2 * x) - 8)/2 + 6.  Would you say that f and g are equal?

If you know a little bit of basic algebra, then you probably can't resist the urge to reduce g to the form x + 2 and proclaim that f and g are, indeed, equal.  And you would be right, at least in middle school, and the discussion would end there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions f and g above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves, at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions f and g both of which take a list as input and produce as output a correctly sorted version of that list?  Are the functions the same?  What if f were defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while g used [quick sort](https://en.wikipedia.org/wiki/Quicksort).  I think most of us would then agree that such f and g are not equal.

In each of the examples above, it is common to say that the two functions f and g are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same (external) output when given the same input, but f and g not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their (internal) definitions differ.

In this module, we describe types (mostly imported from the [Type Topology][] library) that manifest this notion of *extensional equality of functions*, or *function extensionality*.

<pre class="Agda">

<a id="2457" class="Symbol">{-#</a> <a id="2461" class="Keyword">OPTIONS</a> <a id="2469" class="Pragma">--without-K</a> <a id="2481" class="Pragma">--exact-split</a> <a id="2495" class="Pragma">--safe</a> <a id="2502" class="Symbol">#-}</a>

<a id="2507" class="Keyword">module</a> <a id="2514" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="2537" class="Keyword">where</a>

<a id="2544" class="Keyword">open</a> <a id="2549" class="Keyword">import</a> <a id="2556" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a> <a id="2573" class="Keyword">public</a>

</pre>


#### <a id="function-extensionality">Function extensionality</a>

As explained above, a natural notion of function equality, sometimes called *point-wise equality*, is also known as *extensional equality* and is defined as follows: f and g are *extensionally equal* provided ∀ x → f x ≡ g x.  Here is how this notion of equality is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="2995" class="Keyword">open</a> <a id="3000" class="Keyword">import</a> <a id="3007" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3016" class="Keyword">using</a> <a id="3022" class="Symbol">(</a><a id="3023" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="3024" class="Symbol">)</a> <a id="3026" class="Keyword">public</a>

<a id="3034" class="Keyword">module</a> <a id="hide"></a><a id="3041" href="Prelude.Extensionality.html#3041" class="Module">hide</a> <a id="3046" class="Keyword">where</a>

 <a id="hide._∼_"></a><a id="3054" href="Prelude.Extensionality.html#3054" class="Function Operator">_∼_</a> <a id="3058" class="Symbol">:</a> <a id="3060" class="Symbol">{</a><a id="3061" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3063" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3065" class="Symbol">:</a> <a id="3067" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3075" class="Symbol">}{</a><a id="3077" href="Prelude.Extensionality.html#3077" class="Bound">X</a> <a id="3079" class="Symbol">:</a> <a id="3081" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3083" href="Universes.html#403" class="Function Operator">̇</a> <a id="3085" class="Symbol">}</a> <a id="3087" class="Symbol">{</a><a id="3088" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3090" class="Symbol">:</a> <a id="3092" href="Prelude.Extensionality.html#3077" class="Bound">X</a> <a id="3094" class="Symbol">→</a> <a id="3096" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3098" href="Universes.html#403" class="Function Operator">̇</a> <a id="3100" class="Symbol">}</a> <a id="3102" class="Symbol">→</a> <a id="3104" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3106" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3108" class="Symbol">→</a> <a id="3110" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3112" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3114" class="Symbol">→</a> <a id="3116" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3118" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3120" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3122" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3125" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3127" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="3129" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3131" class="Symbol">=</a> <a id="3133" class="Symbol">∀</a> <a id="3135" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3137" class="Symbol">→</a> <a id="3139" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3141" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3143" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3145" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3147" href="Prelude.Extensionality.html#3135" class="Bound">x</a>

 <a id="3151" class="Keyword">infix</a> <a id="3157" class="Number">0</a> <a id="3159" href="Prelude.Extensionality.html#3054" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="3911" href="Prelude.Extensionality.html#3911" class="Function">funext</a> <a id="3918" class="Symbol">:</a> <a id="3920" class="Symbol">∀</a> <a id="3922" href="Prelude.Extensionality.html#3922" class="Bound">𝓤</a> <a id="3924" href="Prelude.Extensionality.html#3924" class="Bound">𝓦</a>  <a id="3927" class="Symbol">→</a> <a id="3929" href="Prelude.Extensionality.html#3922" class="Bound">𝓤</a> <a id="3931" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3933" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3935" href="Prelude.Extensionality.html#3924" class="Bound">𝓦</a> <a id="3937" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3939" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3942" href="Prelude.Extensionality.html#3911" class="Function">funext</a> <a id="3949" href="Prelude.Extensionality.html#3949" class="Bound">𝓤</a> <a id="3951" href="Prelude.Extensionality.html#3951" class="Bound">𝓦</a> <a id="3953" class="Symbol">=</a> <a id="3955" class="Symbol">{</a><a id="3956" href="Prelude.Extensionality.html#3956" class="Bound">A</a> <a id="3958" class="Symbol">:</a> <a id="3960" href="Prelude.Extensionality.html#3949" class="Bound">𝓤</a> <a id="3962" href="Universes.html#403" class="Function Operator">̇</a> <a id="3964" class="Symbol">}</a> <a id="3966" class="Symbol">{</a><a id="3967" href="Prelude.Extensionality.html#3967" class="Bound">B</a> <a id="3969" class="Symbol">:</a> <a id="3971" href="Prelude.Extensionality.html#3951" class="Bound">𝓦</a> <a id="3973" href="Universes.html#403" class="Function Operator">̇</a> <a id="3975" class="Symbol">}</a> <a id="3977" class="Symbol">{</a><a id="3978" href="Prelude.Extensionality.html#3978" class="Bound">f</a> <a id="3980" href="Prelude.Extensionality.html#3980" class="Bound">g</a> <a id="3982" class="Symbol">:</a> <a id="3984" href="Prelude.Extensionality.html#3956" class="Bound">A</a> <a id="3986" class="Symbol">→</a> <a id="3988" href="Prelude.Extensionality.html#3967" class="Bound">B</a><a id="3989" class="Symbol">}</a> <a id="3991" class="Symbol">→</a> <a id="3993" href="Prelude.Extensionality.html#3978" class="Bound">f</a> <a id="3995" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="3997" href="Prelude.Extensionality.html#3980" class="Bound">g</a> <a id="3999" class="Symbol">→</a> <a id="4001" href="Prelude.Extensionality.html#3978" class="Bound">f</a> <a id="4003" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4005" href="Prelude.Extensionality.html#3980" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4193" href="Prelude.Extensionality.html#4193" class="Function">dfunext</a> <a id="4201" class="Symbol">:</a> <a id="4203" class="Symbol">∀</a> <a id="4205" href="Prelude.Extensionality.html#4205" class="Bound">𝓤</a> <a id="4207" href="Prelude.Extensionality.html#4207" class="Bound">𝓦</a> <a id="4209" class="Symbol">→</a> <a id="4211" href="Prelude.Extensionality.html#4205" class="Bound">𝓤</a> <a id="4213" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4215" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4217" href="Prelude.Extensionality.html#4207" class="Bound">𝓦</a> <a id="4219" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4221" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4224" href="Prelude.Extensionality.html#4193" class="Function">dfunext</a> <a id="4232" href="Prelude.Extensionality.html#4232" class="Bound">𝓤</a> <a id="4234" href="Prelude.Extensionality.html#4234" class="Bound">𝓦</a> <a id="4236" class="Symbol">=</a> <a id="4238" class="Symbol">{</a><a id="4239" href="Prelude.Extensionality.html#4239" class="Bound">A</a> <a id="4241" class="Symbol">:</a> <a id="4243" href="Prelude.Extensionality.html#4232" class="Bound">𝓤</a> <a id="4245" href="Universes.html#403" class="Function Operator">̇</a> <a id="4247" class="Symbol">}{</a><a id="4249" href="Prelude.Extensionality.html#4249" class="Bound">B</a> <a id="4251" class="Symbol">:</a> <a id="4253" href="Prelude.Extensionality.html#4239" class="Bound">A</a> <a id="4255" class="Symbol">→</a> <a id="4257" href="Prelude.Extensionality.html#4234" class="Bound">𝓦</a> <a id="4259" href="Universes.html#403" class="Function Operator">̇</a> <a id="4261" class="Symbol">}{</a><a id="4263" href="Prelude.Extensionality.html#4263" class="Bound">f</a> <a id="4265" href="Prelude.Extensionality.html#4265" class="Bound">g</a> <a id="4267" class="Symbol">:</a> <a id="4269" class="Symbol">∀(</a><a id="4271" href="Prelude.Extensionality.html#4271" class="Bound">x</a> <a id="4273" class="Symbol">:</a> <a id="4275" href="Prelude.Extensionality.html#4239" class="Bound">A</a><a id="4276" class="Symbol">)</a> <a id="4278" class="Symbol">→</a> <a id="4280" href="Prelude.Extensionality.html#4249" class="Bound">B</a> <a id="4282" href="Prelude.Extensionality.html#4271" class="Bound">x</a><a id="4283" class="Symbol">}</a> <a id="4285" class="Symbol">→</a>  <a id="4288" href="Prelude.Extensionality.html#4263" class="Bound">f</a> <a id="4290" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4292" href="Prelude.Extensionality.html#4265" class="Bound">g</a>  <a id="4295" class="Symbol">→</a>  <a id="4298" href="Prelude.Extensionality.html#4263" class="Bound">f</a> <a id="4300" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4302" href="Prelude.Extensionality.html#4265" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="4874" href="Prelude.Extensionality.html#4874" class="Function">global-funext</a> <a id="4888" class="Symbol">:</a> <a id="4890" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4894" href="Prelude.Extensionality.html#4874" class="Function">global-funext</a> <a id="4908" class="Symbol">=</a> <a id="4910" class="Symbol">∀</a>  <a id="4913" class="Symbol">{</a><a id="4914" href="Prelude.Extensionality.html#4914" class="Bound">𝓤</a> <a id="4916" href="Prelude.Extensionality.html#4916" class="Bound">𝓥</a><a id="4917" class="Symbol">}</a> <a id="4919" class="Symbol">→</a> <a id="4921" href="Prelude.Extensionality.html#3911" class="Function">funext</a> <a id="4928" href="Prelude.Extensionality.html#4914" class="Bound">𝓤</a> <a id="4930" href="Prelude.Extensionality.html#4916" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="4934" href="Prelude.Extensionality.html#4934" class="Function">global-dfunext</a> <a id="4949" class="Symbol">:</a> <a id="4951" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4955" href="Prelude.Extensionality.html#4934" class="Function">global-dfunext</a> <a id="4970" class="Symbol">=</a> <a id="4972" class="Symbol">∀</a> <a id="4974" class="Symbol">{</a><a id="4975" href="Prelude.Extensionality.html#4975" class="Bound">𝓤</a> <a id="4977" href="Prelude.Extensionality.html#4977" class="Bound">𝓥</a><a id="4978" class="Symbol">}</a> <a id="4980" class="Symbol">→</a> <a id="4982" href="Prelude.Extensionality.html#3911" class="Function">funext</a> <a id="4989" href="Prelude.Extensionality.html#4975" class="Bound">𝓤</a> <a id="4991" href="Prelude.Extensionality.html#4977" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5187" href="Prelude.Extensionality.html#5187" class="Function">extensionality-lemma</a> <a id="5208" class="Symbol">:</a> <a id="5210" class="Symbol">{</a><a id="5211" href="Prelude.Extensionality.html#5211" class="Bound">𝓘</a> <a id="5213" href="Prelude.Extensionality.html#5213" class="Bound">𝓤</a> <a id="5215" href="Prelude.Extensionality.html#5215" class="Bound">𝓥</a> <a id="5217" href="Prelude.Extensionality.html#5217" class="Bound">𝓣</a> <a id="5219" class="Symbol">:</a> <a id="5221" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5229" class="Symbol">}{</a><a id="5231" href="Prelude.Extensionality.html#5231" class="Bound">I</a> <a id="5233" class="Symbol">:</a> <a id="5235" href="Prelude.Extensionality.html#5211" class="Bound">𝓘</a> <a id="5237" href="Universes.html#403" class="Function Operator">̇</a> <a id="5239" class="Symbol">}{</a><a id="5241" href="Prelude.Extensionality.html#5241" class="Bound">X</a> <a id="5243" class="Symbol">:</a> <a id="5245" href="Prelude.Extensionality.html#5213" class="Bound">𝓤</a> <a id="5247" href="Universes.html#403" class="Function Operator">̇</a> <a id="5249" class="Symbol">}{</a><a id="5251" href="Prelude.Extensionality.html#5251" class="Bound">A</a> <a id="5253" class="Symbol">:</a> <a id="5255" href="Prelude.Extensionality.html#5231" class="Bound">I</a> <a id="5257" class="Symbol">→</a> <a id="5259" href="Prelude.Extensionality.html#5215" class="Bound">𝓥</a> <a id="5261" href="Universes.html#403" class="Function Operator">̇</a> <a id="5263" class="Symbol">}</a>
                       <a id="5288" class="Symbol">(</a><a id="5289" href="Prelude.Extensionality.html#5289" class="Bound">p</a> <a id="5291" href="Prelude.Extensionality.html#5291" class="Bound">q</a> <a id="5293" class="Symbol">:</a> <a id="5295" class="Symbol">(</a><a id="5296" href="Prelude.Extensionality.html#5296" class="Bound">i</a> <a id="5298" class="Symbol">:</a> <a id="5300" href="Prelude.Extensionality.html#5231" class="Bound">I</a><a id="5301" class="Symbol">)</a> <a id="5303" class="Symbol">→</a> <a id="5305" class="Symbol">(</a><a id="5306" href="Prelude.Extensionality.html#5241" class="Bound">X</a> <a id="5308" class="Symbol">→</a> <a id="5310" href="Prelude.Extensionality.html#5251" class="Bound">A</a> <a id="5312" href="Prelude.Extensionality.html#5296" class="Bound">i</a><a id="5313" class="Symbol">)</a> <a id="5315" class="Symbol">→</a> <a id="5317" href="Prelude.Extensionality.html#5217" class="Bound">𝓣</a> <a id="5319" href="Universes.html#403" class="Function Operator">̇</a> <a id="5321" class="Symbol">)(</a><a id="5323" href="Prelude.Extensionality.html#5323" class="Bound">args</a> <a id="5328" class="Symbol">:</a> <a id="5330" href="Prelude.Extensionality.html#5241" class="Bound">X</a> <a id="5332" class="Symbol">→</a> <a id="5334" class="Symbol">(</a><a id="5335" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5337" href="Prelude.Extensionality.html#5251" class="Bound">A</a><a id="5338" class="Symbol">))</a>
 <a id="5342" class="Symbol">→</a>                     <a id="5364" href="Prelude.Extensionality.html#5289" class="Bound">p</a> <a id="5366" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5368" href="Prelude.Extensionality.html#5291" class="Bound">q</a>
                       <a id="5393" class="Comment">-------------------------------------------------------------</a>
 <a id="5456" class="Symbol">→</a>                     <a id="5478" class="Symbol">(λ</a> <a id="5481" href="Prelude.Extensionality.html#5481" class="Bound">i</a> <a id="5483" class="Symbol">→</a> <a id="5485" class="Symbol">(</a><a id="5486" href="Prelude.Extensionality.html#5289" class="Bound">p</a> <a id="5488" href="Prelude.Extensionality.html#5481" class="Bound">i</a><a id="5489" class="Symbol">)(λ</a> <a id="5493" href="Prelude.Extensionality.html#5493" class="Bound">x</a> <a id="5495" class="Symbol">→</a> <a id="5497" href="Prelude.Extensionality.html#5323" class="Bound">args</a> <a id="5502" href="Prelude.Extensionality.html#5493" class="Bound">x</a> <a id="5504" href="Prelude.Extensionality.html#5481" class="Bound">i</a><a id="5505" class="Symbol">))</a> <a id="5508" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5510" class="Symbol">(λ</a> <a id="5513" href="Prelude.Extensionality.html#5513" class="Bound">i</a> <a id="5515" class="Symbol">→</a> <a id="5517" class="Symbol">(</a><a id="5518" href="Prelude.Extensionality.html#5291" class="Bound">q</a> <a id="5520" href="Prelude.Extensionality.html#5513" class="Bound">i</a><a id="5521" class="Symbol">)(λ</a> <a id="5525" href="Prelude.Extensionality.html#5525" class="Bound">x</a> <a id="5527" class="Symbol">→</a> <a id="5529" href="Prelude.Extensionality.html#5323" class="Bound">args</a> <a id="5534" href="Prelude.Extensionality.html#5525" class="Bound">x</a> <a id="5536" href="Prelude.Extensionality.html#5513" class="Bound">i</a><a id="5537" class="Symbol">))</a>

<a id="5541" href="Prelude.Extensionality.html#5187" class="Function">extensionality-lemma</a> <a id="5562" href="Prelude.Extensionality.html#5562" class="Bound">p</a> <a id="5564" href="Prelude.Extensionality.html#5564" class="Bound">q</a> <a id="5566" href="Prelude.Extensionality.html#5566" class="Bound">args</a> <a id="5571" href="Prelude.Extensionality.html#5571" class="Bound">p≡q</a> <a id="5575" class="Symbol">=</a> <a id="5577" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5580" class="Symbol">(λ</a> <a id="5583" href="Prelude.Extensionality.html#5583" class="Bound">-</a> <a id="5585" class="Symbol">→</a> <a id="5587" class="Symbol">λ</a> <a id="5589" href="Prelude.Extensionality.html#5589" class="Bound">i</a> <a id="5591" class="Symbol">→</a> <a id="5593" class="Symbol">(</a><a id="5594" href="Prelude.Extensionality.html#5583" class="Bound">-</a> <a id="5596" href="Prelude.Extensionality.html#5589" class="Bound">i</a><a id="5597" class="Symbol">)</a> <a id="5599" class="Symbol">(λ</a> <a id="5602" href="Prelude.Extensionality.html#5602" class="Bound">x</a> <a id="5604" class="Symbol">→</a> <a id="5606" href="Prelude.Extensionality.html#5566" class="Bound">args</a> <a id="5611" href="Prelude.Extensionality.html#5602" class="Bound">x</a> <a id="5613" href="Prelude.Extensionality.html#5589" class="Bound">i</a><a id="5614" class="Symbol">))</a> <a id="5617" href="Prelude.Extensionality.html#5571" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5768" class="Keyword">open</a> <a id="5773" class="Keyword">import</a> <a id="5780" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5789" class="Keyword">using</a> <a id="5795" class="Symbol">(</a><a id="5796" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5799" class="Symbol">)</a>

<a id="extfun"></a><a id="5802" href="Prelude.Extensionality.html#5802" class="Function">extfun</a> <a id="5809" class="Symbol">:</a> <a id="5811" class="Symbol">{</a><a id="5812" href="Prelude.Extensionality.html#5812" class="Bound">𝓤</a> <a id="5814" href="Prelude.Extensionality.html#5814" class="Bound">𝓦</a> <a id="5816" class="Symbol">:</a> <a id="5818" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5826" class="Symbol">}{</a><a id="5828" href="Prelude.Extensionality.html#5828" class="Bound">A</a> <a id="5830" class="Symbol">:</a> <a id="5832" href="Prelude.Extensionality.html#5812" class="Bound">𝓤</a> <a id="5834" href="Universes.html#403" class="Function Operator">̇</a><a id="5835" class="Symbol">}{</a><a id="5837" href="Prelude.Extensionality.html#5837" class="Bound">B</a> <a id="5839" class="Symbol">:</a> <a id="5841" href="Prelude.Extensionality.html#5814" class="Bound">𝓦</a> <a id="5843" href="Universes.html#403" class="Function Operator">̇</a><a id="5844" class="Symbol">}{</a><a id="5846" href="Prelude.Extensionality.html#5846" class="Bound">f</a> <a id="5848" href="Prelude.Extensionality.html#5848" class="Bound">g</a> <a id="5850" class="Symbol">:</a> <a id="5852" href="Prelude.Extensionality.html#5828" class="Bound">A</a> <a id="5854" class="Symbol">→</a> <a id="5856" href="Prelude.Extensionality.html#5837" class="Bound">B</a><a id="5857" class="Symbol">}</a> <a id="5859" class="Symbol">→</a> <a id="5861" href="Prelude.Extensionality.html#5846" class="Bound">f</a> <a id="5863" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5865" href="Prelude.Extensionality.html#5848" class="Bound">g</a>  <a id="5868" class="Symbol">→</a>  <a id="5871" href="Prelude.Extensionality.html#5846" class="Bound">f</a> <a id="5873" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5875" href="Prelude.Extensionality.html#5848" class="Bound">g</a>
<a id="5877" href="Prelude.Extensionality.html#5802" class="Function">extfun</a> <a id="5884" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5889" class="Symbol">_</a>  <a id="5892" class="Symbol">=</a> <a id="5894" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="5978" href="Prelude.Extensionality.html#5978" class="Function">extdfun</a> <a id="5986" class="Symbol">:</a> <a id="5988" class="Symbol">{</a><a id="5989" href="Prelude.Extensionality.html#5989" class="Bound">𝓤</a> <a id="5991" href="Prelude.Extensionality.html#5991" class="Bound">𝓦</a> <a id="5993" class="Symbol">:</a> <a id="5995" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6003" class="Symbol">}</a> <a id="6005" class="Symbol">{</a><a id="6006" href="Prelude.Extensionality.html#6006" class="Bound">A</a> <a id="6008" class="Symbol">:</a> <a id="6010" href="Prelude.Extensionality.html#5989" class="Bound">𝓤</a> <a id="6012" href="Universes.html#403" class="Function Operator">̇</a> <a id="6014" class="Symbol">}</a> <a id="6016" class="Symbol">{</a><a id="6017" href="Prelude.Extensionality.html#6017" class="Bound">B</a> <a id="6019" class="Symbol">:</a> <a id="6021" href="Prelude.Extensionality.html#6006" class="Bound">A</a> <a id="6023" class="Symbol">→</a> <a id="6025" href="Prelude.Extensionality.html#5991" class="Bound">𝓦</a> <a id="6027" href="Universes.html#403" class="Function Operator">̇</a> <a id="6029" class="Symbol">}</a> <a id="6031" class="Symbol">{</a><a id="6032" href="Prelude.Extensionality.html#6032" class="Bound">f</a> <a id="6034" href="Prelude.Extensionality.html#6034" class="Bound">g</a> <a id="6036" class="Symbol">:</a> <a id="6038" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6040" href="Prelude.Extensionality.html#6017" class="Bound">B</a><a id="6041" class="Symbol">}</a> <a id="6043" class="Symbol">→</a> <a id="6045" href="Prelude.Extensionality.html#6032" class="Bound">f</a> <a id="6047" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6049" href="Prelude.Extensionality.html#6034" class="Bound">g</a> <a id="6051" class="Symbol">→</a> <a id="6053" href="Prelude.Extensionality.html#6032" class="Bound">f</a> <a id="6055" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6057" href="Prelude.Extensionality.html#6034" class="Bound">g</a>
<a id="6059" href="Prelude.Extensionality.html#5978" class="Function">extdfun</a> <a id="6067" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6072" class="Symbol">_</a> <a id="6074" class="Symbol">=</a> <a id="6076" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
