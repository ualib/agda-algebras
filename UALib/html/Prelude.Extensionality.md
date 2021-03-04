---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="316" class="Symbol">{-#</a> <a id="320" class="Keyword">OPTIONS</a> <a id="328" class="Pragma">--without-K</a> <a id="340" class="Pragma">--exact-split</a> <a id="354" class="Pragma">--safe</a> <a id="361" class="Symbol">#-}</a>

<a id="366" class="Keyword">module</a> <a id="373" href="Prelude.Extensionality.html" class="Module">Prelude.Extensionality</a> <a id="396" class="Keyword">where</a>

<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="432" class="Keyword">public</a>

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

#### <a id="function-extensionality">Function extensionality</a>

As explained above, a natural notion of function equality, sometimes called *point-wise equality*, is also known as *extensional equality* and is defined as follows: f and g are *extensionally equal* provided ∀ x → f x ≡ g x.  Here is how this notion of equality is expressed as a type in the [Type Topology][] library.

<pre class="Agda">

<a id="3030" class="Keyword">module</a> <a id="hide-funext"></a><a id="3037" href="Prelude.Extensionality.html#3037" class="Module">hide-funext</a> <a id="3049" class="Keyword">where</a>

 <a id="hide-funext._∼_"></a><a id="3057" href="Prelude.Extensionality.html#3057" class="Function Operator">_∼_</a> <a id="3061" class="Symbol">:</a> <a id="3063" class="Symbol">{</a><a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3066" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3068" class="Symbol">:</a> <a id="3070" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3078" class="Symbol">}{</a><a id="3080" href="Prelude.Extensionality.html#3080" class="Bound">X</a> <a id="3082" class="Symbol">:</a> <a id="3084" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3086" href="Universes.html#403" class="Function Operator">̇</a> <a id="3088" class="Symbol">}</a> <a id="3090" class="Symbol">{</a><a id="3091" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3093" class="Symbol">:</a> <a id="3095" href="Prelude.Extensionality.html#3080" class="Bound">X</a> <a id="3097" class="Symbol">→</a> <a id="3099" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3101" href="Universes.html#403" class="Function Operator">̇</a> <a id="3103" class="Symbol">}</a> <a id="3105" class="Symbol">→</a> <a id="3107" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3109" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3111" class="Symbol">→</a> <a id="3113" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3115" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3117" class="Symbol">→</a> <a id="3119" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3121" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3123" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3125" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3128" href="Prelude.Extensionality.html#3128" class="Bound">f</a> <a id="3130" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="3132" href="Prelude.Extensionality.html#3132" class="Bound">g</a> <a id="3134" class="Symbol">=</a> <a id="3136" class="Symbol">∀</a> <a id="3138" href="Prelude.Extensionality.html#3138" class="Bound">x</a> <a id="3140" class="Symbol">→</a> <a id="3142" href="Prelude.Extensionality.html#3128" class="Bound">f</a> <a id="3144" href="Prelude.Extensionality.html#3138" class="Bound">x</a> <a id="3146" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="3148" href="Prelude.Extensionality.html#3132" class="Bound">g</a> <a id="3150" href="Prelude.Extensionality.html#3138" class="Bound">x</a>

 <a id="3154" class="Keyword">infix</a> <a id="3160" class="Number">0</a> <a id="3162" href="Prelude.Extensionality.html#3057" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="4034" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4041" class="Symbol">:</a> <a id="4043" class="Symbol">∀</a> <a id="4045" href="Prelude.Extensionality.html#4045" class="Bound">𝓤</a> <a id="4047" href="Prelude.Extensionality.html#4047" class="Bound">𝓦</a>  <a id="4050" class="Symbol">→</a> <a id="4052" href="Prelude.Extensionality.html#4045" class="Bound">𝓤</a> <a id="4054" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4056" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4058" href="Prelude.Extensionality.html#4047" class="Bound">𝓦</a> <a id="4060" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4062" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4065" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4072" href="Prelude.Extensionality.html#4072" class="Bound">𝓤</a> <a id="4074" href="Prelude.Extensionality.html#4074" class="Bound">𝓦</a> <a id="4076" class="Symbol">=</a> <a id="4078" class="Symbol">{</a><a id="4079" href="Prelude.Extensionality.html#4079" class="Bound">A</a> <a id="4081" class="Symbol">:</a> <a id="4083" href="Prelude.Extensionality.html#4072" class="Bound">𝓤</a> <a id="4085" href="Universes.html#403" class="Function Operator">̇</a> <a id="4087" class="Symbol">}</a> <a id="4089" class="Symbol">{</a><a id="4090" href="Prelude.Extensionality.html#4090" class="Bound">B</a> <a id="4092" class="Symbol">:</a> <a id="4094" href="Prelude.Extensionality.html#4074" class="Bound">𝓦</a> <a id="4096" href="Universes.html#403" class="Function Operator">̇</a> <a id="4098" class="Symbol">}</a> <a id="4100" class="Symbol">{</a><a id="4101" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4103" href="Prelude.Extensionality.html#4103" class="Bound">g</a> <a id="4105" class="Symbol">:</a> <a id="4107" href="Prelude.Extensionality.html#4079" class="Bound">A</a> <a id="4109" class="Symbol">→</a> <a id="4111" href="Prelude.Extensionality.html#4090" class="Bound">B</a><a id="4112" class="Symbol">}</a> <a id="4114" class="Symbol">→</a> <a id="4116" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4118" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="4120" href="Prelude.Extensionality.html#4103" class="Bound">g</a> <a id="4122" class="Symbol">→</a> <a id="4124" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4126" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="4128" href="Prelude.Extensionality.html#4103" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="4239" href="Prelude.Extensionality.html#4239" class="Function">dfunext</a> <a id="4247" class="Symbol">:</a> <a id="4249" class="Symbol">∀</a> <a id="4251" href="Prelude.Extensionality.html#4251" class="Bound">𝓤</a> <a id="4253" href="Prelude.Extensionality.html#4253" class="Bound">𝓦</a> <a id="4255" class="Symbol">→</a> <a id="4257" href="Prelude.Extensionality.html#4251" class="Bound">𝓤</a> <a id="4259" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4261" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4263" href="Prelude.Extensionality.html#4253" class="Bound">𝓦</a> <a id="4265" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4267" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4270" href="Prelude.Extensionality.html#4239" class="Function">dfunext</a> <a id="4278" href="Prelude.Extensionality.html#4278" class="Bound">𝓤</a> <a id="4280" href="Prelude.Extensionality.html#4280" class="Bound">𝓦</a> <a id="4282" class="Symbol">=</a> <a id="4284" class="Symbol">{</a><a id="4285" href="Prelude.Extensionality.html#4285" class="Bound">A</a> <a id="4287" class="Symbol">:</a> <a id="4289" href="Prelude.Extensionality.html#4278" class="Bound">𝓤</a> <a id="4291" href="Universes.html#403" class="Function Operator">̇</a> <a id="4293" class="Symbol">}{</a><a id="4295" href="Prelude.Extensionality.html#4295" class="Bound">B</a> <a id="4297" class="Symbol">:</a> <a id="4299" href="Prelude.Extensionality.html#4285" class="Bound">A</a> <a id="4301" class="Symbol">→</a> <a id="4303" href="Prelude.Extensionality.html#4280" class="Bound">𝓦</a> <a id="4305" href="Universes.html#403" class="Function Operator">̇</a> <a id="4307" class="Symbol">}{</a><a id="4309" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4311" href="Prelude.Extensionality.html#4311" class="Bound">g</a> <a id="4313" class="Symbol">:</a> <a id="4315" class="Symbol">∀(</a><a id="4317" href="Prelude.Extensionality.html#4317" class="Bound">x</a> <a id="4319" class="Symbol">:</a> <a id="4321" href="Prelude.Extensionality.html#4285" class="Bound">A</a><a id="4322" class="Symbol">)</a> <a id="4324" class="Symbol">→</a> <a id="4326" href="Prelude.Extensionality.html#4295" class="Bound">B</a> <a id="4328" href="Prelude.Extensionality.html#4317" class="Bound">x</a><a id="4329" class="Symbol">}</a> <a id="4331" class="Symbol">→</a>  <a id="4334" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4336" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="4338" href="Prelude.Extensionality.html#4311" class="Bound">g</a>  <a id="4341" class="Symbol">→</a>  <a id="4344" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4346" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="4348" href="Prelude.Extensionality.html#4311" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="4920" href="Prelude.Extensionality.html#4920" class="Function">global-funext</a> <a id="4934" class="Symbol">:</a> <a id="4936" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4940" href="Prelude.Extensionality.html#4920" class="Function">global-funext</a> <a id="4954" class="Symbol">=</a> <a id="4956" class="Symbol">∀</a>  <a id="4959" class="Symbol">{</a><a id="4960" href="Prelude.Extensionality.html#4960" class="Bound">𝓤</a> <a id="4962" href="Prelude.Extensionality.html#4962" class="Bound">𝓥</a><a id="4963" class="Symbol">}</a> <a id="4965" class="Symbol">→</a> <a id="4967" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4974" href="Prelude.Extensionality.html#4960" class="Bound">𝓤</a> <a id="4976" href="Prelude.Extensionality.html#4962" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="4980" href="Prelude.Extensionality.html#4980" class="Function">global-dfunext</a> <a id="4995" class="Symbol">:</a> <a id="4997" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5001" href="Prelude.Extensionality.html#4980" class="Function">global-dfunext</a> <a id="5016" class="Symbol">=</a> <a id="5018" class="Symbol">∀</a> <a id="5020" class="Symbol">{</a><a id="5021" href="Prelude.Extensionality.html#5021" class="Bound">𝓤</a> <a id="5023" href="Prelude.Extensionality.html#5023" class="Bound">𝓥</a><a id="5024" class="Symbol">}</a> <a id="5026" class="Symbol">→</a> <a id="5028" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="5035" href="Prelude.Extensionality.html#5021" class="Bound">𝓤</a> <a id="5037" href="Prelude.Extensionality.html#5023" class="Bound">𝓥</a>

</pre>

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5497" class="Keyword">open</a> <a id="5502" class="Keyword">import</a> <a id="5509" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5536" class="Keyword">using</a> <a id="5542" class="Symbol">(</a><a id="5543" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5546" class="Symbol">;</a> <a id="5548" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5554" class="Symbol">;</a> <a id="5556" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5563" class="Symbol">)</a> <a id="5565" class="Keyword">public</a>

</pre>


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

<pre class="Agda">

<a id="5894" class="Keyword">open</a> <a id="5899" class="Keyword">import</a> <a id="5906" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5915" class="Keyword">using</a> <a id="5921" class="Symbol">(</a><a id="5922" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5925" class="Symbol">)</a> <a id="5927" class="Keyword">public</a>

<a id="5935" class="Keyword">module</a> <a id="5942" href="Prelude.Extensionality.html#5942" class="Module">_</a> <a id="5944" class="Symbol">{</a><a id="5945" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="5947" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="5949" class="Symbol">:</a> <a id="5951" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5959" class="Symbol">}</a> <a id="5961" class="Keyword">where</a>

 <a id="5969" href="Prelude.Extensionality.html#5969" class="Function">extfun</a> <a id="5976" class="Symbol">:</a> <a id="5978" class="Symbol">{</a><a id="5979" href="Prelude.Extensionality.html#5979" class="Bound">A</a> <a id="5981" class="Symbol">:</a> <a id="5983" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="5985" href="Universes.html#403" class="Function Operator">̇</a><a id="5986" class="Symbol">}{</a><a id="5988" href="Prelude.Extensionality.html#5988" class="Bound">B</a> <a id="5990" class="Symbol">:</a> <a id="5992" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="5994" href="Universes.html#403" class="Function Operator">̇</a><a id="5995" class="Symbol">}{</a><a id="5997" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="5999" href="Prelude.Extensionality.html#5999" class="Bound">g</a> <a id="6001" class="Symbol">:</a> <a id="6003" href="Prelude.Extensionality.html#5979" class="Bound">A</a> <a id="6005" class="Symbol">→</a> <a id="6007" href="Prelude.Extensionality.html#5988" class="Bound">B</a><a id="6008" class="Symbol">}</a> <a id="6010" class="Symbol">→</a> <a id="6012" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="6014" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="6016" href="Prelude.Extensionality.html#5999" class="Bound">g</a>  <a id="6019" class="Symbol">→</a>  <a id="6022" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="6024" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6026" href="Prelude.Extensionality.html#5999" class="Bound">g</a>
 <a id="6029" href="Prelude.Extensionality.html#5969" class="Function">extfun</a> <a id="6036" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6041" class="Symbol">_</a> <a id="6043" class="Symbol">=</a> <a id="6045" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

 <a id="6130" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="6138" class="Symbol">:</a> <a id="6140" class="Symbol">{</a><a id="6141" href="Prelude.Extensionality.html#6141" class="Bound">A</a> <a id="6143" class="Symbol">:</a> <a id="6145" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="6147" href="Universes.html#403" class="Function Operator">̇</a> <a id="6149" class="Symbol">}{</a><a id="6151" href="Prelude.Extensionality.html#6151" class="Bound">B</a> <a id="6153" class="Symbol">:</a> <a id="6155" href="Prelude.Extensionality.html#6141" class="Bound">A</a> <a id="6157" class="Symbol">→</a> <a id="6159" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="6161" href="Universes.html#403" class="Function Operator">̇</a> <a id="6163" class="Symbol">}(</a><a id="6165" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6167" href="Prelude.Extensionality.html#6167" class="Bound">g</a> <a id="6169" class="Symbol">:</a> <a id="6171" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6173" href="Prelude.Extensionality.html#6151" class="Bound">B</a><a id="6174" class="Symbol">)</a> <a id="6176" class="Symbol">→</a> <a id="6178" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6180" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="6182" href="Prelude.Extensionality.html#6167" class="Bound">g</a> <a id="6184" class="Symbol">→</a> <a id="6186" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6188" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6190" href="Prelude.Extensionality.html#6167" class="Bound">g</a>
 <a id="6193" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="6201" class="Symbol">_</a> <a id="6203" class="Symbol">_</a> <a id="6205" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6210" class="Symbol">_</a> <a id="6212" class="Symbol">=</a> <a id="6214" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follow.

<pre class="Agda">

<a id="8115" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8122" href="Prelude.Extensionality.html#8122" class="Module">hide-tt-defs</a> <a id="8135" class="Symbol">{</a><a id="8136" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8138" class="Symbol">:</a> <a id="8140" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8148" class="Symbol">}</a> <a id="8150" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8158" href="Prelude.Extensionality.html#8158" class="Function">is-center</a> <a id="8168" class="Symbol">:</a> <a id="8170" class="Symbol">(</a><a id="8171" href="Prelude.Extensionality.html#8171" class="Bound">X</a> <a id="8173" class="Symbol">:</a> <a id="8175" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8177" href="Universes.html#403" class="Function Operator">̇</a> <a id="8179" class="Symbol">)</a> <a id="8181" class="Symbol">→</a> <a id="8183" href="Prelude.Extensionality.html#8171" class="Bound">X</a> <a id="8185" class="Symbol">→</a> <a id="8187" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8189" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8192" href="Prelude.Extensionality.html#8158" class="Function">is-center</a> <a id="8202" href="Prelude.Extensionality.html#8202" class="Bound">X</a> <a id="8204" href="Prelude.Extensionality.html#8204" class="Bound">c</a> <a id="8206" class="Symbol">=</a> <a id="8208" class="Symbol">(</a><a id="8209" href="Prelude.Extensionality.html#8209" class="Bound">x</a> <a id="8211" class="Symbol">:</a> <a id="8213" href="Prelude.Extensionality.html#8202" class="Bound">X</a><a id="8214" class="Symbol">)</a> <a id="8216" class="Symbol">→</a> <a id="8218" href="Prelude.Extensionality.html#8204" class="Bound">c</a> <a id="8220" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8222" href="Prelude.Extensionality.html#8209" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8226" href="Prelude.Extensionality.html#8226" class="Function">is-singleton</a> <a id="8239" class="Symbol">:</a> <a id="8241" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8243" href="Universes.html#403" class="Function Operator">̇</a> <a id="8245" class="Symbol">→</a> <a id="8247" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8249" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8252" href="Prelude.Extensionality.html#8226" class="Function">is-singleton</a> <a id="8265" href="Prelude.Extensionality.html#8265" class="Bound">X</a> <a id="8267" class="Symbol">=</a> <a id="8269" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8271" href="Prelude.Extensionality.html#8271" class="Bound">c</a> <a id="8273" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8275" href="Prelude.Extensionality.html#8265" class="Bound">X</a> <a id="8277" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8279" href="Prelude.Extensionality.html#8158" class="Function">is-center</a> <a id="8289" href="Prelude.Extensionality.html#8265" class="Bound">X</a> <a id="8291" href="Prelude.Extensionality.html#8271" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8295" href="Prelude.Extensionality.html#8295" class="Function">is-subsingleton</a> <a id="8311" class="Symbol">:</a> <a id="8313" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8315" href="Universes.html#403" class="Function Operator">̇</a> <a id="8317" class="Symbol">→</a> <a id="8319" href="Prelude.Extensionality.html#8136" class="Bound">𝓤</a> <a id="8321" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8324" href="Prelude.Extensionality.html#8295" class="Function">is-subsingleton</a> <a id="8340" href="Prelude.Extensionality.html#8340" class="Bound">X</a> <a id="8342" class="Symbol">=</a> <a id="8344" class="Symbol">(</a><a id="8345" href="Prelude.Extensionality.html#8345" class="Bound">x</a> <a id="8347" href="Prelude.Extensionality.html#8347" class="Bound">y</a> <a id="8349" class="Symbol">:</a> <a id="8351" href="Prelude.Extensionality.html#8340" class="Bound">X</a><a id="8352" class="Symbol">)</a> <a id="8354" class="Symbol">→</a> <a id="8356" href="Prelude.Extensionality.html#8345" class="Bound">x</a> <a id="8358" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="8360" href="Prelude.Extensionality.html#8347" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

<pre class="Agda">

<a id="8653" class="Keyword">open</a> <a id="8658" class="Keyword">import</a> <a id="8665" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8678" class="Keyword">using</a> <a id="8684" class="Symbol">(</a><a id="8685" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8694" class="Symbol">;</a> <a id="8696" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8708" class="Symbol">;</a> <a id="8710" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8725" class="Symbol">)</a> <a id="8727" class="Keyword">public</a>

</pre>


Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9184" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9191" href="Prelude.Extensionality.html#9191" class="Module">hide-tt-defs&#39;</a> <a id="9205" class="Symbol">{</a><a id="9206" href="Prelude.Extensionality.html#9206" class="Bound">𝓤</a> <a id="9208" href="Prelude.Extensionality.html#9208" class="Bound">𝓦</a> <a id="9210" class="Symbol">:</a> <a id="9212" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9220" class="Symbol">}</a> <a id="9222" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9230" href="Prelude.Extensionality.html#9230" class="Function">fiber</a> <a id="9236" class="Symbol">:</a> <a id="9238" class="Symbol">{</a><a id="9239" href="Prelude.Extensionality.html#9239" class="Bound">X</a> <a id="9241" class="Symbol">:</a> <a id="9243" href="Prelude.Extensionality.html#9206" class="Bound">𝓤</a> <a id="9245" href="Universes.html#403" class="Function Operator">̇</a> <a id="9247" class="Symbol">}</a> <a id="9249" class="Symbol">{</a><a id="9250" href="Prelude.Extensionality.html#9250" class="Bound">Y</a> <a id="9252" class="Symbol">:</a> <a id="9254" href="Prelude.Extensionality.html#9208" class="Bound">𝓦</a> <a id="9256" href="Universes.html#403" class="Function Operator">̇</a> <a id="9258" class="Symbol">}</a> <a id="9260" class="Symbol">(</a><a id="9261" href="Prelude.Extensionality.html#9261" class="Bound">f</a> <a id="9263" class="Symbol">:</a> <a id="9265" href="Prelude.Extensionality.html#9239" class="Bound">X</a> <a id="9267" class="Symbol">→</a> <a id="9269" href="Prelude.Extensionality.html#9250" class="Bound">Y</a><a id="9270" class="Symbol">)</a> <a id="9272" class="Symbol">→</a> <a id="9274" href="Prelude.Extensionality.html#9250" class="Bound">Y</a> <a id="9276" class="Symbol">→</a> <a id="9278" href="Prelude.Extensionality.html#9206" class="Bound">𝓤</a> <a id="9280" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9282" href="Prelude.Extensionality.html#9208" class="Bound">𝓦</a> <a id="9284" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9287" href="Prelude.Extensionality.html#9230" class="Function">fiber</a> <a id="9293" class="Symbol">{</a><a id="9294" href="Prelude.Extensionality.html#9294" class="Bound">X</a><a id="9295" class="Symbol">}</a> <a id="9297" href="Prelude.Extensionality.html#9297" class="Bound">f</a> <a id="9299" href="Prelude.Extensionality.html#9299" class="Bound">y</a> <a id="9301" class="Symbol">=</a> <a id="9303" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9305" href="Prelude.Extensionality.html#9305" class="Bound">x</a> <a id="9307" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9309" href="Prelude.Extensionality.html#9294" class="Bound">X</a> <a id="9311" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9313" href="Prelude.Extensionality.html#9297" class="Bound">f</a> <a id="9315" href="Prelude.Extensionality.html#9305" class="Bound">x</a> <a id="9317" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="9319" href="Prelude.Extensionality.html#9299" class="Bound">y</a>

</pre>

A function is called an **equivalence** if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9427" href="Prelude.Extensionality.html#9427" class="Function">is-equiv</a> <a id="9436" class="Symbol">:</a> <a id="9438" class="Symbol">{</a><a id="9439" href="Prelude.Extensionality.html#9439" class="Bound">X</a> <a id="9441" class="Symbol">:</a> <a id="9443" href="Prelude.Extensionality.html#9206" class="Bound">𝓤</a> <a id="9445" href="Universes.html#403" class="Function Operator">̇</a> <a id="9447" class="Symbol">}</a> <a id="9449" class="Symbol">{</a><a id="9450" href="Prelude.Extensionality.html#9450" class="Bound">Y</a> <a id="9452" class="Symbol">:</a> <a id="9454" href="Prelude.Extensionality.html#9208" class="Bound">𝓦</a> <a id="9456" href="Universes.html#403" class="Function Operator">̇</a> <a id="9458" class="Symbol">}</a> <a id="9460" class="Symbol">→</a> <a id="9462" class="Symbol">(</a><a id="9463" href="Prelude.Extensionality.html#9439" class="Bound">X</a> <a id="9465" class="Symbol">→</a> <a id="9467" href="Prelude.Extensionality.html#9450" class="Bound">Y</a><a id="9468" class="Symbol">)</a> <a id="9470" class="Symbol">→</a> <a id="9472" href="Prelude.Extensionality.html#9206" class="Bound">𝓤</a> <a id="9474" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9476" href="Prelude.Extensionality.html#9208" class="Bound">𝓦</a> <a id="9478" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9481" href="Prelude.Extensionality.html#9427" class="Function">is-equiv</a> <a id="9490" href="Prelude.Extensionality.html#9490" class="Bound">f</a> <a id="9492" class="Symbol">=</a> <a id="9494" class="Symbol">∀</a> <a id="9496" href="Prelude.Extensionality.html#9496" class="Bound">y</a> <a id="9498" class="Symbol">→</a> <a id="9500" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9513" class="Symbol">(</a><a id="9514" href="Prelude.Extensionality.html#9230" class="Function">fiber</a> <a id="9520" href="Prelude.Extensionality.html#9490" class="Bound">f</a> <a id="9522" href="Prelude.Extensionality.html#9496" class="Bound">y</a><a id="9523" class="Symbol">)</a>

</pre>

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>  We will precede its definition with a public import statement so that the types we described above, originally defined in the Type Topology][], will be available throughout the remainder of the [UALib][].

<pre class="Agda">

<a id="9932" class="Keyword">open</a> <a id="9937" class="Keyword">import</a> <a id="9944" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9961" class="Keyword">using</a> <a id="9967" class="Symbol">(</a><a id="9968" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9973" class="Symbol">;</a> <a id="9975" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9983" class="Symbol">)</a> <a id="9985" class="Keyword">public</a>

<a id="9993" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="10000" href="Prelude.Extensionality.html#10000" class="Module">hide-hfunext</a> <a id="10013" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="10021" href="Prelude.Extensionality.html#10021" class="Function">hfunext</a> <a id="10029" class="Symbol">:</a> <a id="10031" class="Symbol">(</a><a id="10032" href="Prelude.Extensionality.html#10032" class="Bound">𝓤</a> <a id="10034" href="Prelude.Extensionality.html#10034" class="Bound">𝓦</a> <a id="10036" class="Symbol">:</a> <a id="10038" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10046" class="Symbol">)</a> <a id="10048" class="Symbol">→</a> <a id="10050" class="Symbol">(</a><a id="10051" href="Prelude.Extensionality.html#10032" class="Bound">𝓤</a> <a id="10053" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10055" href="Prelude.Extensionality.html#10034" class="Bound">𝓦</a><a id="10056" class="Symbol">)</a><a id="10057" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="10059" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10062" href="Prelude.Extensionality.html#10021" class="Function">hfunext</a> <a id="10070" href="Prelude.Extensionality.html#10070" class="Bound">𝓤</a> <a id="10072" href="Prelude.Extensionality.html#10072" class="Bound">𝓦</a> <a id="10074" class="Symbol">=</a> <a id="10076" class="Symbol">{</a><a id="10077" href="Prelude.Extensionality.html#10077" class="Bound">A</a> <a id="10079" class="Symbol">:</a> <a id="10081" href="Prelude.Extensionality.html#10070" class="Bound">𝓤</a> <a id="10083" href="Universes.html#403" class="Function Operator">̇</a><a id="10084" class="Symbol">}{</a><a id="10086" href="Prelude.Extensionality.html#10086" class="Bound">B</a> <a id="10088" class="Symbol">:</a> <a id="10090" href="Prelude.Extensionality.html#10077" class="Bound">A</a> <a id="10092" class="Symbol">→</a> <a id="10094" href="Prelude.Extensionality.html#10072" class="Bound">𝓦</a> <a id="10096" href="Universes.html#403" class="Function Operator">̇</a><a id="10097" class="Symbol">}</a> <a id="10099" class="Symbol">(</a><a id="10100" href="Prelude.Extensionality.html#10100" class="Bound">f</a> <a id="10102" href="Prelude.Extensionality.html#10102" class="Bound">g</a> <a id="10104" class="Symbol">:</a> <a id="10106" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="10108" href="Prelude.Extensionality.html#10086" class="Bound">B</a><a id="10109" class="Symbol">)</a> <a id="10111" class="Symbol">→</a> <a id="10113" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="10122" class="Symbol">(</a><a id="10123" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="10131" href="Prelude.Extensionality.html#10100" class="Bound">f</a> <a id="10133" href="Prelude.Extensionality.html#10102" class="Bound">g</a><a id="10134" class="Symbol">)</a>
<a id="10136" class="Keyword">open</a> <a id="10141" class="Keyword">import</a> <a id="10148" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10175" class="Keyword">using</a> <a id="10181" class="Symbol">(</a><a id="10182" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10189" class="Symbol">)</a> <a id="10191" class="Keyword">public</a>

</pre>

------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>2</sup> <span class="footnote" id="fn2"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>3</sup><span class="footnote" id="fn3"> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library. We initially proved this lemma with a simple invocation of `𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁`, but discovered that this proof leads to an `efunext` type that doesn't play well with other definitions in the [Type Topology][] library (e.g., `NatΠ-is-embedding`).</span>

<sup>4</sup><span class="footnote" id="fn4">  In previous versions of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the [Type Topology][] library, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.

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
