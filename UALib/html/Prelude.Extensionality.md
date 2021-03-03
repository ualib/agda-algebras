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

 <a id="hide-funext._∼_"></a><a id="3057" href="Prelude.Extensionality.html#3057" class="Function Operator">_∼_</a> <a id="3061" class="Symbol">:</a> <a id="3063" class="Symbol">{</a><a id="3064" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3066" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3068" class="Symbol">:</a> <a id="3070" href="Universes.html#205" class="Postulate">Universe</a><a id="3078" class="Symbol">}{</a><a id="3080" href="Prelude.Extensionality.html#3080" class="Bound">X</a> <a id="3082" class="Symbol">:</a> <a id="3084" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3086" href="Universes.html#403" class="Function Operator">̇</a> <a id="3088" class="Symbol">}</a> <a id="3090" class="Symbol">{</a><a id="3091" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3093" class="Symbol">:</a> <a id="3095" href="Prelude.Extensionality.html#3080" class="Bound">X</a> <a id="3097" class="Symbol">→</a> <a id="3099" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3101" href="Universes.html#403" class="Function Operator">̇</a> <a id="3103" class="Symbol">}</a> <a id="3105" class="Symbol">→</a> <a id="3107" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3109" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3111" class="Symbol">→</a> <a id="3113" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3115" href="Prelude.Extensionality.html#3091" class="Bound">A</a> <a id="3117" class="Symbol">→</a> <a id="3119" href="Prelude.Extensionality.html#3064" class="Bound">𝓤</a> <a id="3121" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3123" href="Prelude.Extensionality.html#3066" class="Bound">𝓥</a> <a id="3125" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3128" href="Prelude.Extensionality.html#3128" class="Bound">f</a> <a id="3130" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="3132" href="Prelude.Extensionality.html#3132" class="Bound">g</a> <a id="3134" class="Symbol">=</a> <a id="3136" class="Symbol">∀</a> <a id="3138" href="Prelude.Extensionality.html#3138" class="Bound">x</a> <a id="3140" class="Symbol">→</a> <a id="3142" href="Prelude.Extensionality.html#3128" class="Bound">f</a> <a id="3144" href="Prelude.Extensionality.html#3138" class="Bound">x</a> <a id="3146" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="3148" href="Prelude.Extensionality.html#3132" class="Bound">g</a> <a id="3150" href="Prelude.Extensionality.html#3138" class="Bound">x</a>

 <a id="3154" class="Keyword">infix</a> <a id="3160" class="Number">0</a> <a id="3162" href="Prelude.Extensionality.html#3057" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="4034" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4041" class="Symbol">:</a> <a id="4043" class="Symbol">∀</a> <a id="4045" href="Prelude.Extensionality.html#4045" class="Bound">𝓤</a> <a id="4047" href="Prelude.Extensionality.html#4047" class="Bound">𝓦</a>  <a id="4050" class="Symbol">→</a> <a id="4052" href="Prelude.Extensionality.html#4045" class="Bound">𝓤</a> <a id="4054" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4056" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4058" href="Prelude.Extensionality.html#4047" class="Bound">𝓦</a> <a id="4060" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4062" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4065" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4072" href="Prelude.Extensionality.html#4072" class="Bound">𝓤</a> <a id="4074" href="Prelude.Extensionality.html#4074" class="Bound">𝓦</a> <a id="4076" class="Symbol">=</a> <a id="4078" class="Symbol">{</a><a id="4079" href="Prelude.Extensionality.html#4079" class="Bound">A</a> <a id="4081" class="Symbol">:</a> <a id="4083" href="Prelude.Extensionality.html#4072" class="Bound">𝓤</a> <a id="4085" href="Universes.html#403" class="Function Operator">̇</a> <a id="4087" class="Symbol">}</a> <a id="4089" class="Symbol">{</a><a id="4090" href="Prelude.Extensionality.html#4090" class="Bound">B</a> <a id="4092" class="Symbol">:</a> <a id="4094" href="Prelude.Extensionality.html#4074" class="Bound">𝓦</a> <a id="4096" href="Universes.html#403" class="Function Operator">̇</a> <a id="4098" class="Symbol">}</a> <a id="4100" class="Symbol">{</a><a id="4101" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4103" href="Prelude.Extensionality.html#4103" class="Bound">g</a> <a id="4105" class="Symbol">:</a> <a id="4107" href="Prelude.Extensionality.html#4079" class="Bound">A</a> <a id="4109" class="Symbol">→</a> <a id="4111" href="Prelude.Extensionality.html#4090" class="Bound">B</a><a id="4112" class="Symbol">}</a> <a id="4114" class="Symbol">→</a> <a id="4116" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4118" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="4120" href="Prelude.Extensionality.html#4103" class="Bound">g</a> <a id="4122" class="Symbol">→</a> <a id="4124" href="Prelude.Extensionality.html#4101" class="Bound">f</a> <a id="4126" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="4128" href="Prelude.Extensionality.html#4103" class="Bound">g</a>

</pre>

Similarly, extensionality for *dependent* function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="4239" href="Prelude.Extensionality.html#4239" class="Function">dfunext</a> <a id="4247" class="Symbol">:</a> <a id="4249" class="Symbol">∀</a> <a id="4251" href="Prelude.Extensionality.html#4251" class="Bound">𝓤</a> <a id="4253" href="Prelude.Extensionality.html#4253" class="Bound">𝓦</a> <a id="4255" class="Symbol">→</a> <a id="4257" href="Prelude.Extensionality.html#4251" class="Bound">𝓤</a> <a id="4259" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4261" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4263" href="Prelude.Extensionality.html#4253" class="Bound">𝓦</a> <a id="4265" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="4267" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4270" href="Prelude.Extensionality.html#4239" class="Function">dfunext</a> <a id="4278" href="Prelude.Extensionality.html#4278" class="Bound">𝓤</a> <a id="4280" href="Prelude.Extensionality.html#4280" class="Bound">𝓦</a> <a id="4282" class="Symbol">=</a> <a id="4284" class="Symbol">{</a><a id="4285" href="Prelude.Extensionality.html#4285" class="Bound">A</a> <a id="4287" class="Symbol">:</a> <a id="4289" href="Prelude.Extensionality.html#4278" class="Bound">𝓤</a> <a id="4291" href="Universes.html#403" class="Function Operator">̇</a> <a id="4293" class="Symbol">}{</a><a id="4295" href="Prelude.Extensionality.html#4295" class="Bound">B</a> <a id="4297" class="Symbol">:</a> <a id="4299" href="Prelude.Extensionality.html#4285" class="Bound">A</a> <a id="4301" class="Symbol">→</a> <a id="4303" href="Prelude.Extensionality.html#4280" class="Bound">𝓦</a> <a id="4305" href="Universes.html#403" class="Function Operator">̇</a> <a id="4307" class="Symbol">}{</a><a id="4309" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4311" href="Prelude.Extensionality.html#4311" class="Bound">g</a> <a id="4313" class="Symbol">:</a> <a id="4315" class="Symbol">∀(</a><a id="4317" href="Prelude.Extensionality.html#4317" class="Bound">x</a> <a id="4319" class="Symbol">:</a> <a id="4321" href="Prelude.Extensionality.html#4285" class="Bound">A</a><a id="4322" class="Symbol">)</a> <a id="4324" class="Symbol">→</a> <a id="4326" href="Prelude.Extensionality.html#4295" class="Bound">B</a> <a id="4328" href="Prelude.Extensionality.html#4317" class="Bound">x</a><a id="4329" class="Symbol">}</a> <a id="4331" class="Symbol">→</a>  <a id="4334" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4336" href="Prelude.Extensionality.html#3057" class="Function Operator">∼</a> <a id="4338" href="Prelude.Extensionality.html#4311" class="Bound">g</a>  <a id="4341" class="Symbol">→</a>  <a id="4344" href="Prelude.Extensionality.html#4309" class="Bound">f</a> <a id="4346" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="4348" href="Prelude.Extensionality.html#4311" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="4920" href="Prelude.Extensionality.html#4920" class="Function">global-funext</a> <a id="4934" class="Symbol">:</a> <a id="4936" href="Universes.html#234" class="Primitive">𝓤ω</a>
 <a id="4940" href="Prelude.Extensionality.html#4920" class="Function">global-funext</a> <a id="4954" class="Symbol">=</a> <a id="4956" class="Symbol">∀</a>  <a id="4959" class="Symbol">{</a><a id="4960" href="Prelude.Extensionality.html#4960" class="Bound">𝓤</a> <a id="4962" href="Prelude.Extensionality.html#4962" class="Bound">𝓥</a><a id="4963" class="Symbol">}</a> <a id="4965" class="Symbol">→</a> <a id="4967" href="Prelude.Extensionality.html#4034" class="Function">funext</a> <a id="4974" href="Prelude.Extensionality.html#4960" class="Bound">𝓤</a> <a id="4976" href="Prelude.Extensionality.html#4962" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="4980" href="Prelude.Extensionality.html#4980" class="Function">global-dfunext</a> <a id="4995" class="Symbol">:</a> <a id="4997" href="Universes.html#234" class="Primitive">𝓤ω</a>
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

<a id="5935" class="Keyword">module</a> <a id="5942" href="Prelude.Extensionality.html#5942" class="Module">_</a> <a id="5944" class="Symbol">{</a><a id="5945" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="5947" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="5949" class="Symbol">:</a> <a id="5951" href="Universes.html#205" class="Postulate">Universe</a><a id="5959" class="Symbol">}</a> <a id="5961" class="Keyword">where</a>

 <a id="5969" href="Prelude.Extensionality.html#5969" class="Function">extfun</a> <a id="5976" class="Symbol">:</a> <a id="5978" class="Symbol">{</a><a id="5979" href="Prelude.Extensionality.html#5979" class="Bound">A</a> <a id="5981" class="Symbol">:</a> <a id="5983" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="5985" href="Universes.html#403" class="Function Operator">̇</a><a id="5986" class="Symbol">}{</a><a id="5988" href="Prelude.Extensionality.html#5988" class="Bound">B</a> <a id="5990" class="Symbol">:</a> <a id="5992" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="5994" href="Universes.html#403" class="Function Operator">̇</a><a id="5995" class="Symbol">}{</a><a id="5997" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="5999" href="Prelude.Extensionality.html#5999" class="Bound">g</a> <a id="6001" class="Symbol">:</a> <a id="6003" href="Prelude.Extensionality.html#5979" class="Bound">A</a> <a id="6005" class="Symbol">→</a> <a id="6007" href="Prelude.Extensionality.html#5988" class="Bound">B</a><a id="6008" class="Symbol">}</a> <a id="6010" class="Symbol">→</a> <a id="6012" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="6014" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="6016" href="Prelude.Extensionality.html#5999" class="Bound">g</a>  <a id="6019" class="Symbol">→</a>  <a id="6022" href="Prelude.Extensionality.html#5997" class="Bound">f</a> <a id="6024" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6026" href="Prelude.Extensionality.html#5999" class="Bound">g</a>
 <a id="6029" href="Prelude.Extensionality.html#5969" class="Function">extfun</a> <a id="6036" href="Prelude.Equality.html#1624" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6041" class="Symbol">_</a> <a id="6043" class="Symbol">=</a> <a id="6045" href="Prelude.Equality.html#1624" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

 <a id="6130" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="6138" class="Symbol">:</a> <a id="6140" class="Symbol">{</a><a id="6141" href="Prelude.Extensionality.html#6141" class="Bound">A</a> <a id="6143" class="Symbol">:</a> <a id="6145" href="Prelude.Extensionality.html#5945" class="Bound">𝓤</a> <a id="6147" href="Universes.html#403" class="Function Operator">̇</a> <a id="6149" class="Symbol">}{</a><a id="6151" href="Prelude.Extensionality.html#6151" class="Bound">B</a> <a id="6153" class="Symbol">:</a> <a id="6155" href="Prelude.Extensionality.html#6141" class="Bound">A</a> <a id="6157" class="Symbol">→</a> <a id="6159" href="Prelude.Extensionality.html#5947" class="Bound">𝓦</a> <a id="6161" href="Universes.html#403" class="Function Operator">̇</a> <a id="6163" class="Symbol">}(</a><a id="6165" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6167" href="Prelude.Extensionality.html#6167" class="Bound">g</a> <a id="6169" class="Symbol">:</a> <a id="6171" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6173" href="Prelude.Extensionality.html#6151" class="Bound">B</a><a id="6174" class="Symbol">)</a> <a id="6176" class="Symbol">→</a> <a id="6178" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6180" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="6182" href="Prelude.Extensionality.html#6167" class="Bound">g</a> <a id="6184" class="Symbol">→</a> <a id="6186" href="Prelude.Extensionality.html#6165" class="Bound">f</a> <a id="6188" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6190" href="Prelude.Extensionality.html#6167" class="Bound">g</a>
 <a id="6193" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="6201" class="Symbol">_</a> <a id="6203" class="Symbol">_</a> <a id="6205" href="Prelude.Equality.html#1624" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6210" class="Symbol">_</a> <a id="6212" class="Symbol">=</a> <a id="6214" href="Prelude.Equality.html#1624" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="ext-as-equivalence">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follow.

<pre class="Agda">

<a id="8102" class="Keyword">module</a> <a id="hide-tt-defs"></a><a id="8109" href="Prelude.Extensionality.html#8109" class="Module">hide-tt-defs</a> <a id="8122" class="Symbol">{</a><a id="8123" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8125" class="Symbol">:</a> <a id="8127" href="Universes.html#205" class="Postulate">Universe</a><a id="8135" class="Symbol">}</a> <a id="8137" class="Keyword">where</a>

 <a id="hide-tt-defs.is-center"></a><a id="8145" href="Prelude.Extensionality.html#8145" class="Function">is-center</a> <a id="8155" class="Symbol">:</a> <a id="8157" class="Symbol">(</a><a id="8158" href="Prelude.Extensionality.html#8158" class="Bound">X</a> <a id="8160" class="Symbol">:</a> <a id="8162" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8164" href="Universes.html#403" class="Function Operator">̇</a> <a id="8166" class="Symbol">)</a> <a id="8168" class="Symbol">→</a> <a id="8170" href="Prelude.Extensionality.html#8158" class="Bound">X</a> <a id="8172" class="Symbol">→</a> <a id="8174" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8176" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8179" href="Prelude.Extensionality.html#8145" class="Function">is-center</a> <a id="8189" href="Prelude.Extensionality.html#8189" class="Bound">X</a> <a id="8191" href="Prelude.Extensionality.html#8191" class="Bound">c</a> <a id="8193" class="Symbol">=</a> <a id="8195" class="Symbol">(</a><a id="8196" href="Prelude.Extensionality.html#8196" class="Bound">x</a> <a id="8198" class="Symbol">:</a> <a id="8200" href="Prelude.Extensionality.html#8189" class="Bound">X</a><a id="8201" class="Symbol">)</a> <a id="8203" class="Symbol">→</a> <a id="8205" href="Prelude.Extensionality.html#8191" class="Bound">c</a> <a id="8207" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="8209" href="Prelude.Extensionality.html#8196" class="Bound">x</a>

 <a id="hide-tt-defs.is-singleton"></a><a id="8213" href="Prelude.Extensionality.html#8213" class="Function">is-singleton</a> <a id="8226" class="Symbol">:</a> <a id="8228" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8230" href="Universes.html#403" class="Function Operator">̇</a> <a id="8232" class="Symbol">→</a> <a id="8234" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8236" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8239" href="Prelude.Extensionality.html#8213" class="Function">is-singleton</a> <a id="8252" href="Prelude.Extensionality.html#8252" class="Bound">X</a> <a id="8254" class="Symbol">=</a> <a id="8256" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8258" href="Prelude.Extensionality.html#8258" class="Bound">c</a> <a id="8260" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8262" href="Prelude.Extensionality.html#8252" class="Bound">X</a> <a id="8264" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8266" href="Prelude.Extensionality.html#8145" class="Function">is-center</a> <a id="8276" href="Prelude.Extensionality.html#8252" class="Bound">X</a> <a id="8278" href="Prelude.Extensionality.html#8258" class="Bound">c</a>

 <a id="hide-tt-defs.is-subsingleton"></a><a id="8282" href="Prelude.Extensionality.html#8282" class="Function">is-subsingleton</a> <a id="8298" class="Symbol">:</a> <a id="8300" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8302" href="Universes.html#403" class="Function Operator">̇</a> <a id="8304" class="Symbol">→</a> <a id="8306" href="Prelude.Extensionality.html#8123" class="Bound">𝓤</a> <a id="8308" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8311" href="Prelude.Extensionality.html#8282" class="Function">is-subsingleton</a> <a id="8327" href="Prelude.Extensionality.html#8327" class="Bound">X</a> <a id="8329" class="Symbol">=</a> <a id="8331" class="Symbol">(</a><a id="8332" href="Prelude.Extensionality.html#8332" class="Bound">x</a> <a id="8334" href="Prelude.Extensionality.html#8334" class="Bound">y</a> <a id="8336" class="Symbol">:</a> <a id="8338" href="Prelude.Extensionality.html#8327" class="Bound">X</a><a id="8339" class="Symbol">)</a> <a id="8341" class="Symbol">→</a> <a id="8343" href="Prelude.Extensionality.html#8332" class="Bound">x</a> <a id="8345" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="8347" href="Prelude.Extensionality.html#8334" class="Bound">y</a>

</pre>

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library.<sup>[4](Prelude.Extensionality.html#fn4)</sup>

<pre class="Agda">

<a id="8538" class="Keyword">open</a> <a id="8543" class="Keyword">import</a> <a id="8550" href="MGS-Basic-UF.html" class="Module">MGS-Basic-UF</a> <a id="8563" class="Keyword">using</a> <a id="8569" class="Symbol">(</a><a id="8570" href="MGS-Basic-UF.html#362" class="Function">is-center</a><a id="8579" class="Symbol">;</a> <a id="8581" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a><a id="8593" class="Symbol">;</a> <a id="8595" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a><a id="8610" class="Symbol">)</a> <a id="8612" class="Keyword">public</a>

</pre>


Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

<pre class="Agda">

<a id="9069" class="Keyword">module</a> <a id="hide-tt-defs&#39;"></a><a id="9076" href="Prelude.Extensionality.html#9076" class="Module">hide-tt-defs&#39;</a> <a id="9090" class="Symbol">{</a><a id="9091" href="Prelude.Extensionality.html#9091" class="Bound">𝓤</a> <a id="9093" href="Prelude.Extensionality.html#9093" class="Bound">𝓦</a> <a id="9095" class="Symbol">:</a> <a id="9097" href="Universes.html#205" class="Postulate">Universe</a><a id="9105" class="Symbol">}</a> <a id="9107" class="Keyword">where</a>

 <a id="hide-tt-defs&#39;.fiber"></a><a id="9115" href="Prelude.Extensionality.html#9115" class="Function">fiber</a> <a id="9121" class="Symbol">:</a> <a id="9123" class="Symbol">{</a><a id="9124" href="Prelude.Extensionality.html#9124" class="Bound">X</a> <a id="9126" class="Symbol">:</a> <a id="9128" href="Prelude.Extensionality.html#9091" class="Bound">𝓤</a> <a id="9130" href="Universes.html#403" class="Function Operator">̇</a> <a id="9132" class="Symbol">}</a> <a id="9134" class="Symbol">{</a><a id="9135" href="Prelude.Extensionality.html#9135" class="Bound">Y</a> <a id="9137" class="Symbol">:</a> <a id="9139" href="Prelude.Extensionality.html#9093" class="Bound">𝓦</a> <a id="9141" href="Universes.html#403" class="Function Operator">̇</a> <a id="9143" class="Symbol">}</a> <a id="9145" class="Symbol">(</a><a id="9146" href="Prelude.Extensionality.html#9146" class="Bound">f</a> <a id="9148" class="Symbol">:</a> <a id="9150" href="Prelude.Extensionality.html#9124" class="Bound">X</a> <a id="9152" class="Symbol">→</a> <a id="9154" href="Prelude.Extensionality.html#9135" class="Bound">Y</a><a id="9155" class="Symbol">)</a> <a id="9157" class="Symbol">→</a> <a id="9159" href="Prelude.Extensionality.html#9135" class="Bound">Y</a> <a id="9161" class="Symbol">→</a> <a id="9163" href="Prelude.Extensionality.html#9091" class="Bound">𝓤</a> <a id="9165" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9167" href="Prelude.Extensionality.html#9093" class="Bound">𝓦</a> <a id="9169" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9172" href="Prelude.Extensionality.html#9115" class="Function">fiber</a> <a id="9178" class="Symbol">{</a><a id="9179" href="Prelude.Extensionality.html#9179" class="Bound">X</a><a id="9180" class="Symbol">}</a> <a id="9182" href="Prelude.Extensionality.html#9182" class="Bound">f</a> <a id="9184" href="Prelude.Extensionality.html#9184" class="Bound">y</a> <a id="9186" class="Symbol">=</a> <a id="9188" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9190" href="Prelude.Extensionality.html#9190" class="Bound">x</a> <a id="9192" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9194" href="Prelude.Extensionality.html#9179" class="Bound">X</a> <a id="9196" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9198" href="Prelude.Extensionality.html#9182" class="Bound">f</a> <a id="9200" href="Prelude.Extensionality.html#9190" class="Bound">x</a> <a id="9202" href="Prelude.Equality.html#1610" class="Datatype Operator">≡</a> <a id="9204" href="Prelude.Extensionality.html#9184" class="Bound">y</a>

</pre>

A function is called an **equivalence** if all of its fibers are singletons.

<pre class="Agda">

 <a id="hide-tt-defs&#39;.is-equiv"></a><a id="9312" href="Prelude.Extensionality.html#9312" class="Function">is-equiv</a> <a id="9321" class="Symbol">:</a> <a id="9323" class="Symbol">{</a><a id="9324" href="Prelude.Extensionality.html#9324" class="Bound">X</a> <a id="9326" class="Symbol">:</a> <a id="9328" href="Prelude.Extensionality.html#9091" class="Bound">𝓤</a> <a id="9330" href="Universes.html#403" class="Function Operator">̇</a> <a id="9332" class="Symbol">}</a> <a id="9334" class="Symbol">{</a><a id="9335" href="Prelude.Extensionality.html#9335" class="Bound">Y</a> <a id="9337" class="Symbol">:</a> <a id="9339" href="Prelude.Extensionality.html#9093" class="Bound">𝓦</a> <a id="9341" href="Universes.html#403" class="Function Operator">̇</a> <a id="9343" class="Symbol">}</a> <a id="9345" class="Symbol">→</a> <a id="9347" class="Symbol">(</a><a id="9348" href="Prelude.Extensionality.html#9324" class="Bound">X</a> <a id="9350" class="Symbol">→</a> <a id="9352" href="Prelude.Extensionality.html#9335" class="Bound">Y</a><a id="9353" class="Symbol">)</a> <a id="9355" class="Symbol">→</a> <a id="9357" href="Prelude.Extensionality.html#9091" class="Bound">𝓤</a> <a id="9359" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9361" href="Prelude.Extensionality.html#9093" class="Bound">𝓦</a> <a id="9363" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9366" href="Prelude.Extensionality.html#9312" class="Function">is-equiv</a> <a id="9375" href="Prelude.Extensionality.html#9375" class="Bound">f</a> <a id="9377" class="Symbol">=</a> <a id="9379" class="Symbol">∀</a> <a id="9381" href="Prelude.Extensionality.html#9381" class="Bound">y</a> <a id="9383" class="Symbol">→</a> <a id="9385" href="MGS-Basic-UF.html#428" class="Function">is-singleton</a> <a id="9398" class="Symbol">(</a><a id="9399" href="Prelude.Extensionality.html#9115" class="Function">fiber</a> <a id="9405" href="Prelude.Extensionality.html#9375" class="Bound">f</a> <a id="9407" href="Prelude.Extensionality.html#9381" class="Bound">y</a><a id="9408" class="Symbol">)</a>

</pre>

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[5](Prelude.Extensionality.html#fn5)</sup>  We will precede its definition with a public import statement so that the three types just defined will be available throughout the remainder of the [UALib][].

<pre class="Agda">

<a id="9772" class="Keyword">open</a> <a id="9777" class="Keyword">import</a> <a id="9784" href="MGS-Equivalences.html" class="Module">MGS-Equivalences</a> <a id="9801" class="Keyword">using</a> <a id="9807" class="Symbol">(</a><a id="9808" href="MGS-Equivalences.html#868" class="Function">is-equiv</a><a id="9816" class="Symbol">;</a> <a id="9818" href="MGS-Equivalences.html#501" class="Function">fiber</a><a id="9823" class="Symbol">)</a> <a id="9825" class="Keyword">public</a>

<a id="9833" class="Keyword">module</a> <a id="hide-hfunext"></a><a id="9840" href="Prelude.Extensionality.html#9840" class="Module">hide-hfunext</a> <a id="9853" class="Keyword">where</a>

 <a id="hide-hfunext.hfunext"></a><a id="9861" href="Prelude.Extensionality.html#9861" class="Function">hfunext</a> <a id="9869" class="Symbol">:</a> <a id="9871" class="Symbol">(</a><a id="9872" href="Prelude.Extensionality.html#9872" class="Bound">𝓤</a> <a id="9874" href="Prelude.Extensionality.html#9874" class="Bound">𝓦</a> <a id="9876" class="Symbol">:</a> <a id="9878" href="Universes.html#205" class="Postulate">Universe</a><a id="9886" class="Symbol">)</a> <a id="9888" class="Symbol">→</a> <a id="9890" class="Symbol">(</a><a id="9891" href="Prelude.Extensionality.html#9872" class="Bound">𝓤</a> <a id="9893" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9895" href="Prelude.Extensionality.html#9874" class="Bound">𝓦</a><a id="9896" class="Symbol">)</a><a id="9897" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9899" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9902" href="Prelude.Extensionality.html#9861" class="Function">hfunext</a> <a id="9910" href="Prelude.Extensionality.html#9910" class="Bound">𝓤</a> <a id="9912" href="Prelude.Extensionality.html#9912" class="Bound">𝓦</a> <a id="9914" class="Symbol">=</a> <a id="9916" class="Symbol">{</a><a id="9917" href="Prelude.Extensionality.html#9917" class="Bound">A</a> <a id="9919" class="Symbol">:</a> <a id="9921" href="Prelude.Extensionality.html#9910" class="Bound">𝓤</a> <a id="9923" href="Universes.html#403" class="Function Operator">̇</a><a id="9924" class="Symbol">}{</a><a id="9926" href="Prelude.Extensionality.html#9926" class="Bound">B</a> <a id="9928" class="Symbol">:</a> <a id="9930" href="Prelude.Extensionality.html#9917" class="Bound">A</a> <a id="9932" class="Symbol">→</a> <a id="9934" href="Prelude.Extensionality.html#9912" class="Bound">𝓦</a> <a id="9936" href="Universes.html#403" class="Function Operator">̇</a><a id="9937" class="Symbol">}</a> <a id="9939" class="Symbol">(</a><a id="9940" href="Prelude.Extensionality.html#9940" class="Bound">f</a> <a id="9942" href="Prelude.Extensionality.html#9942" class="Bound">g</a> <a id="9944" class="Symbol">:</a> <a id="9946" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9948" href="Prelude.Extensionality.html#9926" class="Bound">B</a><a id="9949" class="Symbol">)</a> <a id="9951" class="Symbol">→</a> <a id="9953" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="9962" class="Symbol">(</a><a id="9963" href="Prelude.Extensionality.html#6130" class="Function">extdfun</a> <a id="9971" href="Prelude.Extensionality.html#9940" class="Bound">f</a> <a id="9973" href="Prelude.Extensionality.html#9942" class="Bound">g</a><a id="9974" class="Symbol">)</a>

</pre>

<pre class="Agda">

<a id="10003" class="Keyword">open</a> <a id="10008" class="Keyword">import</a> <a id="10015" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="10042" class="Keyword">using</a> <a id="10048" class="Symbol">(</a><a id="10049" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="10056" class="Symbol">)</a> <a id="10058" class="Keyword">public</a>

</pre>

------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.

<span class="footnote" id="fn3"><sup>3</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library. We initiall proved this lemma with a simple invocation of `𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁`, but discovered that this proof leads to an `efunext` type that doesn't play well with other definitions in the [Type Topology][] library (e.g., `NatΠ-is-embedding`).</span>

<span class="footnote" id="fn4"><sup>4</sup> You might be wondering at this point why we don't just use the definitions we just defined inside the "hidden" submodule.  We've decided that in order to both explain the type definitions in a clear, self-contained way, and give credit to their originator ([Martín Escardó][]) the best way to proceed is to redefine the types in a hidden submodule, and then import them from their original source.

<span class="footnote" id="fn5"><sup>5</sup> We defined the type `hfunext` (by another name) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and to benefit anyone who might already be familiar with the [Type Topology][] library, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library.

--------------------

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
