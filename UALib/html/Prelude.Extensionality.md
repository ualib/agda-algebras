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

<a id="2995" class="Keyword">module</a> <a id="hide"></a><a id="3002" href="Prelude.Extensionality.html#3002" class="Module">hide</a> <a id="3007" class="Keyword">where</a>

 <a id="hide._∼_"></a><a id="3015" href="Prelude.Extensionality.html#3015" class="Function Operator">_∼_</a> <a id="3019" class="Symbol">:</a> <a id="3021" class="Symbol">{</a><a id="3022" href="Prelude.Extensionality.html#3022" class="Bound">𝓤</a> <a id="3024" href="Prelude.Extensionality.html#3024" class="Bound">𝓥</a> <a id="3026" class="Symbol">:</a> <a id="3028" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3036" class="Symbol">}{</a><a id="3038" href="Prelude.Extensionality.html#3038" class="Bound">X</a> <a id="3040" class="Symbol">:</a> <a id="3042" href="Prelude.Extensionality.html#3022" class="Bound">𝓤</a> <a id="3044" href="Universes.html#403" class="Function Operator">̇</a> <a id="3046" class="Symbol">}</a> <a id="3048" class="Symbol">{</a><a id="3049" href="Prelude.Extensionality.html#3049" class="Bound">A</a> <a id="3051" class="Symbol">:</a> <a id="3053" href="Prelude.Extensionality.html#3038" class="Bound">X</a> <a id="3055" class="Symbol">→</a> <a id="3057" href="Prelude.Extensionality.html#3024" class="Bound">𝓥</a> <a id="3059" href="Universes.html#403" class="Function Operator">̇</a> <a id="3061" class="Symbol">}</a> <a id="3063" class="Symbol">→</a> <a id="3065" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3067" href="Prelude.Extensionality.html#3049" class="Bound">A</a> <a id="3069" class="Symbol">→</a> <a id="3071" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3073" href="Prelude.Extensionality.html#3049" class="Bound">A</a> <a id="3075" class="Symbol">→</a> <a id="3077" href="Prelude.Extensionality.html#3022" class="Bound">𝓤</a> <a id="3079" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3081" href="Prelude.Extensionality.html#3024" class="Bound">𝓥</a> <a id="3083" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3086" href="Prelude.Extensionality.html#3086" class="Bound">f</a> <a id="3088" href="Prelude.Extensionality.html#3015" class="Function Operator">∼</a> <a id="3090" href="Prelude.Extensionality.html#3090" class="Bound">g</a> <a id="3092" class="Symbol">=</a> <a id="3094" class="Symbol">∀</a> <a id="3096" href="Prelude.Extensionality.html#3096" class="Bound">x</a> <a id="3098" class="Symbol">→</a> <a id="3100" href="Prelude.Extensionality.html#3086" class="Bound">f</a> <a id="3102" href="Prelude.Extensionality.html#3096" class="Bound">x</a> <a id="3104" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3106" href="Prelude.Extensionality.html#3090" class="Bound">g</a> <a id="3108" href="Prelude.Extensionality.html#3096" class="Bound">x</a>

 <a id="3112" class="Keyword">infix</a> <a id="3118" class="Number">0</a> <a id="3120" href="Prelude.Extensionality.html#3015" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="3872" href="Prelude.Extensionality.html#3872" class="Function">funext</a> <a id="3879" class="Symbol">:</a> <a id="3881" class="Symbol">∀</a> <a id="3883" href="Prelude.Extensionality.html#3883" class="Bound">𝓤</a> <a id="3885" href="Prelude.Extensionality.html#3885" class="Bound">𝓦</a>  <a id="3888" class="Symbol">→</a> <a id="3890" href="Prelude.Extensionality.html#3883" class="Bound">𝓤</a> <a id="3892" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3894" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3896" href="Prelude.Extensionality.html#3885" class="Bound">𝓦</a> <a id="3898" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3900" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3903" href="Prelude.Extensionality.html#3872" class="Function">funext</a> <a id="3910" href="Prelude.Extensionality.html#3910" class="Bound">𝓤</a> <a id="3912" href="Prelude.Extensionality.html#3912" class="Bound">𝓦</a> <a id="3914" class="Symbol">=</a> <a id="3916" class="Symbol">{</a><a id="3917" href="Prelude.Extensionality.html#3917" class="Bound">A</a> <a id="3919" class="Symbol">:</a> <a id="3921" href="Prelude.Extensionality.html#3910" class="Bound">𝓤</a> <a id="3923" href="Universes.html#403" class="Function Operator">̇</a> <a id="3925" class="Symbol">}</a> <a id="3927" class="Symbol">{</a><a id="3928" href="Prelude.Extensionality.html#3928" class="Bound">B</a> <a id="3930" class="Symbol">:</a> <a id="3932" href="Prelude.Extensionality.html#3912" class="Bound">𝓦</a> <a id="3934" href="Universes.html#403" class="Function Operator">̇</a> <a id="3936" class="Symbol">}</a> <a id="3938" class="Symbol">{</a><a id="3939" href="Prelude.Extensionality.html#3939" class="Bound">f</a> <a id="3941" href="Prelude.Extensionality.html#3941" class="Bound">g</a> <a id="3943" class="Symbol">:</a> <a id="3945" href="Prelude.Extensionality.html#3917" class="Bound">A</a> <a id="3947" class="Symbol">→</a> <a id="3949" href="Prelude.Extensionality.html#3928" class="Bound">B</a><a id="3950" class="Symbol">}</a> <a id="3952" class="Symbol">→</a> <a id="3954" href="Prelude.Extensionality.html#3939" class="Bound">f</a> <a id="3956" href="Prelude.Extensionality.html#3015" class="Function Operator">∼</a> <a id="3958" href="Prelude.Extensionality.html#3941" class="Bound">g</a> <a id="3960" class="Symbol">→</a> <a id="3962" href="Prelude.Extensionality.html#3939" class="Bound">f</a> <a id="3964" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3966" href="Prelude.Extensionality.html#3941" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4154" href="Prelude.Extensionality.html#4154" class="Function">dfunext</a> <a id="4162" class="Symbol">:</a> <a id="4164" class="Symbol">∀</a> <a id="4166" href="Prelude.Extensionality.html#4166" class="Bound">𝓤</a> <a id="4168" href="Prelude.Extensionality.html#4168" class="Bound">𝓦</a> <a id="4170" class="Symbol">→</a> <a id="4172" href="Prelude.Extensionality.html#4166" class="Bound">𝓤</a> <a id="4174" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4176" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4178" href="Prelude.Extensionality.html#4168" class="Bound">𝓦</a> <a id="4180" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4182" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4185" href="Prelude.Extensionality.html#4154" class="Function">dfunext</a> <a id="4193" href="Prelude.Extensionality.html#4193" class="Bound">𝓤</a> <a id="4195" href="Prelude.Extensionality.html#4195" class="Bound">𝓦</a> <a id="4197" class="Symbol">=</a> <a id="4199" class="Symbol">{</a><a id="4200" href="Prelude.Extensionality.html#4200" class="Bound">A</a> <a id="4202" class="Symbol">:</a> <a id="4204" href="Prelude.Extensionality.html#4193" class="Bound">𝓤</a> <a id="4206" href="Universes.html#403" class="Function Operator">̇</a> <a id="4208" class="Symbol">}{</a><a id="4210" href="Prelude.Extensionality.html#4210" class="Bound">B</a> <a id="4212" class="Symbol">:</a> <a id="4214" href="Prelude.Extensionality.html#4200" class="Bound">A</a> <a id="4216" class="Symbol">→</a> <a id="4218" href="Prelude.Extensionality.html#4195" class="Bound">𝓦</a> <a id="4220" href="Universes.html#403" class="Function Operator">̇</a> <a id="4222" class="Symbol">}{</a><a id="4224" href="Prelude.Extensionality.html#4224" class="Bound">f</a> <a id="4226" href="Prelude.Extensionality.html#4226" class="Bound">g</a> <a id="4228" class="Symbol">:</a> <a id="4230" class="Symbol">∀(</a><a id="4232" href="Prelude.Extensionality.html#4232" class="Bound">x</a> <a id="4234" class="Symbol">:</a> <a id="4236" href="Prelude.Extensionality.html#4200" class="Bound">A</a><a id="4237" class="Symbol">)</a> <a id="4239" class="Symbol">→</a> <a id="4241" href="Prelude.Extensionality.html#4210" class="Bound">B</a> <a id="4243" href="Prelude.Extensionality.html#4232" class="Bound">x</a><a id="4244" class="Symbol">}</a> <a id="4246" class="Symbol">→</a>  <a id="4249" href="Prelude.Extensionality.html#4224" class="Bound">f</a> <a id="4251" href="Prelude.Extensionality.html#3015" class="Function Operator">∼</a> <a id="4253" href="Prelude.Extensionality.html#4226" class="Bound">g</a>  <a id="4256" class="Symbol">→</a>  <a id="4259" href="Prelude.Extensionality.html#4224" class="Bound">f</a> <a id="4261" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4263" href="Prelude.Extensionality.html#4226" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="4835" href="Prelude.Extensionality.html#4835" class="Function">global-funext</a> <a id="4849" class="Symbol">:</a> <a id="4851" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4855" href="Prelude.Extensionality.html#4835" class="Function">global-funext</a> <a id="4869" class="Symbol">=</a> <a id="4871" class="Symbol">∀</a>  <a id="4874" class="Symbol">{</a><a id="4875" href="Prelude.Extensionality.html#4875" class="Bound">𝓤</a> <a id="4877" href="Prelude.Extensionality.html#4877" class="Bound">𝓥</a><a id="4878" class="Symbol">}</a> <a id="4880" class="Symbol">→</a> <a id="4882" href="Prelude.Extensionality.html#3872" class="Function">funext</a> <a id="4889" href="Prelude.Extensionality.html#4875" class="Bound">𝓤</a> <a id="4891" href="Prelude.Extensionality.html#4877" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="4895" href="Prelude.Extensionality.html#4895" class="Function">global-dfunext</a> <a id="4910" class="Symbol">:</a> <a id="4912" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4916" href="Prelude.Extensionality.html#4895" class="Function">global-dfunext</a> <a id="4931" class="Symbol">=</a> <a id="4933" class="Symbol">∀</a> <a id="4935" class="Symbol">{</a><a id="4936" href="Prelude.Extensionality.html#4936" class="Bound">𝓤</a> <a id="4938" href="Prelude.Extensionality.html#4938" class="Bound">𝓥</a><a id="4939" class="Symbol">}</a> <a id="4941" class="Symbol">→</a> <a id="4943" href="Prelude.Extensionality.html#3872" class="Function">funext</a> <a id="4950" href="Prelude.Extensionality.html#4936" class="Bound">𝓤</a> <a id="4952" href="Prelude.Extensionality.html#4938" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5148" href="Prelude.Extensionality.html#5148" class="Function">extensionality-lemma</a> <a id="5169" class="Symbol">:</a> <a id="5171" class="Symbol">{</a><a id="5172" href="Prelude.Extensionality.html#5172" class="Bound">𝓘</a> <a id="5174" href="Prelude.Extensionality.html#5174" class="Bound">𝓤</a> <a id="5176" href="Prelude.Extensionality.html#5176" class="Bound">𝓥</a> <a id="5178" href="Prelude.Extensionality.html#5178" class="Bound">𝓣</a> <a id="5180" class="Symbol">:</a> <a id="5182" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5190" class="Symbol">}{</a><a id="5192" href="Prelude.Extensionality.html#5192" class="Bound">I</a> <a id="5194" class="Symbol">:</a> <a id="5196" href="Prelude.Extensionality.html#5172" class="Bound">𝓘</a> <a id="5198" href="Universes.html#403" class="Function Operator">̇</a> <a id="5200" class="Symbol">}{</a><a id="5202" href="Prelude.Extensionality.html#5202" class="Bound">X</a> <a id="5204" class="Symbol">:</a> <a id="5206" href="Prelude.Extensionality.html#5174" class="Bound">𝓤</a> <a id="5208" href="Universes.html#403" class="Function Operator">̇</a> <a id="5210" class="Symbol">}{</a><a id="5212" href="Prelude.Extensionality.html#5212" class="Bound">A</a> <a id="5214" class="Symbol">:</a> <a id="5216" href="Prelude.Extensionality.html#5192" class="Bound">I</a> <a id="5218" class="Symbol">→</a> <a id="5220" href="Prelude.Extensionality.html#5176" class="Bound">𝓥</a> <a id="5222" href="Universes.html#403" class="Function Operator">̇</a> <a id="5224" class="Symbol">}</a>
                       <a id="5249" class="Symbol">(</a><a id="5250" href="Prelude.Extensionality.html#5250" class="Bound">p</a> <a id="5252" href="Prelude.Extensionality.html#5252" class="Bound">q</a> <a id="5254" class="Symbol">:</a> <a id="5256" class="Symbol">(</a><a id="5257" href="Prelude.Extensionality.html#5257" class="Bound">i</a> <a id="5259" class="Symbol">:</a> <a id="5261" href="Prelude.Extensionality.html#5192" class="Bound">I</a><a id="5262" class="Symbol">)</a> <a id="5264" class="Symbol">→</a> <a id="5266" class="Symbol">(</a><a id="5267" href="Prelude.Extensionality.html#5202" class="Bound">X</a> <a id="5269" class="Symbol">→</a> <a id="5271" href="Prelude.Extensionality.html#5212" class="Bound">A</a> <a id="5273" href="Prelude.Extensionality.html#5257" class="Bound">i</a><a id="5274" class="Symbol">)</a> <a id="5276" class="Symbol">→</a> <a id="5278" href="Prelude.Extensionality.html#5178" class="Bound">𝓣</a> <a id="5280" href="Universes.html#403" class="Function Operator">̇</a> <a id="5282" class="Symbol">)(</a><a id="5284" href="Prelude.Extensionality.html#5284" class="Bound">args</a> <a id="5289" class="Symbol">:</a> <a id="5291" href="Prelude.Extensionality.html#5202" class="Bound">X</a> <a id="5293" class="Symbol">→</a> <a id="5295" class="Symbol">(</a><a id="5296" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5298" href="Prelude.Extensionality.html#5212" class="Bound">A</a><a id="5299" class="Symbol">))</a>
 <a id="5303" class="Symbol">→</a>                     <a id="5325" href="Prelude.Extensionality.html#5250" class="Bound">p</a> <a id="5327" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5329" href="Prelude.Extensionality.html#5252" class="Bound">q</a>
                       <a id="5354" class="Comment">-------------------------------------------------------------</a>
 <a id="5417" class="Symbol">→</a>                     <a id="5439" class="Symbol">(λ</a> <a id="5442" href="Prelude.Extensionality.html#5442" class="Bound">i</a> <a id="5444" class="Symbol">→</a> <a id="5446" class="Symbol">(</a><a id="5447" href="Prelude.Extensionality.html#5250" class="Bound">p</a> <a id="5449" href="Prelude.Extensionality.html#5442" class="Bound">i</a><a id="5450" class="Symbol">)(λ</a> <a id="5454" href="Prelude.Extensionality.html#5454" class="Bound">x</a> <a id="5456" class="Symbol">→</a> <a id="5458" href="Prelude.Extensionality.html#5284" class="Bound">args</a> <a id="5463" href="Prelude.Extensionality.html#5454" class="Bound">x</a> <a id="5465" href="Prelude.Extensionality.html#5442" class="Bound">i</a><a id="5466" class="Symbol">))</a> <a id="5469" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5471" class="Symbol">(λ</a> <a id="5474" href="Prelude.Extensionality.html#5474" class="Bound">i</a> <a id="5476" class="Symbol">→</a> <a id="5478" class="Symbol">(</a><a id="5479" href="Prelude.Extensionality.html#5252" class="Bound">q</a> <a id="5481" href="Prelude.Extensionality.html#5474" class="Bound">i</a><a id="5482" class="Symbol">)(λ</a> <a id="5486" href="Prelude.Extensionality.html#5486" class="Bound">x</a> <a id="5488" class="Symbol">→</a> <a id="5490" href="Prelude.Extensionality.html#5284" class="Bound">args</a> <a id="5495" href="Prelude.Extensionality.html#5486" class="Bound">x</a> <a id="5497" href="Prelude.Extensionality.html#5474" class="Bound">i</a><a id="5498" class="Symbol">))</a>

<a id="5502" href="Prelude.Extensionality.html#5148" class="Function">extensionality-lemma</a> <a id="5523" href="Prelude.Extensionality.html#5523" class="Bound">p</a> <a id="5525" href="Prelude.Extensionality.html#5525" class="Bound">q</a> <a id="5527" href="Prelude.Extensionality.html#5527" class="Bound">args</a> <a id="5532" href="Prelude.Extensionality.html#5532" class="Bound">p≡q</a> <a id="5536" class="Symbol">=</a> <a id="5538" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5541" class="Symbol">(λ</a> <a id="5544" href="Prelude.Extensionality.html#5544" class="Bound">-</a> <a id="5546" class="Symbol">→</a> <a id="5548" class="Symbol">λ</a> <a id="5550" href="Prelude.Extensionality.html#5550" class="Bound">i</a> <a id="5552" class="Symbol">→</a> <a id="5554" class="Symbol">(</a><a id="5555" href="Prelude.Extensionality.html#5544" class="Bound">-</a> <a id="5557" href="Prelude.Extensionality.html#5550" class="Bound">i</a><a id="5558" class="Symbol">)</a> <a id="5560" class="Symbol">(λ</a> <a id="5563" href="Prelude.Extensionality.html#5563" class="Bound">x</a> <a id="5565" class="Symbol">→</a> <a id="5567" href="Prelude.Extensionality.html#5527" class="Bound">args</a> <a id="5572" href="Prelude.Extensionality.html#5563" class="Bound">x</a> <a id="5574" href="Prelude.Extensionality.html#5550" class="Bound">i</a><a id="5575" class="Symbol">))</a> <a id="5578" href="Prelude.Extensionality.html#5532" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="5729" class="Keyword">open</a> <a id="5734" class="Keyword">import</a> <a id="5741" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5750" class="Keyword">using</a> <a id="5756" class="Symbol">(</a><a id="5757" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5760" class="Symbol">)</a>

<a id="extfun"></a><a id="5763" href="Prelude.Extensionality.html#5763" class="Function">extfun</a> <a id="5770" class="Symbol">:</a> <a id="5772" class="Symbol">{</a><a id="5773" href="Prelude.Extensionality.html#5773" class="Bound">𝓤</a> <a id="5775" href="Prelude.Extensionality.html#5775" class="Bound">𝓦</a> <a id="5777" class="Symbol">:</a> <a id="5779" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5787" class="Symbol">}{</a><a id="5789" href="Prelude.Extensionality.html#5789" class="Bound">A</a> <a id="5791" class="Symbol">:</a> <a id="5793" href="Prelude.Extensionality.html#5773" class="Bound">𝓤</a> <a id="5795" href="Universes.html#403" class="Function Operator">̇</a><a id="5796" class="Symbol">}{</a><a id="5798" href="Prelude.Extensionality.html#5798" class="Bound">B</a> <a id="5800" class="Symbol">:</a> <a id="5802" href="Prelude.Extensionality.html#5775" class="Bound">𝓦</a> <a id="5804" href="Universes.html#403" class="Function Operator">̇</a><a id="5805" class="Symbol">}{</a><a id="5807" href="Prelude.Extensionality.html#5807" class="Bound">f</a> <a id="5809" href="Prelude.Extensionality.html#5809" class="Bound">g</a> <a id="5811" class="Symbol">:</a> <a id="5813" href="Prelude.Extensionality.html#5789" class="Bound">A</a> <a id="5815" class="Symbol">→</a> <a id="5817" href="Prelude.Extensionality.html#5798" class="Bound">B</a><a id="5818" class="Symbol">}</a> <a id="5820" class="Symbol">→</a> <a id="5822" href="Prelude.Extensionality.html#5807" class="Bound">f</a> <a id="5824" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5826" href="Prelude.Extensionality.html#5809" class="Bound">g</a>  <a id="5829" class="Symbol">→</a>  <a id="5832" href="Prelude.Extensionality.html#5807" class="Bound">f</a> <a id="5834" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5836" href="Prelude.Extensionality.html#5809" class="Bound">g</a>
<a id="5838" href="Prelude.Extensionality.html#5763" class="Function">extfun</a> <a id="5845" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="5850" class="Symbol">_</a>  <a id="5853" class="Symbol">=</a> <a id="5855" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="5939" href="Prelude.Extensionality.html#5939" class="Function">extdfun</a> <a id="5947" class="Symbol">:</a> <a id="5949" class="Symbol">{</a><a id="5950" href="Prelude.Extensionality.html#5950" class="Bound">𝓤</a> <a id="5952" href="Prelude.Extensionality.html#5952" class="Bound">𝓦</a> <a id="5954" class="Symbol">:</a> <a id="5956" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5964" class="Symbol">}</a> <a id="5966" class="Symbol">{</a><a id="5967" href="Prelude.Extensionality.html#5967" class="Bound">A</a> <a id="5969" class="Symbol">:</a> <a id="5971" href="Prelude.Extensionality.html#5950" class="Bound">𝓤</a> <a id="5973" href="Universes.html#403" class="Function Operator">̇</a> <a id="5975" class="Symbol">}</a> <a id="5977" class="Symbol">{</a><a id="5978" href="Prelude.Extensionality.html#5978" class="Bound">B</a> <a id="5980" class="Symbol">:</a> <a id="5982" href="Prelude.Extensionality.html#5967" class="Bound">A</a> <a id="5984" class="Symbol">→</a> <a id="5986" href="Prelude.Extensionality.html#5952" class="Bound">𝓦</a> <a id="5988" href="Universes.html#403" class="Function Operator">̇</a> <a id="5990" class="Symbol">}</a> <a id="5992" class="Symbol">{</a><a id="5993" href="Prelude.Extensionality.html#5993" class="Bound">f</a> <a id="5995" href="Prelude.Extensionality.html#5995" class="Bound">g</a> <a id="5997" class="Symbol">:</a> <a id="5999" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6001" href="Prelude.Extensionality.html#5978" class="Bound">B</a><a id="6002" class="Symbol">}</a> <a id="6004" class="Symbol">→</a> <a id="6006" href="Prelude.Extensionality.html#5993" class="Bound">f</a> <a id="6008" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6010" href="Prelude.Extensionality.html#5995" class="Bound">g</a> <a id="6012" class="Symbol">→</a> <a id="6014" href="Prelude.Extensionality.html#5993" class="Bound">f</a> <a id="6016" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6018" href="Prelude.Extensionality.html#5995" class="Bound">g</a>
<a id="6020" href="Prelude.Extensionality.html#5939" class="Function">extdfun</a> <a id="6028" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6033" class="Symbol">_</a> <a id="6035" class="Symbol">=</a> <a id="6037" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

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
