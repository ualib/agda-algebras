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

 <a id="hide._∼_"></a><a id="3054" href="Prelude.Extensionality.html#3054" class="Function Operator">_∼_</a> <a id="3058" class="Symbol">:</a> <a id="3060" class="Symbol">{</a><a id="3061" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3063" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3065" class="Symbol">:</a> <a id="3067" href="universes.html#551" class="Postulate">Universe</a><a id="3075" class="Symbol">}{</a><a id="3077" href="Prelude.Extensionality.html#3077" class="Bound">X</a> <a id="3079" class="Symbol">:</a> <a id="3081" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3083" href="universes.html#758" class="Function Operator">̇</a> <a id="3085" class="Symbol">}</a> <a id="3087" class="Symbol">{</a><a id="3088" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3090" class="Symbol">:</a> <a id="3092" href="Prelude.Extensionality.html#3077" class="Bound">X</a> <a id="3094" class="Symbol">→</a> <a id="3096" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3098" href="universes.html#758" class="Function Operator">̇</a> <a id="3100" class="Symbol">}</a> <a id="3102" class="Symbol">→</a> <a id="3104" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3106" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3108" class="Symbol">→</a> <a id="3110" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3112" href="Prelude.Extensionality.html#3088" class="Bound">A</a> <a id="3114" class="Symbol">→</a> <a id="3116" href="Prelude.Extensionality.html#3061" class="Bound">𝓤</a> <a id="3118" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3120" href="Prelude.Extensionality.html#3063" class="Bound">𝓥</a> <a id="3122" href="universes.html#758" class="Function Operator">̇</a>
 <a id="3125" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3127" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="3129" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3131" class="Symbol">=</a> <a id="3133" class="Symbol">∀</a> <a id="3135" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3137" class="Symbol">→</a> <a id="3139" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3141" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3143" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="3145" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3147" href="Prelude.Extensionality.html#3135" class="Bound">x</a>

 <a id="3151" class="Keyword">infix</a> <a id="3157" class="Number">0</a> <a id="3159" href="Prelude.Extensionality.html#3054" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

<div class="color_box" id="mltt-ext">
  <div id="title">MLTT Foundations</div>
  <div id="content">As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
  </div>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4025" href="Prelude.Extensionality.html#4025" class="Function">funext</a> <a id="4032" class="Symbol">:</a> <a id="4034" class="Symbol">∀</a> <a id="4036" href="Prelude.Extensionality.html#4036" class="Bound">𝓤</a> <a id="4038" href="Prelude.Extensionality.html#4038" class="Bound">𝓦</a>  <a id="4041" class="Symbol">→</a> <a id="4043" href="Prelude.Extensionality.html#4036" class="Bound">𝓤</a> <a id="4045" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4047" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4049" href="Prelude.Extensionality.html#4038" class="Bound">𝓦</a> <a id="4051" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4053" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4056" href="Prelude.Extensionality.html#4025" class="Function">funext</a> <a id="4063" href="Prelude.Extensionality.html#4063" class="Bound">𝓤</a> <a id="4065" href="Prelude.Extensionality.html#4065" class="Bound">𝓦</a> <a id="4067" class="Symbol">=</a> <a id="4069" class="Symbol">{</a><a id="4070" href="Prelude.Extensionality.html#4070" class="Bound">A</a> <a id="4072" class="Symbol">:</a> <a id="4074" href="Prelude.Extensionality.html#4063" class="Bound">𝓤</a> <a id="4076" href="universes.html#758" class="Function Operator">̇</a> <a id="4078" class="Symbol">}</a> <a id="4080" class="Symbol">{</a><a id="4081" href="Prelude.Extensionality.html#4081" class="Bound">B</a> <a id="4083" class="Symbol">:</a> <a id="4085" href="Prelude.Extensionality.html#4065" class="Bound">𝓦</a> <a id="4087" href="universes.html#758" class="Function Operator">̇</a> <a id="4089" class="Symbol">}</a> <a id="4091" class="Symbol">{</a><a id="4092" href="Prelude.Extensionality.html#4092" class="Bound">f</a> <a id="4094" href="Prelude.Extensionality.html#4094" class="Bound">g</a> <a id="4096" class="Symbol">:</a> <a id="4098" href="Prelude.Extensionality.html#4070" class="Bound">A</a> <a id="4100" class="Symbol">→</a> <a id="4102" href="Prelude.Extensionality.html#4081" class="Bound">B</a><a id="4103" class="Symbol">}</a> <a id="4105" class="Symbol">→</a> <a id="4107" href="Prelude.Extensionality.html#4092" class="Bound">f</a> <a id="4109" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4111" href="Prelude.Extensionality.html#4094" class="Bound">g</a> <a id="4113" class="Symbol">→</a> <a id="4115" href="Prelude.Extensionality.html#4092" class="Bound">f</a> <a id="4117" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4119" href="Prelude.Extensionality.html#4094" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4307" href="Prelude.Extensionality.html#4307" class="Function">dfunext</a> <a id="4315" class="Symbol">:</a> <a id="4317" class="Symbol">∀</a> <a id="4319" href="Prelude.Extensionality.html#4319" class="Bound">𝓤</a> <a id="4321" href="Prelude.Extensionality.html#4321" class="Bound">𝓦</a> <a id="4323" class="Symbol">→</a> <a id="4325" href="Prelude.Extensionality.html#4319" class="Bound">𝓤</a> <a id="4327" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4329" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4331" href="Prelude.Extensionality.html#4321" class="Bound">𝓦</a> <a id="4333" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4335" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4338" href="Prelude.Extensionality.html#4307" class="Function">dfunext</a> <a id="4346" href="Prelude.Extensionality.html#4346" class="Bound">𝓤</a> <a id="4348" href="Prelude.Extensionality.html#4348" class="Bound">𝓦</a> <a id="4350" class="Symbol">=</a> <a id="4352" class="Symbol">{</a><a id="4353" href="Prelude.Extensionality.html#4353" class="Bound">A</a> <a id="4355" class="Symbol">:</a> <a id="4357" href="Prelude.Extensionality.html#4346" class="Bound">𝓤</a> <a id="4359" href="universes.html#758" class="Function Operator">̇</a> <a id="4361" class="Symbol">}{</a><a id="4363" href="Prelude.Extensionality.html#4363" class="Bound">B</a> <a id="4365" class="Symbol">:</a> <a id="4367" href="Prelude.Extensionality.html#4353" class="Bound">A</a> <a id="4369" class="Symbol">→</a> <a id="4371" href="Prelude.Extensionality.html#4348" class="Bound">𝓦</a> <a id="4373" href="universes.html#758" class="Function Operator">̇</a> <a id="4375" class="Symbol">}{</a><a id="4377" href="Prelude.Extensionality.html#4377" class="Bound">f</a> <a id="4379" href="Prelude.Extensionality.html#4379" class="Bound">g</a> <a id="4381" class="Symbol">:</a> <a id="4383" class="Symbol">∀(</a><a id="4385" href="Prelude.Extensionality.html#4385" class="Bound">x</a> <a id="4387" class="Symbol">:</a> <a id="4389" href="Prelude.Extensionality.html#4353" class="Bound">A</a><a id="4390" class="Symbol">)</a> <a id="4392" class="Symbol">→</a> <a id="4394" href="Prelude.Extensionality.html#4363" class="Bound">B</a> <a id="4396" href="Prelude.Extensionality.html#4385" class="Bound">x</a><a id="4397" class="Symbol">}</a> <a id="4399" class="Symbol">→</a>  <a id="4402" href="Prelude.Extensionality.html#4377" class="Bound">f</a> <a id="4404" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4406" href="Prelude.Extensionality.html#4379" class="Bound">g</a>  <a id="4409" class="Symbol">→</a>  <a id="4412" href="Prelude.Extensionality.html#4377" class="Bound">f</a> <a id="4414" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4416" href="Prelude.Extensionality.html#4379" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="4988" href="Prelude.Extensionality.html#4988" class="Function">global-funext</a> <a id="5002" class="Symbol">:</a> <a id="5004" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5008" href="Prelude.Extensionality.html#4988" class="Function">global-funext</a> <a id="5022" class="Symbol">=</a> <a id="5024" class="Symbol">∀</a>  <a id="5027" class="Symbol">{</a><a id="5028" href="Prelude.Extensionality.html#5028" class="Bound">𝓤</a> <a id="5030" href="Prelude.Extensionality.html#5030" class="Bound">𝓥</a><a id="5031" class="Symbol">}</a> <a id="5033" class="Symbol">→</a> <a id="5035" href="Prelude.Extensionality.html#4025" class="Function">funext</a> <a id="5042" href="Prelude.Extensionality.html#5028" class="Bound">𝓤</a> <a id="5044" href="Prelude.Extensionality.html#5030" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5048" href="Prelude.Extensionality.html#5048" class="Function">global-dfunext</a> <a id="5063" class="Symbol">:</a> <a id="5065" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5069" href="Prelude.Extensionality.html#5048" class="Function">global-dfunext</a> <a id="5084" class="Symbol">=</a> <a id="5086" class="Symbol">∀</a> <a id="5088" class="Symbol">{</a><a id="5089" href="Prelude.Extensionality.html#5089" class="Bound">𝓤</a> <a id="5091" href="Prelude.Extensionality.html#5091" class="Bound">𝓥</a><a id="5092" class="Symbol">}</a> <a id="5094" class="Symbol">→</a> <a id="5096" href="Prelude.Extensionality.html#4025" class="Function">funext</a> <a id="5103" href="Prelude.Extensionality.html#5089" class="Bound">𝓤</a> <a id="5105" href="Prelude.Extensionality.html#5091" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5301" href="Prelude.Extensionality.html#5301" class="Function">extensionality-lemma</a> <a id="5322" class="Symbol">:</a> <a id="5324" class="Symbol">{</a><a id="5325" href="Prelude.Extensionality.html#5325" class="Bound">𝓘</a> <a id="5327" href="Prelude.Extensionality.html#5327" class="Bound">𝓤</a> <a id="5329" href="Prelude.Extensionality.html#5329" class="Bound">𝓥</a> <a id="5331" href="Prelude.Extensionality.html#5331" class="Bound">𝓣</a> <a id="5333" class="Symbol">:</a> <a id="5335" href="universes.html#551" class="Postulate">Universe</a><a id="5343" class="Symbol">}{</a><a id="5345" href="Prelude.Extensionality.html#5345" class="Bound">I</a> <a id="5347" class="Symbol">:</a> <a id="5349" href="Prelude.Extensionality.html#5325" class="Bound">𝓘</a> <a id="5351" href="universes.html#758" class="Function Operator">̇</a> <a id="5353" class="Symbol">}{</a><a id="5355" href="Prelude.Extensionality.html#5355" class="Bound">X</a> <a id="5357" class="Symbol">:</a> <a id="5359" href="Prelude.Extensionality.html#5327" class="Bound">𝓤</a> <a id="5361" href="universes.html#758" class="Function Operator">̇</a> <a id="5363" class="Symbol">}{</a><a id="5365" href="Prelude.Extensionality.html#5365" class="Bound">A</a> <a id="5367" class="Symbol">:</a> <a id="5369" href="Prelude.Extensionality.html#5345" class="Bound">I</a> <a id="5371" class="Symbol">→</a> <a id="5373" href="Prelude.Extensionality.html#5329" class="Bound">𝓥</a> <a id="5375" href="universes.html#758" class="Function Operator">̇</a> <a id="5377" class="Symbol">}</a>
                       <a id="5402" class="Symbol">(</a><a id="5403" href="Prelude.Extensionality.html#5403" class="Bound">p</a> <a id="5405" href="Prelude.Extensionality.html#5405" class="Bound">q</a> <a id="5407" class="Symbol">:</a> <a id="5409" class="Symbol">(</a><a id="5410" href="Prelude.Extensionality.html#5410" class="Bound">i</a> <a id="5412" class="Symbol">:</a> <a id="5414" href="Prelude.Extensionality.html#5345" class="Bound">I</a><a id="5415" class="Symbol">)</a> <a id="5417" class="Symbol">→</a> <a id="5419" class="Symbol">(</a><a id="5420" href="Prelude.Extensionality.html#5355" class="Bound">X</a> <a id="5422" class="Symbol">→</a> <a id="5424" href="Prelude.Extensionality.html#5365" class="Bound">A</a> <a id="5426" href="Prelude.Extensionality.html#5410" class="Bound">i</a><a id="5427" class="Symbol">)</a> <a id="5429" class="Symbol">→</a> <a id="5431" href="Prelude.Extensionality.html#5331" class="Bound">𝓣</a> <a id="5433" href="universes.html#758" class="Function Operator">̇</a> <a id="5435" class="Symbol">)(</a><a id="5437" href="Prelude.Extensionality.html#5437" class="Bound">args</a> <a id="5442" class="Symbol">:</a> <a id="5444" href="Prelude.Extensionality.html#5355" class="Bound">X</a> <a id="5446" class="Symbol">→</a> <a id="5448" class="Symbol">(</a><a id="5449" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5451" href="Prelude.Extensionality.html#5365" class="Bound">A</a><a id="5452" class="Symbol">))</a>
 <a id="5456" class="Symbol">→</a>                     <a id="5478" href="Prelude.Extensionality.html#5403" class="Bound">p</a> <a id="5480" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5482" href="Prelude.Extensionality.html#5405" class="Bound">q</a>
                       <a id="5507" class="Comment">-------------------------------------------------------------</a>
 <a id="5570" class="Symbol">→</a>                     <a id="5592" class="Symbol">(λ</a> <a id="5595" href="Prelude.Extensionality.html#5595" class="Bound">i</a> <a id="5597" class="Symbol">→</a> <a id="5599" class="Symbol">(</a><a id="5600" href="Prelude.Extensionality.html#5403" class="Bound">p</a> <a id="5602" href="Prelude.Extensionality.html#5595" class="Bound">i</a><a id="5603" class="Symbol">)(λ</a> <a id="5607" href="Prelude.Extensionality.html#5607" class="Bound">x</a> <a id="5609" class="Symbol">→</a> <a id="5611" href="Prelude.Extensionality.html#5437" class="Bound">args</a> <a id="5616" href="Prelude.Extensionality.html#5607" class="Bound">x</a> <a id="5618" href="Prelude.Extensionality.html#5595" class="Bound">i</a><a id="5619" class="Symbol">))</a> <a id="5622" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5624" class="Symbol">(λ</a> <a id="5627" href="Prelude.Extensionality.html#5627" class="Bound">i</a> <a id="5629" class="Symbol">→</a> <a id="5631" class="Symbol">(</a><a id="5632" href="Prelude.Extensionality.html#5405" class="Bound">q</a> <a id="5634" href="Prelude.Extensionality.html#5627" class="Bound">i</a><a id="5635" class="Symbol">)(λ</a> <a id="5639" href="Prelude.Extensionality.html#5639" class="Bound">x</a> <a id="5641" class="Symbol">→</a> <a id="5643" href="Prelude.Extensionality.html#5437" class="Bound">args</a> <a id="5648" href="Prelude.Extensionality.html#5639" class="Bound">x</a> <a id="5650" href="Prelude.Extensionality.html#5627" class="Bound">i</a><a id="5651" class="Symbol">))</a>

<a id="5655" href="Prelude.Extensionality.html#5301" class="Function">extensionality-lemma</a> <a id="5676" href="Prelude.Extensionality.html#5676" class="Bound">p</a> <a id="5678" href="Prelude.Extensionality.html#5678" class="Bound">q</a> <a id="5680" href="Prelude.Extensionality.html#5680" class="Bound">args</a> <a id="5685" href="Prelude.Extensionality.html#5685" class="Bound">p≡q</a> <a id="5689" class="Symbol">=</a> <a id="5691" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5694" class="Symbol">(λ</a> <a id="5697" href="Prelude.Extensionality.html#5697" class="Bound">-</a> <a id="5699" class="Symbol">→</a> <a id="5701" class="Symbol">λ</a> <a id="5703" href="Prelude.Extensionality.html#5703" class="Bound">i</a> <a id="5705" class="Symbol">→</a> <a id="5707" class="Symbol">(</a><a id="5708" href="Prelude.Extensionality.html#5697" class="Bound">-</a> <a id="5710" href="Prelude.Extensionality.html#5703" class="Bound">i</a><a id="5711" class="Symbol">)</a> <a id="5713" class="Symbol">(λ</a> <a id="5716" href="Prelude.Extensionality.html#5716" class="Bound">x</a> <a id="5718" class="Symbol">→</a> <a id="5720" href="Prelude.Extensionality.html#5680" class="Bound">args</a> <a id="5725" href="Prelude.Extensionality.html#5716" class="Bound">x</a> <a id="5727" href="Prelude.Extensionality.html#5703" class="Bound">i</a><a id="5728" class="Symbol">))</a> <a id="5731" href="Prelude.Extensionality.html#5685" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="5886" class="Keyword">open</a> <a id="5891" class="Keyword">import</a> <a id="5898" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5907" class="Keyword">using</a> <a id="5913" class="Symbol">(</a><a id="5914" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5917" class="Symbol">)</a>

<a id="extfun"></a><a id="5920" href="Prelude.Extensionality.html#5920" class="Function">extfun</a> <a id="5927" class="Symbol">:</a> <a id="5929" class="Symbol">{</a><a id="5930" href="Prelude.Extensionality.html#5930" class="Bound">𝓤</a> <a id="5932" href="Prelude.Extensionality.html#5932" class="Bound">𝓦</a> <a id="5934" class="Symbol">:</a> <a id="5936" href="universes.html#551" class="Postulate">Universe</a><a id="5944" class="Symbol">}{</a><a id="5946" href="Prelude.Extensionality.html#5946" class="Bound">A</a> <a id="5948" class="Symbol">:</a> <a id="5950" href="Prelude.Extensionality.html#5930" class="Bound">𝓤</a> <a id="5952" href="universes.html#758" class="Function Operator">̇</a><a id="5953" class="Symbol">}{</a><a id="5955" href="Prelude.Extensionality.html#5955" class="Bound">B</a> <a id="5957" class="Symbol">:</a> <a id="5959" href="Prelude.Extensionality.html#5932" class="Bound">𝓦</a> <a id="5961" href="universes.html#758" class="Function Operator">̇</a><a id="5962" class="Symbol">}{</a><a id="5964" href="Prelude.Extensionality.html#5964" class="Bound">f</a> <a id="5966" href="Prelude.Extensionality.html#5966" class="Bound">g</a> <a id="5968" class="Symbol">:</a> <a id="5970" href="Prelude.Extensionality.html#5946" class="Bound">A</a> <a id="5972" class="Symbol">→</a> <a id="5974" href="Prelude.Extensionality.html#5955" class="Bound">B</a><a id="5975" class="Symbol">}</a> <a id="5977" class="Symbol">→</a> <a id="5979" href="Prelude.Extensionality.html#5964" class="Bound">f</a> <a id="5981" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5983" href="Prelude.Extensionality.html#5966" class="Bound">g</a>  <a id="5986" class="Symbol">→</a>  <a id="5989" href="Prelude.Extensionality.html#5964" class="Bound">f</a> <a id="5991" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5993" href="Prelude.Extensionality.html#5966" class="Bound">g</a>
<a id="5995" href="Prelude.Extensionality.html#5920" class="Function">extfun</a> <a id="6002" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6007" class="Symbol">_</a>  <a id="6010" class="Symbol">=</a> <a id="6012" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6096" href="Prelude.Extensionality.html#6096" class="Function">extdfun</a> <a id="6104" class="Symbol">:</a> <a id="6106" class="Symbol">{</a><a id="6107" href="Prelude.Extensionality.html#6107" class="Bound">𝓤</a> <a id="6109" href="Prelude.Extensionality.html#6109" class="Bound">𝓦</a> <a id="6111" class="Symbol">:</a> <a id="6113" href="universes.html#551" class="Postulate">Universe</a><a id="6121" class="Symbol">}</a> <a id="6123" class="Symbol">{</a><a id="6124" href="Prelude.Extensionality.html#6124" class="Bound">A</a> <a id="6126" class="Symbol">:</a> <a id="6128" href="Prelude.Extensionality.html#6107" class="Bound">𝓤</a> <a id="6130" href="universes.html#758" class="Function Operator">̇</a> <a id="6132" class="Symbol">}</a> <a id="6134" class="Symbol">{</a><a id="6135" href="Prelude.Extensionality.html#6135" class="Bound">B</a> <a id="6137" class="Symbol">:</a> <a id="6139" href="Prelude.Extensionality.html#6124" class="Bound">A</a> <a id="6141" class="Symbol">→</a> <a id="6143" href="Prelude.Extensionality.html#6109" class="Bound">𝓦</a> <a id="6145" href="universes.html#758" class="Function Operator">̇</a> <a id="6147" class="Symbol">}</a> <a id="6149" class="Symbol">{</a><a id="6150" href="Prelude.Extensionality.html#6150" class="Bound">f</a> <a id="6152" href="Prelude.Extensionality.html#6152" class="Bound">g</a> <a id="6154" class="Symbol">:</a> <a id="6156" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6158" href="Prelude.Extensionality.html#6135" class="Bound">B</a><a id="6159" class="Symbol">}</a> <a id="6161" class="Symbol">→</a> <a id="6163" href="Prelude.Extensionality.html#6150" class="Bound">f</a> <a id="6165" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6167" href="Prelude.Extensionality.html#6152" class="Bound">g</a> <a id="6169" class="Symbol">→</a> <a id="6171" href="Prelude.Extensionality.html#6150" class="Bound">f</a> <a id="6173" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6175" href="Prelude.Extensionality.html#6152" class="Bound">g</a>
<a id="6177" href="Prelude.Extensionality.html#6096" class="Function">extdfun</a> <a id="6185" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6190" class="Symbol">_</a> <a id="6192" class="Symbol">=</a> <a id="6194" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but, as noted above, the existence of such a witness cannot be proved in Martin-L\"of type theory.

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>f one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
