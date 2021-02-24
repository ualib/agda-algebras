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

<fieldset style="border: 1px #EA9258 dotted">
 <legend style="border: 1px #5F38AD solid;margin-left: 1em; padding: 0.2em 0.8em ">Foundations Note</legend>

 As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fieldset>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4079" href="Prelude.Extensionality.html#4079" class="Function">funext</a> <a id="4086" class="Symbol">:</a> <a id="4088" class="Symbol">∀</a> <a id="4090" href="Prelude.Extensionality.html#4090" class="Bound">𝓤</a> <a id="4092" href="Prelude.Extensionality.html#4092" class="Bound">𝓦</a>  <a id="4095" class="Symbol">→</a> <a id="4097" href="Prelude.Extensionality.html#4090" class="Bound">𝓤</a> <a id="4099" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4101" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4103" href="Prelude.Extensionality.html#4092" class="Bound">𝓦</a> <a id="4105" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4107" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4110" href="Prelude.Extensionality.html#4079" class="Function">funext</a> <a id="4117" href="Prelude.Extensionality.html#4117" class="Bound">𝓤</a> <a id="4119" href="Prelude.Extensionality.html#4119" class="Bound">𝓦</a> <a id="4121" class="Symbol">=</a> <a id="4123" class="Symbol">{</a><a id="4124" href="Prelude.Extensionality.html#4124" class="Bound">A</a> <a id="4126" class="Symbol">:</a> <a id="4128" href="Prelude.Extensionality.html#4117" class="Bound">𝓤</a> <a id="4130" href="Universes.html#403" class="Function Operator">̇</a> <a id="4132" class="Symbol">}</a> <a id="4134" class="Symbol">{</a><a id="4135" href="Prelude.Extensionality.html#4135" class="Bound">B</a> <a id="4137" class="Symbol">:</a> <a id="4139" href="Prelude.Extensionality.html#4119" class="Bound">𝓦</a> <a id="4141" href="Universes.html#403" class="Function Operator">̇</a> <a id="4143" class="Symbol">}</a> <a id="4145" class="Symbol">{</a><a id="4146" href="Prelude.Extensionality.html#4146" class="Bound">f</a> <a id="4148" href="Prelude.Extensionality.html#4148" class="Bound">g</a> <a id="4150" class="Symbol">:</a> <a id="4152" href="Prelude.Extensionality.html#4124" class="Bound">A</a> <a id="4154" class="Symbol">→</a> <a id="4156" href="Prelude.Extensionality.html#4135" class="Bound">B</a><a id="4157" class="Symbol">}</a> <a id="4159" class="Symbol">→</a> <a id="4161" href="Prelude.Extensionality.html#4146" class="Bound">f</a> <a id="4163" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4165" href="Prelude.Extensionality.html#4148" class="Bound">g</a> <a id="4167" class="Symbol">→</a> <a id="4169" href="Prelude.Extensionality.html#4146" class="Bound">f</a> <a id="4171" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4173" href="Prelude.Extensionality.html#4148" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4361" href="Prelude.Extensionality.html#4361" class="Function">dfunext</a> <a id="4369" class="Symbol">:</a> <a id="4371" class="Symbol">∀</a> <a id="4373" href="Prelude.Extensionality.html#4373" class="Bound">𝓤</a> <a id="4375" href="Prelude.Extensionality.html#4375" class="Bound">𝓦</a> <a id="4377" class="Symbol">→</a> <a id="4379" href="Prelude.Extensionality.html#4373" class="Bound">𝓤</a> <a id="4381" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4383" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4385" href="Prelude.Extensionality.html#4375" class="Bound">𝓦</a> <a id="4387" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4389" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4392" href="Prelude.Extensionality.html#4361" class="Function">dfunext</a> <a id="4400" href="Prelude.Extensionality.html#4400" class="Bound">𝓤</a> <a id="4402" href="Prelude.Extensionality.html#4402" class="Bound">𝓦</a> <a id="4404" class="Symbol">=</a> <a id="4406" class="Symbol">{</a><a id="4407" href="Prelude.Extensionality.html#4407" class="Bound">A</a> <a id="4409" class="Symbol">:</a> <a id="4411" href="Prelude.Extensionality.html#4400" class="Bound">𝓤</a> <a id="4413" href="Universes.html#403" class="Function Operator">̇</a> <a id="4415" class="Symbol">}{</a><a id="4417" href="Prelude.Extensionality.html#4417" class="Bound">B</a> <a id="4419" class="Symbol">:</a> <a id="4421" href="Prelude.Extensionality.html#4407" class="Bound">A</a> <a id="4423" class="Symbol">→</a> <a id="4425" href="Prelude.Extensionality.html#4402" class="Bound">𝓦</a> <a id="4427" href="Universes.html#403" class="Function Operator">̇</a> <a id="4429" class="Symbol">}{</a><a id="4431" href="Prelude.Extensionality.html#4431" class="Bound">f</a> <a id="4433" href="Prelude.Extensionality.html#4433" class="Bound">g</a> <a id="4435" class="Symbol">:</a> <a id="4437" class="Symbol">∀(</a><a id="4439" href="Prelude.Extensionality.html#4439" class="Bound">x</a> <a id="4441" class="Symbol">:</a> <a id="4443" href="Prelude.Extensionality.html#4407" class="Bound">A</a><a id="4444" class="Symbol">)</a> <a id="4446" class="Symbol">→</a> <a id="4448" href="Prelude.Extensionality.html#4417" class="Bound">B</a> <a id="4450" href="Prelude.Extensionality.html#4439" class="Bound">x</a><a id="4451" class="Symbol">}</a> <a id="4453" class="Symbol">→</a>  <a id="4456" href="Prelude.Extensionality.html#4431" class="Bound">f</a> <a id="4458" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4460" href="Prelude.Extensionality.html#4433" class="Bound">g</a>  <a id="4463" class="Symbol">→</a>  <a id="4466" href="Prelude.Extensionality.html#4431" class="Bound">f</a> <a id="4468" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4470" href="Prelude.Extensionality.html#4433" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5042" href="Prelude.Extensionality.html#5042" class="Function">global-funext</a> <a id="5056" class="Symbol">:</a> <a id="5058" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5062" href="Prelude.Extensionality.html#5042" class="Function">global-funext</a> <a id="5076" class="Symbol">=</a> <a id="5078" class="Symbol">∀</a>  <a id="5081" class="Symbol">{</a><a id="5082" href="Prelude.Extensionality.html#5082" class="Bound">𝓤</a> <a id="5084" href="Prelude.Extensionality.html#5084" class="Bound">𝓥</a><a id="5085" class="Symbol">}</a> <a id="5087" class="Symbol">→</a> <a id="5089" href="Prelude.Extensionality.html#4079" class="Function">funext</a> <a id="5096" href="Prelude.Extensionality.html#5082" class="Bound">𝓤</a> <a id="5098" href="Prelude.Extensionality.html#5084" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5102" href="Prelude.Extensionality.html#5102" class="Function">global-dfunext</a> <a id="5117" class="Symbol">:</a> <a id="5119" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5123" href="Prelude.Extensionality.html#5102" class="Function">global-dfunext</a> <a id="5138" class="Symbol">=</a> <a id="5140" class="Symbol">∀</a> <a id="5142" class="Symbol">{</a><a id="5143" href="Prelude.Extensionality.html#5143" class="Bound">𝓤</a> <a id="5145" href="Prelude.Extensionality.html#5145" class="Bound">𝓥</a><a id="5146" class="Symbol">}</a> <a id="5148" class="Symbol">→</a> <a id="5150" href="Prelude.Extensionality.html#4079" class="Function">funext</a> <a id="5157" href="Prelude.Extensionality.html#5143" class="Bound">𝓤</a> <a id="5159" href="Prelude.Extensionality.html#5145" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5355" href="Prelude.Extensionality.html#5355" class="Function">extensionality-lemma</a> <a id="5376" class="Symbol">:</a> <a id="5378" class="Symbol">{</a><a id="5379" href="Prelude.Extensionality.html#5379" class="Bound">𝓘</a> <a id="5381" href="Prelude.Extensionality.html#5381" class="Bound">𝓤</a> <a id="5383" href="Prelude.Extensionality.html#5383" class="Bound">𝓥</a> <a id="5385" href="Prelude.Extensionality.html#5385" class="Bound">𝓣</a> <a id="5387" class="Symbol">:</a> <a id="5389" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5397" class="Symbol">}{</a><a id="5399" href="Prelude.Extensionality.html#5399" class="Bound">I</a> <a id="5401" class="Symbol">:</a> <a id="5403" href="Prelude.Extensionality.html#5379" class="Bound">𝓘</a> <a id="5405" href="Universes.html#403" class="Function Operator">̇</a> <a id="5407" class="Symbol">}{</a><a id="5409" href="Prelude.Extensionality.html#5409" class="Bound">X</a> <a id="5411" class="Symbol">:</a> <a id="5413" href="Prelude.Extensionality.html#5381" class="Bound">𝓤</a> <a id="5415" href="Universes.html#403" class="Function Operator">̇</a> <a id="5417" class="Symbol">}{</a><a id="5419" href="Prelude.Extensionality.html#5419" class="Bound">A</a> <a id="5421" class="Symbol">:</a> <a id="5423" href="Prelude.Extensionality.html#5399" class="Bound">I</a> <a id="5425" class="Symbol">→</a> <a id="5427" href="Prelude.Extensionality.html#5383" class="Bound">𝓥</a> <a id="5429" href="Universes.html#403" class="Function Operator">̇</a> <a id="5431" class="Symbol">}</a>
                       <a id="5456" class="Symbol">(</a><a id="5457" href="Prelude.Extensionality.html#5457" class="Bound">p</a> <a id="5459" href="Prelude.Extensionality.html#5459" class="Bound">q</a> <a id="5461" class="Symbol">:</a> <a id="5463" class="Symbol">(</a><a id="5464" href="Prelude.Extensionality.html#5464" class="Bound">i</a> <a id="5466" class="Symbol">:</a> <a id="5468" href="Prelude.Extensionality.html#5399" class="Bound">I</a><a id="5469" class="Symbol">)</a> <a id="5471" class="Symbol">→</a> <a id="5473" class="Symbol">(</a><a id="5474" href="Prelude.Extensionality.html#5409" class="Bound">X</a> <a id="5476" class="Symbol">→</a> <a id="5478" href="Prelude.Extensionality.html#5419" class="Bound">A</a> <a id="5480" href="Prelude.Extensionality.html#5464" class="Bound">i</a><a id="5481" class="Symbol">)</a> <a id="5483" class="Symbol">→</a> <a id="5485" href="Prelude.Extensionality.html#5385" class="Bound">𝓣</a> <a id="5487" href="Universes.html#403" class="Function Operator">̇</a> <a id="5489" class="Symbol">)(</a><a id="5491" href="Prelude.Extensionality.html#5491" class="Bound">args</a> <a id="5496" class="Symbol">:</a> <a id="5498" href="Prelude.Extensionality.html#5409" class="Bound">X</a> <a id="5500" class="Symbol">→</a> <a id="5502" class="Symbol">(</a><a id="5503" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5505" href="Prelude.Extensionality.html#5419" class="Bound">A</a><a id="5506" class="Symbol">))</a>
 <a id="5510" class="Symbol">→</a>                     <a id="5532" href="Prelude.Extensionality.html#5457" class="Bound">p</a> <a id="5534" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5536" href="Prelude.Extensionality.html#5459" class="Bound">q</a>
                       <a id="5561" class="Comment">-------------------------------------------------------------</a>
 <a id="5624" class="Symbol">→</a>                     <a id="5646" class="Symbol">(λ</a> <a id="5649" href="Prelude.Extensionality.html#5649" class="Bound">i</a> <a id="5651" class="Symbol">→</a> <a id="5653" class="Symbol">(</a><a id="5654" href="Prelude.Extensionality.html#5457" class="Bound">p</a> <a id="5656" href="Prelude.Extensionality.html#5649" class="Bound">i</a><a id="5657" class="Symbol">)(λ</a> <a id="5661" href="Prelude.Extensionality.html#5661" class="Bound">x</a> <a id="5663" class="Symbol">→</a> <a id="5665" href="Prelude.Extensionality.html#5491" class="Bound">args</a> <a id="5670" href="Prelude.Extensionality.html#5661" class="Bound">x</a> <a id="5672" href="Prelude.Extensionality.html#5649" class="Bound">i</a><a id="5673" class="Symbol">))</a> <a id="5676" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5678" class="Symbol">(λ</a> <a id="5681" href="Prelude.Extensionality.html#5681" class="Bound">i</a> <a id="5683" class="Symbol">→</a> <a id="5685" class="Symbol">(</a><a id="5686" href="Prelude.Extensionality.html#5459" class="Bound">q</a> <a id="5688" href="Prelude.Extensionality.html#5681" class="Bound">i</a><a id="5689" class="Symbol">)(λ</a> <a id="5693" href="Prelude.Extensionality.html#5693" class="Bound">x</a> <a id="5695" class="Symbol">→</a> <a id="5697" href="Prelude.Extensionality.html#5491" class="Bound">args</a> <a id="5702" href="Prelude.Extensionality.html#5693" class="Bound">x</a> <a id="5704" href="Prelude.Extensionality.html#5681" class="Bound">i</a><a id="5705" class="Symbol">))</a>

<a id="5709" href="Prelude.Extensionality.html#5355" class="Function">extensionality-lemma</a> <a id="5730" href="Prelude.Extensionality.html#5730" class="Bound">p</a> <a id="5732" href="Prelude.Extensionality.html#5732" class="Bound">q</a> <a id="5734" href="Prelude.Extensionality.html#5734" class="Bound">args</a> <a id="5739" href="Prelude.Extensionality.html#5739" class="Bound">p≡q</a> <a id="5743" class="Symbol">=</a> <a id="5745" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5748" class="Symbol">(λ</a> <a id="5751" href="Prelude.Extensionality.html#5751" class="Bound">-</a> <a id="5753" class="Symbol">→</a> <a id="5755" class="Symbol">λ</a> <a id="5757" href="Prelude.Extensionality.html#5757" class="Bound">i</a> <a id="5759" class="Symbol">→</a> <a id="5761" class="Symbol">(</a><a id="5762" href="Prelude.Extensionality.html#5751" class="Bound">-</a> <a id="5764" href="Prelude.Extensionality.html#5757" class="Bound">i</a><a id="5765" class="Symbol">)</a> <a id="5767" class="Symbol">(λ</a> <a id="5770" href="Prelude.Extensionality.html#5770" class="Bound">x</a> <a id="5772" class="Symbol">→</a> <a id="5774" href="Prelude.Extensionality.html#5734" class="Bound">args</a> <a id="5779" href="Prelude.Extensionality.html#5770" class="Bound">x</a> <a id="5781" href="Prelude.Extensionality.html#5757" class="Bound">i</a><a id="5782" class="Symbol">))</a> <a id="5785" href="Prelude.Extensionality.html#5739" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="5940" class="Keyword">open</a> <a id="5945" class="Keyword">import</a> <a id="5952" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5961" class="Keyword">using</a> <a id="5967" class="Symbol">(</a><a id="5968" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5971" class="Symbol">)</a>

<a id="extfun"></a><a id="5974" href="Prelude.Extensionality.html#5974" class="Function">extfun</a> <a id="5981" class="Symbol">:</a> <a id="5983" class="Symbol">{</a><a id="5984" href="Prelude.Extensionality.html#5984" class="Bound">𝓤</a> <a id="5986" href="Prelude.Extensionality.html#5986" class="Bound">𝓦</a> <a id="5988" class="Symbol">:</a> <a id="5990" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5998" class="Symbol">}{</a><a id="6000" href="Prelude.Extensionality.html#6000" class="Bound">A</a> <a id="6002" class="Symbol">:</a> <a id="6004" href="Prelude.Extensionality.html#5984" class="Bound">𝓤</a> <a id="6006" href="Universes.html#403" class="Function Operator">̇</a><a id="6007" class="Symbol">}{</a><a id="6009" href="Prelude.Extensionality.html#6009" class="Bound">B</a> <a id="6011" class="Symbol">:</a> <a id="6013" href="Prelude.Extensionality.html#5986" class="Bound">𝓦</a> <a id="6015" href="Universes.html#403" class="Function Operator">̇</a><a id="6016" class="Symbol">}{</a><a id="6018" href="Prelude.Extensionality.html#6018" class="Bound">f</a> <a id="6020" href="Prelude.Extensionality.html#6020" class="Bound">g</a> <a id="6022" class="Symbol">:</a> <a id="6024" href="Prelude.Extensionality.html#6000" class="Bound">A</a> <a id="6026" class="Symbol">→</a> <a id="6028" href="Prelude.Extensionality.html#6009" class="Bound">B</a><a id="6029" class="Symbol">}</a> <a id="6031" class="Symbol">→</a> <a id="6033" href="Prelude.Extensionality.html#6018" class="Bound">f</a> <a id="6035" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6037" href="Prelude.Extensionality.html#6020" class="Bound">g</a>  <a id="6040" class="Symbol">→</a>  <a id="6043" href="Prelude.Extensionality.html#6018" class="Bound">f</a> <a id="6045" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6047" href="Prelude.Extensionality.html#6020" class="Bound">g</a>
<a id="6049" href="Prelude.Extensionality.html#5974" class="Function">extfun</a> <a id="6056" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6061" class="Symbol">_</a>  <a id="6064" class="Symbol">=</a> <a id="6066" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6150" href="Prelude.Extensionality.html#6150" class="Function">extdfun</a> <a id="6158" class="Symbol">:</a> <a id="6160" class="Symbol">{</a><a id="6161" href="Prelude.Extensionality.html#6161" class="Bound">𝓤</a> <a id="6163" href="Prelude.Extensionality.html#6163" class="Bound">𝓦</a> <a id="6165" class="Symbol">:</a> <a id="6167" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6175" class="Symbol">}</a> <a id="6177" class="Symbol">{</a><a id="6178" href="Prelude.Extensionality.html#6178" class="Bound">A</a> <a id="6180" class="Symbol">:</a> <a id="6182" href="Prelude.Extensionality.html#6161" class="Bound">𝓤</a> <a id="6184" href="Universes.html#403" class="Function Operator">̇</a> <a id="6186" class="Symbol">}</a> <a id="6188" class="Symbol">{</a><a id="6189" href="Prelude.Extensionality.html#6189" class="Bound">B</a> <a id="6191" class="Symbol">:</a> <a id="6193" href="Prelude.Extensionality.html#6178" class="Bound">A</a> <a id="6195" class="Symbol">→</a> <a id="6197" href="Prelude.Extensionality.html#6163" class="Bound">𝓦</a> <a id="6199" href="Universes.html#403" class="Function Operator">̇</a> <a id="6201" class="Symbol">}</a> <a id="6203" class="Symbol">{</a><a id="6204" href="Prelude.Extensionality.html#6204" class="Bound">f</a> <a id="6206" href="Prelude.Extensionality.html#6206" class="Bound">g</a> <a id="6208" class="Symbol">:</a> <a id="6210" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6212" href="Prelude.Extensionality.html#6189" class="Bound">B</a><a id="6213" class="Symbol">}</a> <a id="6215" class="Symbol">→</a> <a id="6217" href="Prelude.Extensionality.html#6204" class="Bound">f</a> <a id="6219" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6221" href="Prelude.Extensionality.html#6206" class="Bound">g</a> <a id="6223" class="Symbol">→</a> <a id="6225" href="Prelude.Extensionality.html#6204" class="Bound">f</a> <a id="6227" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6229" href="Prelude.Extensionality.html#6206" class="Bound">g</a>
<a id="6231" href="Prelude.Extensionality.html#6150" class="Function">extdfun</a> <a id="6239" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6244" class="Symbol">_</a> <a id="6246" class="Symbol">=</a> <a id="6248" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

<fieldset style="border: 1px #EA9258 dotted">
 <legend style="border: 1px #5F38AD solid;margin-left: 1em; padding: 0.2em 0.8em ">Foundations Note</legend>
An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted in Foundations Box above, the existence of such a witness cannot be proved in Martin-L\"of type theory.
</fieldset>

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
