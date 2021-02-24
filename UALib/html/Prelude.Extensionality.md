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

<div class="color_box" id="mltt-ext">
  <div id="title">MLTT Foundations Note</div>
  <div id="content">As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
  </div>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4030" href="Prelude.Extensionality.html#4030" class="Function">funext</a> <a id="4037" class="Symbol">:</a> <a id="4039" class="Symbol">∀</a> <a id="4041" href="Prelude.Extensionality.html#4041" class="Bound">𝓤</a> <a id="4043" href="Prelude.Extensionality.html#4043" class="Bound">𝓦</a>  <a id="4046" class="Symbol">→</a> <a id="4048" href="Prelude.Extensionality.html#4041" class="Bound">𝓤</a> <a id="4050" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4052" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4054" href="Prelude.Extensionality.html#4043" class="Bound">𝓦</a> <a id="4056" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4058" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4061" href="Prelude.Extensionality.html#4030" class="Function">funext</a> <a id="4068" href="Prelude.Extensionality.html#4068" class="Bound">𝓤</a> <a id="4070" href="Prelude.Extensionality.html#4070" class="Bound">𝓦</a> <a id="4072" class="Symbol">=</a> <a id="4074" class="Symbol">{</a><a id="4075" href="Prelude.Extensionality.html#4075" class="Bound">A</a> <a id="4077" class="Symbol">:</a> <a id="4079" href="Prelude.Extensionality.html#4068" class="Bound">𝓤</a> <a id="4081" href="Universes.html#403" class="Function Operator">̇</a> <a id="4083" class="Symbol">}</a> <a id="4085" class="Symbol">{</a><a id="4086" href="Prelude.Extensionality.html#4086" class="Bound">B</a> <a id="4088" class="Symbol">:</a> <a id="4090" href="Prelude.Extensionality.html#4070" class="Bound">𝓦</a> <a id="4092" href="Universes.html#403" class="Function Operator">̇</a> <a id="4094" class="Symbol">}</a> <a id="4096" class="Symbol">{</a><a id="4097" href="Prelude.Extensionality.html#4097" class="Bound">f</a> <a id="4099" href="Prelude.Extensionality.html#4099" class="Bound">g</a> <a id="4101" class="Symbol">:</a> <a id="4103" href="Prelude.Extensionality.html#4075" class="Bound">A</a> <a id="4105" class="Symbol">→</a> <a id="4107" href="Prelude.Extensionality.html#4086" class="Bound">B</a><a id="4108" class="Symbol">}</a> <a id="4110" class="Symbol">→</a> <a id="4112" href="Prelude.Extensionality.html#4097" class="Bound">f</a> <a id="4114" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4116" href="Prelude.Extensionality.html#4099" class="Bound">g</a> <a id="4118" class="Symbol">→</a> <a id="4120" href="Prelude.Extensionality.html#4097" class="Bound">f</a> <a id="4122" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4124" href="Prelude.Extensionality.html#4099" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4312" href="Prelude.Extensionality.html#4312" class="Function">dfunext</a> <a id="4320" class="Symbol">:</a> <a id="4322" class="Symbol">∀</a> <a id="4324" href="Prelude.Extensionality.html#4324" class="Bound">𝓤</a> <a id="4326" href="Prelude.Extensionality.html#4326" class="Bound">𝓦</a> <a id="4328" class="Symbol">→</a> <a id="4330" href="Prelude.Extensionality.html#4324" class="Bound">𝓤</a> <a id="4332" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4334" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4336" href="Prelude.Extensionality.html#4326" class="Bound">𝓦</a> <a id="4338" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4340" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4343" href="Prelude.Extensionality.html#4312" class="Function">dfunext</a> <a id="4351" href="Prelude.Extensionality.html#4351" class="Bound">𝓤</a> <a id="4353" href="Prelude.Extensionality.html#4353" class="Bound">𝓦</a> <a id="4355" class="Symbol">=</a> <a id="4357" class="Symbol">{</a><a id="4358" href="Prelude.Extensionality.html#4358" class="Bound">A</a> <a id="4360" class="Symbol">:</a> <a id="4362" href="Prelude.Extensionality.html#4351" class="Bound">𝓤</a> <a id="4364" href="Universes.html#403" class="Function Operator">̇</a> <a id="4366" class="Symbol">}{</a><a id="4368" href="Prelude.Extensionality.html#4368" class="Bound">B</a> <a id="4370" class="Symbol">:</a> <a id="4372" href="Prelude.Extensionality.html#4358" class="Bound">A</a> <a id="4374" class="Symbol">→</a> <a id="4376" href="Prelude.Extensionality.html#4353" class="Bound">𝓦</a> <a id="4378" href="Universes.html#403" class="Function Operator">̇</a> <a id="4380" class="Symbol">}{</a><a id="4382" href="Prelude.Extensionality.html#4382" class="Bound">f</a> <a id="4384" href="Prelude.Extensionality.html#4384" class="Bound">g</a> <a id="4386" class="Symbol">:</a> <a id="4388" class="Symbol">∀(</a><a id="4390" href="Prelude.Extensionality.html#4390" class="Bound">x</a> <a id="4392" class="Symbol">:</a> <a id="4394" href="Prelude.Extensionality.html#4358" class="Bound">A</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">→</a> <a id="4399" href="Prelude.Extensionality.html#4368" class="Bound">B</a> <a id="4401" href="Prelude.Extensionality.html#4390" class="Bound">x</a><a id="4402" class="Symbol">}</a> <a id="4404" class="Symbol">→</a>  <a id="4407" href="Prelude.Extensionality.html#4382" class="Bound">f</a> <a id="4409" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4411" href="Prelude.Extensionality.html#4384" class="Bound">g</a>  <a id="4414" class="Symbol">→</a>  <a id="4417" href="Prelude.Extensionality.html#4382" class="Bound">f</a> <a id="4419" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4421" href="Prelude.Extensionality.html#4384" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="4993" href="Prelude.Extensionality.html#4993" class="Function">global-funext</a> <a id="5007" class="Symbol">:</a> <a id="5009" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5013" href="Prelude.Extensionality.html#4993" class="Function">global-funext</a> <a id="5027" class="Symbol">=</a> <a id="5029" class="Symbol">∀</a>  <a id="5032" class="Symbol">{</a><a id="5033" href="Prelude.Extensionality.html#5033" class="Bound">𝓤</a> <a id="5035" href="Prelude.Extensionality.html#5035" class="Bound">𝓥</a><a id="5036" class="Symbol">}</a> <a id="5038" class="Symbol">→</a> <a id="5040" href="Prelude.Extensionality.html#4030" class="Function">funext</a> <a id="5047" href="Prelude.Extensionality.html#5033" class="Bound">𝓤</a> <a id="5049" href="Prelude.Extensionality.html#5035" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5053" href="Prelude.Extensionality.html#5053" class="Function">global-dfunext</a> <a id="5068" class="Symbol">:</a> <a id="5070" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5074" href="Prelude.Extensionality.html#5053" class="Function">global-dfunext</a> <a id="5089" class="Symbol">=</a> <a id="5091" class="Symbol">∀</a> <a id="5093" class="Symbol">{</a><a id="5094" href="Prelude.Extensionality.html#5094" class="Bound">𝓤</a> <a id="5096" href="Prelude.Extensionality.html#5096" class="Bound">𝓥</a><a id="5097" class="Symbol">}</a> <a id="5099" class="Symbol">→</a> <a id="5101" href="Prelude.Extensionality.html#4030" class="Function">funext</a> <a id="5108" href="Prelude.Extensionality.html#5094" class="Bound">𝓤</a> <a id="5110" href="Prelude.Extensionality.html#5096" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5306" href="Prelude.Extensionality.html#5306" class="Function">extensionality-lemma</a> <a id="5327" class="Symbol">:</a> <a id="5329" class="Symbol">{</a><a id="5330" href="Prelude.Extensionality.html#5330" class="Bound">𝓘</a> <a id="5332" href="Prelude.Extensionality.html#5332" class="Bound">𝓤</a> <a id="5334" href="Prelude.Extensionality.html#5334" class="Bound">𝓥</a> <a id="5336" href="Prelude.Extensionality.html#5336" class="Bound">𝓣</a> <a id="5338" class="Symbol">:</a> <a id="5340" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5348" class="Symbol">}{</a><a id="5350" href="Prelude.Extensionality.html#5350" class="Bound">I</a> <a id="5352" class="Symbol">:</a> <a id="5354" href="Prelude.Extensionality.html#5330" class="Bound">𝓘</a> <a id="5356" href="Universes.html#403" class="Function Operator">̇</a> <a id="5358" class="Symbol">}{</a><a id="5360" href="Prelude.Extensionality.html#5360" class="Bound">X</a> <a id="5362" class="Symbol">:</a> <a id="5364" href="Prelude.Extensionality.html#5332" class="Bound">𝓤</a> <a id="5366" href="Universes.html#403" class="Function Operator">̇</a> <a id="5368" class="Symbol">}{</a><a id="5370" href="Prelude.Extensionality.html#5370" class="Bound">A</a> <a id="5372" class="Symbol">:</a> <a id="5374" href="Prelude.Extensionality.html#5350" class="Bound">I</a> <a id="5376" class="Symbol">→</a> <a id="5378" href="Prelude.Extensionality.html#5334" class="Bound">𝓥</a> <a id="5380" href="Universes.html#403" class="Function Operator">̇</a> <a id="5382" class="Symbol">}</a>
                       <a id="5407" class="Symbol">(</a><a id="5408" href="Prelude.Extensionality.html#5408" class="Bound">p</a> <a id="5410" href="Prelude.Extensionality.html#5410" class="Bound">q</a> <a id="5412" class="Symbol">:</a> <a id="5414" class="Symbol">(</a><a id="5415" href="Prelude.Extensionality.html#5415" class="Bound">i</a> <a id="5417" class="Symbol">:</a> <a id="5419" href="Prelude.Extensionality.html#5350" class="Bound">I</a><a id="5420" class="Symbol">)</a> <a id="5422" class="Symbol">→</a> <a id="5424" class="Symbol">(</a><a id="5425" href="Prelude.Extensionality.html#5360" class="Bound">X</a> <a id="5427" class="Symbol">→</a> <a id="5429" href="Prelude.Extensionality.html#5370" class="Bound">A</a> <a id="5431" href="Prelude.Extensionality.html#5415" class="Bound">i</a><a id="5432" class="Symbol">)</a> <a id="5434" class="Symbol">→</a> <a id="5436" href="Prelude.Extensionality.html#5336" class="Bound">𝓣</a> <a id="5438" href="Universes.html#403" class="Function Operator">̇</a> <a id="5440" class="Symbol">)(</a><a id="5442" href="Prelude.Extensionality.html#5442" class="Bound">args</a> <a id="5447" class="Symbol">:</a> <a id="5449" href="Prelude.Extensionality.html#5360" class="Bound">X</a> <a id="5451" class="Symbol">→</a> <a id="5453" class="Symbol">(</a><a id="5454" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5456" href="Prelude.Extensionality.html#5370" class="Bound">A</a><a id="5457" class="Symbol">))</a>
 <a id="5461" class="Symbol">→</a>                     <a id="5483" href="Prelude.Extensionality.html#5408" class="Bound">p</a> <a id="5485" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5487" href="Prelude.Extensionality.html#5410" class="Bound">q</a>
                       <a id="5512" class="Comment">-------------------------------------------------------------</a>
 <a id="5575" class="Symbol">→</a>                     <a id="5597" class="Symbol">(λ</a> <a id="5600" href="Prelude.Extensionality.html#5600" class="Bound">i</a> <a id="5602" class="Symbol">→</a> <a id="5604" class="Symbol">(</a><a id="5605" href="Prelude.Extensionality.html#5408" class="Bound">p</a> <a id="5607" href="Prelude.Extensionality.html#5600" class="Bound">i</a><a id="5608" class="Symbol">)(λ</a> <a id="5612" href="Prelude.Extensionality.html#5612" class="Bound">x</a> <a id="5614" class="Symbol">→</a> <a id="5616" href="Prelude.Extensionality.html#5442" class="Bound">args</a> <a id="5621" href="Prelude.Extensionality.html#5612" class="Bound">x</a> <a id="5623" href="Prelude.Extensionality.html#5600" class="Bound">i</a><a id="5624" class="Symbol">))</a> <a id="5627" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5629" class="Symbol">(λ</a> <a id="5632" href="Prelude.Extensionality.html#5632" class="Bound">i</a> <a id="5634" class="Symbol">→</a> <a id="5636" class="Symbol">(</a><a id="5637" href="Prelude.Extensionality.html#5410" class="Bound">q</a> <a id="5639" href="Prelude.Extensionality.html#5632" class="Bound">i</a><a id="5640" class="Symbol">)(λ</a> <a id="5644" href="Prelude.Extensionality.html#5644" class="Bound">x</a> <a id="5646" class="Symbol">→</a> <a id="5648" href="Prelude.Extensionality.html#5442" class="Bound">args</a> <a id="5653" href="Prelude.Extensionality.html#5644" class="Bound">x</a> <a id="5655" href="Prelude.Extensionality.html#5632" class="Bound">i</a><a id="5656" class="Symbol">))</a>

<a id="5660" href="Prelude.Extensionality.html#5306" class="Function">extensionality-lemma</a> <a id="5681" href="Prelude.Extensionality.html#5681" class="Bound">p</a> <a id="5683" href="Prelude.Extensionality.html#5683" class="Bound">q</a> <a id="5685" href="Prelude.Extensionality.html#5685" class="Bound">args</a> <a id="5690" href="Prelude.Extensionality.html#5690" class="Bound">p≡q</a> <a id="5694" class="Symbol">=</a> <a id="5696" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5699" class="Symbol">(λ</a> <a id="5702" href="Prelude.Extensionality.html#5702" class="Bound">-</a> <a id="5704" class="Symbol">→</a> <a id="5706" class="Symbol">λ</a> <a id="5708" href="Prelude.Extensionality.html#5708" class="Bound">i</a> <a id="5710" class="Symbol">→</a> <a id="5712" class="Symbol">(</a><a id="5713" href="Prelude.Extensionality.html#5702" class="Bound">-</a> <a id="5715" href="Prelude.Extensionality.html#5708" class="Bound">i</a><a id="5716" class="Symbol">)</a> <a id="5718" class="Symbol">(λ</a> <a id="5721" href="Prelude.Extensionality.html#5721" class="Bound">x</a> <a id="5723" class="Symbol">→</a> <a id="5725" href="Prelude.Extensionality.html#5685" class="Bound">args</a> <a id="5730" href="Prelude.Extensionality.html#5721" class="Bound">x</a> <a id="5732" href="Prelude.Extensionality.html#5708" class="Bound">i</a><a id="5733" class="Symbol">))</a> <a id="5736" href="Prelude.Extensionality.html#5690" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="5891" class="Keyword">open</a> <a id="5896" class="Keyword">import</a> <a id="5903" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5912" class="Keyword">using</a> <a id="5918" class="Symbol">(</a><a id="5919" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5922" class="Symbol">)</a>

<a id="extfun"></a><a id="5925" href="Prelude.Extensionality.html#5925" class="Function">extfun</a> <a id="5932" class="Symbol">:</a> <a id="5934" class="Symbol">{</a><a id="5935" href="Prelude.Extensionality.html#5935" class="Bound">𝓤</a> <a id="5937" href="Prelude.Extensionality.html#5937" class="Bound">𝓦</a> <a id="5939" class="Symbol">:</a> <a id="5941" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5949" class="Symbol">}{</a><a id="5951" href="Prelude.Extensionality.html#5951" class="Bound">A</a> <a id="5953" class="Symbol">:</a> <a id="5955" href="Prelude.Extensionality.html#5935" class="Bound">𝓤</a> <a id="5957" href="Universes.html#403" class="Function Operator">̇</a><a id="5958" class="Symbol">}{</a><a id="5960" href="Prelude.Extensionality.html#5960" class="Bound">B</a> <a id="5962" class="Symbol">:</a> <a id="5964" href="Prelude.Extensionality.html#5937" class="Bound">𝓦</a> <a id="5966" href="Universes.html#403" class="Function Operator">̇</a><a id="5967" class="Symbol">}{</a><a id="5969" href="Prelude.Extensionality.html#5969" class="Bound">f</a> <a id="5971" href="Prelude.Extensionality.html#5971" class="Bound">g</a> <a id="5973" class="Symbol">:</a> <a id="5975" href="Prelude.Extensionality.html#5951" class="Bound">A</a> <a id="5977" class="Symbol">→</a> <a id="5979" href="Prelude.Extensionality.html#5960" class="Bound">B</a><a id="5980" class="Symbol">}</a> <a id="5982" class="Symbol">→</a> <a id="5984" href="Prelude.Extensionality.html#5969" class="Bound">f</a> <a id="5986" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5988" href="Prelude.Extensionality.html#5971" class="Bound">g</a>  <a id="5991" class="Symbol">→</a>  <a id="5994" href="Prelude.Extensionality.html#5969" class="Bound">f</a> <a id="5996" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="5998" href="Prelude.Extensionality.html#5971" class="Bound">g</a>
<a id="6000" href="Prelude.Extensionality.html#5925" class="Function">extfun</a> <a id="6007" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6012" class="Symbol">_</a>  <a id="6015" class="Symbol">=</a> <a id="6017" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6101" href="Prelude.Extensionality.html#6101" class="Function">extdfun</a> <a id="6109" class="Symbol">:</a> <a id="6111" class="Symbol">{</a><a id="6112" href="Prelude.Extensionality.html#6112" class="Bound">𝓤</a> <a id="6114" href="Prelude.Extensionality.html#6114" class="Bound">𝓦</a> <a id="6116" class="Symbol">:</a> <a id="6118" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6126" class="Symbol">}</a> <a id="6128" class="Symbol">{</a><a id="6129" href="Prelude.Extensionality.html#6129" class="Bound">A</a> <a id="6131" class="Symbol">:</a> <a id="6133" href="Prelude.Extensionality.html#6112" class="Bound">𝓤</a> <a id="6135" href="Universes.html#403" class="Function Operator">̇</a> <a id="6137" class="Symbol">}</a> <a id="6139" class="Symbol">{</a><a id="6140" href="Prelude.Extensionality.html#6140" class="Bound">B</a> <a id="6142" class="Symbol">:</a> <a id="6144" href="Prelude.Extensionality.html#6129" class="Bound">A</a> <a id="6146" class="Symbol">→</a> <a id="6148" href="Prelude.Extensionality.html#6114" class="Bound">𝓦</a> <a id="6150" href="Universes.html#403" class="Function Operator">̇</a> <a id="6152" class="Symbol">}</a> <a id="6154" class="Symbol">{</a><a id="6155" href="Prelude.Extensionality.html#6155" class="Bound">f</a> <a id="6157" href="Prelude.Extensionality.html#6157" class="Bound">g</a> <a id="6159" class="Symbol">:</a> <a id="6161" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6163" href="Prelude.Extensionality.html#6140" class="Bound">B</a><a id="6164" class="Symbol">}</a> <a id="6166" class="Symbol">→</a> <a id="6168" href="Prelude.Extensionality.html#6155" class="Bound">f</a> <a id="6170" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6172" href="Prelude.Extensionality.html#6157" class="Bound">g</a> <a id="6174" class="Symbol">→</a> <a id="6176" href="Prelude.Extensionality.html#6155" class="Bound">f</a> <a id="6178" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6180" href="Prelude.Extensionality.html#6157" class="Bound">g</a>
<a id="6182" href="Prelude.Extensionality.html#6101" class="Function">extdfun</a> <a id="6190" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6195" class="Symbol">_</a> <a id="6197" class="Symbol">=</a> <a id="6199" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but, as noted above, the existence of such a witness cannot be proved in Martin-L\"of type theory.

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
