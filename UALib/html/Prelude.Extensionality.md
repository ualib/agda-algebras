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

  </div>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4084" href="Prelude.Extensionality.html#4084" class="Function">funext</a> <a id="4091" class="Symbol">:</a> <a id="4093" class="Symbol">∀</a> <a id="4095" href="Prelude.Extensionality.html#4095" class="Bound">𝓤</a> <a id="4097" href="Prelude.Extensionality.html#4097" class="Bound">𝓦</a>  <a id="4100" class="Symbol">→</a> <a id="4102" href="Prelude.Extensionality.html#4095" class="Bound">𝓤</a> <a id="4104" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4106" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4108" href="Prelude.Extensionality.html#4097" class="Bound">𝓦</a> <a id="4110" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4112" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4115" href="Prelude.Extensionality.html#4084" class="Function">funext</a> <a id="4122" href="Prelude.Extensionality.html#4122" class="Bound">𝓤</a> <a id="4124" href="Prelude.Extensionality.html#4124" class="Bound">𝓦</a> <a id="4126" class="Symbol">=</a> <a id="4128" class="Symbol">{</a><a id="4129" href="Prelude.Extensionality.html#4129" class="Bound">A</a> <a id="4131" class="Symbol">:</a> <a id="4133" href="Prelude.Extensionality.html#4122" class="Bound">𝓤</a> <a id="4135" href="Universes.html#403" class="Function Operator">̇</a> <a id="4137" class="Symbol">}</a> <a id="4139" class="Symbol">{</a><a id="4140" href="Prelude.Extensionality.html#4140" class="Bound">B</a> <a id="4142" class="Symbol">:</a> <a id="4144" href="Prelude.Extensionality.html#4124" class="Bound">𝓦</a> <a id="4146" href="Universes.html#403" class="Function Operator">̇</a> <a id="4148" class="Symbol">}</a> <a id="4150" class="Symbol">{</a><a id="4151" href="Prelude.Extensionality.html#4151" class="Bound">f</a> <a id="4153" href="Prelude.Extensionality.html#4153" class="Bound">g</a> <a id="4155" class="Symbol">:</a> <a id="4157" href="Prelude.Extensionality.html#4129" class="Bound">A</a> <a id="4159" class="Symbol">→</a> <a id="4161" href="Prelude.Extensionality.html#4140" class="Bound">B</a><a id="4162" class="Symbol">}</a> <a id="4164" class="Symbol">→</a> <a id="4166" href="Prelude.Extensionality.html#4151" class="Bound">f</a> <a id="4168" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4170" href="Prelude.Extensionality.html#4153" class="Bound">g</a> <a id="4172" class="Symbol">→</a> <a id="4174" href="Prelude.Extensionality.html#4151" class="Bound">f</a> <a id="4176" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4178" href="Prelude.Extensionality.html#4153" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4366" href="Prelude.Extensionality.html#4366" class="Function">dfunext</a> <a id="4374" class="Symbol">:</a> <a id="4376" class="Symbol">∀</a> <a id="4378" href="Prelude.Extensionality.html#4378" class="Bound">𝓤</a> <a id="4380" href="Prelude.Extensionality.html#4380" class="Bound">𝓦</a> <a id="4382" class="Symbol">→</a> <a id="4384" href="Prelude.Extensionality.html#4378" class="Bound">𝓤</a> <a id="4386" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4388" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4390" href="Prelude.Extensionality.html#4380" class="Bound">𝓦</a> <a id="4392" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4394" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4397" href="Prelude.Extensionality.html#4366" class="Function">dfunext</a> <a id="4405" href="Prelude.Extensionality.html#4405" class="Bound">𝓤</a> <a id="4407" href="Prelude.Extensionality.html#4407" class="Bound">𝓦</a> <a id="4409" class="Symbol">=</a> <a id="4411" class="Symbol">{</a><a id="4412" href="Prelude.Extensionality.html#4412" class="Bound">A</a> <a id="4414" class="Symbol">:</a> <a id="4416" href="Prelude.Extensionality.html#4405" class="Bound">𝓤</a> <a id="4418" href="Universes.html#403" class="Function Operator">̇</a> <a id="4420" class="Symbol">}{</a><a id="4422" href="Prelude.Extensionality.html#4422" class="Bound">B</a> <a id="4424" class="Symbol">:</a> <a id="4426" href="Prelude.Extensionality.html#4412" class="Bound">A</a> <a id="4428" class="Symbol">→</a> <a id="4430" href="Prelude.Extensionality.html#4407" class="Bound">𝓦</a> <a id="4432" href="Universes.html#403" class="Function Operator">̇</a> <a id="4434" class="Symbol">}{</a><a id="4436" href="Prelude.Extensionality.html#4436" class="Bound">f</a> <a id="4438" href="Prelude.Extensionality.html#4438" class="Bound">g</a> <a id="4440" class="Symbol">:</a> <a id="4442" class="Symbol">∀(</a><a id="4444" href="Prelude.Extensionality.html#4444" class="Bound">x</a> <a id="4446" class="Symbol">:</a> <a id="4448" href="Prelude.Extensionality.html#4412" class="Bound">A</a><a id="4449" class="Symbol">)</a> <a id="4451" class="Symbol">→</a> <a id="4453" href="Prelude.Extensionality.html#4422" class="Bound">B</a> <a id="4455" href="Prelude.Extensionality.html#4444" class="Bound">x</a><a id="4456" class="Symbol">}</a> <a id="4458" class="Symbol">→</a>  <a id="4461" href="Prelude.Extensionality.html#4436" class="Bound">f</a> <a id="4463" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4465" href="Prelude.Extensionality.html#4438" class="Bound">g</a>  <a id="4468" class="Symbol">→</a>  <a id="4471" href="Prelude.Extensionality.html#4436" class="Bound">f</a> <a id="4473" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4475" href="Prelude.Extensionality.html#4438" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5047" href="Prelude.Extensionality.html#5047" class="Function">global-funext</a> <a id="5061" class="Symbol">:</a> <a id="5063" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5067" href="Prelude.Extensionality.html#5047" class="Function">global-funext</a> <a id="5081" class="Symbol">=</a> <a id="5083" class="Symbol">∀</a>  <a id="5086" class="Symbol">{</a><a id="5087" href="Prelude.Extensionality.html#5087" class="Bound">𝓤</a> <a id="5089" href="Prelude.Extensionality.html#5089" class="Bound">𝓥</a><a id="5090" class="Symbol">}</a> <a id="5092" class="Symbol">→</a> <a id="5094" href="Prelude.Extensionality.html#4084" class="Function">funext</a> <a id="5101" href="Prelude.Extensionality.html#5087" class="Bound">𝓤</a> <a id="5103" href="Prelude.Extensionality.html#5089" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5107" href="Prelude.Extensionality.html#5107" class="Function">global-dfunext</a> <a id="5122" class="Symbol">:</a> <a id="5124" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="5128" href="Prelude.Extensionality.html#5107" class="Function">global-dfunext</a> <a id="5143" class="Symbol">=</a> <a id="5145" class="Symbol">∀</a> <a id="5147" class="Symbol">{</a><a id="5148" href="Prelude.Extensionality.html#5148" class="Bound">𝓤</a> <a id="5150" href="Prelude.Extensionality.html#5150" class="Bound">𝓥</a><a id="5151" class="Symbol">}</a> <a id="5153" class="Symbol">→</a> <a id="5155" href="Prelude.Extensionality.html#4084" class="Function">funext</a> <a id="5162" href="Prelude.Extensionality.html#5148" class="Bound">𝓤</a> <a id="5164" href="Prelude.Extensionality.html#5150" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5360" href="Prelude.Extensionality.html#5360" class="Function">extensionality-lemma</a> <a id="5381" class="Symbol">:</a> <a id="5383" class="Symbol">{</a><a id="5384" href="Prelude.Extensionality.html#5384" class="Bound">𝓘</a> <a id="5386" href="Prelude.Extensionality.html#5386" class="Bound">𝓤</a> <a id="5388" href="Prelude.Extensionality.html#5388" class="Bound">𝓥</a> <a id="5390" href="Prelude.Extensionality.html#5390" class="Bound">𝓣</a> <a id="5392" class="Symbol">:</a> <a id="5394" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5402" class="Symbol">}{</a><a id="5404" href="Prelude.Extensionality.html#5404" class="Bound">I</a> <a id="5406" class="Symbol">:</a> <a id="5408" href="Prelude.Extensionality.html#5384" class="Bound">𝓘</a> <a id="5410" href="Universes.html#403" class="Function Operator">̇</a> <a id="5412" class="Symbol">}{</a><a id="5414" href="Prelude.Extensionality.html#5414" class="Bound">X</a> <a id="5416" class="Symbol">:</a> <a id="5418" href="Prelude.Extensionality.html#5386" class="Bound">𝓤</a> <a id="5420" href="Universes.html#403" class="Function Operator">̇</a> <a id="5422" class="Symbol">}{</a><a id="5424" href="Prelude.Extensionality.html#5424" class="Bound">A</a> <a id="5426" class="Symbol">:</a> <a id="5428" href="Prelude.Extensionality.html#5404" class="Bound">I</a> <a id="5430" class="Symbol">→</a> <a id="5432" href="Prelude.Extensionality.html#5388" class="Bound">𝓥</a> <a id="5434" href="Universes.html#403" class="Function Operator">̇</a> <a id="5436" class="Symbol">}</a>
                       <a id="5461" class="Symbol">(</a><a id="5462" href="Prelude.Extensionality.html#5462" class="Bound">p</a> <a id="5464" href="Prelude.Extensionality.html#5464" class="Bound">q</a> <a id="5466" class="Symbol">:</a> <a id="5468" class="Symbol">(</a><a id="5469" href="Prelude.Extensionality.html#5469" class="Bound">i</a> <a id="5471" class="Symbol">:</a> <a id="5473" href="Prelude.Extensionality.html#5404" class="Bound">I</a><a id="5474" class="Symbol">)</a> <a id="5476" class="Symbol">→</a> <a id="5478" class="Symbol">(</a><a id="5479" href="Prelude.Extensionality.html#5414" class="Bound">X</a> <a id="5481" class="Symbol">→</a> <a id="5483" href="Prelude.Extensionality.html#5424" class="Bound">A</a> <a id="5485" href="Prelude.Extensionality.html#5469" class="Bound">i</a><a id="5486" class="Symbol">)</a> <a id="5488" class="Symbol">→</a> <a id="5490" href="Prelude.Extensionality.html#5390" class="Bound">𝓣</a> <a id="5492" href="Universes.html#403" class="Function Operator">̇</a> <a id="5494" class="Symbol">)(</a><a id="5496" href="Prelude.Extensionality.html#5496" class="Bound">args</a> <a id="5501" class="Symbol">:</a> <a id="5503" href="Prelude.Extensionality.html#5414" class="Bound">X</a> <a id="5505" class="Symbol">→</a> <a id="5507" class="Symbol">(</a><a id="5508" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5510" href="Prelude.Extensionality.html#5424" class="Bound">A</a><a id="5511" class="Symbol">))</a>
 <a id="5515" class="Symbol">→</a>                     <a id="5537" href="Prelude.Extensionality.html#5462" class="Bound">p</a> <a id="5539" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5541" href="Prelude.Extensionality.html#5464" class="Bound">q</a>
                       <a id="5566" class="Comment">-------------------------------------------------------------</a>
 <a id="5629" class="Symbol">→</a>                     <a id="5651" class="Symbol">(λ</a> <a id="5654" href="Prelude.Extensionality.html#5654" class="Bound">i</a> <a id="5656" class="Symbol">→</a> <a id="5658" class="Symbol">(</a><a id="5659" href="Prelude.Extensionality.html#5462" class="Bound">p</a> <a id="5661" href="Prelude.Extensionality.html#5654" class="Bound">i</a><a id="5662" class="Symbol">)(λ</a> <a id="5666" href="Prelude.Extensionality.html#5666" class="Bound">x</a> <a id="5668" class="Symbol">→</a> <a id="5670" href="Prelude.Extensionality.html#5496" class="Bound">args</a> <a id="5675" href="Prelude.Extensionality.html#5666" class="Bound">x</a> <a id="5677" href="Prelude.Extensionality.html#5654" class="Bound">i</a><a id="5678" class="Symbol">))</a> <a id="5681" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5683" class="Symbol">(λ</a> <a id="5686" href="Prelude.Extensionality.html#5686" class="Bound">i</a> <a id="5688" class="Symbol">→</a> <a id="5690" class="Symbol">(</a><a id="5691" href="Prelude.Extensionality.html#5464" class="Bound">q</a> <a id="5693" href="Prelude.Extensionality.html#5686" class="Bound">i</a><a id="5694" class="Symbol">)(λ</a> <a id="5698" href="Prelude.Extensionality.html#5698" class="Bound">x</a> <a id="5700" class="Symbol">→</a> <a id="5702" href="Prelude.Extensionality.html#5496" class="Bound">args</a> <a id="5707" href="Prelude.Extensionality.html#5698" class="Bound">x</a> <a id="5709" href="Prelude.Extensionality.html#5686" class="Bound">i</a><a id="5710" class="Symbol">))</a>

<a id="5714" href="Prelude.Extensionality.html#5360" class="Function">extensionality-lemma</a> <a id="5735" href="Prelude.Extensionality.html#5735" class="Bound">p</a> <a id="5737" href="Prelude.Extensionality.html#5737" class="Bound">q</a> <a id="5739" href="Prelude.Extensionality.html#5739" class="Bound">args</a> <a id="5744" href="Prelude.Extensionality.html#5744" class="Bound">p≡q</a> <a id="5748" class="Symbol">=</a> <a id="5750" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5753" class="Symbol">(λ</a> <a id="5756" href="Prelude.Extensionality.html#5756" class="Bound">-</a> <a id="5758" class="Symbol">→</a> <a id="5760" class="Symbol">λ</a> <a id="5762" href="Prelude.Extensionality.html#5762" class="Bound">i</a> <a id="5764" class="Symbol">→</a> <a id="5766" class="Symbol">(</a><a id="5767" href="Prelude.Extensionality.html#5756" class="Bound">-</a> <a id="5769" href="Prelude.Extensionality.html#5762" class="Bound">i</a><a id="5770" class="Symbol">)</a> <a id="5772" class="Symbol">(λ</a> <a id="5775" href="Prelude.Extensionality.html#5775" class="Bound">x</a> <a id="5777" class="Symbol">→</a> <a id="5779" href="Prelude.Extensionality.html#5739" class="Bound">args</a> <a id="5784" href="Prelude.Extensionality.html#5775" class="Bound">x</a> <a id="5786" href="Prelude.Extensionality.html#5762" class="Bound">i</a><a id="5787" class="Symbol">))</a> <a id="5790" href="Prelude.Extensionality.html#5744" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="5945" class="Keyword">open</a> <a id="5950" class="Keyword">import</a> <a id="5957" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="5966" class="Keyword">using</a> <a id="5972" class="Symbol">(</a><a id="5973" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="5976" class="Symbol">)</a>

<a id="extfun"></a><a id="5979" href="Prelude.Extensionality.html#5979" class="Function">extfun</a> <a id="5986" class="Symbol">:</a> <a id="5988" class="Symbol">{</a><a id="5989" href="Prelude.Extensionality.html#5989" class="Bound">𝓤</a> <a id="5991" href="Prelude.Extensionality.html#5991" class="Bound">𝓦</a> <a id="5993" class="Symbol">:</a> <a id="5995" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6003" class="Symbol">}{</a><a id="6005" href="Prelude.Extensionality.html#6005" class="Bound">A</a> <a id="6007" class="Symbol">:</a> <a id="6009" href="Prelude.Extensionality.html#5989" class="Bound">𝓤</a> <a id="6011" href="Universes.html#403" class="Function Operator">̇</a><a id="6012" class="Symbol">}{</a><a id="6014" href="Prelude.Extensionality.html#6014" class="Bound">B</a> <a id="6016" class="Symbol">:</a> <a id="6018" href="Prelude.Extensionality.html#5991" class="Bound">𝓦</a> <a id="6020" href="Universes.html#403" class="Function Operator">̇</a><a id="6021" class="Symbol">}{</a><a id="6023" href="Prelude.Extensionality.html#6023" class="Bound">f</a> <a id="6025" href="Prelude.Extensionality.html#6025" class="Bound">g</a> <a id="6027" class="Symbol">:</a> <a id="6029" href="Prelude.Extensionality.html#6005" class="Bound">A</a> <a id="6031" class="Symbol">→</a> <a id="6033" href="Prelude.Extensionality.html#6014" class="Bound">B</a><a id="6034" class="Symbol">}</a> <a id="6036" class="Symbol">→</a> <a id="6038" href="Prelude.Extensionality.html#6023" class="Bound">f</a> <a id="6040" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6042" href="Prelude.Extensionality.html#6025" class="Bound">g</a>  <a id="6045" class="Symbol">→</a>  <a id="6048" href="Prelude.Extensionality.html#6023" class="Bound">f</a> <a id="6050" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6052" href="Prelude.Extensionality.html#6025" class="Bound">g</a>
<a id="6054" href="Prelude.Extensionality.html#5979" class="Function">extfun</a> <a id="6061" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6066" class="Symbol">_</a>  <a id="6069" class="Symbol">=</a> <a id="6071" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6155" href="Prelude.Extensionality.html#6155" class="Function">extdfun</a> <a id="6163" class="Symbol">:</a> <a id="6165" class="Symbol">{</a><a id="6166" href="Prelude.Extensionality.html#6166" class="Bound">𝓤</a> <a id="6168" href="Prelude.Extensionality.html#6168" class="Bound">𝓦</a> <a id="6170" class="Symbol">:</a> <a id="6172" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6180" class="Symbol">}</a> <a id="6182" class="Symbol">{</a><a id="6183" href="Prelude.Extensionality.html#6183" class="Bound">A</a> <a id="6185" class="Symbol">:</a> <a id="6187" href="Prelude.Extensionality.html#6166" class="Bound">𝓤</a> <a id="6189" href="Universes.html#403" class="Function Operator">̇</a> <a id="6191" class="Symbol">}</a> <a id="6193" class="Symbol">{</a><a id="6194" href="Prelude.Extensionality.html#6194" class="Bound">B</a> <a id="6196" class="Symbol">:</a> <a id="6198" href="Prelude.Extensionality.html#6183" class="Bound">A</a> <a id="6200" class="Symbol">→</a> <a id="6202" href="Prelude.Extensionality.html#6168" class="Bound">𝓦</a> <a id="6204" href="Universes.html#403" class="Function Operator">̇</a> <a id="6206" class="Symbol">}</a> <a id="6208" class="Symbol">{</a><a id="6209" href="Prelude.Extensionality.html#6209" class="Bound">f</a> <a id="6211" href="Prelude.Extensionality.html#6211" class="Bound">g</a> <a id="6213" class="Symbol">:</a> <a id="6215" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6217" href="Prelude.Extensionality.html#6194" class="Bound">B</a><a id="6218" class="Symbol">}</a> <a id="6220" class="Symbol">→</a> <a id="6222" href="Prelude.Extensionality.html#6209" class="Bound">f</a> <a id="6224" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6226" href="Prelude.Extensionality.html#6211" class="Bound">g</a> <a id="6228" class="Symbol">→</a> <a id="6230" href="Prelude.Extensionality.html#6209" class="Bound">f</a> <a id="6232" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6234" href="Prelude.Extensionality.html#6211" class="Bound">g</a>
<a id="6236" href="Prelude.Extensionality.html#6155" class="Function">extdfun</a> <a id="6244" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6249" class="Symbol">_</a> <a id="6251" class="Symbol">=</a> <a id="6253" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

<fieldset style="border: 1px #EA9258 dotted">
 <legend style="border: 1px #5F38AD solid;margin-left: 1em; padding: 0.2em 0.8em ">Agda Note</legend>
An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted in Foundations Box above, the existence of such a witness cannot be proved in Martin-L\"of type theory.
</div>
</div>

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
