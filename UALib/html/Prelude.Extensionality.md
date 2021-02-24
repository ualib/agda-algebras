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

<fieldset style="border: 1px #A020F0 solid">
<legend style="border: 1px #A020F0 solid;margin-left: 0.1em; padding: 0.2em 0.2em ">MLTT Foundations</legend>
As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fieldset>


<div class="color_box" id="mltt-ext">
  <div id="title">MLTT Foundations</div>
  <div id="content">As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
  </div>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4461" href="Prelude.Extensionality.html#4461" class="Function">funext</a> <a id="4468" class="Symbol">:</a> <a id="4470" class="Symbol">∀</a> <a id="4472" href="Prelude.Extensionality.html#4472" class="Bound">𝓤</a> <a id="4474" href="Prelude.Extensionality.html#4474" class="Bound">𝓦</a>  <a id="4477" class="Symbol">→</a> <a id="4479" href="Prelude.Extensionality.html#4472" class="Bound">𝓤</a> <a id="4481" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4483" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4485" href="Prelude.Extensionality.html#4474" class="Bound">𝓦</a> <a id="4487" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4489" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4492" href="Prelude.Extensionality.html#4461" class="Function">funext</a> <a id="4499" href="Prelude.Extensionality.html#4499" class="Bound">𝓤</a> <a id="4501" href="Prelude.Extensionality.html#4501" class="Bound">𝓦</a> <a id="4503" class="Symbol">=</a> <a id="4505" class="Symbol">{</a><a id="4506" href="Prelude.Extensionality.html#4506" class="Bound">A</a> <a id="4508" class="Symbol">:</a> <a id="4510" href="Prelude.Extensionality.html#4499" class="Bound">𝓤</a> <a id="4512" href="universes.html#758" class="Function Operator">̇</a> <a id="4514" class="Symbol">}</a> <a id="4516" class="Symbol">{</a><a id="4517" href="Prelude.Extensionality.html#4517" class="Bound">B</a> <a id="4519" class="Symbol">:</a> <a id="4521" href="Prelude.Extensionality.html#4501" class="Bound">𝓦</a> <a id="4523" href="universes.html#758" class="Function Operator">̇</a> <a id="4525" class="Symbol">}</a> <a id="4527" class="Symbol">{</a><a id="4528" href="Prelude.Extensionality.html#4528" class="Bound">f</a> <a id="4530" href="Prelude.Extensionality.html#4530" class="Bound">g</a> <a id="4532" class="Symbol">:</a> <a id="4534" href="Prelude.Extensionality.html#4506" class="Bound">A</a> <a id="4536" class="Symbol">→</a> <a id="4538" href="Prelude.Extensionality.html#4517" class="Bound">B</a><a id="4539" class="Symbol">}</a> <a id="4541" class="Symbol">→</a> <a id="4543" href="Prelude.Extensionality.html#4528" class="Bound">f</a> <a id="4545" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4547" href="Prelude.Extensionality.html#4530" class="Bound">g</a> <a id="4549" class="Symbol">→</a> <a id="4551" href="Prelude.Extensionality.html#4528" class="Bound">f</a> <a id="4553" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4555" href="Prelude.Extensionality.html#4530" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4743" href="Prelude.Extensionality.html#4743" class="Function">dfunext</a> <a id="4751" class="Symbol">:</a> <a id="4753" class="Symbol">∀</a> <a id="4755" href="Prelude.Extensionality.html#4755" class="Bound">𝓤</a> <a id="4757" href="Prelude.Extensionality.html#4757" class="Bound">𝓦</a> <a id="4759" class="Symbol">→</a> <a id="4761" href="Prelude.Extensionality.html#4755" class="Bound">𝓤</a> <a id="4763" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4765" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4767" href="Prelude.Extensionality.html#4757" class="Bound">𝓦</a> <a id="4769" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4771" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4774" href="Prelude.Extensionality.html#4743" class="Function">dfunext</a> <a id="4782" href="Prelude.Extensionality.html#4782" class="Bound">𝓤</a> <a id="4784" href="Prelude.Extensionality.html#4784" class="Bound">𝓦</a> <a id="4786" class="Symbol">=</a> <a id="4788" class="Symbol">{</a><a id="4789" href="Prelude.Extensionality.html#4789" class="Bound">A</a> <a id="4791" class="Symbol">:</a> <a id="4793" href="Prelude.Extensionality.html#4782" class="Bound">𝓤</a> <a id="4795" href="universes.html#758" class="Function Operator">̇</a> <a id="4797" class="Symbol">}{</a><a id="4799" href="Prelude.Extensionality.html#4799" class="Bound">B</a> <a id="4801" class="Symbol">:</a> <a id="4803" href="Prelude.Extensionality.html#4789" class="Bound">A</a> <a id="4805" class="Symbol">→</a> <a id="4807" href="Prelude.Extensionality.html#4784" class="Bound">𝓦</a> <a id="4809" href="universes.html#758" class="Function Operator">̇</a> <a id="4811" class="Symbol">}{</a><a id="4813" href="Prelude.Extensionality.html#4813" class="Bound">f</a> <a id="4815" href="Prelude.Extensionality.html#4815" class="Bound">g</a> <a id="4817" class="Symbol">:</a> <a id="4819" class="Symbol">∀(</a><a id="4821" href="Prelude.Extensionality.html#4821" class="Bound">x</a> <a id="4823" class="Symbol">:</a> <a id="4825" href="Prelude.Extensionality.html#4789" class="Bound">A</a><a id="4826" class="Symbol">)</a> <a id="4828" class="Symbol">→</a> <a id="4830" href="Prelude.Extensionality.html#4799" class="Bound">B</a> <a id="4832" href="Prelude.Extensionality.html#4821" class="Bound">x</a><a id="4833" class="Symbol">}</a> <a id="4835" class="Symbol">→</a>  <a id="4838" href="Prelude.Extensionality.html#4813" class="Bound">f</a> <a id="4840" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4842" href="Prelude.Extensionality.html#4815" class="Bound">g</a>  <a id="4845" class="Symbol">→</a>  <a id="4848" href="Prelude.Extensionality.html#4813" class="Bound">f</a> <a id="4850" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4852" href="Prelude.Extensionality.html#4815" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5424" href="Prelude.Extensionality.html#5424" class="Function">global-funext</a> <a id="5438" class="Symbol">:</a> <a id="5440" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5444" href="Prelude.Extensionality.html#5424" class="Function">global-funext</a> <a id="5458" class="Symbol">=</a> <a id="5460" class="Symbol">∀</a>  <a id="5463" class="Symbol">{</a><a id="5464" href="Prelude.Extensionality.html#5464" class="Bound">𝓤</a> <a id="5466" href="Prelude.Extensionality.html#5466" class="Bound">𝓥</a><a id="5467" class="Symbol">}</a> <a id="5469" class="Symbol">→</a> <a id="5471" href="Prelude.Extensionality.html#4461" class="Function">funext</a> <a id="5478" href="Prelude.Extensionality.html#5464" class="Bound">𝓤</a> <a id="5480" href="Prelude.Extensionality.html#5466" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5484" href="Prelude.Extensionality.html#5484" class="Function">global-dfunext</a> <a id="5499" class="Symbol">:</a> <a id="5501" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5505" href="Prelude.Extensionality.html#5484" class="Function">global-dfunext</a> <a id="5520" class="Symbol">=</a> <a id="5522" class="Symbol">∀</a> <a id="5524" class="Symbol">{</a><a id="5525" href="Prelude.Extensionality.html#5525" class="Bound">𝓤</a> <a id="5527" href="Prelude.Extensionality.html#5527" class="Bound">𝓥</a><a id="5528" class="Symbol">}</a> <a id="5530" class="Symbol">→</a> <a id="5532" href="Prelude.Extensionality.html#4461" class="Function">funext</a> <a id="5539" href="Prelude.Extensionality.html#5525" class="Bound">𝓤</a> <a id="5541" href="Prelude.Extensionality.html#5527" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5737" href="Prelude.Extensionality.html#5737" class="Function">extensionality-lemma</a> <a id="5758" class="Symbol">:</a> <a id="5760" class="Symbol">{</a><a id="5761" href="Prelude.Extensionality.html#5761" class="Bound">𝓘</a> <a id="5763" href="Prelude.Extensionality.html#5763" class="Bound">𝓤</a> <a id="5765" href="Prelude.Extensionality.html#5765" class="Bound">𝓥</a> <a id="5767" href="Prelude.Extensionality.html#5767" class="Bound">𝓣</a> <a id="5769" class="Symbol">:</a> <a id="5771" href="universes.html#551" class="Postulate">Universe</a><a id="5779" class="Symbol">}{</a><a id="5781" href="Prelude.Extensionality.html#5781" class="Bound">I</a> <a id="5783" class="Symbol">:</a> <a id="5785" href="Prelude.Extensionality.html#5761" class="Bound">𝓘</a> <a id="5787" href="universes.html#758" class="Function Operator">̇</a> <a id="5789" class="Symbol">}{</a><a id="5791" href="Prelude.Extensionality.html#5791" class="Bound">X</a> <a id="5793" class="Symbol">:</a> <a id="5795" href="Prelude.Extensionality.html#5763" class="Bound">𝓤</a> <a id="5797" href="universes.html#758" class="Function Operator">̇</a> <a id="5799" class="Symbol">}{</a><a id="5801" href="Prelude.Extensionality.html#5801" class="Bound">A</a> <a id="5803" class="Symbol">:</a> <a id="5805" href="Prelude.Extensionality.html#5781" class="Bound">I</a> <a id="5807" class="Symbol">→</a> <a id="5809" href="Prelude.Extensionality.html#5765" class="Bound">𝓥</a> <a id="5811" href="universes.html#758" class="Function Operator">̇</a> <a id="5813" class="Symbol">}</a>
                       <a id="5838" class="Symbol">(</a><a id="5839" href="Prelude.Extensionality.html#5839" class="Bound">p</a> <a id="5841" href="Prelude.Extensionality.html#5841" class="Bound">q</a> <a id="5843" class="Symbol">:</a> <a id="5845" class="Symbol">(</a><a id="5846" href="Prelude.Extensionality.html#5846" class="Bound">i</a> <a id="5848" class="Symbol">:</a> <a id="5850" href="Prelude.Extensionality.html#5781" class="Bound">I</a><a id="5851" class="Symbol">)</a> <a id="5853" class="Symbol">→</a> <a id="5855" class="Symbol">(</a><a id="5856" href="Prelude.Extensionality.html#5791" class="Bound">X</a> <a id="5858" class="Symbol">→</a> <a id="5860" href="Prelude.Extensionality.html#5801" class="Bound">A</a> <a id="5862" href="Prelude.Extensionality.html#5846" class="Bound">i</a><a id="5863" class="Symbol">)</a> <a id="5865" class="Symbol">→</a> <a id="5867" href="Prelude.Extensionality.html#5767" class="Bound">𝓣</a> <a id="5869" href="universes.html#758" class="Function Operator">̇</a> <a id="5871" class="Symbol">)(</a><a id="5873" href="Prelude.Extensionality.html#5873" class="Bound">args</a> <a id="5878" class="Symbol">:</a> <a id="5880" href="Prelude.Extensionality.html#5791" class="Bound">X</a> <a id="5882" class="Symbol">→</a> <a id="5884" class="Symbol">(</a><a id="5885" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5887" href="Prelude.Extensionality.html#5801" class="Bound">A</a><a id="5888" class="Symbol">))</a>
 <a id="5892" class="Symbol">→</a>                     <a id="5914" href="Prelude.Extensionality.html#5839" class="Bound">p</a> <a id="5916" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5918" href="Prelude.Extensionality.html#5841" class="Bound">q</a>
                       <a id="5943" class="Comment">-------------------------------------------------------------</a>
 <a id="6006" class="Symbol">→</a>                     <a id="6028" class="Symbol">(λ</a> <a id="6031" href="Prelude.Extensionality.html#6031" class="Bound">i</a> <a id="6033" class="Symbol">→</a> <a id="6035" class="Symbol">(</a><a id="6036" href="Prelude.Extensionality.html#5839" class="Bound">p</a> <a id="6038" href="Prelude.Extensionality.html#6031" class="Bound">i</a><a id="6039" class="Symbol">)(λ</a> <a id="6043" href="Prelude.Extensionality.html#6043" class="Bound">x</a> <a id="6045" class="Symbol">→</a> <a id="6047" href="Prelude.Extensionality.html#5873" class="Bound">args</a> <a id="6052" href="Prelude.Extensionality.html#6043" class="Bound">x</a> <a id="6054" href="Prelude.Extensionality.html#6031" class="Bound">i</a><a id="6055" class="Symbol">))</a> <a id="6058" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6060" class="Symbol">(λ</a> <a id="6063" href="Prelude.Extensionality.html#6063" class="Bound">i</a> <a id="6065" class="Symbol">→</a> <a id="6067" class="Symbol">(</a><a id="6068" href="Prelude.Extensionality.html#5841" class="Bound">q</a> <a id="6070" href="Prelude.Extensionality.html#6063" class="Bound">i</a><a id="6071" class="Symbol">)(λ</a> <a id="6075" href="Prelude.Extensionality.html#6075" class="Bound">x</a> <a id="6077" class="Symbol">→</a> <a id="6079" href="Prelude.Extensionality.html#5873" class="Bound">args</a> <a id="6084" href="Prelude.Extensionality.html#6075" class="Bound">x</a> <a id="6086" href="Prelude.Extensionality.html#6063" class="Bound">i</a><a id="6087" class="Symbol">))</a>

<a id="6091" href="Prelude.Extensionality.html#5737" class="Function">extensionality-lemma</a> <a id="6112" href="Prelude.Extensionality.html#6112" class="Bound">p</a> <a id="6114" href="Prelude.Extensionality.html#6114" class="Bound">q</a> <a id="6116" href="Prelude.Extensionality.html#6116" class="Bound">args</a> <a id="6121" href="Prelude.Extensionality.html#6121" class="Bound">p≡q</a> <a id="6125" class="Symbol">=</a> <a id="6127" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="6130" class="Symbol">(λ</a> <a id="6133" href="Prelude.Extensionality.html#6133" class="Bound">-</a> <a id="6135" class="Symbol">→</a> <a id="6137" class="Symbol">λ</a> <a id="6139" href="Prelude.Extensionality.html#6139" class="Bound">i</a> <a id="6141" class="Symbol">→</a> <a id="6143" class="Symbol">(</a><a id="6144" href="Prelude.Extensionality.html#6133" class="Bound">-</a> <a id="6146" href="Prelude.Extensionality.html#6139" class="Bound">i</a><a id="6147" class="Symbol">)</a> <a id="6149" class="Symbol">(λ</a> <a id="6152" href="Prelude.Extensionality.html#6152" class="Bound">x</a> <a id="6154" class="Symbol">→</a> <a id="6156" href="Prelude.Extensionality.html#6116" class="Bound">args</a> <a id="6161" href="Prelude.Extensionality.html#6152" class="Bound">x</a> <a id="6163" href="Prelude.Extensionality.html#6139" class="Bound">i</a><a id="6164" class="Symbol">))</a> <a id="6167" href="Prelude.Extensionality.html#6121" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="6322" class="Keyword">open</a> <a id="6327" class="Keyword">import</a> <a id="6334" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6343" class="Keyword">using</a> <a id="6349" class="Symbol">(</a><a id="6350" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6353" class="Symbol">)</a>

<a id="extfun"></a><a id="6356" href="Prelude.Extensionality.html#6356" class="Function">extfun</a> <a id="6363" class="Symbol">:</a> <a id="6365" class="Symbol">{</a><a id="6366" href="Prelude.Extensionality.html#6366" class="Bound">𝓤</a> <a id="6368" href="Prelude.Extensionality.html#6368" class="Bound">𝓦</a> <a id="6370" class="Symbol">:</a> <a id="6372" href="universes.html#551" class="Postulate">Universe</a><a id="6380" class="Symbol">}{</a><a id="6382" href="Prelude.Extensionality.html#6382" class="Bound">A</a> <a id="6384" class="Symbol">:</a> <a id="6386" href="Prelude.Extensionality.html#6366" class="Bound">𝓤</a> <a id="6388" href="universes.html#758" class="Function Operator">̇</a><a id="6389" class="Symbol">}{</a><a id="6391" href="Prelude.Extensionality.html#6391" class="Bound">B</a> <a id="6393" class="Symbol">:</a> <a id="6395" href="Prelude.Extensionality.html#6368" class="Bound">𝓦</a> <a id="6397" href="universes.html#758" class="Function Operator">̇</a><a id="6398" class="Symbol">}{</a><a id="6400" href="Prelude.Extensionality.html#6400" class="Bound">f</a> <a id="6402" href="Prelude.Extensionality.html#6402" class="Bound">g</a> <a id="6404" class="Symbol">:</a> <a id="6406" href="Prelude.Extensionality.html#6382" class="Bound">A</a> <a id="6408" class="Symbol">→</a> <a id="6410" href="Prelude.Extensionality.html#6391" class="Bound">B</a><a id="6411" class="Symbol">}</a> <a id="6413" class="Symbol">→</a> <a id="6415" href="Prelude.Extensionality.html#6400" class="Bound">f</a> <a id="6417" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6419" href="Prelude.Extensionality.html#6402" class="Bound">g</a>  <a id="6422" class="Symbol">→</a>  <a id="6425" href="Prelude.Extensionality.html#6400" class="Bound">f</a> <a id="6427" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6429" href="Prelude.Extensionality.html#6402" class="Bound">g</a>
<a id="6431" href="Prelude.Extensionality.html#6356" class="Function">extfun</a> <a id="6438" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6443" class="Symbol">_</a>  <a id="6446" class="Symbol">=</a> <a id="6448" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6532" href="Prelude.Extensionality.html#6532" class="Function">extdfun</a> <a id="6540" class="Symbol">:</a> <a id="6542" class="Symbol">{</a><a id="6543" href="Prelude.Extensionality.html#6543" class="Bound">𝓤</a> <a id="6545" href="Prelude.Extensionality.html#6545" class="Bound">𝓦</a> <a id="6547" class="Symbol">:</a> <a id="6549" href="universes.html#551" class="Postulate">Universe</a><a id="6557" class="Symbol">}</a> <a id="6559" class="Symbol">{</a><a id="6560" href="Prelude.Extensionality.html#6560" class="Bound">A</a> <a id="6562" class="Symbol">:</a> <a id="6564" href="Prelude.Extensionality.html#6543" class="Bound">𝓤</a> <a id="6566" href="universes.html#758" class="Function Operator">̇</a> <a id="6568" class="Symbol">}</a> <a id="6570" class="Symbol">{</a><a id="6571" href="Prelude.Extensionality.html#6571" class="Bound">B</a> <a id="6573" class="Symbol">:</a> <a id="6575" href="Prelude.Extensionality.html#6560" class="Bound">A</a> <a id="6577" class="Symbol">→</a> <a id="6579" href="Prelude.Extensionality.html#6545" class="Bound">𝓦</a> <a id="6581" href="universes.html#758" class="Function Operator">̇</a> <a id="6583" class="Symbol">}</a> <a id="6585" class="Symbol">{</a><a id="6586" href="Prelude.Extensionality.html#6586" class="Bound">f</a> <a id="6588" href="Prelude.Extensionality.html#6588" class="Bound">g</a> <a id="6590" class="Symbol">:</a> <a id="6592" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6594" href="Prelude.Extensionality.html#6571" class="Bound">B</a><a id="6595" class="Symbol">}</a> <a id="6597" class="Symbol">→</a> <a id="6599" href="Prelude.Extensionality.html#6586" class="Bound">f</a> <a id="6601" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6603" href="Prelude.Extensionality.html#6588" class="Bound">g</a> <a id="6605" class="Symbol">→</a> <a id="6607" href="Prelude.Extensionality.html#6586" class="Bound">f</a> <a id="6609" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6611" href="Prelude.Extensionality.html#6588" class="Bound">g</a>
<a id="6613" href="Prelude.Extensionality.html#6532" class="Function">extdfun</a> <a id="6621" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6626" class="Symbol">_</a> <a id="6628" class="Symbol">=</a> <a id="6630" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

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
