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


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<a href="fn:ext1"><sup>1</sup></a> However, it is important to keep in mind the following

<fieldset style="border: 1px #A020F0 solid">
<legend style="border: 1px #A020F0 solid;margin-left: 0.2em; padding: 0.2em 0.2em ">Foundations Note</legend>
As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fieldset>


<div class="fnote" id="bill_to">
<h4><a id="note-on-foundations-function-extensionality-is-independent-of-MLTT">Note on Foundations: function extensionality is independent of MLTT</a></h4>

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4530" href="Prelude.Extensionality.html#4530" class="Function">funext</a> <a id="4537" class="Symbol">:</a> <a id="4539" class="Symbol">∀</a> <a id="4541" href="Prelude.Extensionality.html#4541" class="Bound">𝓤</a> <a id="4543" href="Prelude.Extensionality.html#4543" class="Bound">𝓦</a>  <a id="4546" class="Symbol">→</a> <a id="4548" href="Prelude.Extensionality.html#4541" class="Bound">𝓤</a> <a id="4550" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4552" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4554" href="Prelude.Extensionality.html#4543" class="Bound">𝓦</a> <a id="4556" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4558" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4561" href="Prelude.Extensionality.html#4530" class="Function">funext</a> <a id="4568" href="Prelude.Extensionality.html#4568" class="Bound">𝓤</a> <a id="4570" href="Prelude.Extensionality.html#4570" class="Bound">𝓦</a> <a id="4572" class="Symbol">=</a> <a id="4574" class="Symbol">{</a><a id="4575" href="Prelude.Extensionality.html#4575" class="Bound">A</a> <a id="4577" class="Symbol">:</a> <a id="4579" href="Prelude.Extensionality.html#4568" class="Bound">𝓤</a> <a id="4581" href="universes.html#758" class="Function Operator">̇</a> <a id="4583" class="Symbol">}</a> <a id="4585" class="Symbol">{</a><a id="4586" href="Prelude.Extensionality.html#4586" class="Bound">B</a> <a id="4588" class="Symbol">:</a> <a id="4590" href="Prelude.Extensionality.html#4570" class="Bound">𝓦</a> <a id="4592" href="universes.html#758" class="Function Operator">̇</a> <a id="4594" class="Symbol">}</a> <a id="4596" class="Symbol">{</a><a id="4597" href="Prelude.Extensionality.html#4597" class="Bound">f</a> <a id="4599" href="Prelude.Extensionality.html#4599" class="Bound">g</a> <a id="4601" class="Symbol">:</a> <a id="4603" href="Prelude.Extensionality.html#4575" class="Bound">A</a> <a id="4605" class="Symbol">→</a> <a id="4607" href="Prelude.Extensionality.html#4586" class="Bound">B</a><a id="4608" class="Symbol">}</a> <a id="4610" class="Symbol">→</a> <a id="4612" href="Prelude.Extensionality.html#4597" class="Bound">f</a> <a id="4614" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4616" href="Prelude.Extensionality.html#4599" class="Bound">g</a> <a id="4618" class="Symbol">→</a> <a id="4620" href="Prelude.Extensionality.html#4597" class="Bound">f</a> <a id="4622" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4624" href="Prelude.Extensionality.html#4599" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4812" href="Prelude.Extensionality.html#4812" class="Function">dfunext</a> <a id="4820" class="Symbol">:</a> <a id="4822" class="Symbol">∀</a> <a id="4824" href="Prelude.Extensionality.html#4824" class="Bound">𝓤</a> <a id="4826" href="Prelude.Extensionality.html#4826" class="Bound">𝓦</a> <a id="4828" class="Symbol">→</a> <a id="4830" href="Prelude.Extensionality.html#4824" class="Bound">𝓤</a> <a id="4832" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4834" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4836" href="Prelude.Extensionality.html#4826" class="Bound">𝓦</a> <a id="4838" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4840" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4843" href="Prelude.Extensionality.html#4812" class="Function">dfunext</a> <a id="4851" href="Prelude.Extensionality.html#4851" class="Bound">𝓤</a> <a id="4853" href="Prelude.Extensionality.html#4853" class="Bound">𝓦</a> <a id="4855" class="Symbol">=</a> <a id="4857" class="Symbol">{</a><a id="4858" href="Prelude.Extensionality.html#4858" class="Bound">A</a> <a id="4860" class="Symbol">:</a> <a id="4862" href="Prelude.Extensionality.html#4851" class="Bound">𝓤</a> <a id="4864" href="universes.html#758" class="Function Operator">̇</a> <a id="4866" class="Symbol">}{</a><a id="4868" href="Prelude.Extensionality.html#4868" class="Bound">B</a> <a id="4870" class="Symbol">:</a> <a id="4872" href="Prelude.Extensionality.html#4858" class="Bound">A</a> <a id="4874" class="Symbol">→</a> <a id="4876" href="Prelude.Extensionality.html#4853" class="Bound">𝓦</a> <a id="4878" href="universes.html#758" class="Function Operator">̇</a> <a id="4880" class="Symbol">}{</a><a id="4882" href="Prelude.Extensionality.html#4882" class="Bound">f</a> <a id="4884" href="Prelude.Extensionality.html#4884" class="Bound">g</a> <a id="4886" class="Symbol">:</a> <a id="4888" class="Symbol">∀(</a><a id="4890" href="Prelude.Extensionality.html#4890" class="Bound">x</a> <a id="4892" class="Symbol">:</a> <a id="4894" href="Prelude.Extensionality.html#4858" class="Bound">A</a><a id="4895" class="Symbol">)</a> <a id="4897" class="Symbol">→</a> <a id="4899" href="Prelude.Extensionality.html#4868" class="Bound">B</a> <a id="4901" href="Prelude.Extensionality.html#4890" class="Bound">x</a><a id="4902" class="Symbol">}</a> <a id="4904" class="Symbol">→</a>  <a id="4907" href="Prelude.Extensionality.html#4882" class="Bound">f</a> <a id="4909" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4911" href="Prelude.Extensionality.html#4884" class="Bound">g</a>  <a id="4914" class="Symbol">→</a>  <a id="4917" href="Prelude.Extensionality.html#4882" class="Bound">f</a> <a id="4919" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4921" href="Prelude.Extensionality.html#4884" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5493" href="Prelude.Extensionality.html#5493" class="Function">global-funext</a> <a id="5507" class="Symbol">:</a> <a id="5509" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5513" href="Prelude.Extensionality.html#5493" class="Function">global-funext</a> <a id="5527" class="Symbol">=</a> <a id="5529" class="Symbol">∀</a>  <a id="5532" class="Symbol">{</a><a id="5533" href="Prelude.Extensionality.html#5533" class="Bound">𝓤</a> <a id="5535" href="Prelude.Extensionality.html#5535" class="Bound">𝓥</a><a id="5536" class="Symbol">}</a> <a id="5538" class="Symbol">→</a> <a id="5540" href="Prelude.Extensionality.html#4530" class="Function">funext</a> <a id="5547" href="Prelude.Extensionality.html#5533" class="Bound">𝓤</a> <a id="5549" href="Prelude.Extensionality.html#5535" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5553" href="Prelude.Extensionality.html#5553" class="Function">global-dfunext</a> <a id="5568" class="Symbol">:</a> <a id="5570" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5574" href="Prelude.Extensionality.html#5553" class="Function">global-dfunext</a> <a id="5589" class="Symbol">=</a> <a id="5591" class="Symbol">∀</a> <a id="5593" class="Symbol">{</a><a id="5594" href="Prelude.Extensionality.html#5594" class="Bound">𝓤</a> <a id="5596" href="Prelude.Extensionality.html#5596" class="Bound">𝓥</a><a id="5597" class="Symbol">}</a> <a id="5599" class="Symbol">→</a> <a id="5601" href="Prelude.Extensionality.html#4530" class="Function">funext</a> <a id="5608" href="Prelude.Extensionality.html#5594" class="Bound">𝓤</a> <a id="5610" href="Prelude.Extensionality.html#5596" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5806" href="Prelude.Extensionality.html#5806" class="Function">extensionality-lemma</a> <a id="5827" class="Symbol">:</a> <a id="5829" class="Symbol">{</a><a id="5830" href="Prelude.Extensionality.html#5830" class="Bound">𝓘</a> <a id="5832" href="Prelude.Extensionality.html#5832" class="Bound">𝓤</a> <a id="5834" href="Prelude.Extensionality.html#5834" class="Bound">𝓥</a> <a id="5836" href="Prelude.Extensionality.html#5836" class="Bound">𝓣</a> <a id="5838" class="Symbol">:</a> <a id="5840" href="universes.html#551" class="Postulate">Universe</a><a id="5848" class="Symbol">}{</a><a id="5850" href="Prelude.Extensionality.html#5850" class="Bound">I</a> <a id="5852" class="Symbol">:</a> <a id="5854" href="Prelude.Extensionality.html#5830" class="Bound">𝓘</a> <a id="5856" href="universes.html#758" class="Function Operator">̇</a> <a id="5858" class="Symbol">}{</a><a id="5860" href="Prelude.Extensionality.html#5860" class="Bound">X</a> <a id="5862" class="Symbol">:</a> <a id="5864" href="Prelude.Extensionality.html#5832" class="Bound">𝓤</a> <a id="5866" href="universes.html#758" class="Function Operator">̇</a> <a id="5868" class="Symbol">}{</a><a id="5870" href="Prelude.Extensionality.html#5870" class="Bound">A</a> <a id="5872" class="Symbol">:</a> <a id="5874" href="Prelude.Extensionality.html#5850" class="Bound">I</a> <a id="5876" class="Symbol">→</a> <a id="5878" href="Prelude.Extensionality.html#5834" class="Bound">𝓥</a> <a id="5880" href="universes.html#758" class="Function Operator">̇</a> <a id="5882" class="Symbol">}</a>
                       <a id="5907" class="Symbol">(</a><a id="5908" href="Prelude.Extensionality.html#5908" class="Bound">p</a> <a id="5910" href="Prelude.Extensionality.html#5910" class="Bound">q</a> <a id="5912" class="Symbol">:</a> <a id="5914" class="Symbol">(</a><a id="5915" href="Prelude.Extensionality.html#5915" class="Bound">i</a> <a id="5917" class="Symbol">:</a> <a id="5919" href="Prelude.Extensionality.html#5850" class="Bound">I</a><a id="5920" class="Symbol">)</a> <a id="5922" class="Symbol">→</a> <a id="5924" class="Symbol">(</a><a id="5925" href="Prelude.Extensionality.html#5860" class="Bound">X</a> <a id="5927" class="Symbol">→</a> <a id="5929" href="Prelude.Extensionality.html#5870" class="Bound">A</a> <a id="5931" href="Prelude.Extensionality.html#5915" class="Bound">i</a><a id="5932" class="Symbol">)</a> <a id="5934" class="Symbol">→</a> <a id="5936" href="Prelude.Extensionality.html#5836" class="Bound">𝓣</a> <a id="5938" href="universes.html#758" class="Function Operator">̇</a> <a id="5940" class="Symbol">)(</a><a id="5942" href="Prelude.Extensionality.html#5942" class="Bound">args</a> <a id="5947" class="Symbol">:</a> <a id="5949" href="Prelude.Extensionality.html#5860" class="Bound">X</a> <a id="5951" class="Symbol">→</a> <a id="5953" class="Symbol">(</a><a id="5954" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5956" href="Prelude.Extensionality.html#5870" class="Bound">A</a><a id="5957" class="Symbol">))</a>
 <a id="5961" class="Symbol">→</a>                     <a id="5983" href="Prelude.Extensionality.html#5908" class="Bound">p</a> <a id="5985" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="5987" href="Prelude.Extensionality.html#5910" class="Bound">q</a>
                       <a id="6012" class="Comment">-------------------------------------------------------------</a>
 <a id="6075" class="Symbol">→</a>                     <a id="6097" class="Symbol">(λ</a> <a id="6100" href="Prelude.Extensionality.html#6100" class="Bound">i</a> <a id="6102" class="Symbol">→</a> <a id="6104" class="Symbol">(</a><a id="6105" href="Prelude.Extensionality.html#5908" class="Bound">p</a> <a id="6107" href="Prelude.Extensionality.html#6100" class="Bound">i</a><a id="6108" class="Symbol">)(λ</a> <a id="6112" href="Prelude.Extensionality.html#6112" class="Bound">x</a> <a id="6114" class="Symbol">→</a> <a id="6116" href="Prelude.Extensionality.html#5942" class="Bound">args</a> <a id="6121" href="Prelude.Extensionality.html#6112" class="Bound">x</a> <a id="6123" href="Prelude.Extensionality.html#6100" class="Bound">i</a><a id="6124" class="Symbol">))</a> <a id="6127" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6129" class="Symbol">(λ</a> <a id="6132" href="Prelude.Extensionality.html#6132" class="Bound">i</a> <a id="6134" class="Symbol">→</a> <a id="6136" class="Symbol">(</a><a id="6137" href="Prelude.Extensionality.html#5910" class="Bound">q</a> <a id="6139" href="Prelude.Extensionality.html#6132" class="Bound">i</a><a id="6140" class="Symbol">)(λ</a> <a id="6144" href="Prelude.Extensionality.html#6144" class="Bound">x</a> <a id="6146" class="Symbol">→</a> <a id="6148" href="Prelude.Extensionality.html#5942" class="Bound">args</a> <a id="6153" href="Prelude.Extensionality.html#6144" class="Bound">x</a> <a id="6155" href="Prelude.Extensionality.html#6132" class="Bound">i</a><a id="6156" class="Symbol">))</a>

<a id="6160" href="Prelude.Extensionality.html#5806" class="Function">extensionality-lemma</a> <a id="6181" href="Prelude.Extensionality.html#6181" class="Bound">p</a> <a id="6183" href="Prelude.Extensionality.html#6183" class="Bound">q</a> <a id="6185" href="Prelude.Extensionality.html#6185" class="Bound">args</a> <a id="6190" href="Prelude.Extensionality.html#6190" class="Bound">p≡q</a> <a id="6194" class="Symbol">=</a> <a id="6196" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="6199" class="Symbol">(λ</a> <a id="6202" href="Prelude.Extensionality.html#6202" class="Bound">-</a> <a id="6204" class="Symbol">→</a> <a id="6206" class="Symbol">λ</a> <a id="6208" href="Prelude.Extensionality.html#6208" class="Bound">i</a> <a id="6210" class="Symbol">→</a> <a id="6212" class="Symbol">(</a><a id="6213" href="Prelude.Extensionality.html#6202" class="Bound">-</a> <a id="6215" href="Prelude.Extensionality.html#6208" class="Bound">i</a><a id="6216" class="Symbol">)</a> <a id="6218" class="Symbol">(λ</a> <a id="6221" href="Prelude.Extensionality.html#6221" class="Bound">x</a> <a id="6223" class="Symbol">→</a> <a id="6225" href="Prelude.Extensionality.html#6185" class="Bound">args</a> <a id="6230" href="Prelude.Extensionality.html#6221" class="Bound">x</a> <a id="6232" href="Prelude.Extensionality.html#6208" class="Bound">i</a><a id="6233" class="Symbol">))</a> <a id="6236" href="Prelude.Extensionality.html#6190" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<a href="fn:ext2"><sup>2</sup></a>

<pre class="Agda">

<a id="6374" class="Keyword">open</a> <a id="6379" class="Keyword">import</a> <a id="6386" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6395" class="Keyword">using</a> <a id="6401" class="Symbol">(</a><a id="6402" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6405" class="Symbol">)</a>

<a id="extfun"></a><a id="6408" href="Prelude.Extensionality.html#6408" class="Function">extfun</a> <a id="6415" class="Symbol">:</a> <a id="6417" class="Symbol">{</a><a id="6418" href="Prelude.Extensionality.html#6418" class="Bound">𝓤</a> <a id="6420" href="Prelude.Extensionality.html#6420" class="Bound">𝓦</a> <a id="6422" class="Symbol">:</a> <a id="6424" href="universes.html#551" class="Postulate">Universe</a><a id="6432" class="Symbol">}{</a><a id="6434" href="Prelude.Extensionality.html#6434" class="Bound">A</a> <a id="6436" class="Symbol">:</a> <a id="6438" href="Prelude.Extensionality.html#6418" class="Bound">𝓤</a> <a id="6440" href="universes.html#758" class="Function Operator">̇</a><a id="6441" class="Symbol">}{</a><a id="6443" href="Prelude.Extensionality.html#6443" class="Bound">B</a> <a id="6445" class="Symbol">:</a> <a id="6447" href="Prelude.Extensionality.html#6420" class="Bound">𝓦</a> <a id="6449" href="universes.html#758" class="Function Operator">̇</a><a id="6450" class="Symbol">}{</a><a id="6452" href="Prelude.Extensionality.html#6452" class="Bound">f</a> <a id="6454" href="Prelude.Extensionality.html#6454" class="Bound">g</a> <a id="6456" class="Symbol">:</a> <a id="6458" href="Prelude.Extensionality.html#6434" class="Bound">A</a> <a id="6460" class="Symbol">→</a> <a id="6462" href="Prelude.Extensionality.html#6443" class="Bound">B</a><a id="6463" class="Symbol">}</a> <a id="6465" class="Symbol">→</a> <a id="6467" href="Prelude.Extensionality.html#6452" class="Bound">f</a> <a id="6469" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6471" href="Prelude.Extensionality.html#6454" class="Bound">g</a>  <a id="6474" class="Symbol">→</a>  <a id="6477" href="Prelude.Extensionality.html#6452" class="Bound">f</a> <a id="6479" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6481" href="Prelude.Extensionality.html#6454" class="Bound">g</a>
<a id="6483" href="Prelude.Extensionality.html#6408" class="Function">extfun</a> <a id="6490" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6495" class="Symbol">_</a>  <a id="6498" class="Symbol">=</a> <a id="6500" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6584" href="Prelude.Extensionality.html#6584" class="Function">extdfun</a> <a id="6592" class="Symbol">:</a> <a id="6594" class="Symbol">{</a><a id="6595" href="Prelude.Extensionality.html#6595" class="Bound">𝓤</a> <a id="6597" href="Prelude.Extensionality.html#6597" class="Bound">𝓦</a> <a id="6599" class="Symbol">:</a> <a id="6601" href="universes.html#551" class="Postulate">Universe</a><a id="6609" class="Symbol">}</a> <a id="6611" class="Symbol">{</a><a id="6612" href="Prelude.Extensionality.html#6612" class="Bound">A</a> <a id="6614" class="Symbol">:</a> <a id="6616" href="Prelude.Extensionality.html#6595" class="Bound">𝓤</a> <a id="6618" href="universes.html#758" class="Function Operator">̇</a> <a id="6620" class="Symbol">}</a> <a id="6622" class="Symbol">{</a><a id="6623" href="Prelude.Extensionality.html#6623" class="Bound">B</a> <a id="6625" class="Symbol">:</a> <a id="6627" href="Prelude.Extensionality.html#6612" class="Bound">A</a> <a id="6629" class="Symbol">→</a> <a id="6631" href="Prelude.Extensionality.html#6597" class="Bound">𝓦</a> <a id="6633" href="universes.html#758" class="Function Operator">̇</a> <a id="6635" class="Symbol">}</a> <a id="6637" class="Symbol">{</a><a id="6638" href="Prelude.Extensionality.html#6638" class="Bound">f</a> <a id="6640" href="Prelude.Extensionality.html#6640" class="Bound">g</a> <a id="6642" class="Symbol">:</a> <a id="6644" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6646" href="Prelude.Extensionality.html#6623" class="Bound">B</a><a id="6647" class="Symbol">}</a> <a id="6649" class="Symbol">→</a> <a id="6651" href="Prelude.Extensionality.html#6638" class="Bound">f</a> <a id="6653" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6655" href="Prelude.Extensionality.html#6640" class="Bound">g</a> <a id="6657" class="Symbol">→</a> <a id="6659" href="Prelude.Extensionality.html#6638" class="Bound">f</a> <a id="6661" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6663" href="Prelude.Extensionality.html#6640" class="Bound">g</a>
<a id="6665" href="Prelude.Extensionality.html#6584" class="Function">extdfun</a> <a id="6673" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6678" class="Symbol">_</a> <a id="6680" class="Symbol">=</a> <a id="6682" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but, as noted above, the existence of such a witness cannot be proved in Martin-L\"of type theory.

-------------------------------------

<span class="footnote" id="fn:ext1"><sup>1</sup>f one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn:ext2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
