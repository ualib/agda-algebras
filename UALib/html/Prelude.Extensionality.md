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
 <a id="3125" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3127" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="3129" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3131" class="Symbol">=</a> <a id="3133" class="Symbol">∀</a> <a id="3135" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3137" class="Symbol">→</a> <a id="3139" href="Prelude.Extensionality.html#3125" class="Bound">f</a> <a id="3141" href="Prelude.Extensionality.html#3135" class="Bound">x</a> <a id="3143" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="3145" href="Prelude.Extensionality.html#3129" class="Bound">g</a> <a id="3147" href="Prelude.Extensionality.html#3135" class="Bound">x</a>

 <a id="3151" class="Keyword">infix</a> <a id="3157" class="Number">0</a> <a id="3159" href="Prelude.Extensionality.html#3054" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<span class="footnote"><sup>1</sup></span> However, it is important to keep in mind the following

<fieldset style="border: 1px black solid">
<legend style="border: 1px black solid;margin-left: 1em; padding: 0.2em 0.8em ">Foundations Note</legend>
As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fieldset>


<div><fnote>
<h4><a id="note-on-foundations-function-extensionality-is-independent-of-MLTT">Note on Foundations: function extensionality is independent of MLTT</a></h4>

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fnote>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4521" href="Prelude.Extensionality.html#4521" class="Function">funext</a> <a id="4528" class="Symbol">:</a> <a id="4530" class="Symbol">∀</a> <a id="4532" href="Prelude.Extensionality.html#4532" class="Bound">𝓤</a> <a id="4534" href="Prelude.Extensionality.html#4534" class="Bound">𝓦</a>  <a id="4537" class="Symbol">→</a> <a id="4539" href="Prelude.Extensionality.html#4532" class="Bound">𝓤</a> <a id="4541" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4543" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4545" href="Prelude.Extensionality.html#4534" class="Bound">𝓦</a> <a id="4547" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4549" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4552" href="Prelude.Extensionality.html#4521" class="Function">funext</a> <a id="4559" href="Prelude.Extensionality.html#4559" class="Bound">𝓤</a> <a id="4561" href="Prelude.Extensionality.html#4561" class="Bound">𝓦</a> <a id="4563" class="Symbol">=</a> <a id="4565" class="Symbol">{</a><a id="4566" href="Prelude.Extensionality.html#4566" class="Bound">A</a> <a id="4568" class="Symbol">:</a> <a id="4570" href="Prelude.Extensionality.html#4559" class="Bound">𝓤</a> <a id="4572" href="universes.html#758" class="Function Operator">̇</a> <a id="4574" class="Symbol">}</a> <a id="4576" class="Symbol">{</a><a id="4577" href="Prelude.Extensionality.html#4577" class="Bound">B</a> <a id="4579" class="Symbol">:</a> <a id="4581" href="Prelude.Extensionality.html#4561" class="Bound">𝓦</a> <a id="4583" href="universes.html#758" class="Function Operator">̇</a> <a id="4585" class="Symbol">}</a> <a id="4587" class="Symbol">{</a><a id="4588" href="Prelude.Extensionality.html#4588" class="Bound">f</a> <a id="4590" href="Prelude.Extensionality.html#4590" class="Bound">g</a> <a id="4592" class="Symbol">:</a> <a id="4594" href="Prelude.Extensionality.html#4566" class="Bound">A</a> <a id="4596" class="Symbol">→</a> <a id="4598" href="Prelude.Extensionality.html#4577" class="Bound">B</a><a id="4599" class="Symbol">}</a> <a id="4601" class="Symbol">→</a> <a id="4603" href="Prelude.Extensionality.html#4588" class="Bound">f</a> <a id="4605" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4607" href="Prelude.Extensionality.html#4590" class="Bound">g</a> <a id="4609" class="Symbol">→</a> <a id="4611" href="Prelude.Extensionality.html#4588" class="Bound">f</a> <a id="4613" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="4615" href="Prelude.Extensionality.html#4590" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4803" href="Prelude.Extensionality.html#4803" class="Function">dfunext</a> <a id="4811" class="Symbol">:</a> <a id="4813" class="Symbol">∀</a> <a id="4815" href="Prelude.Extensionality.html#4815" class="Bound">𝓤</a> <a id="4817" href="Prelude.Extensionality.html#4817" class="Bound">𝓦</a> <a id="4819" class="Symbol">→</a> <a id="4821" href="Prelude.Extensionality.html#4815" class="Bound">𝓤</a> <a id="4823" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4825" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4827" href="Prelude.Extensionality.html#4817" class="Bound">𝓦</a> <a id="4829" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4831" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4834" href="Prelude.Extensionality.html#4803" class="Function">dfunext</a> <a id="4842" href="Prelude.Extensionality.html#4842" class="Bound">𝓤</a> <a id="4844" href="Prelude.Extensionality.html#4844" class="Bound">𝓦</a> <a id="4846" class="Symbol">=</a> <a id="4848" class="Symbol">{</a><a id="4849" href="Prelude.Extensionality.html#4849" class="Bound">A</a> <a id="4851" class="Symbol">:</a> <a id="4853" href="Prelude.Extensionality.html#4842" class="Bound">𝓤</a> <a id="4855" href="universes.html#758" class="Function Operator">̇</a> <a id="4857" class="Symbol">}{</a><a id="4859" href="Prelude.Extensionality.html#4859" class="Bound">B</a> <a id="4861" class="Symbol">:</a> <a id="4863" href="Prelude.Extensionality.html#4849" class="Bound">A</a> <a id="4865" class="Symbol">→</a> <a id="4867" href="Prelude.Extensionality.html#4844" class="Bound">𝓦</a> <a id="4869" href="universes.html#758" class="Function Operator">̇</a> <a id="4871" class="Symbol">}{</a><a id="4873" href="Prelude.Extensionality.html#4873" class="Bound">f</a> <a id="4875" href="Prelude.Extensionality.html#4875" class="Bound">g</a> <a id="4877" class="Symbol">:</a> <a id="4879" class="Symbol">∀(</a><a id="4881" href="Prelude.Extensionality.html#4881" class="Bound">x</a> <a id="4883" class="Symbol">:</a> <a id="4885" href="Prelude.Extensionality.html#4849" class="Bound">A</a><a id="4886" class="Symbol">)</a> <a id="4888" class="Symbol">→</a> <a id="4890" href="Prelude.Extensionality.html#4859" class="Bound">B</a> <a id="4892" href="Prelude.Extensionality.html#4881" class="Bound">x</a><a id="4893" class="Symbol">}</a> <a id="4895" class="Symbol">→</a>  <a id="4898" href="Prelude.Extensionality.html#4873" class="Bound">f</a> <a id="4900" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4902" href="Prelude.Extensionality.html#4875" class="Bound">g</a>  <a id="4905" class="Symbol">→</a>  <a id="4908" href="Prelude.Extensionality.html#4873" class="Bound">f</a> <a id="4910" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="4912" href="Prelude.Extensionality.html#4875" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5484" href="Prelude.Extensionality.html#5484" class="Function">global-funext</a> <a id="5498" class="Symbol">:</a> <a id="5500" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5504" href="Prelude.Extensionality.html#5484" class="Function">global-funext</a> <a id="5518" class="Symbol">=</a> <a id="5520" class="Symbol">∀</a>  <a id="5523" class="Symbol">{</a><a id="5524" href="Prelude.Extensionality.html#5524" class="Bound">𝓤</a> <a id="5526" href="Prelude.Extensionality.html#5526" class="Bound">𝓥</a><a id="5527" class="Symbol">}</a> <a id="5529" class="Symbol">→</a> <a id="5531" href="Prelude.Extensionality.html#4521" class="Function">funext</a> <a id="5538" href="Prelude.Extensionality.html#5524" class="Bound">𝓤</a> <a id="5540" href="Prelude.Extensionality.html#5526" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5544" href="Prelude.Extensionality.html#5544" class="Function">global-dfunext</a> <a id="5559" class="Symbol">:</a> <a id="5561" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5565" href="Prelude.Extensionality.html#5544" class="Function">global-dfunext</a> <a id="5580" class="Symbol">=</a> <a id="5582" class="Symbol">∀</a> <a id="5584" class="Symbol">{</a><a id="5585" href="Prelude.Extensionality.html#5585" class="Bound">𝓤</a> <a id="5587" href="Prelude.Extensionality.html#5587" class="Bound">𝓥</a><a id="5588" class="Symbol">}</a> <a id="5590" class="Symbol">→</a> <a id="5592" href="Prelude.Extensionality.html#4521" class="Function">funext</a> <a id="5599" href="Prelude.Extensionality.html#5585" class="Bound">𝓤</a> <a id="5601" href="Prelude.Extensionality.html#5587" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5797" href="Prelude.Extensionality.html#5797" class="Function">extensionality-lemma</a> <a id="5818" class="Symbol">:</a> <a id="5820" class="Symbol">{</a><a id="5821" href="Prelude.Extensionality.html#5821" class="Bound">𝓘</a> <a id="5823" href="Prelude.Extensionality.html#5823" class="Bound">𝓤</a> <a id="5825" href="Prelude.Extensionality.html#5825" class="Bound">𝓥</a> <a id="5827" href="Prelude.Extensionality.html#5827" class="Bound">𝓣</a> <a id="5829" class="Symbol">:</a> <a id="5831" href="universes.html#551" class="Postulate">Universe</a><a id="5839" class="Symbol">}{</a><a id="5841" href="Prelude.Extensionality.html#5841" class="Bound">I</a> <a id="5843" class="Symbol">:</a> <a id="5845" href="Prelude.Extensionality.html#5821" class="Bound">𝓘</a> <a id="5847" href="universes.html#758" class="Function Operator">̇</a> <a id="5849" class="Symbol">}{</a><a id="5851" href="Prelude.Extensionality.html#5851" class="Bound">X</a> <a id="5853" class="Symbol">:</a> <a id="5855" href="Prelude.Extensionality.html#5823" class="Bound">𝓤</a> <a id="5857" href="universes.html#758" class="Function Operator">̇</a> <a id="5859" class="Symbol">}{</a><a id="5861" href="Prelude.Extensionality.html#5861" class="Bound">A</a> <a id="5863" class="Symbol">:</a> <a id="5865" href="Prelude.Extensionality.html#5841" class="Bound">I</a> <a id="5867" class="Symbol">→</a> <a id="5869" href="Prelude.Extensionality.html#5825" class="Bound">𝓥</a> <a id="5871" href="universes.html#758" class="Function Operator">̇</a> <a id="5873" class="Symbol">}</a>
                       <a id="5898" class="Symbol">(</a><a id="5899" href="Prelude.Extensionality.html#5899" class="Bound">p</a> <a id="5901" href="Prelude.Extensionality.html#5901" class="Bound">q</a> <a id="5903" class="Symbol">:</a> <a id="5905" class="Symbol">(</a><a id="5906" href="Prelude.Extensionality.html#5906" class="Bound">i</a> <a id="5908" class="Symbol">:</a> <a id="5910" href="Prelude.Extensionality.html#5841" class="Bound">I</a><a id="5911" class="Symbol">)</a> <a id="5913" class="Symbol">→</a> <a id="5915" class="Symbol">(</a><a id="5916" href="Prelude.Extensionality.html#5851" class="Bound">X</a> <a id="5918" class="Symbol">→</a> <a id="5920" href="Prelude.Extensionality.html#5861" class="Bound">A</a> <a id="5922" href="Prelude.Extensionality.html#5906" class="Bound">i</a><a id="5923" class="Symbol">)</a> <a id="5925" class="Symbol">→</a> <a id="5927" href="Prelude.Extensionality.html#5827" class="Bound">𝓣</a> <a id="5929" href="universes.html#758" class="Function Operator">̇</a> <a id="5931" class="Symbol">)(</a><a id="5933" href="Prelude.Extensionality.html#5933" class="Bound">args</a> <a id="5938" class="Symbol">:</a> <a id="5940" href="Prelude.Extensionality.html#5851" class="Bound">X</a> <a id="5942" class="Symbol">→</a> <a id="5944" class="Symbol">(</a><a id="5945" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5947" href="Prelude.Extensionality.html#5861" class="Bound">A</a><a id="5948" class="Symbol">))</a>
 <a id="5952" class="Symbol">→</a>                     <a id="5974" href="Prelude.Extensionality.html#5899" class="Bound">p</a> <a id="5976" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="5978" href="Prelude.Extensionality.html#5901" class="Bound">q</a>
                       <a id="6003" class="Comment">-------------------------------------------------------------</a>
 <a id="6066" class="Symbol">→</a>                     <a id="6088" class="Symbol">(λ</a> <a id="6091" href="Prelude.Extensionality.html#6091" class="Bound">i</a> <a id="6093" class="Symbol">→</a> <a id="6095" class="Symbol">(</a><a id="6096" href="Prelude.Extensionality.html#5899" class="Bound">p</a> <a id="6098" href="Prelude.Extensionality.html#6091" class="Bound">i</a><a id="6099" class="Symbol">)(λ</a> <a id="6103" href="Prelude.Extensionality.html#6103" class="Bound">x</a> <a id="6105" class="Symbol">→</a> <a id="6107" href="Prelude.Extensionality.html#5933" class="Bound">args</a> <a id="6112" href="Prelude.Extensionality.html#6103" class="Bound">x</a> <a id="6114" href="Prelude.Extensionality.html#6091" class="Bound">i</a><a id="6115" class="Symbol">))</a> <a id="6118" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="6120" class="Symbol">(λ</a> <a id="6123" href="Prelude.Extensionality.html#6123" class="Bound">i</a> <a id="6125" class="Symbol">→</a> <a id="6127" class="Symbol">(</a><a id="6128" href="Prelude.Extensionality.html#5901" class="Bound">q</a> <a id="6130" href="Prelude.Extensionality.html#6123" class="Bound">i</a><a id="6131" class="Symbol">)(λ</a> <a id="6135" href="Prelude.Extensionality.html#6135" class="Bound">x</a> <a id="6137" class="Symbol">→</a> <a id="6139" href="Prelude.Extensionality.html#5933" class="Bound">args</a> <a id="6144" href="Prelude.Extensionality.html#6135" class="Bound">x</a> <a id="6146" href="Prelude.Extensionality.html#6123" class="Bound">i</a><a id="6147" class="Symbol">))</a>

<a id="6151" href="Prelude.Extensionality.html#5797" class="Function">extensionality-lemma</a> <a id="6172" href="Prelude.Extensionality.html#6172" class="Bound">p</a> <a id="6174" href="Prelude.Extensionality.html#6174" class="Bound">q</a> <a id="6176" href="Prelude.Extensionality.html#6176" class="Bound">args</a> <a id="6181" href="Prelude.Extensionality.html#6181" class="Bound">p≡q</a> <a id="6185" class="Symbol">=</a> <a id="6187" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="6190" class="Symbol">(λ</a> <a id="6193" href="Prelude.Extensionality.html#6193" class="Bound">-</a> <a id="6195" class="Symbol">→</a> <a id="6197" class="Symbol">λ</a> <a id="6199" href="Prelude.Extensionality.html#6199" class="Bound">i</a> <a id="6201" class="Symbol">→</a> <a id="6203" class="Symbol">(</a><a id="6204" href="Prelude.Extensionality.html#6193" class="Bound">-</a> <a id="6206" href="Prelude.Extensionality.html#6199" class="Bound">i</a><a id="6207" class="Symbol">)</a> <a id="6209" class="Symbol">(λ</a> <a id="6212" href="Prelude.Extensionality.html#6212" class="Bound">x</a> <a id="6214" class="Symbol">→</a> <a id="6216" href="Prelude.Extensionality.html#6176" class="Bound">args</a> <a id="6221" href="Prelude.Extensionality.html#6212" class="Bound">x</a> <a id="6223" href="Prelude.Extensionality.html#6199" class="Bound">i</a><a id="6224" class="Symbol">))</a> <a id="6227" href="Prelude.Extensionality.html#6181" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<span class="footnote"><sup>2</sup></span>

<pre class="Agda">

<a id="6373" class="Keyword">open</a> <a id="6378" class="Keyword">import</a> <a id="6385" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6394" class="Keyword">using</a> <a id="6400" class="Symbol">(</a><a id="6401" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6404" class="Symbol">)</a>

<a id="extfun"></a><a id="6407" href="Prelude.Extensionality.html#6407" class="Function">extfun</a> <a id="6414" class="Symbol">:</a> <a id="6416" class="Symbol">{</a><a id="6417" href="Prelude.Extensionality.html#6417" class="Bound">𝓤</a> <a id="6419" href="Prelude.Extensionality.html#6419" class="Bound">𝓦</a> <a id="6421" class="Symbol">:</a> <a id="6423" href="universes.html#551" class="Postulate">Universe</a><a id="6431" class="Symbol">}{</a><a id="6433" href="Prelude.Extensionality.html#6433" class="Bound">A</a> <a id="6435" class="Symbol">:</a> <a id="6437" href="Prelude.Extensionality.html#6417" class="Bound">𝓤</a> <a id="6439" href="universes.html#758" class="Function Operator">̇</a><a id="6440" class="Symbol">}{</a><a id="6442" href="Prelude.Extensionality.html#6442" class="Bound">B</a> <a id="6444" class="Symbol">:</a> <a id="6446" href="Prelude.Extensionality.html#6419" class="Bound">𝓦</a> <a id="6448" href="universes.html#758" class="Function Operator">̇</a><a id="6449" class="Symbol">}{</a><a id="6451" href="Prelude.Extensionality.html#6451" class="Bound">f</a> <a id="6453" href="Prelude.Extensionality.html#6453" class="Bound">g</a> <a id="6455" class="Symbol">:</a> <a id="6457" href="Prelude.Extensionality.html#6433" class="Bound">A</a> <a id="6459" class="Symbol">→</a> <a id="6461" href="Prelude.Extensionality.html#6442" class="Bound">B</a><a id="6462" class="Symbol">}</a> <a id="6464" class="Symbol">→</a> <a id="6466" href="Prelude.Extensionality.html#6451" class="Bound">f</a> <a id="6468" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="6470" href="Prelude.Extensionality.html#6453" class="Bound">g</a>  <a id="6473" class="Symbol">→</a>  <a id="6476" href="Prelude.Extensionality.html#6451" class="Bound">f</a> <a id="6478" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6480" href="Prelude.Extensionality.html#6453" class="Bound">g</a>
<a id="6482" href="Prelude.Extensionality.html#6407" class="Function">extfun</a> <a id="6489" href="Prelude.Inverses.html#574" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6494" class="Symbol">_</a>  <a id="6497" class="Symbol">=</a> <a id="6499" href="Prelude.Inverses.html#574" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6583" href="Prelude.Extensionality.html#6583" class="Function">extdfun</a> <a id="6591" class="Symbol">:</a> <a id="6593" class="Symbol">{</a><a id="6594" href="Prelude.Extensionality.html#6594" class="Bound">𝓤</a> <a id="6596" href="Prelude.Extensionality.html#6596" class="Bound">𝓦</a> <a id="6598" class="Symbol">:</a> <a id="6600" href="universes.html#551" class="Postulate">Universe</a><a id="6608" class="Symbol">}</a> <a id="6610" class="Symbol">{</a><a id="6611" href="Prelude.Extensionality.html#6611" class="Bound">A</a> <a id="6613" class="Symbol">:</a> <a id="6615" href="Prelude.Extensionality.html#6594" class="Bound">𝓤</a> <a id="6617" href="universes.html#758" class="Function Operator">̇</a> <a id="6619" class="Symbol">}</a> <a id="6621" class="Symbol">{</a><a id="6622" href="Prelude.Extensionality.html#6622" class="Bound">B</a> <a id="6624" class="Symbol">:</a> <a id="6626" href="Prelude.Extensionality.html#6611" class="Bound">A</a> <a id="6628" class="Symbol">→</a> <a id="6630" href="Prelude.Extensionality.html#6596" class="Bound">𝓦</a> <a id="6632" href="universes.html#758" class="Function Operator">̇</a> <a id="6634" class="Symbol">}</a> <a id="6636" class="Symbol">{</a><a id="6637" href="Prelude.Extensionality.html#6637" class="Bound">f</a> <a id="6639" href="Prelude.Extensionality.html#6639" class="Bound">g</a> <a id="6641" class="Symbol">:</a> <a id="6643" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6645" href="Prelude.Extensionality.html#6622" class="Bound">B</a><a id="6646" class="Symbol">}</a> <a id="6648" class="Symbol">→</a> <a id="6650" href="Prelude.Extensionality.html#6637" class="Bound">f</a> <a id="6652" href="Prelude.Inverses.html#560" class="Datatype Operator">≡</a> <a id="6654" href="Prelude.Extensionality.html#6639" class="Bound">g</a> <a id="6656" class="Symbol">→</a> <a id="6658" href="Prelude.Extensionality.html#6637" class="Bound">f</a> <a id="6660" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6662" href="Prelude.Extensionality.html#6639" class="Bound">g</a>
<a id="6664" href="Prelude.Extensionality.html#6583" class="Function">extdfun</a> <a id="6672" href="Prelude.Inverses.html#574" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6677" class="Symbol">_</a> <a id="6679" class="Symbol">=</a> <a id="6681" href="Prelude.Inverses.html#574" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but, as noted above, the existence of such a witness cannot be proved in Martin-L\"of type theory.

-------------------------------------

<span class="footnote"><sup>1</sup></span>f one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).

<span class="footnote"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
