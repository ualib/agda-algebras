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
<legend style="border: 1px #A020F0 solid;margin-left: 0.2em; padding: 0.2em 0.2em ">Foundations Note</legend>
As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</fieldset>


<div class="fnote" id="bill_to">
<h4><a id="note-on-foundations-function-extensionality-is-independent-of-MLTT">Note on Foundations: function extensionality is independent of MLTT</a></h4>

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide.funext"></a><a id="4543" href="Prelude.Extensionality.html#4543" class="Function">funext</a> <a id="4550" class="Symbol">:</a> <a id="4552" class="Symbol">∀</a> <a id="4554" href="Prelude.Extensionality.html#4554" class="Bound">𝓤</a> <a id="4556" href="Prelude.Extensionality.html#4556" class="Bound">𝓦</a>  <a id="4559" class="Symbol">→</a> <a id="4561" href="Prelude.Extensionality.html#4554" class="Bound">𝓤</a> <a id="4563" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4565" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4567" href="Prelude.Extensionality.html#4556" class="Bound">𝓦</a> <a id="4569" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4571" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4574" href="Prelude.Extensionality.html#4543" class="Function">funext</a> <a id="4581" href="Prelude.Extensionality.html#4581" class="Bound">𝓤</a> <a id="4583" href="Prelude.Extensionality.html#4583" class="Bound">𝓦</a> <a id="4585" class="Symbol">=</a> <a id="4587" class="Symbol">{</a><a id="4588" href="Prelude.Extensionality.html#4588" class="Bound">A</a> <a id="4590" class="Symbol">:</a> <a id="4592" href="Prelude.Extensionality.html#4581" class="Bound">𝓤</a> <a id="4594" href="universes.html#758" class="Function Operator">̇</a> <a id="4596" class="Symbol">}</a> <a id="4598" class="Symbol">{</a><a id="4599" href="Prelude.Extensionality.html#4599" class="Bound">B</a> <a id="4601" class="Symbol">:</a> <a id="4603" href="Prelude.Extensionality.html#4583" class="Bound">𝓦</a> <a id="4605" href="universes.html#758" class="Function Operator">̇</a> <a id="4607" class="Symbol">}</a> <a id="4609" class="Symbol">{</a><a id="4610" href="Prelude.Extensionality.html#4610" class="Bound">f</a> <a id="4612" href="Prelude.Extensionality.html#4612" class="Bound">g</a> <a id="4614" class="Symbol">:</a> <a id="4616" href="Prelude.Extensionality.html#4588" class="Bound">A</a> <a id="4618" class="Symbol">→</a> <a id="4620" href="Prelude.Extensionality.html#4599" class="Bound">B</a><a id="4621" class="Symbol">}</a> <a id="4623" class="Symbol">→</a> <a id="4625" href="Prelude.Extensionality.html#4610" class="Bound">f</a> <a id="4627" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4629" href="Prelude.Extensionality.html#4612" class="Bound">g</a> <a id="4631" class="Symbol">→</a> <a id="4633" href="Prelude.Extensionality.html#4610" class="Bound">f</a> <a id="4635" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4637" href="Prelude.Extensionality.html#4612" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide.dfunext"></a><a id="4825" href="Prelude.Extensionality.html#4825" class="Function">dfunext</a> <a id="4833" class="Symbol">:</a> <a id="4835" class="Symbol">∀</a> <a id="4837" href="Prelude.Extensionality.html#4837" class="Bound">𝓤</a> <a id="4839" href="Prelude.Extensionality.html#4839" class="Bound">𝓦</a> <a id="4841" class="Symbol">→</a> <a id="4843" href="Prelude.Extensionality.html#4837" class="Bound">𝓤</a> <a id="4845" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4847" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4849" href="Prelude.Extensionality.html#4839" class="Bound">𝓦</a> <a id="4851" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="4853" href="universes.html#758" class="Function Operator">̇</a>
 <a id="4856" href="Prelude.Extensionality.html#4825" class="Function">dfunext</a> <a id="4864" href="Prelude.Extensionality.html#4864" class="Bound">𝓤</a> <a id="4866" href="Prelude.Extensionality.html#4866" class="Bound">𝓦</a> <a id="4868" class="Symbol">=</a> <a id="4870" class="Symbol">{</a><a id="4871" href="Prelude.Extensionality.html#4871" class="Bound">A</a> <a id="4873" class="Symbol">:</a> <a id="4875" href="Prelude.Extensionality.html#4864" class="Bound">𝓤</a> <a id="4877" href="universes.html#758" class="Function Operator">̇</a> <a id="4879" class="Symbol">}{</a><a id="4881" href="Prelude.Extensionality.html#4881" class="Bound">B</a> <a id="4883" class="Symbol">:</a> <a id="4885" href="Prelude.Extensionality.html#4871" class="Bound">A</a> <a id="4887" class="Symbol">→</a> <a id="4889" href="Prelude.Extensionality.html#4866" class="Bound">𝓦</a> <a id="4891" href="universes.html#758" class="Function Operator">̇</a> <a id="4893" class="Symbol">}{</a><a id="4895" href="Prelude.Extensionality.html#4895" class="Bound">f</a> <a id="4897" href="Prelude.Extensionality.html#4897" class="Bound">g</a> <a id="4899" class="Symbol">:</a> <a id="4901" class="Symbol">∀(</a><a id="4903" href="Prelude.Extensionality.html#4903" class="Bound">x</a> <a id="4905" class="Symbol">:</a> <a id="4907" href="Prelude.Extensionality.html#4871" class="Bound">A</a><a id="4908" class="Symbol">)</a> <a id="4910" class="Symbol">→</a> <a id="4912" href="Prelude.Extensionality.html#4881" class="Bound">B</a> <a id="4914" href="Prelude.Extensionality.html#4903" class="Bound">x</a><a id="4915" class="Symbol">}</a> <a id="4917" class="Symbol">→</a>  <a id="4920" href="Prelude.Extensionality.html#4895" class="Bound">f</a> <a id="4922" href="Prelude.Extensionality.html#3054" class="Function Operator">∼</a> <a id="4924" href="Prelude.Extensionality.html#4897" class="Bound">g</a>  <a id="4927" class="Symbol">→</a>  <a id="4930" href="Prelude.Extensionality.html#4895" class="Bound">f</a> <a id="4932" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="4934" href="Prelude.Extensionality.html#4897" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide.global-funext"></a><a id="5506" href="Prelude.Extensionality.html#5506" class="Function">global-funext</a> <a id="5520" class="Symbol">:</a> <a id="5522" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5526" href="Prelude.Extensionality.html#5506" class="Function">global-funext</a> <a id="5540" class="Symbol">=</a> <a id="5542" class="Symbol">∀</a>  <a id="5545" class="Symbol">{</a><a id="5546" href="Prelude.Extensionality.html#5546" class="Bound">𝓤</a> <a id="5548" href="Prelude.Extensionality.html#5548" class="Bound">𝓥</a><a id="5549" class="Symbol">}</a> <a id="5551" class="Symbol">→</a> <a id="5553" href="Prelude.Extensionality.html#4543" class="Function">funext</a> <a id="5560" href="Prelude.Extensionality.html#5546" class="Bound">𝓤</a> <a id="5562" href="Prelude.Extensionality.html#5548" class="Bound">𝓥</a>

 <a id="hide.global-dfunext"></a><a id="5566" href="Prelude.Extensionality.html#5566" class="Function">global-dfunext</a> <a id="5581" class="Symbol">:</a> <a id="5583" href="universes.html#580" class="Primitive">𝓤ω</a>
 <a id="5587" href="Prelude.Extensionality.html#5566" class="Function">global-dfunext</a> <a id="5602" class="Symbol">=</a> <a id="5604" class="Symbol">∀</a> <a id="5606" class="Symbol">{</a><a id="5607" href="Prelude.Extensionality.html#5607" class="Bound">𝓤</a> <a id="5609" href="Prelude.Extensionality.html#5609" class="Bound">𝓥</a><a id="5610" class="Symbol">}</a> <a id="5612" class="Symbol">→</a> <a id="5614" href="Prelude.Extensionality.html#4543" class="Function">funext</a> <a id="5621" href="Prelude.Extensionality.html#5607" class="Bound">𝓤</a> <a id="5623" href="Prelude.Extensionality.html#5609" class="Bound">𝓥</a>

</pre>


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5819" href="Prelude.Extensionality.html#5819" class="Function">extensionality-lemma</a> <a id="5840" class="Symbol">:</a> <a id="5842" class="Symbol">{</a><a id="5843" href="Prelude.Extensionality.html#5843" class="Bound">𝓘</a> <a id="5845" href="Prelude.Extensionality.html#5845" class="Bound">𝓤</a> <a id="5847" href="Prelude.Extensionality.html#5847" class="Bound">𝓥</a> <a id="5849" href="Prelude.Extensionality.html#5849" class="Bound">𝓣</a> <a id="5851" class="Symbol">:</a> <a id="5853" href="universes.html#551" class="Postulate">Universe</a><a id="5861" class="Symbol">}{</a><a id="5863" href="Prelude.Extensionality.html#5863" class="Bound">I</a> <a id="5865" class="Symbol">:</a> <a id="5867" href="Prelude.Extensionality.html#5843" class="Bound">𝓘</a> <a id="5869" href="universes.html#758" class="Function Operator">̇</a> <a id="5871" class="Symbol">}{</a><a id="5873" href="Prelude.Extensionality.html#5873" class="Bound">X</a> <a id="5875" class="Symbol">:</a> <a id="5877" href="Prelude.Extensionality.html#5845" class="Bound">𝓤</a> <a id="5879" href="universes.html#758" class="Function Operator">̇</a> <a id="5881" class="Symbol">}{</a><a id="5883" href="Prelude.Extensionality.html#5883" class="Bound">A</a> <a id="5885" class="Symbol">:</a> <a id="5887" href="Prelude.Extensionality.html#5863" class="Bound">I</a> <a id="5889" class="Symbol">→</a> <a id="5891" href="Prelude.Extensionality.html#5847" class="Bound">𝓥</a> <a id="5893" href="universes.html#758" class="Function Operator">̇</a> <a id="5895" class="Symbol">}</a>
                       <a id="5920" class="Symbol">(</a><a id="5921" href="Prelude.Extensionality.html#5921" class="Bound">p</a> <a id="5923" href="Prelude.Extensionality.html#5923" class="Bound">q</a> <a id="5925" class="Symbol">:</a> <a id="5927" class="Symbol">(</a><a id="5928" href="Prelude.Extensionality.html#5928" class="Bound">i</a> <a id="5930" class="Symbol">:</a> <a id="5932" href="Prelude.Extensionality.html#5863" class="Bound">I</a><a id="5933" class="Symbol">)</a> <a id="5935" class="Symbol">→</a> <a id="5937" class="Symbol">(</a><a id="5938" href="Prelude.Extensionality.html#5873" class="Bound">X</a> <a id="5940" class="Symbol">→</a> <a id="5942" href="Prelude.Extensionality.html#5883" class="Bound">A</a> <a id="5944" href="Prelude.Extensionality.html#5928" class="Bound">i</a><a id="5945" class="Symbol">)</a> <a id="5947" class="Symbol">→</a> <a id="5949" href="Prelude.Extensionality.html#5849" class="Bound">𝓣</a> <a id="5951" href="universes.html#758" class="Function Operator">̇</a> <a id="5953" class="Symbol">)(</a><a id="5955" href="Prelude.Extensionality.html#5955" class="Bound">args</a> <a id="5960" class="Symbol">:</a> <a id="5962" href="Prelude.Extensionality.html#5873" class="Bound">X</a> <a id="5964" class="Symbol">→</a> <a id="5966" class="Symbol">(</a><a id="5967" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5969" href="Prelude.Extensionality.html#5883" class="Bound">A</a><a id="5970" class="Symbol">))</a>
 <a id="5974" class="Symbol">→</a>                     <a id="5996" href="Prelude.Extensionality.html#5921" class="Bound">p</a> <a id="5998" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6000" href="Prelude.Extensionality.html#5923" class="Bound">q</a>
                       <a id="6025" class="Comment">-------------------------------------------------------------</a>
 <a id="6088" class="Symbol">→</a>                     <a id="6110" class="Symbol">(λ</a> <a id="6113" href="Prelude.Extensionality.html#6113" class="Bound">i</a> <a id="6115" class="Symbol">→</a> <a id="6117" class="Symbol">(</a><a id="6118" href="Prelude.Extensionality.html#5921" class="Bound">p</a> <a id="6120" href="Prelude.Extensionality.html#6113" class="Bound">i</a><a id="6121" class="Symbol">)(λ</a> <a id="6125" href="Prelude.Extensionality.html#6125" class="Bound">x</a> <a id="6127" class="Symbol">→</a> <a id="6129" href="Prelude.Extensionality.html#5955" class="Bound">args</a> <a id="6134" href="Prelude.Extensionality.html#6125" class="Bound">x</a> <a id="6136" href="Prelude.Extensionality.html#6113" class="Bound">i</a><a id="6137" class="Symbol">))</a> <a id="6140" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6142" class="Symbol">(λ</a> <a id="6145" href="Prelude.Extensionality.html#6145" class="Bound">i</a> <a id="6147" class="Symbol">→</a> <a id="6149" class="Symbol">(</a><a id="6150" href="Prelude.Extensionality.html#5923" class="Bound">q</a> <a id="6152" href="Prelude.Extensionality.html#6145" class="Bound">i</a><a id="6153" class="Symbol">)(λ</a> <a id="6157" href="Prelude.Extensionality.html#6157" class="Bound">x</a> <a id="6159" class="Symbol">→</a> <a id="6161" href="Prelude.Extensionality.html#5955" class="Bound">args</a> <a id="6166" href="Prelude.Extensionality.html#6157" class="Bound">x</a> <a id="6168" href="Prelude.Extensionality.html#6145" class="Bound">i</a><a id="6169" class="Symbol">))</a>

<a id="6173" href="Prelude.Extensionality.html#5819" class="Function">extensionality-lemma</a> <a id="6194" href="Prelude.Extensionality.html#6194" class="Bound">p</a> <a id="6196" href="Prelude.Extensionality.html#6196" class="Bound">q</a> <a id="6198" href="Prelude.Extensionality.html#6198" class="Bound">args</a> <a id="6203" href="Prelude.Extensionality.html#6203" class="Bound">p≡q</a> <a id="6207" class="Symbol">=</a> <a id="6209" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="6212" class="Symbol">(λ</a> <a id="6215" href="Prelude.Extensionality.html#6215" class="Bound">-</a> <a id="6217" class="Symbol">→</a> <a id="6219" class="Symbol">λ</a> <a id="6221" href="Prelude.Extensionality.html#6221" class="Bound">i</a> <a id="6223" class="Symbol">→</a> <a id="6225" class="Symbol">(</a><a id="6226" href="Prelude.Extensionality.html#6215" class="Bound">-</a> <a id="6228" href="Prelude.Extensionality.html#6221" class="Bound">i</a><a id="6229" class="Symbol">)</a> <a id="6231" class="Symbol">(λ</a> <a id="6234" href="Prelude.Extensionality.html#6234" class="Bound">x</a> <a id="6236" class="Symbol">→</a> <a id="6238" href="Prelude.Extensionality.html#6198" class="Bound">args</a> <a id="6243" href="Prelude.Extensionality.html#6234" class="Bound">x</a> <a id="6245" href="Prelude.Extensionality.html#6221" class="Bound">i</a><a id="6246" class="Symbol">))</a> <a id="6249" href="Prelude.Extensionality.html#6203" class="Bound">p≡q</a>

</pre>

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

<pre class="Agda">

<a id="6404" class="Keyword">open</a> <a id="6409" class="Keyword">import</a> <a id="6416" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6425" class="Keyword">using</a> <a id="6431" class="Symbol">(</a><a id="6432" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6435" class="Symbol">)</a>

<a id="extfun"></a><a id="6438" href="Prelude.Extensionality.html#6438" class="Function">extfun</a> <a id="6445" class="Symbol">:</a> <a id="6447" class="Symbol">{</a><a id="6448" href="Prelude.Extensionality.html#6448" class="Bound">𝓤</a> <a id="6450" href="Prelude.Extensionality.html#6450" class="Bound">𝓦</a> <a id="6452" class="Symbol">:</a> <a id="6454" href="universes.html#551" class="Postulate">Universe</a><a id="6462" class="Symbol">}{</a><a id="6464" href="Prelude.Extensionality.html#6464" class="Bound">A</a> <a id="6466" class="Symbol">:</a> <a id="6468" href="Prelude.Extensionality.html#6448" class="Bound">𝓤</a> <a id="6470" href="universes.html#758" class="Function Operator">̇</a><a id="6471" class="Symbol">}{</a><a id="6473" href="Prelude.Extensionality.html#6473" class="Bound">B</a> <a id="6475" class="Symbol">:</a> <a id="6477" href="Prelude.Extensionality.html#6450" class="Bound">𝓦</a> <a id="6479" href="universes.html#758" class="Function Operator">̇</a><a id="6480" class="Symbol">}{</a><a id="6482" href="Prelude.Extensionality.html#6482" class="Bound">f</a> <a id="6484" href="Prelude.Extensionality.html#6484" class="Bound">g</a> <a id="6486" class="Symbol">:</a> <a id="6488" href="Prelude.Extensionality.html#6464" class="Bound">A</a> <a id="6490" class="Symbol">→</a> <a id="6492" href="Prelude.Extensionality.html#6473" class="Bound">B</a><a id="6493" class="Symbol">}</a> <a id="6495" class="Symbol">→</a> <a id="6497" href="Prelude.Extensionality.html#6482" class="Bound">f</a> <a id="6499" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6501" href="Prelude.Extensionality.html#6484" class="Bound">g</a>  <a id="6504" class="Symbol">→</a>  <a id="6507" href="Prelude.Extensionality.html#6482" class="Bound">f</a> <a id="6509" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6511" href="Prelude.Extensionality.html#6484" class="Bound">g</a>
<a id="6513" href="Prelude.Extensionality.html#6438" class="Function">extfun</a> <a id="6520" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6525" class="Symbol">_</a>  <a id="6528" class="Symbol">=</a> <a id="6530" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

<a id="extdfun"></a><a id="6614" href="Prelude.Extensionality.html#6614" class="Function">extdfun</a> <a id="6622" class="Symbol">:</a> <a id="6624" class="Symbol">{</a><a id="6625" href="Prelude.Extensionality.html#6625" class="Bound">𝓤</a> <a id="6627" href="Prelude.Extensionality.html#6627" class="Bound">𝓦</a> <a id="6629" class="Symbol">:</a> <a id="6631" href="universes.html#551" class="Postulate">Universe</a><a id="6639" class="Symbol">}</a> <a id="6641" class="Symbol">{</a><a id="6642" href="Prelude.Extensionality.html#6642" class="Bound">A</a> <a id="6644" class="Symbol">:</a> <a id="6646" href="Prelude.Extensionality.html#6625" class="Bound">𝓤</a> <a id="6648" href="universes.html#758" class="Function Operator">̇</a> <a id="6650" class="Symbol">}</a> <a id="6652" class="Symbol">{</a><a id="6653" href="Prelude.Extensionality.html#6653" class="Bound">B</a> <a id="6655" class="Symbol">:</a> <a id="6657" href="Prelude.Extensionality.html#6642" class="Bound">A</a> <a id="6659" class="Symbol">→</a> <a id="6661" href="Prelude.Extensionality.html#6627" class="Bound">𝓦</a> <a id="6663" href="universes.html#758" class="Function Operator">̇</a> <a id="6665" class="Symbol">}</a> <a id="6667" class="Symbol">{</a><a id="6668" href="Prelude.Extensionality.html#6668" class="Bound">f</a> <a id="6670" href="Prelude.Extensionality.html#6670" class="Bound">g</a> <a id="6672" class="Symbol">:</a> <a id="6674" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6676" href="Prelude.Extensionality.html#6653" class="Bound">B</a><a id="6677" class="Symbol">}</a> <a id="6679" class="Symbol">→</a> <a id="6681" href="Prelude.Extensionality.html#6668" class="Bound">f</a> <a id="6683" href="Prelude.Inverses.html#620" class="Datatype Operator">≡</a> <a id="6685" href="Prelude.Extensionality.html#6670" class="Bound">g</a> <a id="6687" class="Symbol">→</a> <a id="6689" href="Prelude.Extensionality.html#6668" class="Bound">f</a> <a id="6691" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6693" href="Prelude.Extensionality.html#6670" class="Bound">g</a>
<a id="6695" href="Prelude.Extensionality.html#6614" class="Function">extdfun</a> <a id="6703" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6708" class="Symbol">_</a> <a id="6710" class="Symbol">=</a> <a id="6712" href="Prelude.Inverses.html#634" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

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
