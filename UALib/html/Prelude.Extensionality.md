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

<a id="2995" class="Keyword">module</a> <a id="hide-funext"></a><a id="3002" href="Prelude.Extensionality.html#3002" class="Module">hide-funext</a> <a id="3014" class="Keyword">where</a>

 <a id="hide-funext._∼_"></a><a id="3022" href="Prelude.Extensionality.html#3022" class="Function Operator">_∼_</a> <a id="3026" class="Symbol">:</a> <a id="3028" class="Symbol">{</a><a id="3029" href="Prelude.Extensionality.html#3029" class="Bound">𝓤</a> <a id="3031" href="Prelude.Extensionality.html#3031" class="Bound">𝓥</a> <a id="3033" class="Symbol">:</a> <a id="3035" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3043" class="Symbol">}{</a><a id="3045" href="Prelude.Extensionality.html#3045" class="Bound">X</a> <a id="3047" class="Symbol">:</a> <a id="3049" href="Prelude.Extensionality.html#3029" class="Bound">𝓤</a> <a id="3051" href="Universes.html#403" class="Function Operator">̇</a> <a id="3053" class="Symbol">}</a> <a id="3055" class="Symbol">{</a><a id="3056" href="Prelude.Extensionality.html#3056" class="Bound">A</a> <a id="3058" class="Symbol">:</a> <a id="3060" href="Prelude.Extensionality.html#3045" class="Bound">X</a> <a id="3062" class="Symbol">→</a> <a id="3064" href="Prelude.Extensionality.html#3031" class="Bound">𝓥</a> <a id="3066" href="Universes.html#403" class="Function Operator">̇</a> <a id="3068" class="Symbol">}</a> <a id="3070" class="Symbol">→</a> <a id="3072" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3074" href="Prelude.Extensionality.html#3056" class="Bound">A</a> <a id="3076" class="Symbol">→</a> <a id="3078" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3080" href="Prelude.Extensionality.html#3056" class="Bound">A</a> <a id="3082" class="Symbol">→</a> <a id="3084" href="Prelude.Extensionality.html#3029" class="Bound">𝓤</a> <a id="3086" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3088" href="Prelude.Extensionality.html#3031" class="Bound">𝓥</a> <a id="3090" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3093" href="Prelude.Extensionality.html#3093" class="Bound">f</a> <a id="3095" href="Prelude.Extensionality.html#3022" class="Function Operator">∼</a> <a id="3097" href="Prelude.Extensionality.html#3097" class="Bound">g</a> <a id="3099" class="Symbol">=</a> <a id="3101" class="Symbol">∀</a> <a id="3103" href="Prelude.Extensionality.html#3103" class="Bound">x</a> <a id="3105" class="Symbol">→</a> <a id="3107" href="Prelude.Extensionality.html#3093" class="Bound">f</a> <a id="3109" href="Prelude.Extensionality.html#3103" class="Bound">x</a> <a id="3111" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="3113" href="Prelude.Extensionality.html#3097" class="Bound">g</a> <a id="3115" href="Prelude.Extensionality.html#3103" class="Bound">x</a>

 <a id="3119" class="Keyword">infix</a> <a id="3125" class="Number">0</a> <a id="3127" href="Prelude.Extensionality.html#3022" class="Function Operator">_∼_</a>

</pre>


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó points out</a>, *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

<pre class="Agda">

 <a id="hide-funext.funext"></a><a id="3879" href="Prelude.Extensionality.html#3879" class="Function">funext</a> <a id="3886" class="Symbol">:</a> <a id="3888" class="Symbol">∀</a> <a id="3890" href="Prelude.Extensionality.html#3890" class="Bound">𝓤</a> <a id="3892" href="Prelude.Extensionality.html#3892" class="Bound">𝓦</a>  <a id="3895" class="Symbol">→</a> <a id="3897" href="Prelude.Extensionality.html#3890" class="Bound">𝓤</a> <a id="3899" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3901" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3903" href="Prelude.Extensionality.html#3892" class="Bound">𝓦</a> <a id="3905" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3907" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3910" href="Prelude.Extensionality.html#3879" class="Function">funext</a> <a id="3917" href="Prelude.Extensionality.html#3917" class="Bound">𝓤</a> <a id="3919" href="Prelude.Extensionality.html#3919" class="Bound">𝓦</a> <a id="3921" class="Symbol">=</a> <a id="3923" class="Symbol">{</a><a id="3924" href="Prelude.Extensionality.html#3924" class="Bound">A</a> <a id="3926" class="Symbol">:</a> <a id="3928" href="Prelude.Extensionality.html#3917" class="Bound">𝓤</a> <a id="3930" href="Universes.html#403" class="Function Operator">̇</a> <a id="3932" class="Symbol">}</a> <a id="3934" class="Symbol">{</a><a id="3935" href="Prelude.Extensionality.html#3935" class="Bound">B</a> <a id="3937" class="Symbol">:</a> <a id="3939" href="Prelude.Extensionality.html#3919" class="Bound">𝓦</a> <a id="3941" href="Universes.html#403" class="Function Operator">̇</a> <a id="3943" class="Symbol">}</a> <a id="3945" class="Symbol">{</a><a id="3946" href="Prelude.Extensionality.html#3946" class="Bound">f</a> <a id="3948" href="Prelude.Extensionality.html#3948" class="Bound">g</a> <a id="3950" class="Symbol">:</a> <a id="3952" href="Prelude.Extensionality.html#3924" class="Bound">A</a> <a id="3954" class="Symbol">→</a> <a id="3956" href="Prelude.Extensionality.html#3935" class="Bound">B</a><a id="3957" class="Symbol">}</a> <a id="3959" class="Symbol">→</a> <a id="3961" href="Prelude.Extensionality.html#3946" class="Bound">f</a> <a id="3963" href="Prelude.Extensionality.html#3022" class="Function Operator">∼</a> <a id="3965" href="Prelude.Extensionality.html#3948" class="Bound">g</a> <a id="3967" class="Symbol">→</a> <a id="3969" href="Prelude.Extensionality.html#3946" class="Bound">f</a> <a id="3971" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="3973" href="Prelude.Extensionality.html#3948" class="Bound">g</a>

</pre>





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

 <a id="hide-funext.dfunext"></a><a id="4161" href="Prelude.Extensionality.html#4161" class="Function">dfunext</a> <a id="4169" class="Symbol">:</a> <a id="4171" class="Symbol">∀</a> <a id="4173" href="Prelude.Extensionality.html#4173" class="Bound">𝓤</a> <a id="4175" href="Prelude.Extensionality.html#4175" class="Bound">𝓦</a> <a id="4177" class="Symbol">→</a> <a id="4179" href="Prelude.Extensionality.html#4173" class="Bound">𝓤</a> <a id="4181" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4183" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4185" href="Prelude.Extensionality.html#4175" class="Bound">𝓦</a> <a id="4187" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4189" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4192" href="Prelude.Extensionality.html#4161" class="Function">dfunext</a> <a id="4200" href="Prelude.Extensionality.html#4200" class="Bound">𝓤</a> <a id="4202" href="Prelude.Extensionality.html#4202" class="Bound">𝓦</a> <a id="4204" class="Symbol">=</a> <a id="4206" class="Symbol">{</a><a id="4207" href="Prelude.Extensionality.html#4207" class="Bound">A</a> <a id="4209" class="Symbol">:</a> <a id="4211" href="Prelude.Extensionality.html#4200" class="Bound">𝓤</a> <a id="4213" href="Universes.html#403" class="Function Operator">̇</a> <a id="4215" class="Symbol">}{</a><a id="4217" href="Prelude.Extensionality.html#4217" class="Bound">B</a> <a id="4219" class="Symbol">:</a> <a id="4221" href="Prelude.Extensionality.html#4207" class="Bound">A</a> <a id="4223" class="Symbol">→</a> <a id="4225" href="Prelude.Extensionality.html#4202" class="Bound">𝓦</a> <a id="4227" href="Universes.html#403" class="Function Operator">̇</a> <a id="4229" class="Symbol">}{</a><a id="4231" href="Prelude.Extensionality.html#4231" class="Bound">f</a> <a id="4233" href="Prelude.Extensionality.html#4233" class="Bound">g</a> <a id="4235" class="Symbol">:</a> <a id="4237" class="Symbol">∀(</a><a id="4239" href="Prelude.Extensionality.html#4239" class="Bound">x</a> <a id="4241" class="Symbol">:</a> <a id="4243" href="Prelude.Extensionality.html#4207" class="Bound">A</a><a id="4244" class="Symbol">)</a> <a id="4246" class="Symbol">→</a> <a id="4248" href="Prelude.Extensionality.html#4217" class="Bound">B</a> <a id="4250" href="Prelude.Extensionality.html#4239" class="Bound">x</a><a id="4251" class="Symbol">}</a> <a id="4253" class="Symbol">→</a>  <a id="4256" href="Prelude.Extensionality.html#4231" class="Bound">f</a> <a id="4258" href="Prelude.Extensionality.html#3022" class="Function Operator">∼</a> <a id="4260" href="Prelude.Extensionality.html#4233" class="Bound">g</a>  <a id="4263" class="Symbol">→</a>  <a id="4266" href="Prelude.Extensionality.html#4231" class="Bound">f</a> <a id="4268" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="4270" href="Prelude.Extensionality.html#4233" class="Bound">g</a>

</pre>

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

<pre class="Agda">

 <a id="hide-funext.global-funext"></a><a id="4842" href="Prelude.Extensionality.html#4842" class="Function">global-funext</a> <a id="4856" class="Symbol">:</a> <a id="4858" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4862" href="Prelude.Extensionality.html#4842" class="Function">global-funext</a> <a id="4876" class="Symbol">=</a> <a id="4878" class="Symbol">∀</a>  <a id="4881" class="Symbol">{</a><a id="4882" href="Prelude.Extensionality.html#4882" class="Bound">𝓤</a> <a id="4884" href="Prelude.Extensionality.html#4884" class="Bound">𝓥</a><a id="4885" class="Symbol">}</a> <a id="4887" class="Symbol">→</a> <a id="4889" href="Prelude.Extensionality.html#3879" class="Function">funext</a> <a id="4896" href="Prelude.Extensionality.html#4882" class="Bound">𝓤</a> <a id="4898" href="Prelude.Extensionality.html#4884" class="Bound">𝓥</a>

 <a id="hide-funext.global-dfunext"></a><a id="4902" href="Prelude.Extensionality.html#4902" class="Function">global-dfunext</a> <a id="4917" class="Symbol">:</a> <a id="4919" href="Agda.Primitive.html#787" class="Primitive">𝓤ω</a>
 <a id="4923" href="Prelude.Extensionality.html#4902" class="Function">global-dfunext</a> <a id="4938" class="Symbol">=</a> <a id="4940" class="Symbol">∀</a> <a id="4942" class="Symbol">{</a><a id="4943" href="Prelude.Extensionality.html#4943" class="Bound">𝓤</a> <a id="4945" href="Prelude.Extensionality.html#4945" class="Bound">𝓥</a><a id="4946" class="Symbol">}</a> <a id="4948" class="Symbol">→</a> <a id="4950" href="Prelude.Extensionality.html#3879" class="Function">funext</a> <a id="4957" href="Prelude.Extensionality.html#4943" class="Bound">𝓤</a> <a id="4959" href="Prelude.Extensionality.html#4945" class="Bound">𝓥</a>

</pre>

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).

Let us make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

<pre class="Agda">

<a id="5325" class="Keyword">open</a> <a id="5330" class="Keyword">import</a> <a id="5337" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="5364" class="Keyword">using</a> <a id="5370" class="Symbol">(</a><a id="5371" href="MGS-FunExt-from-Univalence.html#393" class="Function">funext</a><a id="5377" class="Symbol">;</a> <a id="5379" href="MGS-FunExt-from-Univalence.html#2039" class="Function">dfunext</a><a id="5386" class="Symbol">)</a> <a id="5388" class="Keyword">public</a>

</pre>

Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="5594" href="Prelude.Extensionality.html#5594" class="Function">extensionality-lemma</a> <a id="5615" class="Symbol">:</a> <a id="5617" class="Symbol">{</a><a id="5618" href="Prelude.Extensionality.html#5618" class="Bound">𝓘</a> <a id="5620" href="Prelude.Extensionality.html#5620" class="Bound">𝓤</a> <a id="5622" href="Prelude.Extensionality.html#5622" class="Bound">𝓥</a> <a id="5624" href="Prelude.Extensionality.html#5624" class="Bound">𝓣</a> <a id="5626" class="Symbol">:</a> <a id="5628" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5636" class="Symbol">}{</a><a id="5638" href="Prelude.Extensionality.html#5638" class="Bound">I</a> <a id="5640" class="Symbol">:</a> <a id="5642" href="Prelude.Extensionality.html#5618" class="Bound">𝓘</a> <a id="5644" href="Universes.html#403" class="Function Operator">̇</a> <a id="5646" class="Symbol">}{</a><a id="5648" href="Prelude.Extensionality.html#5648" class="Bound">X</a> <a id="5650" class="Symbol">:</a> <a id="5652" href="Prelude.Extensionality.html#5620" class="Bound">𝓤</a> <a id="5654" href="Universes.html#403" class="Function Operator">̇</a> <a id="5656" class="Symbol">}{</a><a id="5658" href="Prelude.Extensionality.html#5658" class="Bound">A</a> <a id="5660" class="Symbol">:</a> <a id="5662" href="Prelude.Extensionality.html#5638" class="Bound">I</a> <a id="5664" class="Symbol">→</a> <a id="5666" href="Prelude.Extensionality.html#5622" class="Bound">𝓥</a> <a id="5668" href="Universes.html#403" class="Function Operator">̇</a> <a id="5670" class="Symbol">}</a>
                       <a id="5695" class="Symbol">(</a><a id="5696" href="Prelude.Extensionality.html#5696" class="Bound">p</a> <a id="5698" href="Prelude.Extensionality.html#5698" class="Bound">q</a> <a id="5700" class="Symbol">:</a> <a id="5702" class="Symbol">(</a><a id="5703" href="Prelude.Extensionality.html#5703" class="Bound">i</a> <a id="5705" class="Symbol">:</a> <a id="5707" href="Prelude.Extensionality.html#5638" class="Bound">I</a><a id="5708" class="Symbol">)</a> <a id="5710" class="Symbol">→</a> <a id="5712" class="Symbol">(</a><a id="5713" href="Prelude.Extensionality.html#5648" class="Bound">X</a> <a id="5715" class="Symbol">→</a> <a id="5717" href="Prelude.Extensionality.html#5658" class="Bound">A</a> <a id="5719" href="Prelude.Extensionality.html#5703" class="Bound">i</a><a id="5720" class="Symbol">)</a> <a id="5722" class="Symbol">→</a> <a id="5724" href="Prelude.Extensionality.html#5624" class="Bound">𝓣</a> <a id="5726" href="Universes.html#403" class="Function Operator">̇</a> <a id="5728" class="Symbol">)(</a><a id="5730" href="Prelude.Extensionality.html#5730" class="Bound">args</a> <a id="5735" class="Symbol">:</a> <a id="5737" href="Prelude.Extensionality.html#5648" class="Bound">X</a> <a id="5739" class="Symbol">→</a> <a id="5741" class="Symbol">(</a><a id="5742" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5744" href="Prelude.Extensionality.html#5658" class="Bound">A</a><a id="5745" class="Symbol">))</a>
 <a id="5749" class="Symbol">→</a>                     <a id="5771" href="Prelude.Extensionality.html#5696" class="Bound">p</a> <a id="5773" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="5775" href="Prelude.Extensionality.html#5698" class="Bound">q</a>
                       <a id="5800" class="Comment">-------------------------------------------------------------</a>
 <a id="5863" class="Symbol">→</a>                     <a id="5885" class="Symbol">(λ</a> <a id="5888" href="Prelude.Extensionality.html#5888" class="Bound">i</a> <a id="5890" class="Symbol">→</a> <a id="5892" class="Symbol">(</a><a id="5893" href="Prelude.Extensionality.html#5696" class="Bound">p</a> <a id="5895" href="Prelude.Extensionality.html#5888" class="Bound">i</a><a id="5896" class="Symbol">)(λ</a> <a id="5900" href="Prelude.Extensionality.html#5900" class="Bound">x</a> <a id="5902" class="Symbol">→</a> <a id="5904" href="Prelude.Extensionality.html#5730" class="Bound">args</a> <a id="5909" href="Prelude.Extensionality.html#5900" class="Bound">x</a> <a id="5911" href="Prelude.Extensionality.html#5888" class="Bound">i</a><a id="5912" class="Symbol">))</a> <a id="5915" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="5917" class="Symbol">(λ</a> <a id="5920" href="Prelude.Extensionality.html#5920" class="Bound">i</a> <a id="5922" class="Symbol">→</a> <a id="5924" class="Symbol">(</a><a id="5925" href="Prelude.Extensionality.html#5698" class="Bound">q</a> <a id="5927" href="Prelude.Extensionality.html#5920" class="Bound">i</a><a id="5928" class="Symbol">)(λ</a> <a id="5932" href="Prelude.Extensionality.html#5932" class="Bound">x</a> <a id="5934" class="Symbol">→</a> <a id="5936" href="Prelude.Extensionality.html#5730" class="Bound">args</a> <a id="5941" href="Prelude.Extensionality.html#5932" class="Bound">x</a> <a id="5943" href="Prelude.Extensionality.html#5920" class="Bound">i</a><a id="5944" class="Symbol">))</a>

<a id="5948" href="Prelude.Extensionality.html#5594" class="Function">extensionality-lemma</a> <a id="5969" href="Prelude.Extensionality.html#5969" class="Bound">p</a> <a id="5971" href="Prelude.Extensionality.html#5971" class="Bound">q</a> <a id="5973" href="Prelude.Extensionality.html#5973" class="Bound">args</a> <a id="5978" href="Prelude.Extensionality.html#5978" class="Bound">p≡q</a> <a id="5982" class="Symbol">=</a> <a id="5984" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="5987" class="Symbol">(λ</a> <a id="5990" href="Prelude.Extensionality.html#5990" class="Bound">-</a> <a id="5992" class="Symbol">→</a> <a id="5994" class="Symbol">λ</a> <a id="5996" href="Prelude.Extensionality.html#5996" class="Bound">i</a> <a id="5998" class="Symbol">→</a> <a id="6000" class="Symbol">(</a><a id="6001" href="Prelude.Extensionality.html#5990" class="Bound">-</a> <a id="6003" href="Prelude.Extensionality.html#5996" class="Bound">i</a><a id="6004" class="Symbol">)</a> <a id="6006" class="Symbol">(λ</a> <a id="6009" href="Prelude.Extensionality.html#6009" class="Bound">x</a> <a id="6011" class="Symbol">→</a> <a id="6013" href="Prelude.Extensionality.html#5973" class="Bound">args</a> <a id="6018" href="Prelude.Extensionality.html#6009" class="Bound">x</a> <a id="6020" href="Prelude.Extensionality.html#5996" class="Bound">i</a><a id="6021" class="Symbol">))</a> <a id="6024" href="Prelude.Extensionality.html#5978" class="Bound">p≡q</a>

</pre>


The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup>

<pre class="Agda">

<a id="6176" class="Keyword">open</a> <a id="6181" class="Keyword">import</a> <a id="6188" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6197" class="Keyword">using</a> <a id="6203" class="Symbol">(</a><a id="6204" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="6207" class="Symbol">)</a> <a id="6209" class="Keyword">public</a>

<a id="6217" class="Keyword">module</a> <a id="6224" href="Prelude.Extensionality.html#6224" class="Module">_</a> <a id="6226" class="Symbol">{</a><a id="6227" href="Prelude.Extensionality.html#6227" class="Bound">𝓤</a> <a id="6229" href="Prelude.Extensionality.html#6229" class="Bound">𝓦</a> <a id="6231" class="Symbol">:</a> <a id="6233" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6241" class="Symbol">}</a> <a id="6243" class="Keyword">where</a>

 <a id="6251" href="Prelude.Extensionality.html#6251" class="Function">extfun</a> <a id="6258" class="Symbol">:</a> <a id="6260" class="Symbol">{</a><a id="6261" href="Prelude.Extensionality.html#6261" class="Bound">A</a> <a id="6263" class="Symbol">:</a> <a id="6265" href="Prelude.Extensionality.html#6227" class="Bound">𝓤</a> <a id="6267" href="Universes.html#403" class="Function Operator">̇</a><a id="6268" class="Symbol">}{</a><a id="6270" href="Prelude.Extensionality.html#6270" class="Bound">B</a> <a id="6272" class="Symbol">:</a> <a id="6274" href="Prelude.Extensionality.html#6229" class="Bound">𝓦</a> <a id="6276" href="Universes.html#403" class="Function Operator">̇</a><a id="6277" class="Symbol">}{</a><a id="6279" href="Prelude.Extensionality.html#6279" class="Bound">f</a> <a id="6281" href="Prelude.Extensionality.html#6281" class="Bound">g</a> <a id="6283" class="Symbol">:</a> <a id="6285" href="Prelude.Extensionality.html#6261" class="Bound">A</a> <a id="6287" class="Symbol">→</a> <a id="6289" href="Prelude.Extensionality.html#6270" class="Bound">B</a><a id="6290" class="Symbol">}</a> <a id="6292" class="Symbol">→</a> <a id="6294" href="Prelude.Extensionality.html#6279" class="Bound">f</a> <a id="6296" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="6298" href="Prelude.Extensionality.html#6281" class="Bound">g</a>  <a id="6301" class="Symbol">→</a>  <a id="6304" href="Prelude.Extensionality.html#6279" class="Bound">f</a> <a id="6306" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6308" href="Prelude.Extensionality.html#6281" class="Bound">g</a>
 <a id="6311" href="Prelude.Extensionality.html#6251" class="Function">extfun</a> <a id="6318" href="Prelude.Inverses.html#635" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6323" class="Symbol">_</a> <a id="6325" class="Symbol">=</a> <a id="6327" href="Prelude.Inverses.html#635" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>

Here is the analogue for dependent function types.

<pre class="Agda">

 <a id="6412" href="Prelude.Extensionality.html#6412" class="Function">extdfun</a> <a id="6420" class="Symbol">:</a> <a id="6422" class="Symbol">{</a><a id="6423" href="Prelude.Extensionality.html#6423" class="Bound">A</a> <a id="6425" class="Symbol">:</a> <a id="6427" href="Prelude.Extensionality.html#6227" class="Bound">𝓤</a> <a id="6429" href="Universes.html#403" class="Function Operator">̇</a> <a id="6431" class="Symbol">}{</a><a id="6433" href="Prelude.Extensionality.html#6433" class="Bound">B</a> <a id="6435" class="Symbol">:</a> <a id="6437" href="Prelude.Extensionality.html#6423" class="Bound">A</a> <a id="6439" class="Symbol">→</a> <a id="6441" href="Prelude.Extensionality.html#6229" class="Bound">𝓦</a> <a id="6443" href="Universes.html#403" class="Function Operator">̇</a> <a id="6445" class="Symbol">}(</a><a id="6447" href="Prelude.Extensionality.html#6447" class="Bound">f</a> <a id="6449" href="Prelude.Extensionality.html#6449" class="Bound">g</a> <a id="6451" class="Symbol">:</a> <a id="6453" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6455" href="Prelude.Extensionality.html#6433" class="Bound">B</a><a id="6456" class="Symbol">)</a> <a id="6458" class="Symbol">→</a> <a id="6460" href="Prelude.Extensionality.html#6447" class="Bound">f</a> <a id="6462" href="Prelude.Inverses.html#621" class="Datatype Operator">≡</a> <a id="6464" href="Prelude.Extensionality.html#6449" class="Bound">g</a> <a id="6466" class="Symbol">→</a> <a id="6468" href="Prelude.Extensionality.html#6447" class="Bound">f</a> <a id="6470" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="6472" href="Prelude.Extensionality.html#6449" class="Bound">g</a>
 <a id="6475" href="Prelude.Extensionality.html#6412" class="Function">extdfun</a> <a id="6483" class="Symbol">_</a> <a id="6485" class="Symbol">_</a> <a id="6487" href="Prelude.Inverses.html#635" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="6492" class="Symbol">_</a> <a id="6494" class="Symbol">=</a> <a id="6496" href="Prelude.Inverses.html#635" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

Finally, an alternative way to express dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that `extdfun` is an equivalence (cf. `hfunext` in the [Type Topology][] library).

<pre class="Agda">

<a id="efunext"></a><a id="7842" href="Prelude.Extensionality.html#7842" class="Function">efunext</a> <a id="7850" class="Symbol">:</a> <a id="7852" class="Symbol">(</a><a id="7853" href="Prelude.Extensionality.html#7853" class="Bound">𝓤</a> <a id="7855" href="Prelude.Extensionality.html#7855" class="Bound">𝓦</a> <a id="7857" class="Symbol">:</a> <a id="7859" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7867" class="Symbol">)</a> <a id="7869" class="Symbol">→</a> <a id="7871" class="Symbol">(</a><a id="7872" href="Prelude.Extensionality.html#7853" class="Bound">𝓤</a> <a id="7874" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7876" href="Prelude.Extensionality.html#7855" class="Bound">𝓦</a><a id="7877" class="Symbol">)</a><a id="7878" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="7880" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7882" href="Prelude.Extensionality.html#7842" class="Function">efunext</a> <a id="7890" href="Prelude.Extensionality.html#7890" class="Bound">𝓤</a> <a id="7892" href="Prelude.Extensionality.html#7892" class="Bound">𝓦</a> <a id="7894" class="Symbol">=</a> <a id="7896" class="Symbol">{</a><a id="7897" href="Prelude.Extensionality.html#7897" class="Bound">A</a> <a id="7899" class="Symbol">:</a> <a id="7901" href="Prelude.Extensionality.html#7890" class="Bound">𝓤</a> <a id="7903" href="Universes.html#403" class="Function Operator">̇</a><a id="7904" class="Symbol">}{</a><a id="7906" href="Prelude.Extensionality.html#7906" class="Bound">B</a> <a id="7908" class="Symbol">:</a> <a id="7910" href="Prelude.Extensionality.html#7897" class="Bound">A</a> <a id="7912" class="Symbol">→</a> <a id="7914" href="Prelude.Extensionality.html#7892" class="Bound">𝓦</a> <a id="7916" href="Universes.html#403" class="Function Operator">̇</a><a id="7917" class="Symbol">}</a> <a id="7919" class="Symbol">(</a><a id="7920" href="Prelude.Extensionality.html#7920" class="Bound">f</a> <a id="7922" href="Prelude.Extensionality.html#7922" class="Bound">g</a> <a id="7924" class="Symbol">:</a> <a id="7926" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="7928" href="Prelude.Extensionality.html#7906" class="Bound">B</a><a id="7929" class="Symbol">)</a> <a id="7931" class="Symbol">→</a> <a id="7933" href="MGS-Equivalences.html#868" class="Function">is-equiv</a> <a id="7942" class="Symbol">(</a><a id="7943" href="Prelude.Extensionality.html#6412" class="Function">extdfun</a> <a id="7951" href="Prelude.Extensionality.html#7920" class="Bound">f</a> <a id="7953" href="Prelude.Extensionality.html#7922" class="Bound">g</a><a id="7954" class="Symbol">)</a>

</pre>

We defined the types above before realizing that the [Type Topology][] already has types that are equivalent to these. For consistency and to benefit anyone who might already be familiar with the [Type Topology][] library, we will import these functions from that library and refer to them by these names (instead of `extfun`, `extdfun`, or `efunext`).

<pre class="Agda">

<a id="8337" class="Keyword">open</a> <a id="8342" class="Keyword">import</a> <a id="8349" href="MGS-FunExt-from-Univalence.html" class="Module">MGS-FunExt-from-Univalence</a> <a id="8376" class="Keyword">using</a> <a id="8382" class="Symbol">(</a><a id="8383" href="MGS-FunExt-from-Univalence.html#2235" class="Function">hfunext</a><a id="8390" class="Symbol">)</a> <a id="8392" class="Keyword">public</a>

</pre>

------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library. We initiall proved this lemma with a simple invocation of `𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁`, but discovered that this proof leads to an `efunext` type that doesn't play well with other definitions in the [Type Topology][] library (e.g., `NatΠ-is-embedding`).</span>

--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
