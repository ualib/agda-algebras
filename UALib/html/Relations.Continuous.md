---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This section presents the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `GenRel` to be the type `(I → A) → 𝓦 ̇` and we will call `GenRel` the type of **general relations**.  This generalizes the unary and binary relations we saw earlier in the sense that general relations can have arbitrarily large arities. However, relations of type `GenRel` are not completely general because they are defined over a single type.

Just as `Rel A 𝓦` was the "single-sorted" special case of the "multisorted" `REL A B 𝓦` type, so too will `GenRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A i'` to `A i''` to ….  We will refer to such relations as **dependent relations** because in order to define a type to represent them, we absolutely need depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) captures this completely general notion of relation.

<pre class="Agda">

<a id="2129" class="Symbol">{-#</a> <a id="2133" class="Keyword">OPTIONS</a> <a id="2141" class="Pragma">--without-K</a> <a id="2153" class="Pragma">--exact-split</a> <a id="2167" class="Pragma">--safe</a> <a id="2174" class="Symbol">#-}</a>

<a id="2179" class="Keyword">module</a> <a id="2186" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="2207" class="Keyword">where</a>

<a id="2214" class="Keyword">open</a> <a id="2219" class="Keyword">import</a> <a id="2226" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="2245" class="Keyword">public</a>

</pre>

#### <a id="general-relations">General relations</a>

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="GenRel"></a><a id="2852" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="2859" class="Symbol">:</a> <a id="2861" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2863" href="Universes.html#403" class="Function Operator">̇</a> <a id="2865" class="Symbol">→</a> <a id="2867" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2869" href="Universes.html#403" class="Function Operator">̇</a> <a id="2871" class="Symbol">→</a> <a id="2873" class="Symbol">(</a><a id="2874" href="Relations.Continuous.html#2874" class="Bound">𝓦</a> <a id="2876" class="Symbol">:</a> <a id="2878" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2886" class="Symbol">)</a> <a id="2888" class="Symbol">→</a> <a id="2890" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2892" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2894" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2896" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2898" href="Relations.Continuous.html#2874" class="Bound">𝓦</a> <a id="2900" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="2902" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2904" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="2911" href="Relations.Continuous.html#2911" class="Bound">I</a> <a id="2913" href="Relations.Continuous.html#2913" class="Bound">A</a> <a id="2915" href="Relations.Continuous.html#2915" class="Bound">𝓦</a> <a id="2917" class="Symbol">=</a> <a id="2919" class="Symbol">(</a><a id="2920" href="Relations.Continuous.html#2911" class="Bound">I</a> <a id="2922" class="Symbol">→</a> <a id="2924" href="Relations.Continuous.html#2913" class="Bound">A</a><a id="2925" class="Symbol">)</a> <a id="2927" class="Symbol">→</a> <a id="2929" href="Relations.Continuous.html#2915" class="Bound">𝓦</a> <a id="2931" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with general relations.

<pre class="Agda">

<a id="3181" class="Keyword">module</a> <a id="3188" href="Relations.Continuous.html#3188" class="Module">_</a> <a id="3190" class="Symbol">{</a><a id="3191" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3193" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3195" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3197" class="Symbol">:</a> <a id="3199" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3207" class="Symbol">}</a> <a id="3209" class="Symbol">{</a><a id="3210" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3212" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3214" class="Symbol">:</a> <a id="3216" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3218" href="Universes.html#403" class="Function Operator">̇</a><a id="3219" class="Symbol">}</a> <a id="3221" class="Symbol">{</a><a id="3222" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3224" class="Symbol">:</a> <a id="3226" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3228" href="Universes.html#403" class="Function Operator">̇</a><a id="3229" class="Symbol">}</a> <a id="3231" class="Keyword">where</a>

 <a id="3239" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3252" class="Symbol">:</a> <a id="3254" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="3261" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3263" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3265" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3267" class="Symbol">→</a> <a id="3269" class="Symbol">(</a><a id="3270" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3272" class="Symbol">→</a> <a id="3274" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3276" class="Symbol">→</a> <a id="3278" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3279" class="Symbol">)</a> <a id="3281" class="Symbol">→</a> <a id="3283" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3285" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3287" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3289" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3292" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3305" href="Relations.Continuous.html#3305" class="Bound">R</a> <a id="3307" href="Relations.Continuous.html#3307" class="Bound">𝕒</a> <a id="3309" class="Symbol">=</a> <a id="3311" class="Symbol">∀</a> <a id="3313" class="Symbol">(</a><a id="3314" href="Relations.Continuous.html#3314" class="Bound">j</a> <a id="3316" class="Symbol">:</a> <a id="3318" href="Relations.Continuous.html#3212" class="Bound">J</a><a id="3319" class="Symbol">)</a> <a id="3321" class="Symbol">→</a> <a id="3323" href="Relations.Continuous.html#3305" class="Bound">R</a> <a id="3325" class="Symbol">λ</a> <a id="3327" href="Relations.Continuous.html#3327" class="Bound">i</a> <a id="3329" class="Symbol">→</a> <a id="3331" class="Symbol">(</a><a id="3332" href="Relations.Continuous.html#3307" class="Bound">𝕒</a> <a id="3334" href="Relations.Continuous.html#3327" class="Bound">i</a><a id="3335" class="Symbol">)</a> <a id="3337" href="Relations.Continuous.html#3314" class="Bound">j</a>

 <a id="3341" href="Relations.Continuous.html#3341" class="Function">gen-compatible-fun</a> <a id="3360" class="Symbol">:</a> <a id="3362" class="Symbol">(</a><a id="3363" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3365" class="Symbol">→</a> <a id="3367" class="Symbol">(</a><a id="3368" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3370" class="Symbol">→</a> <a id="3372" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3373" class="Symbol">)</a> <a id="3375" class="Symbol">→</a> <a id="3377" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3378" class="Symbol">)</a> <a id="3380" class="Symbol">→</a> <a id="3382" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="3389" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3391" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3393" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3395" class="Symbol">→</a> <a id="3397" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3399" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3401" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3403" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3405" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3407" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3410" href="Relations.Continuous.html#3341" class="Function">gen-compatible-fun</a> <a id="3429" href="Relations.Continuous.html#3429" class="Bound">𝕗</a> <a id="3431" href="Relations.Continuous.html#3431" class="Bound">R</a>  <a id="3434" class="Symbol">=</a> <a id="3436" class="Symbol">∀</a> <a id="3438" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3440" class="Symbol">→</a> <a id="3442" class="Symbol">(</a><a id="3443" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3456" href="Relations.Continuous.html#3431" class="Bound">R</a><a id="3457" class="Symbol">)</a> <a id="3459" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3461" class="Symbol">→</a> <a id="3463" href="Relations.Continuous.html#3431" class="Bound">R</a> <a id="3465" class="Symbol">λ</a> <a id="3467" href="Relations.Continuous.html#3467" class="Bound">i</a> <a id="3469" class="Symbol">→</a> <a id="3471" class="Symbol">(</a><a id="3472" href="Relations.Continuous.html#3429" class="Bound">𝕗</a> <a id="3474" href="Relations.Continuous.html#3467" class="Bound">i</a><a id="3475" class="Symbol">)</a> <a id="3477" class="Symbol">(</a><a id="3478" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3480" href="Relations.Continuous.html#3467" class="Bound">i</a><a id="3481" class="Symbol">)</a>

</pre>

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a general relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each general relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝕒 i 1      𝕒 k 1
𝕒 i 2      𝕒 k 2
𝕒 i 3      𝕒 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝕒 i J      𝕒 k J
```

Now `lift-gen-rel R 𝕒` is defined by `∀ j → R (λ i → (𝕒 i) j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `gen-compatible-fun`.  Here, `𝕗 : I → (J → A) → A` denotes an `I`-tuple of `J`-ary operations on `A`.  That is, for each `i : I`, the function `𝕗 i` takes a `J`-tuple `𝕒 i : J → A` and evaluates to some `(𝕗 i) (𝕒 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝕒 : I → (J → A)` is precisely the type on which the relation `lift-gen-rel R` is defined.


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` may not even be enumerable).

<pre class="Agda">

<a id="DepRel"></a><a id="6045" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6052" class="Symbol">:</a> <a id="6054" class="Symbol">(</a><a id="6055" href="Relations.Continuous.html#6055" class="Bound">I</a> <a id="6057" class="Symbol">:</a> <a id="6059" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6061" href="Universes.html#403" class="Function Operator">̇</a><a id="6062" class="Symbol">)(</a><a id="6064" href="Relations.Continuous.html#6064" class="Bound">A</a> <a id="6066" class="Symbol">:</a> <a id="6068" href="Relations.Continuous.html#6055" class="Bound">I</a> <a id="6070" class="Symbol">→</a> <a id="6072" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6074" href="Universes.html#403" class="Function Operator">̇</a><a id="6075" class="Symbol">)(</a><a id="6077" href="Relations.Continuous.html#6077" class="Bound">𝓦</a> <a id="6079" class="Symbol">:</a> <a id="6081" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6089" class="Symbol">)</a> <a id="6091" class="Symbol">→</a> <a id="6093" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6095" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6097" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6099" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6101" href="Relations.Continuous.html#6077" class="Bound">𝓦</a> <a id="6103" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6105" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6107" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6114" href="Relations.Continuous.html#6114" class="Bound">I</a> <a id="6116" href="Relations.Continuous.html#6116" class="Bound">A</a> <a id="6118" href="Relations.Continuous.html#6118" class="Bound">𝓦</a> <a id="6120" class="Symbol">=</a> <a id="6122" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6124" href="Relations.Continuous.html#6116" class="Bound">A</a> <a id="6126" class="Symbol">→</a> <a id="6128" href="Relations.Continuous.html#6118" class="Bound">𝓦</a> <a id="6130" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of general relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6630" class="Keyword">module</a> <a id="6637" href="Relations.Continuous.html#6637" class="Module">_</a> <a id="6639" class="Symbol">{</a><a id="6640" href="Relations.Continuous.html#6640" class="Bound">𝓤</a> <a id="6642" href="Relations.Continuous.html#6642" class="Bound">𝓥</a> <a id="6644" href="Relations.Continuous.html#6644" class="Bound">𝓦</a> <a id="6646" class="Symbol">:</a> <a id="6648" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6656" class="Symbol">}</a> <a id="6658" class="Symbol">{</a><a id="6659" href="Relations.Continuous.html#6659" class="Bound">I</a> <a id="6661" href="Relations.Continuous.html#6661" class="Bound">J</a> <a id="6663" class="Symbol">:</a> <a id="6665" href="Relations.Continuous.html#6642" class="Bound">𝓥</a> <a id="6667" href="Universes.html#403" class="Function Operator">̇</a><a id="6668" class="Symbol">}</a> <a id="6670" class="Symbol">{</a><a id="6671" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6673" class="Symbol">:</a> <a id="6675" href="Relations.Continuous.html#6659" class="Bound">I</a> <a id="6677" class="Symbol">→</a> <a id="6679" href="Relations.Continuous.html#6640" class="Bound">𝓤</a> <a id="6681" href="Universes.html#403" class="Function Operator">̇</a><a id="6682" class="Symbol">}</a> <a id="6684" class="Keyword">where</a>

 <a id="6692" href="Relations.Continuous.html#6692" class="Function">lift-dep-rel</a> <a id="6705" class="Symbol">:</a> <a id="6707" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6714" href="Relations.Continuous.html#6659" class="Bound">I</a> <a id="6716" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6718" href="Relations.Continuous.html#6644" class="Bound">𝓦</a> <a id="6720" class="Symbol">→</a> <a id="6722" class="Symbol">(∀</a> <a id="6725" href="Relations.Continuous.html#6725" class="Bound">i</a> <a id="6727" class="Symbol">→</a> <a id="6729" href="Relations.Continuous.html#6661" class="Bound">J</a> <a id="6731" class="Symbol">→</a> <a id="6733" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6735" href="Relations.Continuous.html#6725" class="Bound">i</a><a id="6736" class="Symbol">)</a> <a id="6738" class="Symbol">→</a> <a id="6740" href="Relations.Continuous.html#6642" class="Bound">𝓥</a> <a id="6742" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6744" href="Relations.Continuous.html#6644" class="Bound">𝓦</a> <a id="6746" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6749" href="Relations.Continuous.html#6692" class="Function">lift-dep-rel</a> <a id="6762" href="Relations.Continuous.html#6762" class="Bound">R</a> <a id="6764" href="Relations.Continuous.html#6764" class="Bound">𝕒</a> <a id="6766" class="Symbol">=</a> <a id="6768" class="Symbol">∀</a> <a id="6770" class="Symbol">(</a><a id="6771" href="Relations.Continuous.html#6771" class="Bound">j</a> <a id="6773" class="Symbol">:</a> <a id="6775" href="Relations.Continuous.html#6661" class="Bound">J</a><a id="6776" class="Symbol">)</a> <a id="6778" class="Symbol">→</a> <a id="6780" href="Relations.Continuous.html#6762" class="Bound">R</a> <a id="6782" class="Symbol">(λ</a> <a id="6785" href="Relations.Continuous.html#6785" class="Bound">i</a> <a id="6787" class="Symbol">→</a> <a id="6789" class="Symbol">(</a><a id="6790" href="Relations.Continuous.html#6764" class="Bound">𝕒</a> <a id="6792" href="Relations.Continuous.html#6785" class="Bound">i</a><a id="6793" class="Symbol">)</a> <a id="6795" href="Relations.Continuous.html#6771" class="Bound">j</a><a id="6796" class="Symbol">)</a>

 <a id="6800" href="Relations.Continuous.html#6800" class="Function">dep-compatible-fun</a> <a id="6819" class="Symbol">:</a> <a id="6821" class="Symbol">(∀</a> <a id="6824" href="Relations.Continuous.html#6824" class="Bound">i</a> <a id="6826" class="Symbol">→</a> <a id="6828" class="Symbol">(</a><a id="6829" href="Relations.Continuous.html#6661" class="Bound">J</a> <a id="6831" class="Symbol">→</a> <a id="6833" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6835" href="Relations.Continuous.html#6824" class="Bound">i</a><a id="6836" class="Symbol">)</a> <a id="6838" class="Symbol">→</a> <a id="6840" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6842" href="Relations.Continuous.html#6824" class="Bound">i</a><a id="6843" class="Symbol">)</a> <a id="6845" class="Symbol">→</a> <a id="6847" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6854" href="Relations.Continuous.html#6659" class="Bound">I</a> <a id="6856" href="Relations.Continuous.html#6671" class="Bound">A</a> <a id="6858" href="Relations.Continuous.html#6644" class="Bound">𝓦</a> <a id="6860" class="Symbol">→</a> <a id="6862" href="Relations.Continuous.html#6642" class="Bound">𝓥</a> <a id="6864" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6866" href="Relations.Continuous.html#6640" class="Bound">𝓤</a> <a id="6868" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6870" href="Relations.Continuous.html#6644" class="Bound">𝓦</a> <a id="6872" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6875" href="Relations.Continuous.html#6800" class="Function">dep-compatible-fun</a> <a id="6894" href="Relations.Continuous.html#6894" class="Bound">𝕗</a> <a id="6896" href="Relations.Continuous.html#6896" class="Bound">R</a>  <a id="6899" class="Symbol">=</a> <a id="6901" class="Symbol">∀</a> <a id="6903" href="Relations.Continuous.html#6903" class="Bound">𝕒</a> <a id="6905" class="Symbol">→</a> <a id="6907" class="Symbol">(</a><a id="6908" href="Relations.Continuous.html#6692" class="Function">lift-dep-rel</a> <a id="6921" href="Relations.Continuous.html#6896" class="Bound">R</a><a id="6922" class="Symbol">)</a> <a id="6924" href="Relations.Continuous.html#6903" class="Bound">𝕒</a> <a id="6926" class="Symbol">→</a> <a id="6928" href="Relations.Continuous.html#6896" class="Bound">R</a> <a id="6930" class="Symbol">λ</a> <a id="6932" href="Relations.Continuous.html#6932" class="Bound">i</a> <a id="6934" class="Symbol">→</a> <a id="6936" class="Symbol">(</a><a id="6937" href="Relations.Continuous.html#6894" class="Bound">𝕗</a> <a id="6939" href="Relations.Continuous.html#6932" class="Bound">i</a><a id="6940" class="Symbol">)(</a><a id="6942" href="Relations.Continuous.html#6903" class="Bound">𝕒</a> <a id="6944" href="Relations.Continuous.html#6932" class="Bound">i</a><a id="6945" class="Symbol">)</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → J → A i`.


--------------------------------------

<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
