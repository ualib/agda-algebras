---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This is the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="298" class="Symbol">{-#</a> <a id="302" class="Keyword">OPTIONS</a> <a id="310" class="Pragma">--without-K</a> <a id="322" class="Pragma">--exact-split</a> <a id="336" class="Pragma">--safe</a> <a id="343" class="Symbol">#-}</a>

<a id="348" class="Keyword">module</a> <a id="355" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="376" class="Keyword">where</a>

<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="414" class="Keyword">public</a>

</pre>

#### <a id="motivation">Motivation</a>
In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ConRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ConRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, ternary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type---said another way, they are *single-sorted* relations---but we will remove this limitation as well when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ConRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

#### <a id="continuous-relations">Continuous relations</a>

We now define the type `ConRel` which represents predicates of arbitrary arity over a single type `A`. We call this the type of *continuous relations*.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ConRel"></a><a id="3210" href="Relations.Continuous.html#3210" class="Function">ConRel</a> <a id="3217" class="Symbol">:</a> <a id="3219" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3221" href="Universes.html#403" class="Function Operator">̇</a> <a id="3223" class="Symbol">→</a> <a id="3225" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3227" href="Universes.html#403" class="Function Operator">̇</a> <a id="3229" class="Symbol">→</a> <a id="3231" class="Symbol">(</a><a id="3232" href="Relations.Continuous.html#3232" class="Bound">𝓦</a> <a id="3234" class="Symbol">:</a> <a id="3236" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3244" class="Symbol">)</a> <a id="3246" class="Symbol">→</a> <a id="3248" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3250" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3252" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3254" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3256" href="Relations.Continuous.html#3232" class="Bound">𝓦</a> <a id="3258" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3260" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3262" href="Relations.Continuous.html#3210" class="Function">ConRel</a> <a id="3269" href="Relations.Continuous.html#3269" class="Bound">I</a> <a id="3271" href="Relations.Continuous.html#3271" class="Bound">A</a> <a id="3273" href="Relations.Continuous.html#3273" class="Bound">𝓦</a> <a id="3275" class="Symbol">=</a> <a id="3277" class="Symbol">(</a><a id="3278" href="Relations.Continuous.html#3269" class="Bound">I</a> <a id="3280" class="Symbol">→</a> <a id="3282" href="Relations.Continuous.html#3271" class="Bound">A</a><a id="3283" class="Symbol">)</a> <a id="3285" class="Symbol">→</a> <a id="3287" href="Relations.Continuous.html#3273" class="Bound">𝓦</a> <a id="3289" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3548" class="Keyword">module</a> <a id="3555" href="Relations.Continuous.html#3555" class="Module">_</a> <a id="3557" class="Symbol">{</a><a id="3558" href="Relations.Continuous.html#3558" class="Bound">𝓤</a> <a id="3560" href="Relations.Continuous.html#3560" class="Bound">𝓥</a> <a id="3562" href="Relations.Continuous.html#3562" class="Bound">𝓦</a> <a id="3564" class="Symbol">:</a> <a id="3566" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3574" class="Symbol">}</a> <a id="3576" class="Symbol">{</a><a id="3577" href="Relations.Continuous.html#3577" class="Bound">I</a> <a id="3579" href="Relations.Continuous.html#3579" class="Bound">J</a> <a id="3581" class="Symbol">:</a> <a id="3583" href="Relations.Continuous.html#3560" class="Bound">𝓥</a> <a id="3585" href="Universes.html#403" class="Function Operator">̇</a><a id="3586" class="Symbol">}</a> <a id="3588" class="Symbol">{</a><a id="3589" href="Relations.Continuous.html#3589" class="Bound">A</a> <a id="3591" class="Symbol">:</a> <a id="3593" href="Relations.Continuous.html#3558" class="Bound">𝓤</a> <a id="3595" href="Universes.html#403" class="Function Operator">̇</a><a id="3596" class="Symbol">}</a> <a id="3598" class="Keyword">where</a>

 <a id="3606" href="Relations.Continuous.html#3606" class="Function">lift-con-rel</a> <a id="3619" class="Symbol">:</a> <a id="3621" href="Relations.Continuous.html#3210" class="Function">ConRel</a> <a id="3628" href="Relations.Continuous.html#3577" class="Bound">I</a> <a id="3630" href="Relations.Continuous.html#3589" class="Bound">A</a> <a id="3632" href="Relations.Continuous.html#3562" class="Bound">𝓦</a> <a id="3634" class="Symbol">→</a> <a id="3636" class="Symbol">(</a><a id="3637" href="Relations.Continuous.html#3577" class="Bound">I</a> <a id="3639" class="Symbol">→</a> <a id="3641" href="Relations.Continuous.html#3579" class="Bound">J</a> <a id="3643" class="Symbol">→</a> <a id="3645" href="Relations.Continuous.html#3589" class="Bound">A</a><a id="3646" class="Symbol">)</a> <a id="3648" class="Symbol">→</a> <a id="3650" href="Relations.Continuous.html#3560" class="Bound">𝓥</a> <a id="3652" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3654" href="Relations.Continuous.html#3562" class="Bound">𝓦</a> <a id="3656" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3659" href="Relations.Continuous.html#3606" class="Function">lift-con-rel</a> <a id="3672" href="Relations.Continuous.html#3672" class="Bound">R</a> <a id="3674" href="Relations.Continuous.html#3674" class="Bound">𝕒</a> <a id="3676" class="Symbol">=</a> <a id="3678" class="Symbol">∀</a> <a id="3680" class="Symbol">(</a><a id="3681" href="Relations.Continuous.html#3681" class="Bound">j</a> <a id="3683" class="Symbol">:</a> <a id="3685" href="Relations.Continuous.html#3579" class="Bound">J</a><a id="3686" class="Symbol">)</a> <a id="3688" class="Symbol">→</a> <a id="3690" href="Relations.Continuous.html#3672" class="Bound">R</a> <a id="3692" class="Symbol">λ</a> <a id="3694" href="Relations.Continuous.html#3694" class="Bound">i</a> <a id="3696" class="Symbol">→</a> <a id="3698" class="Symbol">(</a><a id="3699" href="Relations.Continuous.html#3674" class="Bound">𝕒</a> <a id="3701" href="Relations.Continuous.html#3694" class="Bound">i</a><a id="3702" class="Symbol">)</a> <a id="3704" href="Relations.Continuous.html#3681" class="Bound">j</a>

 <a id="3708" href="Relations.Continuous.html#3708" class="Function">con-compatible-fun</a> <a id="3727" class="Symbol">:</a> <a id="3729" class="Symbol">(</a><a id="3730" href="Relations.Continuous.html#3577" class="Bound">I</a> <a id="3732" class="Symbol">→</a> <a id="3734" class="Symbol">(</a><a id="3735" href="Relations.Continuous.html#3579" class="Bound">J</a> <a id="3737" class="Symbol">→</a> <a id="3739" href="Relations.Continuous.html#3589" class="Bound">A</a><a id="3740" class="Symbol">)</a> <a id="3742" class="Symbol">→</a> <a id="3744" href="Relations.Continuous.html#3589" class="Bound">A</a><a id="3745" class="Symbol">)</a> <a id="3747" class="Symbol">→</a> <a id="3749" href="Relations.Continuous.html#3210" class="Function">ConRel</a> <a id="3756" href="Relations.Continuous.html#3577" class="Bound">I</a> <a id="3758" href="Relations.Continuous.html#3589" class="Bound">A</a> <a id="3760" href="Relations.Continuous.html#3562" class="Bound">𝓦</a> <a id="3762" class="Symbol">→</a> <a id="3764" href="Relations.Continuous.html#3560" class="Bound">𝓥</a> <a id="3766" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3768" href="Relations.Continuous.html#3558" class="Bound">𝓤</a> <a id="3770" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3772" href="Relations.Continuous.html#3562" class="Bound">𝓦</a> <a id="3774" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3777" href="Relations.Continuous.html#3708" class="Function">con-compatible-fun</a> <a id="3796" href="Relations.Continuous.html#3796" class="Bound">𝕗</a> <a id="3798" href="Relations.Continuous.html#3798" class="Bound">R</a>  <a id="3801" class="Symbol">=</a> <a id="3803" class="Symbol">∀</a> <a id="3805" href="Relations.Continuous.html#3805" class="Bound">𝕒</a> <a id="3807" class="Symbol">→</a> <a id="3809" class="Symbol">(</a><a id="3810" href="Relations.Continuous.html#3606" class="Function">lift-con-rel</a> <a id="3823" href="Relations.Continuous.html#3798" class="Bound">R</a><a id="3824" class="Symbol">)</a> <a id="3826" href="Relations.Continuous.html#3805" class="Bound">𝕒</a> <a id="3828" class="Symbol">→</a> <a id="3830" href="Relations.Continuous.html#3798" class="Bound">R</a> <a id="3832" class="Symbol">λ</a> <a id="3834" href="Relations.Continuous.html#3834" class="Bound">i</a> <a id="3836" class="Symbol">→</a> <a id="3838" class="Symbol">(</a><a id="3839" href="Relations.Continuous.html#3796" class="Bound">𝕗</a> <a id="3841" href="Relations.Continuous.html#3834" class="Bound">i</a><a id="3842" class="Symbol">)</a> <a id="3844" class="Symbol">(</a><a id="3845" href="Relations.Continuous.html#3805" class="Bound">𝕒</a> <a id="3847" href="Relations.Continuous.html#3834" class="Bound">i</a><a id="3848" class="Symbol">)</a>

</pre>

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a continuous relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each continuous relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

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

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i` to `A j` to `A k` to ….

<pre class="Agda">

<a id="DepRel"></a><a id="6325" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6332" class="Symbol">:</a> <a id="6334" class="Symbol">(</a><a id="6335" href="Relations.Continuous.html#6335" class="Bound">I</a> <a id="6337" class="Symbol">:</a> <a id="6339" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6341" href="Universes.html#403" class="Function Operator">̇</a><a id="6342" class="Symbol">)(</a><a id="6344" href="Relations.Continuous.html#6344" class="Bound">A</a> <a id="6346" class="Symbol">:</a> <a id="6348" href="Relations.Continuous.html#6335" class="Bound">I</a> <a id="6350" class="Symbol">→</a> <a id="6352" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6354" href="Universes.html#403" class="Function Operator">̇</a><a id="6355" class="Symbol">)(</a><a id="6357" href="Relations.Continuous.html#6357" class="Bound">𝓦</a> <a id="6359" class="Symbol">:</a> <a id="6361" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6369" class="Symbol">)</a> <a id="6371" class="Symbol">→</a> <a id="6373" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6375" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6377" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6379" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6381" href="Relations.Continuous.html#6357" class="Bound">𝓦</a> <a id="6383" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6385" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6387" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6394" href="Relations.Continuous.html#6394" class="Bound">I</a> <a id="6396" href="Relations.Continuous.html#6396" class="Bound">A</a> <a id="6398" href="Relations.Continuous.html#6398" class="Bound">𝓦</a> <a id="6400" class="Symbol">=</a> <a id="6402" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6404" href="Relations.Continuous.html#6396" class="Bound">A</a> <a id="6406" class="Symbol">→</a> <a id="6408" href="Relations.Continuous.html#6398" class="Bound">𝓦</a> <a id="6410" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6911" class="Keyword">module</a> <a id="6918" href="Relations.Continuous.html#6918" class="Module">_</a> <a id="6920" class="Symbol">{</a><a id="6921" href="Relations.Continuous.html#6921" class="Bound">𝓤</a> <a id="6923" href="Relations.Continuous.html#6923" class="Bound">𝓥</a> <a id="6925" href="Relations.Continuous.html#6925" class="Bound">𝓦</a> <a id="6927" class="Symbol">:</a> <a id="6929" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6937" class="Symbol">}</a> <a id="6939" class="Symbol">{</a><a id="6940" href="Relations.Continuous.html#6940" class="Bound">I</a> <a id="6942" href="Relations.Continuous.html#6942" class="Bound">J</a> <a id="6944" class="Symbol">:</a> <a id="6946" href="Relations.Continuous.html#6923" class="Bound">𝓥</a> <a id="6948" href="Universes.html#403" class="Function Operator">̇</a><a id="6949" class="Symbol">}</a> <a id="6951" class="Symbol">{</a><a id="6952" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="6954" class="Symbol">:</a> <a id="6956" href="Relations.Continuous.html#6940" class="Bound">I</a> <a id="6958" class="Symbol">→</a> <a id="6960" href="Relations.Continuous.html#6921" class="Bound">𝓤</a> <a id="6962" href="Universes.html#403" class="Function Operator">̇</a><a id="6963" class="Symbol">}</a> <a id="6965" class="Keyword">where</a>

 <a id="6973" href="Relations.Continuous.html#6973" class="Function">lift-dep-rel</a> <a id="6986" class="Symbol">:</a> <a id="6988" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6995" href="Relations.Continuous.html#6940" class="Bound">I</a> <a id="6997" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="6999" href="Relations.Continuous.html#6925" class="Bound">𝓦</a> <a id="7001" class="Symbol">→</a> <a id="7003" class="Symbol">(∀</a> <a id="7006" href="Relations.Continuous.html#7006" class="Bound">i</a> <a id="7008" class="Symbol">→</a> <a id="7010" href="Relations.Continuous.html#6942" class="Bound">J</a> <a id="7012" class="Symbol">→</a> <a id="7014" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="7016" href="Relations.Continuous.html#7006" class="Bound">i</a><a id="7017" class="Symbol">)</a> <a id="7019" class="Symbol">→</a> <a id="7021" href="Relations.Continuous.html#6923" class="Bound">𝓥</a> <a id="7023" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7025" href="Relations.Continuous.html#6925" class="Bound">𝓦</a> <a id="7027" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7030" href="Relations.Continuous.html#6973" class="Function">lift-dep-rel</a> <a id="7043" href="Relations.Continuous.html#7043" class="Bound">R</a> <a id="7045" href="Relations.Continuous.html#7045" class="Bound">𝕒</a> <a id="7047" class="Symbol">=</a> <a id="7049" class="Symbol">∀</a> <a id="7051" class="Symbol">(</a><a id="7052" href="Relations.Continuous.html#7052" class="Bound">j</a> <a id="7054" class="Symbol">:</a> <a id="7056" href="Relations.Continuous.html#6942" class="Bound">J</a><a id="7057" class="Symbol">)</a> <a id="7059" class="Symbol">→</a> <a id="7061" href="Relations.Continuous.html#7043" class="Bound">R</a> <a id="7063" class="Symbol">(λ</a> <a id="7066" href="Relations.Continuous.html#7066" class="Bound">i</a> <a id="7068" class="Symbol">→</a> <a id="7070" class="Symbol">(</a><a id="7071" href="Relations.Continuous.html#7045" class="Bound">𝕒</a> <a id="7073" href="Relations.Continuous.html#7066" class="Bound">i</a><a id="7074" class="Symbol">)</a> <a id="7076" href="Relations.Continuous.html#7052" class="Bound">j</a><a id="7077" class="Symbol">)</a>

 <a id="7081" href="Relations.Continuous.html#7081" class="Function">dep-compatible-fun</a> <a id="7100" class="Symbol">:</a> <a id="7102" class="Symbol">(∀</a> <a id="7105" href="Relations.Continuous.html#7105" class="Bound">i</a> <a id="7107" class="Symbol">→</a> <a id="7109" class="Symbol">(</a><a id="7110" href="Relations.Continuous.html#6942" class="Bound">J</a> <a id="7112" class="Symbol">→</a> <a id="7114" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="7116" href="Relations.Continuous.html#7105" class="Bound">i</a><a id="7117" class="Symbol">)</a> <a id="7119" class="Symbol">→</a> <a id="7121" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="7123" href="Relations.Continuous.html#7105" class="Bound">i</a><a id="7124" class="Symbol">)</a> <a id="7126" class="Symbol">→</a> <a id="7128" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="7135" href="Relations.Continuous.html#6940" class="Bound">I</a> <a id="7137" href="Relations.Continuous.html#6952" class="Bound">A</a> <a id="7139" href="Relations.Continuous.html#6925" class="Bound">𝓦</a> <a id="7141" class="Symbol">→</a> <a id="7143" href="Relations.Continuous.html#6923" class="Bound">𝓥</a> <a id="7145" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7147" href="Relations.Continuous.html#6921" class="Bound">𝓤</a> <a id="7149" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7151" href="Relations.Continuous.html#6925" class="Bound">𝓦</a> <a id="7153" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7156" href="Relations.Continuous.html#7081" class="Function">dep-compatible-fun</a> <a id="7175" href="Relations.Continuous.html#7175" class="Bound">𝕗</a> <a id="7177" href="Relations.Continuous.html#7177" class="Bound">R</a>  <a id="7180" class="Symbol">=</a> <a id="7182" class="Symbol">∀</a> <a id="7184" href="Relations.Continuous.html#7184" class="Bound">𝕒</a> <a id="7186" class="Symbol">→</a> <a id="7188" class="Symbol">(</a><a id="7189" href="Relations.Continuous.html#6973" class="Function">lift-dep-rel</a> <a id="7202" href="Relations.Continuous.html#7177" class="Bound">R</a><a id="7203" class="Symbol">)</a> <a id="7205" href="Relations.Continuous.html#7184" class="Bound">𝕒</a> <a id="7207" class="Symbol">→</a> <a id="7209" href="Relations.Continuous.html#7177" class="Bound">R</a> <a id="7211" class="Symbol">λ</a> <a id="7213" href="Relations.Continuous.html#7213" class="Bound">i</a> <a id="7215" class="Symbol">→</a> <a id="7217" class="Symbol">(</a><a id="7218" href="Relations.Continuous.html#7175" class="Bound">𝕗</a> <a id="7220" href="Relations.Continuous.html#7213" class="Bound">i</a><a id="7221" class="Symbol">)(</a><a id="7223" href="Relations.Continuous.html#7184" class="Bound">𝕒</a> <a id="7225" href="Relations.Continuous.html#7213" class="Bound">i</a><a id="7226" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → A i` of `𝕒`.)


--------------------------------------

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
