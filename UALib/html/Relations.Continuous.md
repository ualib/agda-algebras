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

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ConRel"></a><a id="3215" href="Relations.Continuous.html#3215" class="Function">ConRel</a> <a id="3222" class="Symbol">:</a> <a id="3224" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3226" href="Universes.html#403" class="Function Operator">̇</a> <a id="3228" class="Symbol">→</a> <a id="3230" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3232" href="Universes.html#403" class="Function Operator">̇</a> <a id="3234" class="Symbol">→</a> <a id="3236" class="Symbol">(</a><a id="3237" href="Relations.Continuous.html#3237" class="Bound">𝓦</a> <a id="3239" class="Symbol">:</a> <a id="3241" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3249" class="Symbol">)</a> <a id="3251" class="Symbol">→</a> <a id="3253" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3255" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3257" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3259" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3261" href="Relations.Continuous.html#3237" class="Bound">𝓦</a> <a id="3263" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3265" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3267" href="Relations.Continuous.html#3215" class="Function">ConRel</a> <a id="3274" href="Relations.Continuous.html#3274" class="Bound">I</a> <a id="3276" href="Relations.Continuous.html#3276" class="Bound">A</a> <a id="3278" href="Relations.Continuous.html#3278" class="Bound">𝓦</a> <a id="3280" class="Symbol">=</a> <a id="3282" class="Symbol">(</a><a id="3283" href="Relations.Continuous.html#3274" class="Bound">I</a> <a id="3285" class="Symbol">→</a> <a id="3287" href="Relations.Continuous.html#3276" class="Bound">A</a><a id="3288" class="Symbol">)</a> <a id="3290" class="Symbol">→</a> <a id="3292" href="Relations.Continuous.html#3278" class="Bound">𝓦</a> <a id="3294" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3553" class="Keyword">module</a> <a id="3560" href="Relations.Continuous.html#3560" class="Module">_</a> <a id="3562" class="Symbol">{</a><a id="3563" href="Relations.Continuous.html#3563" class="Bound">I</a> <a id="3565" href="Relations.Continuous.html#3565" class="Bound">J</a> <a id="3567" class="Symbol">:</a> <a id="3569" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3571" href="Universes.html#403" class="Function Operator">̇</a><a id="3572" class="Symbol">}</a> <a id="3574" class="Symbol">{</a><a id="3575" href="Relations.Continuous.html#3575" class="Bound">A</a> <a id="3577" class="Symbol">:</a> <a id="3579" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3581" href="Universes.html#403" class="Function Operator">̇</a><a id="3582" class="Symbol">}</a> <a id="3584" class="Keyword">where</a>

 <a id="3592" href="Relations.Continuous.html#3592" class="Function">lift-con-rel</a> <a id="3605" class="Symbol">:</a> <a id="3607" href="Relations.Continuous.html#3215" class="Function">ConRel</a> <a id="3614" href="Relations.Continuous.html#3563" class="Bound">I</a> <a id="3616" href="Relations.Continuous.html#3575" class="Bound">A</a> <a id="3618" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3620" class="Symbol">→</a> <a id="3622" class="Symbol">(</a><a id="3623" href="Relations.Continuous.html#3563" class="Bound">I</a> <a id="3625" class="Symbol">→</a> <a id="3627" href="Relations.Continuous.html#3565" class="Bound">J</a> <a id="3629" class="Symbol">→</a> <a id="3631" href="Relations.Continuous.html#3575" class="Bound">A</a><a id="3632" class="Symbol">)</a> <a id="3634" class="Symbol">→</a> <a id="3636" href="Relations.Continuous.html#3569" class="Bound">𝓥</a> <a id="3638" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3640" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3642" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3645" href="Relations.Continuous.html#3592" class="Function">lift-con-rel</a> <a id="3658" href="Relations.Continuous.html#3658" class="Bound">R</a> <a id="3660" href="Relations.Continuous.html#3660" class="Bound">𝕒</a> <a id="3662" class="Symbol">=</a> <a id="3664" class="Symbol">∀</a> <a id="3666" class="Symbol">(</a><a id="3667" href="Relations.Continuous.html#3667" class="Bound">j</a> <a id="3669" class="Symbol">:</a> <a id="3671" href="Relations.Continuous.html#3565" class="Bound">J</a><a id="3672" class="Symbol">)</a> <a id="3674" class="Symbol">→</a> <a id="3676" href="Relations.Continuous.html#3658" class="Bound">R</a> <a id="3678" class="Symbol">λ</a> <a id="3680" href="Relations.Continuous.html#3680" class="Bound">i</a> <a id="3682" class="Symbol">→</a> <a id="3684" class="Symbol">(</a><a id="3685" href="Relations.Continuous.html#3660" class="Bound">𝕒</a> <a id="3687" href="Relations.Continuous.html#3680" class="Bound">i</a><a id="3688" class="Symbol">)</a> <a id="3690" href="Relations.Continuous.html#3667" class="Bound">j</a>

 <a id="3694" href="Relations.Continuous.html#3694" class="Function">con-compatible-fun</a> <a id="3713" class="Symbol">:</a> <a id="3715" class="Symbol">(</a><a id="3716" href="Relations.Continuous.html#3563" class="Bound">I</a> <a id="3718" class="Symbol">→</a> <a id="3720" class="Symbol">(</a><a id="3721" href="Relations.Continuous.html#3565" class="Bound">J</a> <a id="3723" class="Symbol">→</a> <a id="3725" href="Relations.Continuous.html#3575" class="Bound">A</a><a id="3726" class="Symbol">)</a> <a id="3728" class="Symbol">→</a> <a id="3730" href="Relations.Continuous.html#3575" class="Bound">A</a><a id="3731" class="Symbol">)</a> <a id="3733" class="Symbol">→</a> <a id="3735" href="Relations.Continuous.html#3215" class="Function">ConRel</a> <a id="3742" href="Relations.Continuous.html#3563" class="Bound">I</a> <a id="3744" href="Relations.Continuous.html#3575" class="Bound">A</a> <a id="3746" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3748" class="Symbol">→</a> <a id="3750" href="Relations.Continuous.html#3569" class="Bound">𝓥</a> <a id="3752" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3754" href="Relations.Continuous.html#3579" class="Bound">𝓤</a> <a id="3756" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3758" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3760" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3763" href="Relations.Continuous.html#3694" class="Function">con-compatible-fun</a> <a id="3782" href="Relations.Continuous.html#3782" class="Bound">𝕗</a> <a id="3784" href="Relations.Continuous.html#3784" class="Bound">R</a>  <a id="3787" class="Symbol">=</a> <a id="3789" class="Symbol">∀</a> <a id="3791" href="Relations.Continuous.html#3791" class="Bound">𝕒</a> <a id="3793" class="Symbol">→</a> <a id="3795" class="Symbol">(</a><a id="3796" href="Relations.Continuous.html#3592" class="Function">lift-con-rel</a> <a id="3809" href="Relations.Continuous.html#3784" class="Bound">R</a><a id="3810" class="Symbol">)</a> <a id="3812" href="Relations.Continuous.html#3791" class="Bound">𝕒</a> <a id="3814" class="Symbol">→</a> <a id="3816" href="Relations.Continuous.html#3784" class="Bound">R</a> <a id="3818" class="Symbol">λ</a> <a id="3820" href="Relations.Continuous.html#3820" class="Bound">i</a> <a id="3822" class="Symbol">→</a> <a id="3824" class="Symbol">(</a><a id="3825" href="Relations.Continuous.html#3782" class="Bound">𝕗</a> <a id="3827" href="Relations.Continuous.html#3820" class="Bound">i</a><a id="3828" class="Symbol">)</a> <a id="3830" class="Symbol">(</a><a id="3831" href="Relations.Continuous.html#3791" class="Bound">𝕒</a> <a id="3833" href="Relations.Continuous.html#3820" class="Bound">i</a><a id="3834" class="Symbol">)</a>

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

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type `𝒜 : I → 𝓤 ̇`, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `𝒜 i` to `𝒜 j` to `𝒜 k` to ….

<pre class="Agda">

<a id="DepRel"></a><a id="6325" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6332" class="Symbol">:</a> <a id="6334" class="Symbol">(</a><a id="6335" href="Relations.Continuous.html#6335" class="Bound">I</a> <a id="6337" class="Symbol">:</a> <a id="6339" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6341" href="Universes.html#403" class="Function Operator">̇</a><a id="6342" class="Symbol">)</a> <a id="6344" class="Symbol">→</a> <a id="6346" class="Symbol">(</a><a id="6347" href="Relations.Continuous.html#6335" class="Bound">I</a> <a id="6349" class="Symbol">→</a> <a id="6351" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6353" href="Universes.html#403" class="Function Operator">̇</a><a id="6354" class="Symbol">)</a> <a id="6356" class="Symbol">→</a> <a id="6358" class="Symbol">(</a><a id="6359" href="Relations.Continuous.html#6359" class="Bound">𝓦</a> <a id="6361" class="Symbol">:</a> <a id="6363" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6371" class="Symbol">)</a> <a id="6373" class="Symbol">→</a> <a id="6375" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6377" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6379" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6381" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6383" href="Relations.Continuous.html#6359" class="Bound">𝓦</a> <a id="6385" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6387" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6389" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6396" href="Relations.Continuous.html#6396" class="Bound">I</a> <a id="6398" href="Relations.Continuous.html#6398" class="Bound">𝒜</a> <a id="6400" href="Relations.Continuous.html#6400" class="Bound">𝓦</a> <a id="6402" class="Symbol">=</a> <a id="6404" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6406" href="Relations.Continuous.html#6398" class="Bound">𝒜</a> <a id="6408" class="Symbol">→</a> <a id="6410" href="Relations.Continuous.html#6400" class="Bound">𝓦</a> <a id="6412" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6913" class="Keyword">module</a> <a id="6920" href="Relations.Continuous.html#6920" class="Module">_</a> <a id="6922" class="Symbol">{</a><a id="6923" href="Relations.Continuous.html#6923" class="Bound">I</a> <a id="6925" href="Relations.Continuous.html#6925" class="Bound">J</a> <a id="6927" class="Symbol">:</a> <a id="6929" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6931" href="Universes.html#403" class="Function Operator">̇</a><a id="6932" class="Symbol">}</a> <a id="6934" class="Symbol">{</a><a id="6935" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="6937" class="Symbol">:</a> <a id="6939" href="Relations.Continuous.html#6923" class="Bound">I</a> <a id="6941" class="Symbol">→</a> <a id="6943" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6945" href="Universes.html#403" class="Function Operator">̇</a><a id="6946" class="Symbol">}</a> <a id="6948" class="Keyword">where</a>

 <a id="6956" href="Relations.Continuous.html#6956" class="Function">lift-dep-rel</a> <a id="6969" class="Symbol">:</a> <a id="6971" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="6978" href="Relations.Continuous.html#6923" class="Bound">I</a> <a id="6980" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="6982" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6984" class="Symbol">→</a> <a id="6986" class="Symbol">(∀</a> <a id="6989" href="Relations.Continuous.html#6989" class="Bound">i</a> <a id="6991" class="Symbol">→</a> <a id="6993" href="Relations.Continuous.html#6925" class="Bound">J</a> <a id="6995" class="Symbol">→</a> <a id="6997" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="6999" href="Relations.Continuous.html#6989" class="Bound">i</a><a id="7000" class="Symbol">)</a> <a id="7002" class="Symbol">→</a> <a id="7004" href="Relations.Continuous.html#6929" class="Bound">𝓥</a> <a id="7006" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7008" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7010" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7013" href="Relations.Continuous.html#6956" class="Function">lift-dep-rel</a> <a id="7026" href="Relations.Continuous.html#7026" class="Bound">R</a> <a id="7028" href="Relations.Continuous.html#7028" class="Bound">𝕒</a> <a id="7030" class="Symbol">=</a> <a id="7032" class="Symbol">∀</a> <a id="7034" class="Symbol">(</a><a id="7035" href="Relations.Continuous.html#7035" class="Bound">j</a> <a id="7037" class="Symbol">:</a> <a id="7039" href="Relations.Continuous.html#6925" class="Bound">J</a><a id="7040" class="Symbol">)</a> <a id="7042" class="Symbol">→</a> <a id="7044" href="Relations.Continuous.html#7026" class="Bound">R</a> <a id="7046" class="Symbol">(λ</a> <a id="7049" href="Relations.Continuous.html#7049" class="Bound">i</a> <a id="7051" class="Symbol">→</a> <a id="7053" class="Symbol">(</a><a id="7054" href="Relations.Continuous.html#7028" class="Bound">𝕒</a> <a id="7056" href="Relations.Continuous.html#7049" class="Bound">i</a><a id="7057" class="Symbol">)</a> <a id="7059" href="Relations.Continuous.html#7035" class="Bound">j</a><a id="7060" class="Symbol">)</a>

 <a id="7064" href="Relations.Continuous.html#7064" class="Function">dep-compatible-fun</a> <a id="7083" class="Symbol">:</a> <a id="7085" class="Symbol">(∀</a> <a id="7088" href="Relations.Continuous.html#7088" class="Bound">i</a> <a id="7090" class="Symbol">→</a> <a id="7092" class="Symbol">(</a><a id="7093" href="Relations.Continuous.html#6925" class="Bound">J</a> <a id="7095" class="Symbol">→</a> <a id="7097" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="7099" href="Relations.Continuous.html#7088" class="Bound">i</a><a id="7100" class="Symbol">)</a> <a id="7102" class="Symbol">→</a> <a id="7104" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="7106" href="Relations.Continuous.html#7088" class="Bound">i</a><a id="7107" class="Symbol">)</a> <a id="7109" class="Symbol">→</a> <a id="7111" href="Relations.Continuous.html#6325" class="Function">DepRel</a> <a id="7118" href="Relations.Continuous.html#6923" class="Bound">I</a> <a id="7120" href="Relations.Continuous.html#6935" class="Bound">𝒜</a> <a id="7122" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7124" class="Symbol">→</a> <a id="7126" href="Relations.Continuous.html#6929" class="Bound">𝓥</a> <a id="7128" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7130" href="Relations.Continuous.html#6943" class="Bound">𝓤</a> <a id="7132" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7134" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7136" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7139" href="Relations.Continuous.html#7064" class="Function">dep-compatible-fun</a> <a id="7158" href="Relations.Continuous.html#7158" class="Bound">𝕗</a> <a id="7160" href="Relations.Continuous.html#7160" class="Bound">R</a>  <a id="7163" class="Symbol">=</a> <a id="7165" class="Symbol">∀</a> <a id="7167" href="Relations.Continuous.html#7167" class="Bound">𝕒</a> <a id="7169" class="Symbol">→</a> <a id="7171" class="Symbol">(</a><a id="7172" href="Relations.Continuous.html#6956" class="Function">lift-dep-rel</a> <a id="7185" href="Relations.Continuous.html#7160" class="Bound">R</a><a id="7186" class="Symbol">)</a> <a id="7188" href="Relations.Continuous.html#7167" class="Bound">𝕒</a> <a id="7190" class="Symbol">→</a> <a id="7192" href="Relations.Continuous.html#7160" class="Bound">R</a> <a id="7194" class="Symbol">λ</a> <a id="7196" href="Relations.Continuous.html#7196" class="Bound">i</a> <a id="7198" class="Symbol">→</a> <a id="7200" class="Symbol">(</a><a id="7201" href="Relations.Continuous.html#7158" class="Bound">𝕗</a> <a id="7203" href="Relations.Continuous.html#7196" class="Bound">i</a><a id="7204" class="Symbol">)(</a><a id="7206" href="Relations.Continuous.html#7167" class="Bound">𝕒</a> <a id="7208" href="Relations.Continuous.html#7196" class="Bound">i</a><a id="7209" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → 𝒜 i` of `𝕒`.)


--------------------------------------

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
