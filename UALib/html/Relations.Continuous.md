---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="continuous-relations">Continuous Relations*</a>

This is the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].<sup>[*](Relations.Continuous.html#fn0)</sup>

<pre class="Agda">

<a id="351" class="Symbol">{-#</a> <a id="355" class="Keyword">OPTIONS</a> <a id="363" class="Pragma">--without-K</a> <a id="375" class="Pragma">--exact-split</a> <a id="389" class="Pragma">--safe</a> <a id="396" class="Symbol">#-}</a>

<a id="401" class="Keyword">module</a> <a id="408" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="429" class="Keyword">where</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="467" class="Keyword">public</a>

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

<a id="ConRel"></a><a id="3268" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="3275" class="Symbol">:</a> <a id="3277" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3279" href="Universes.html#403" class="Function Operator">̇</a> <a id="3281" class="Symbol">→</a> <a id="3283" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3285" href="Universes.html#403" class="Function Operator">̇</a> <a id="3287" class="Symbol">→</a> <a id="3289" class="Symbol">(</a><a id="3290" href="Relations.Continuous.html#3290" class="Bound">𝓦</a> <a id="3292" class="Symbol">:</a> <a id="3294" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3302" class="Symbol">)</a> <a id="3304" class="Symbol">→</a> <a id="3306" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3308" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3310" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3312" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3314" href="Relations.Continuous.html#3290" class="Bound">𝓦</a> <a id="3316" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3318" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3320" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="3327" href="Relations.Continuous.html#3327" class="Bound">I</a> <a id="3329" href="Relations.Continuous.html#3329" class="Bound">A</a> <a id="3331" href="Relations.Continuous.html#3331" class="Bound">𝓦</a> <a id="3333" class="Symbol">=</a> <a id="3335" class="Symbol">(</a><a id="3336" href="Relations.Continuous.html#3327" class="Bound">I</a> <a id="3338" class="Symbol">→</a> <a id="3340" href="Relations.Continuous.html#3329" class="Bound">A</a><a id="3341" class="Symbol">)</a> <a id="3343" class="Symbol">→</a> <a id="3345" href="Relations.Continuous.html#3331" class="Bound">𝓦</a> <a id="3347" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3606" class="Keyword">module</a> <a id="3613" href="Relations.Continuous.html#3613" class="Module">_</a> <a id="3615" class="Symbol">{</a><a id="3616" href="Relations.Continuous.html#3616" class="Bound">I</a> <a id="3618" href="Relations.Continuous.html#3618" class="Bound">J</a> <a id="3620" class="Symbol">:</a> <a id="3622" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3624" href="Universes.html#403" class="Function Operator">̇</a><a id="3625" class="Symbol">}</a> <a id="3627" class="Symbol">{</a><a id="3628" href="Relations.Continuous.html#3628" class="Bound">A</a> <a id="3630" class="Symbol">:</a> <a id="3632" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3634" href="Universes.html#403" class="Function Operator">̇</a><a id="3635" class="Symbol">}</a> <a id="3637" class="Keyword">where</a>

 <a id="3645" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a> <a id="3658" class="Symbol">:</a> <a id="3660" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="3667" href="Relations.Continuous.html#3616" class="Bound">I</a> <a id="3669" href="Relations.Continuous.html#3628" class="Bound">A</a> <a id="3671" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3673" class="Symbol">→</a> <a id="3675" class="Symbol">(</a><a id="3676" href="Relations.Continuous.html#3616" class="Bound">I</a> <a id="3678" class="Symbol">→</a> <a id="3680" href="Relations.Continuous.html#3618" class="Bound">J</a> <a id="3682" class="Symbol">→</a> <a id="3684" href="Relations.Continuous.html#3628" class="Bound">A</a><a id="3685" class="Symbol">)</a> <a id="3687" class="Symbol">→</a> <a id="3689" href="Relations.Continuous.html#3622" class="Bound">𝓥</a> <a id="3691" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3693" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3695" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3698" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a> <a id="3711" href="Relations.Continuous.html#3711" class="Bound">R</a> <a id="3713" href="Relations.Continuous.html#3713" class="Bound">𝕒</a> <a id="3715" class="Symbol">=</a> <a id="3717" class="Symbol">∀</a> <a id="3719" class="Symbol">(</a><a id="3720" href="Relations.Continuous.html#3720" class="Bound">j</a> <a id="3722" class="Symbol">:</a> <a id="3724" href="Relations.Continuous.html#3618" class="Bound">J</a><a id="3725" class="Symbol">)</a> <a id="3727" class="Symbol">→</a> <a id="3729" href="Relations.Continuous.html#3711" class="Bound">R</a> <a id="3731" class="Symbol">λ</a> <a id="3733" href="Relations.Continuous.html#3733" class="Bound">i</a> <a id="3735" class="Symbol">→</a> <a id="3737" class="Symbol">(</a><a id="3738" href="Relations.Continuous.html#3713" class="Bound">𝕒</a> <a id="3740" href="Relations.Continuous.html#3733" class="Bound">i</a><a id="3741" class="Symbol">)</a> <a id="3743" href="Relations.Continuous.html#3720" class="Bound">j</a>

 <a id="3747" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a> <a id="3766" class="Symbol">:</a> <a id="3768" class="Symbol">(</a><a id="3769" href="Relations.Continuous.html#3616" class="Bound">I</a> <a id="3771" class="Symbol">→</a> <a id="3773" class="Symbol">(</a><a id="3774" href="Relations.Continuous.html#3618" class="Bound">J</a> <a id="3776" class="Symbol">→</a> <a id="3778" href="Relations.Continuous.html#3628" class="Bound">A</a><a id="3779" class="Symbol">)</a> <a id="3781" class="Symbol">→</a> <a id="3783" href="Relations.Continuous.html#3628" class="Bound">A</a><a id="3784" class="Symbol">)</a> <a id="3786" class="Symbol">→</a> <a id="3788" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="3795" href="Relations.Continuous.html#3616" class="Bound">I</a> <a id="3797" href="Relations.Continuous.html#3628" class="Bound">A</a> <a id="3799" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3801" class="Symbol">→</a> <a id="3803" href="Relations.Continuous.html#3622" class="Bound">𝓥</a> <a id="3805" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3807" href="Relations.Continuous.html#3632" class="Bound">𝓤</a> <a id="3809" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3811" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3813" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3816" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a> <a id="3835" href="Relations.Continuous.html#3835" class="Bound">𝕗</a> <a id="3837" href="Relations.Continuous.html#3837" class="Bound">R</a>  <a id="3840" class="Symbol">=</a> <a id="3842" class="Symbol">∀</a> <a id="3844" href="Relations.Continuous.html#3844" class="Bound">𝕒</a> <a id="3846" class="Symbol">→</a> <a id="3848" class="Symbol">(</a><a id="3849" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a> <a id="3862" href="Relations.Continuous.html#3837" class="Bound">R</a><a id="3863" class="Symbol">)</a> <a id="3865" href="Relations.Continuous.html#3844" class="Bound">𝕒</a> <a id="3867" class="Symbol">→</a> <a id="3869" href="Relations.Continuous.html#3837" class="Bound">R</a> <a id="3871" class="Symbol">λ</a> <a id="3873" href="Relations.Continuous.html#3873" class="Bound">i</a> <a id="3875" class="Symbol">→</a> <a id="3877" class="Symbol">(</a><a id="3878" href="Relations.Continuous.html#3835" class="Bound">𝕗</a> <a id="3880" href="Relations.Continuous.html#3873" class="Bound">i</a><a id="3881" class="Symbol">)</a> <a id="3883" class="Symbol">(</a><a id="3884" href="Relations.Continuous.html#3844" class="Bound">𝕒</a> <a id="3886" href="Relations.Continuous.html#3873" class="Bound">i</a><a id="3887" class="Symbol">)</a>

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

<a id="DepRel"></a><a id="6378" href="Relations.Continuous.html#6378" class="Function">DepRel</a> <a id="6385" class="Symbol">:</a> <a id="6387" class="Symbol">(</a><a id="6388" href="Relations.Continuous.html#6388" class="Bound">I</a> <a id="6390" class="Symbol">:</a> <a id="6392" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6394" href="Universes.html#403" class="Function Operator">̇</a><a id="6395" class="Symbol">)</a> <a id="6397" class="Symbol">→</a> <a id="6399" class="Symbol">(</a><a id="6400" href="Relations.Continuous.html#6388" class="Bound">I</a> <a id="6402" class="Symbol">→</a> <a id="6404" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6406" href="Universes.html#403" class="Function Operator">̇</a><a id="6407" class="Symbol">)</a> <a id="6409" class="Symbol">→</a> <a id="6411" class="Symbol">(</a><a id="6412" href="Relations.Continuous.html#6412" class="Bound">𝓦</a> <a id="6414" class="Symbol">:</a> <a id="6416" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6424" class="Symbol">)</a> <a id="6426" class="Symbol">→</a> <a id="6428" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6430" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6432" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6434" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6436" href="Relations.Continuous.html#6412" class="Bound">𝓦</a> <a id="6438" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6440" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6442" href="Relations.Continuous.html#6378" class="Function">DepRel</a> <a id="6449" href="Relations.Continuous.html#6449" class="Bound">I</a> <a id="6451" href="Relations.Continuous.html#6451" class="Bound">𝒜</a> <a id="6453" href="Relations.Continuous.html#6453" class="Bound">𝓦</a> <a id="6455" class="Symbol">=</a> <a id="6457" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6459" href="Relations.Continuous.html#6451" class="Bound">𝒜</a> <a id="6461" class="Symbol">→</a> <a id="6463" href="Relations.Continuous.html#6453" class="Bound">𝓦</a> <a id="6465" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6966" class="Keyword">module</a> <a id="6973" href="Relations.Continuous.html#6973" class="Module">_</a> <a id="6975" class="Symbol">{</a><a id="6976" href="Relations.Continuous.html#6976" class="Bound">I</a> <a id="6978" href="Relations.Continuous.html#6978" class="Bound">J</a> <a id="6980" class="Symbol">:</a> <a id="6982" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6984" href="Universes.html#403" class="Function Operator">̇</a><a id="6985" class="Symbol">}</a> <a id="6987" class="Symbol">{</a><a id="6988" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="6990" class="Symbol">:</a> <a id="6992" href="Relations.Continuous.html#6976" class="Bound">I</a> <a id="6994" class="Symbol">→</a> <a id="6996" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6998" href="Universes.html#403" class="Function Operator">̇</a><a id="6999" class="Symbol">}</a> <a id="7001" class="Keyword">where</a>

 <a id="7009" href="Relations.Continuous.html#7009" class="Function">lift-dep-rel</a> <a id="7022" class="Symbol">:</a> <a id="7024" href="Relations.Continuous.html#6378" class="Function">DepRel</a> <a id="7031" href="Relations.Continuous.html#6976" class="Bound">I</a> <a id="7033" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="7035" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7037" class="Symbol">→</a> <a id="7039" class="Symbol">(∀</a> <a id="7042" href="Relations.Continuous.html#7042" class="Bound">i</a> <a id="7044" class="Symbol">→</a> <a id="7046" href="Relations.Continuous.html#6978" class="Bound">J</a> <a id="7048" class="Symbol">→</a> <a id="7050" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="7052" href="Relations.Continuous.html#7042" class="Bound">i</a><a id="7053" class="Symbol">)</a> <a id="7055" class="Symbol">→</a> <a id="7057" href="Relations.Continuous.html#6982" class="Bound">𝓥</a> <a id="7059" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7061" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7063" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7066" href="Relations.Continuous.html#7009" class="Function">lift-dep-rel</a> <a id="7079" href="Relations.Continuous.html#7079" class="Bound">R</a> <a id="7081" href="Relations.Continuous.html#7081" class="Bound">𝕒</a> <a id="7083" class="Symbol">=</a> <a id="7085" class="Symbol">∀</a> <a id="7087" class="Symbol">(</a><a id="7088" href="Relations.Continuous.html#7088" class="Bound">j</a> <a id="7090" class="Symbol">:</a> <a id="7092" href="Relations.Continuous.html#6978" class="Bound">J</a><a id="7093" class="Symbol">)</a> <a id="7095" class="Symbol">→</a> <a id="7097" href="Relations.Continuous.html#7079" class="Bound">R</a> <a id="7099" class="Symbol">(λ</a> <a id="7102" href="Relations.Continuous.html#7102" class="Bound">i</a> <a id="7104" class="Symbol">→</a> <a id="7106" class="Symbol">(</a><a id="7107" href="Relations.Continuous.html#7081" class="Bound">𝕒</a> <a id="7109" href="Relations.Continuous.html#7102" class="Bound">i</a><a id="7110" class="Symbol">)</a> <a id="7112" href="Relations.Continuous.html#7088" class="Bound">j</a><a id="7113" class="Symbol">)</a>

 <a id="7117" href="Relations.Continuous.html#7117" class="Function">dep-compatible-fun</a> <a id="7136" class="Symbol">:</a> <a id="7138" class="Symbol">(∀</a> <a id="7141" href="Relations.Continuous.html#7141" class="Bound">i</a> <a id="7143" class="Symbol">→</a> <a id="7145" class="Symbol">(</a><a id="7146" href="Relations.Continuous.html#6978" class="Bound">J</a> <a id="7148" class="Symbol">→</a> <a id="7150" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="7152" href="Relations.Continuous.html#7141" class="Bound">i</a><a id="7153" class="Symbol">)</a> <a id="7155" class="Symbol">→</a> <a id="7157" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="7159" href="Relations.Continuous.html#7141" class="Bound">i</a><a id="7160" class="Symbol">)</a> <a id="7162" class="Symbol">→</a> <a id="7164" href="Relations.Continuous.html#6378" class="Function">DepRel</a> <a id="7171" href="Relations.Continuous.html#6976" class="Bound">I</a> <a id="7173" href="Relations.Continuous.html#6988" class="Bound">𝒜</a> <a id="7175" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7177" class="Symbol">→</a> <a id="7179" href="Relations.Continuous.html#6982" class="Bound">𝓥</a> <a id="7181" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7183" href="Relations.Continuous.html#6996" class="Bound">𝓤</a> <a id="7185" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7187" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7189" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7192" href="Relations.Continuous.html#7117" class="Function">dep-compatible-fun</a> <a id="7211" href="Relations.Continuous.html#7211" class="Bound">𝕗</a> <a id="7213" href="Relations.Continuous.html#7213" class="Bound">R</a>  <a id="7216" class="Symbol">=</a> <a id="7218" class="Symbol">∀</a> <a id="7220" href="Relations.Continuous.html#7220" class="Bound">𝕒</a> <a id="7222" class="Symbol">→</a> <a id="7224" class="Symbol">(</a><a id="7225" href="Relations.Continuous.html#7009" class="Function">lift-dep-rel</a> <a id="7238" href="Relations.Continuous.html#7213" class="Bound">R</a><a id="7239" class="Symbol">)</a> <a id="7241" href="Relations.Continuous.html#7220" class="Bound">𝕒</a> <a id="7243" class="Symbol">→</a> <a id="7245" href="Relations.Continuous.html#7213" class="Bound">R</a> <a id="7247" class="Symbol">λ</a> <a id="7249" href="Relations.Continuous.html#7249" class="Bound">i</a> <a id="7251" class="Symbol">→</a> <a id="7253" class="Symbol">(</a><a id="7254" href="Relations.Continuous.html#7211" class="Bound">𝕗</a> <a id="7256" href="Relations.Continuous.html#7249" class="Bound">i</a><a id="7257" class="Symbol">)(</a><a id="7259" href="Relations.Continuous.html#7220" class="Bound">𝕒</a> <a id="7261" href="Relations.Continuous.html#7249" class="Bound">i</a><a id="7262" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → 𝒜 i` of `𝕒`.)


--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
