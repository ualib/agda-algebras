---
layout: default
title : Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="continuous-relations">Continuous Relations*</a>

This is the [Relations.Continuous][] module of the [Agda Universal Algebra Library][].<sup>[*](Relations.Continuous.html#fn0)</sup>

<pre class="Agda">

<a id="339" class="Symbol">{-#</a> <a id="343" class="Keyword">OPTIONS</a> <a id="351" class="Pragma">--without-K</a> <a id="363" class="Pragma">--exact-split</a> <a id="377" class="Pragma">--safe</a> <a id="384" class="Symbol">#-}</a>

<a id="389" class="Keyword">module</a> <a id="396" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="417" class="Keyword">where</a>

<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="455" class="Keyword">public</a>

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

<a id="ConRel"></a><a id="3256" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="3263" class="Symbol">:</a> <a id="3265" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3267" href="Universes.html#403" class="Function Operator">̇</a> <a id="3269" class="Symbol">→</a> <a id="3271" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3273" href="Universes.html#403" class="Function Operator">̇</a> <a id="3275" class="Symbol">→</a> <a id="3277" class="Symbol">(</a><a id="3278" href="Relations.Continuous.html#3278" class="Bound">𝓦</a> <a id="3280" class="Symbol">:</a> <a id="3282" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3290" class="Symbol">)</a> <a id="3292" class="Symbol">→</a> <a id="3294" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3296" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3298" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3300" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3302" href="Relations.Continuous.html#3278" class="Bound">𝓦</a> <a id="3304" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3306" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3308" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="3315" href="Relations.Continuous.html#3315" class="Bound">I</a> <a id="3317" href="Relations.Continuous.html#3317" class="Bound">A</a> <a id="3319" href="Relations.Continuous.html#3319" class="Bound">𝓦</a> <a id="3321" class="Symbol">=</a> <a id="3323" class="Symbol">(</a><a id="3324" href="Relations.Continuous.html#3315" class="Bound">I</a> <a id="3326" class="Symbol">→</a> <a id="3328" href="Relations.Continuous.html#3317" class="Bound">A</a><a id="3329" class="Symbol">)</a> <a id="3331" class="Symbol">→</a> <a id="3333" href="Relations.Continuous.html#3319" class="Bound">𝓦</a> <a id="3335" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3594" class="Keyword">module</a> <a id="3601" href="Relations.Continuous.html#3601" class="Module">_</a> <a id="3603" class="Symbol">{</a><a id="3604" href="Relations.Continuous.html#3604" class="Bound">I</a> <a id="3606" href="Relations.Continuous.html#3606" class="Bound">J</a> <a id="3608" class="Symbol">:</a> <a id="3610" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3612" href="Universes.html#403" class="Function Operator">̇</a><a id="3613" class="Symbol">}</a> <a id="3615" class="Symbol">{</a><a id="3616" href="Relations.Continuous.html#3616" class="Bound">A</a> <a id="3618" class="Symbol">:</a> <a id="3620" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3622" href="Universes.html#403" class="Function Operator">̇</a><a id="3623" class="Symbol">}</a> <a id="3625" class="Keyword">where</a>

 <a id="3633" href="Relations.Continuous.html#3633" class="Function">lift-con-rel</a> <a id="3646" class="Symbol">:</a> <a id="3648" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="3655" href="Relations.Continuous.html#3604" class="Bound">I</a> <a id="3657" href="Relations.Continuous.html#3616" class="Bound">A</a> <a id="3659" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3661" class="Symbol">→</a> <a id="3663" class="Symbol">(</a><a id="3664" href="Relations.Continuous.html#3604" class="Bound">I</a> <a id="3666" class="Symbol">→</a> <a id="3668" href="Relations.Continuous.html#3606" class="Bound">J</a> <a id="3670" class="Symbol">→</a> <a id="3672" href="Relations.Continuous.html#3616" class="Bound">A</a><a id="3673" class="Symbol">)</a> <a id="3675" class="Symbol">→</a> <a id="3677" href="Relations.Continuous.html#3610" class="Bound">𝓥</a> <a id="3679" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3681" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3683" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3686" href="Relations.Continuous.html#3633" class="Function">lift-con-rel</a> <a id="3699" href="Relations.Continuous.html#3699" class="Bound">R</a> <a id="3701" href="Relations.Continuous.html#3701" class="Bound">𝕒</a> <a id="3703" class="Symbol">=</a> <a id="3705" class="Symbol">∀</a> <a id="3707" class="Symbol">(</a><a id="3708" href="Relations.Continuous.html#3708" class="Bound">j</a> <a id="3710" class="Symbol">:</a> <a id="3712" href="Relations.Continuous.html#3606" class="Bound">J</a><a id="3713" class="Symbol">)</a> <a id="3715" class="Symbol">→</a> <a id="3717" href="Relations.Continuous.html#3699" class="Bound">R</a> <a id="3719" class="Symbol">λ</a> <a id="3721" href="Relations.Continuous.html#3721" class="Bound">i</a> <a id="3723" class="Symbol">→</a> <a id="3725" class="Symbol">(</a><a id="3726" href="Relations.Continuous.html#3701" class="Bound">𝕒</a> <a id="3728" href="Relations.Continuous.html#3721" class="Bound">i</a><a id="3729" class="Symbol">)</a> <a id="3731" href="Relations.Continuous.html#3708" class="Bound">j</a>

 <a id="3735" href="Relations.Continuous.html#3735" class="Function">con-compatible-fun</a> <a id="3754" class="Symbol">:</a> <a id="3756" class="Symbol">(</a><a id="3757" href="Relations.Continuous.html#3604" class="Bound">I</a> <a id="3759" class="Symbol">→</a> <a id="3761" class="Symbol">(</a><a id="3762" href="Relations.Continuous.html#3606" class="Bound">J</a> <a id="3764" class="Symbol">→</a> <a id="3766" href="Relations.Continuous.html#3616" class="Bound">A</a><a id="3767" class="Symbol">)</a> <a id="3769" class="Symbol">→</a> <a id="3771" href="Relations.Continuous.html#3616" class="Bound">A</a><a id="3772" class="Symbol">)</a> <a id="3774" class="Symbol">→</a> <a id="3776" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="3783" href="Relations.Continuous.html#3604" class="Bound">I</a> <a id="3785" href="Relations.Continuous.html#3616" class="Bound">A</a> <a id="3787" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3789" class="Symbol">→</a> <a id="3791" href="Relations.Continuous.html#3610" class="Bound">𝓥</a> <a id="3793" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3795" href="Relations.Continuous.html#3620" class="Bound">𝓤</a> <a id="3797" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3799" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3801" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3804" href="Relations.Continuous.html#3735" class="Function">con-compatible-fun</a> <a id="3823" href="Relations.Continuous.html#3823" class="Bound">𝕗</a> <a id="3825" href="Relations.Continuous.html#3825" class="Bound">R</a>  <a id="3828" class="Symbol">=</a> <a id="3830" class="Symbol">∀</a> <a id="3832" href="Relations.Continuous.html#3832" class="Bound">𝕒</a> <a id="3834" class="Symbol">→</a> <a id="3836" class="Symbol">(</a><a id="3837" href="Relations.Continuous.html#3633" class="Function">lift-con-rel</a> <a id="3850" href="Relations.Continuous.html#3825" class="Bound">R</a><a id="3851" class="Symbol">)</a> <a id="3853" href="Relations.Continuous.html#3832" class="Bound">𝕒</a> <a id="3855" class="Symbol">→</a> <a id="3857" href="Relations.Continuous.html#3825" class="Bound">R</a> <a id="3859" class="Symbol">λ</a> <a id="3861" href="Relations.Continuous.html#3861" class="Bound">i</a> <a id="3863" class="Symbol">→</a> <a id="3865" class="Symbol">(</a><a id="3866" href="Relations.Continuous.html#3823" class="Bound">𝕗</a> <a id="3868" href="Relations.Continuous.html#3861" class="Bound">i</a><a id="3869" class="Symbol">)</a> <a id="3871" class="Symbol">(</a><a id="3872" href="Relations.Continuous.html#3832" class="Bound">𝕒</a> <a id="3874" href="Relations.Continuous.html#3861" class="Bound">i</a><a id="3875" class="Symbol">)</a>

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

<a id="DepRel"></a><a id="6366" href="Relations.Continuous.html#6366" class="Function">DepRel</a> <a id="6373" class="Symbol">:</a> <a id="6375" class="Symbol">(</a><a id="6376" href="Relations.Continuous.html#6376" class="Bound">I</a> <a id="6378" class="Symbol">:</a> <a id="6380" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6382" href="Universes.html#403" class="Function Operator">̇</a><a id="6383" class="Symbol">)</a> <a id="6385" class="Symbol">→</a> <a id="6387" class="Symbol">(</a><a id="6388" href="Relations.Continuous.html#6376" class="Bound">I</a> <a id="6390" class="Symbol">→</a> <a id="6392" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6394" href="Universes.html#403" class="Function Operator">̇</a><a id="6395" class="Symbol">)</a> <a id="6397" class="Symbol">→</a> <a id="6399" class="Symbol">(</a><a id="6400" href="Relations.Continuous.html#6400" class="Bound">𝓦</a> <a id="6402" class="Symbol">:</a> <a id="6404" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6412" class="Symbol">)</a> <a id="6414" class="Symbol">→</a> <a id="6416" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6418" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6420" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6422" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6424" href="Relations.Continuous.html#6400" class="Bound">𝓦</a> <a id="6426" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6428" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6430" href="Relations.Continuous.html#6366" class="Function">DepRel</a> <a id="6437" href="Relations.Continuous.html#6437" class="Bound">I</a> <a id="6439" href="Relations.Continuous.html#6439" class="Bound">𝒜</a> <a id="6441" href="Relations.Continuous.html#6441" class="Bound">𝓦</a> <a id="6443" class="Symbol">=</a> <a id="6445" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6447" href="Relations.Continuous.html#6439" class="Bound">𝒜</a> <a id="6449" class="Symbol">→</a> <a id="6451" href="Relations.Continuous.html#6441" class="Bound">𝓦</a> <a id="6453" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6954" class="Keyword">module</a> <a id="6961" href="Relations.Continuous.html#6961" class="Module">_</a> <a id="6963" class="Symbol">{</a><a id="6964" href="Relations.Continuous.html#6964" class="Bound">I</a> <a id="6966" href="Relations.Continuous.html#6966" class="Bound">J</a> <a id="6968" class="Symbol">:</a> <a id="6970" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6972" href="Universes.html#403" class="Function Operator">̇</a><a id="6973" class="Symbol">}</a> <a id="6975" class="Symbol">{</a><a id="6976" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="6978" class="Symbol">:</a> <a id="6980" href="Relations.Continuous.html#6964" class="Bound">I</a> <a id="6982" class="Symbol">→</a> <a id="6984" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6986" href="Universes.html#403" class="Function Operator">̇</a><a id="6987" class="Symbol">}</a> <a id="6989" class="Keyword">where</a>

 <a id="6997" href="Relations.Continuous.html#6997" class="Function">lift-dep-rel</a> <a id="7010" class="Symbol">:</a> <a id="7012" href="Relations.Continuous.html#6366" class="Function">DepRel</a> <a id="7019" href="Relations.Continuous.html#6964" class="Bound">I</a> <a id="7021" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="7023" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7025" class="Symbol">→</a> <a id="7027" class="Symbol">(∀</a> <a id="7030" href="Relations.Continuous.html#7030" class="Bound">i</a> <a id="7032" class="Symbol">→</a> <a id="7034" href="Relations.Continuous.html#6966" class="Bound">J</a> <a id="7036" class="Symbol">→</a> <a id="7038" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="7040" href="Relations.Continuous.html#7030" class="Bound">i</a><a id="7041" class="Symbol">)</a> <a id="7043" class="Symbol">→</a> <a id="7045" href="Relations.Continuous.html#6970" class="Bound">𝓥</a> <a id="7047" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7049" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7051" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7054" href="Relations.Continuous.html#6997" class="Function">lift-dep-rel</a> <a id="7067" href="Relations.Continuous.html#7067" class="Bound">R</a> <a id="7069" href="Relations.Continuous.html#7069" class="Bound">𝕒</a> <a id="7071" class="Symbol">=</a> <a id="7073" class="Symbol">∀</a> <a id="7075" class="Symbol">(</a><a id="7076" href="Relations.Continuous.html#7076" class="Bound">j</a> <a id="7078" class="Symbol">:</a> <a id="7080" href="Relations.Continuous.html#6966" class="Bound">J</a><a id="7081" class="Symbol">)</a> <a id="7083" class="Symbol">→</a> <a id="7085" href="Relations.Continuous.html#7067" class="Bound">R</a> <a id="7087" class="Symbol">(λ</a> <a id="7090" href="Relations.Continuous.html#7090" class="Bound">i</a> <a id="7092" class="Symbol">→</a> <a id="7094" class="Symbol">(</a><a id="7095" href="Relations.Continuous.html#7069" class="Bound">𝕒</a> <a id="7097" href="Relations.Continuous.html#7090" class="Bound">i</a><a id="7098" class="Symbol">)</a> <a id="7100" href="Relations.Continuous.html#7076" class="Bound">j</a><a id="7101" class="Symbol">)</a>

 <a id="7105" href="Relations.Continuous.html#7105" class="Function">dep-compatible-fun</a> <a id="7124" class="Symbol">:</a> <a id="7126" class="Symbol">(∀</a> <a id="7129" href="Relations.Continuous.html#7129" class="Bound">i</a> <a id="7131" class="Symbol">→</a> <a id="7133" class="Symbol">(</a><a id="7134" href="Relations.Continuous.html#6966" class="Bound">J</a> <a id="7136" class="Symbol">→</a> <a id="7138" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="7140" href="Relations.Continuous.html#7129" class="Bound">i</a><a id="7141" class="Symbol">)</a> <a id="7143" class="Symbol">→</a> <a id="7145" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="7147" href="Relations.Continuous.html#7129" class="Bound">i</a><a id="7148" class="Symbol">)</a> <a id="7150" class="Symbol">→</a> <a id="7152" href="Relations.Continuous.html#6366" class="Function">DepRel</a> <a id="7159" href="Relations.Continuous.html#6964" class="Bound">I</a> <a id="7161" href="Relations.Continuous.html#6976" class="Bound">𝒜</a> <a id="7163" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7165" class="Symbol">→</a> <a id="7167" href="Relations.Continuous.html#6970" class="Bound">𝓥</a> <a id="7169" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7171" href="Relations.Continuous.html#6984" class="Bound">𝓤</a> <a id="7173" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7175" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7177" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7180" href="Relations.Continuous.html#7105" class="Function">dep-compatible-fun</a> <a id="7199" href="Relations.Continuous.html#7199" class="Bound">𝕗</a> <a id="7201" href="Relations.Continuous.html#7201" class="Bound">R</a>  <a id="7204" class="Symbol">=</a> <a id="7206" class="Symbol">∀</a> <a id="7208" href="Relations.Continuous.html#7208" class="Bound">𝕒</a> <a id="7210" class="Symbol">→</a> <a id="7212" class="Symbol">(</a><a id="7213" href="Relations.Continuous.html#6997" class="Function">lift-dep-rel</a> <a id="7226" href="Relations.Continuous.html#7201" class="Bound">R</a><a id="7227" class="Symbol">)</a> <a id="7229" href="Relations.Continuous.html#7208" class="Bound">𝕒</a> <a id="7231" class="Symbol">→</a> <a id="7233" href="Relations.Continuous.html#7201" class="Bound">R</a> <a id="7235" class="Symbol">λ</a> <a id="7237" href="Relations.Continuous.html#7237" class="Bound">i</a> <a id="7239" class="Symbol">→</a> <a id="7241" class="Symbol">(</a><a id="7242" href="Relations.Continuous.html#7199" class="Bound">𝕗</a> <a id="7244" href="Relations.Continuous.html#7237" class="Bound">i</a><a id="7245" class="Symbol">)(</a><a id="7247" href="Relations.Continuous.html#7208" class="Bound">𝕒</a> <a id="7249" href="Relations.Continuous.html#7237" class="Bound">i</a><a id="7250" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → 𝒜 i` of `𝕒`.)


--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
