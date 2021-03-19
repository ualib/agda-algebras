---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This section presents the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ConRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ConRel` the type of **continuous relations**.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, ternary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type---said another way, they are *single-sorted* relations---but we will remove this limitation as well when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ConRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A j` to `A k` to … *ad infinitum*, where the collection represented by the ``indexing'' type \ab I might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We will refer to such relations as **dependent continuous relations** (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

<pre class="Agda">

<a id="2508" class="Symbol">{-#</a> <a id="2512" class="Keyword">OPTIONS</a> <a id="2520" class="Pragma">--without-K</a> <a id="2532" class="Pragma">--exact-split</a> <a id="2546" class="Pragma">--safe</a> <a id="2553" class="Symbol">#-}</a>

<a id="2558" class="Keyword">module</a> <a id="2565" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="2586" class="Keyword">where</a>

<a id="2593" class="Keyword">open</a> <a id="2598" class="Keyword">import</a> <a id="2605" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="2624" class="Keyword">public</a>

</pre>

#### <a id="continuous-relations">Continuous relations</a>

In this subsection we define the type `ConRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **continuous relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ConRel"></a><a id="3240" href="Relations.Continuous.html#3240" class="Function">ConRel</a> <a id="3247" class="Symbol">:</a> <a id="3249" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3251" href="Universes.html#403" class="Function Operator">̇</a> <a id="3253" class="Symbol">→</a> <a id="3255" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3257" href="Universes.html#403" class="Function Operator">̇</a> <a id="3259" class="Symbol">→</a> <a id="3261" class="Symbol">(</a><a id="3262" href="Relations.Continuous.html#3262" class="Bound">𝓦</a> <a id="3264" class="Symbol">:</a> <a id="3266" href="Universes.html#205" class="Postulate">Universe</a><a id="3274" class="Symbol">)</a> <a id="3276" class="Symbol">→</a> <a id="3278" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3280" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3282" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3284" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3286" href="Relations.Continuous.html#3262" class="Bound">𝓦</a> <a id="3288" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3290" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3292" href="Relations.Continuous.html#3240" class="Function">ConRel</a> <a id="3299" href="Relations.Continuous.html#3299" class="Bound">I</a> <a id="3301" href="Relations.Continuous.html#3301" class="Bound">A</a> <a id="3303" href="Relations.Continuous.html#3303" class="Bound">𝓦</a> <a id="3305" class="Symbol">=</a> <a id="3307" class="Symbol">(</a><a id="3308" href="Relations.Continuous.html#3299" class="Bound">I</a> <a id="3310" class="Symbol">→</a> <a id="3312" href="Relations.Continuous.html#3301" class="Bound">A</a><a id="3313" class="Symbol">)</a> <a id="3315" class="Symbol">→</a> <a id="3317" href="Relations.Continuous.html#3303" class="Bound">𝓦</a> <a id="3319" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3578" class="Keyword">module</a> <a id="3585" href="Relations.Continuous.html#3585" class="Module">_</a> <a id="3587" class="Symbol">{</a><a id="3588" href="Relations.Continuous.html#3588" class="Bound">𝓤</a> <a id="3590" href="Relations.Continuous.html#3590" class="Bound">𝓥</a> <a id="3592" href="Relations.Continuous.html#3592" class="Bound">𝓦</a> <a id="3594" class="Symbol">:</a> <a id="3596" href="Universes.html#205" class="Postulate">Universe</a><a id="3604" class="Symbol">}</a> <a id="3606" class="Symbol">{</a><a id="3607" href="Relations.Continuous.html#3607" class="Bound">I</a> <a id="3609" href="Relations.Continuous.html#3609" class="Bound">J</a> <a id="3611" class="Symbol">:</a> <a id="3613" href="Relations.Continuous.html#3590" class="Bound">𝓥</a> <a id="3615" href="Universes.html#403" class="Function Operator">̇</a><a id="3616" class="Symbol">}</a> <a id="3618" class="Symbol">{</a><a id="3619" href="Relations.Continuous.html#3619" class="Bound">A</a> <a id="3621" class="Symbol">:</a> <a id="3623" href="Relations.Continuous.html#3588" class="Bound">𝓤</a> <a id="3625" href="Universes.html#403" class="Function Operator">̇</a><a id="3626" class="Symbol">}</a> <a id="3628" class="Keyword">where</a>

 <a id="3636" href="Relations.Continuous.html#3636" class="Function">lift-con-rel</a> <a id="3649" class="Symbol">:</a> <a id="3651" href="Relations.Continuous.html#3240" class="Function">ConRel</a> <a id="3658" href="Relations.Continuous.html#3607" class="Bound">I</a> <a id="3660" href="Relations.Continuous.html#3619" class="Bound">A</a> <a id="3662" href="Relations.Continuous.html#3592" class="Bound">𝓦</a> <a id="3664" class="Symbol">→</a> <a id="3666" class="Symbol">(</a><a id="3667" href="Relations.Continuous.html#3607" class="Bound">I</a> <a id="3669" class="Symbol">→</a> <a id="3671" href="Relations.Continuous.html#3609" class="Bound">J</a> <a id="3673" class="Symbol">→</a> <a id="3675" href="Relations.Continuous.html#3619" class="Bound">A</a><a id="3676" class="Symbol">)</a> <a id="3678" class="Symbol">→</a> <a id="3680" href="Relations.Continuous.html#3590" class="Bound">𝓥</a> <a id="3682" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3684" href="Relations.Continuous.html#3592" class="Bound">𝓦</a> <a id="3686" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3689" href="Relations.Continuous.html#3636" class="Function">lift-con-rel</a> <a id="3702" href="Relations.Continuous.html#3702" class="Bound">R</a> <a id="3704" href="Relations.Continuous.html#3704" class="Bound">𝕒</a> <a id="3706" class="Symbol">=</a> <a id="3708" class="Symbol">∀</a> <a id="3710" class="Symbol">(</a><a id="3711" href="Relations.Continuous.html#3711" class="Bound">j</a> <a id="3713" class="Symbol">:</a> <a id="3715" href="Relations.Continuous.html#3609" class="Bound">J</a><a id="3716" class="Symbol">)</a> <a id="3718" class="Symbol">→</a> <a id="3720" href="Relations.Continuous.html#3702" class="Bound">R</a> <a id="3722" class="Symbol">λ</a> <a id="3724" href="Relations.Continuous.html#3724" class="Bound">i</a> <a id="3726" class="Symbol">→</a> <a id="3728" class="Symbol">(</a><a id="3729" href="Relations.Continuous.html#3704" class="Bound">𝕒</a> <a id="3731" href="Relations.Continuous.html#3724" class="Bound">i</a><a id="3732" class="Symbol">)</a> <a id="3734" href="Relations.Continuous.html#3711" class="Bound">j</a>

 <a id="3738" href="Relations.Continuous.html#3738" class="Function">con-compatible-fun</a> <a id="3757" class="Symbol">:</a> <a id="3759" class="Symbol">(</a><a id="3760" href="Relations.Continuous.html#3607" class="Bound">I</a> <a id="3762" class="Symbol">→</a> <a id="3764" class="Symbol">(</a><a id="3765" href="Relations.Continuous.html#3609" class="Bound">J</a> <a id="3767" class="Symbol">→</a> <a id="3769" href="Relations.Continuous.html#3619" class="Bound">A</a><a id="3770" class="Symbol">)</a> <a id="3772" class="Symbol">→</a> <a id="3774" href="Relations.Continuous.html#3619" class="Bound">A</a><a id="3775" class="Symbol">)</a> <a id="3777" class="Symbol">→</a> <a id="3779" href="Relations.Continuous.html#3240" class="Function">ConRel</a> <a id="3786" href="Relations.Continuous.html#3607" class="Bound">I</a> <a id="3788" href="Relations.Continuous.html#3619" class="Bound">A</a> <a id="3790" href="Relations.Continuous.html#3592" class="Bound">𝓦</a> <a id="3792" class="Symbol">→</a> <a id="3794" href="Relations.Continuous.html#3590" class="Bound">𝓥</a> <a id="3796" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3798" href="Relations.Continuous.html#3588" class="Bound">𝓤</a> <a id="3800" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3802" href="Relations.Continuous.html#3592" class="Bound">𝓦</a> <a id="3804" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3807" href="Relations.Continuous.html#3738" class="Function">con-compatible-fun</a> <a id="3826" href="Relations.Continuous.html#3826" class="Bound">𝕗</a> <a id="3828" href="Relations.Continuous.html#3828" class="Bound">R</a>  <a id="3831" class="Symbol">=</a> <a id="3833" class="Symbol">∀</a> <a id="3835" href="Relations.Continuous.html#3835" class="Bound">𝕒</a> <a id="3837" class="Symbol">→</a> <a id="3839" class="Symbol">(</a><a id="3840" href="Relations.Continuous.html#3636" class="Function">lift-con-rel</a> <a id="3853" href="Relations.Continuous.html#3828" class="Bound">R</a><a id="3854" class="Symbol">)</a> <a id="3856" href="Relations.Continuous.html#3835" class="Bound">𝕒</a> <a id="3858" class="Symbol">→</a> <a id="3860" href="Relations.Continuous.html#3828" class="Bound">R</a> <a id="3862" class="Symbol">λ</a> <a id="3864" href="Relations.Continuous.html#3864" class="Bound">i</a> <a id="3866" class="Symbol">→</a> <a id="3868" class="Symbol">(</a><a id="3869" href="Relations.Continuous.html#3826" class="Bound">𝕗</a> <a id="3871" href="Relations.Continuous.html#3864" class="Bound">i</a><a id="3872" class="Symbol">)</a> <a id="3874" class="Symbol">(</a><a id="3875" href="Relations.Continuous.html#3835" class="Bound">𝕒</a> <a id="3877" href="Relations.Continuous.html#3864" class="Bound">i</a><a id="3878" class="Symbol">)</a>

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

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` may not even be enumerable).

<pre class="Agda">

<a id="DepRel"></a><a id="6448" href="Relations.Continuous.html#6448" class="Function">DepRel</a> <a id="6455" class="Symbol">:</a> <a id="6457" class="Symbol">(</a><a id="6458" href="Relations.Continuous.html#6458" class="Bound">I</a> <a id="6460" class="Symbol">:</a> <a id="6462" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6464" href="Universes.html#403" class="Function Operator">̇</a><a id="6465" class="Symbol">)(</a><a id="6467" href="Relations.Continuous.html#6467" class="Bound">A</a> <a id="6469" class="Symbol">:</a> <a id="6471" href="Relations.Continuous.html#6458" class="Bound">I</a> <a id="6473" class="Symbol">→</a> <a id="6475" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6477" href="Universes.html#403" class="Function Operator">̇</a><a id="6478" class="Symbol">)(</a><a id="6480" href="Relations.Continuous.html#6480" class="Bound">𝓦</a> <a id="6482" class="Symbol">:</a> <a id="6484" href="Universes.html#205" class="Postulate">Universe</a><a id="6492" class="Symbol">)</a> <a id="6494" class="Symbol">→</a> <a id="6496" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6498" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6500" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6502" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6504" href="Relations.Continuous.html#6480" class="Bound">𝓦</a> <a id="6506" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="6508" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6510" href="Relations.Continuous.html#6448" class="Function">DepRel</a> <a id="6517" href="Relations.Continuous.html#6517" class="Bound">I</a> <a id="6519" href="Relations.Continuous.html#6519" class="Bound">A</a> <a id="6521" href="Relations.Continuous.html#6521" class="Bound">𝓦</a> <a id="6523" class="Symbol">=</a> <a id="6525" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6527" href="Relations.Continuous.html#6519" class="Bound">A</a> <a id="6529" class="Symbol">→</a> <a id="6531" href="Relations.Continuous.html#6521" class="Bound">𝓦</a> <a id="6533" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="7036" class="Keyword">module</a> <a id="7043" href="Relations.Continuous.html#7043" class="Module">_</a> <a id="7045" class="Symbol">{</a><a id="7046" href="Relations.Continuous.html#7046" class="Bound">𝓤</a> <a id="7048" href="Relations.Continuous.html#7048" class="Bound">𝓥</a> <a id="7050" href="Relations.Continuous.html#7050" class="Bound">𝓦</a> <a id="7052" class="Symbol">:</a> <a id="7054" href="Universes.html#205" class="Postulate">Universe</a><a id="7062" class="Symbol">}</a> <a id="7064" class="Symbol">{</a><a id="7065" href="Relations.Continuous.html#7065" class="Bound">I</a> <a id="7067" href="Relations.Continuous.html#7067" class="Bound">J</a> <a id="7069" class="Symbol">:</a> <a id="7071" href="Relations.Continuous.html#7048" class="Bound">𝓥</a> <a id="7073" href="Universes.html#403" class="Function Operator">̇</a><a id="7074" class="Symbol">}</a> <a id="7076" class="Symbol">{</a><a id="7077" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7079" class="Symbol">:</a> <a id="7081" href="Relations.Continuous.html#7065" class="Bound">I</a> <a id="7083" class="Symbol">→</a> <a id="7085" href="Relations.Continuous.html#7046" class="Bound">𝓤</a> <a id="7087" href="Universes.html#403" class="Function Operator">̇</a><a id="7088" class="Symbol">}</a> <a id="7090" class="Keyword">where</a>

 <a id="7098" href="Relations.Continuous.html#7098" class="Function">lift-dep-rel</a> <a id="7111" class="Symbol">:</a> <a id="7113" href="Relations.Continuous.html#6448" class="Function">DepRel</a> <a id="7120" href="Relations.Continuous.html#7065" class="Bound">I</a> <a id="7122" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7124" href="Relations.Continuous.html#7050" class="Bound">𝓦</a> <a id="7126" class="Symbol">→</a> <a id="7128" class="Symbol">(∀</a> <a id="7131" href="Relations.Continuous.html#7131" class="Bound">i</a> <a id="7133" class="Symbol">→</a> <a id="7135" href="Relations.Continuous.html#7067" class="Bound">J</a> <a id="7137" class="Symbol">→</a> <a id="7139" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7141" href="Relations.Continuous.html#7131" class="Bound">i</a><a id="7142" class="Symbol">)</a> <a id="7144" class="Symbol">→</a> <a id="7146" href="Relations.Continuous.html#7048" class="Bound">𝓥</a> <a id="7148" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7150" href="Relations.Continuous.html#7050" class="Bound">𝓦</a> <a id="7152" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7155" href="Relations.Continuous.html#7098" class="Function">lift-dep-rel</a> <a id="7168" href="Relations.Continuous.html#7168" class="Bound">R</a> <a id="7170" href="Relations.Continuous.html#7170" class="Bound">𝕒</a> <a id="7172" class="Symbol">=</a> <a id="7174" class="Symbol">∀</a> <a id="7176" class="Symbol">(</a><a id="7177" href="Relations.Continuous.html#7177" class="Bound">j</a> <a id="7179" class="Symbol">:</a> <a id="7181" href="Relations.Continuous.html#7067" class="Bound">J</a><a id="7182" class="Symbol">)</a> <a id="7184" class="Symbol">→</a> <a id="7186" href="Relations.Continuous.html#7168" class="Bound">R</a> <a id="7188" class="Symbol">(λ</a> <a id="7191" href="Relations.Continuous.html#7191" class="Bound">i</a> <a id="7193" class="Symbol">→</a> <a id="7195" class="Symbol">(</a><a id="7196" href="Relations.Continuous.html#7170" class="Bound">𝕒</a> <a id="7198" href="Relations.Continuous.html#7191" class="Bound">i</a><a id="7199" class="Symbol">)</a> <a id="7201" href="Relations.Continuous.html#7177" class="Bound">j</a><a id="7202" class="Symbol">)</a>

 <a id="7206" href="Relations.Continuous.html#7206" class="Function">dep-compatible-fun</a> <a id="7225" class="Symbol">:</a> <a id="7227" class="Symbol">(∀</a> <a id="7230" href="Relations.Continuous.html#7230" class="Bound">i</a> <a id="7232" class="Symbol">→</a> <a id="7234" class="Symbol">(</a><a id="7235" href="Relations.Continuous.html#7067" class="Bound">J</a> <a id="7237" class="Symbol">→</a> <a id="7239" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7241" href="Relations.Continuous.html#7230" class="Bound">i</a><a id="7242" class="Symbol">)</a> <a id="7244" class="Symbol">→</a> <a id="7246" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7248" href="Relations.Continuous.html#7230" class="Bound">i</a><a id="7249" class="Symbol">)</a> <a id="7251" class="Symbol">→</a> <a id="7253" href="Relations.Continuous.html#6448" class="Function">DepRel</a> <a id="7260" href="Relations.Continuous.html#7065" class="Bound">I</a> <a id="7262" href="Relations.Continuous.html#7077" class="Bound">A</a> <a id="7264" href="Relations.Continuous.html#7050" class="Bound">𝓦</a> <a id="7266" class="Symbol">→</a> <a id="7268" href="Relations.Continuous.html#7048" class="Bound">𝓥</a> <a id="7270" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7272" href="Relations.Continuous.html#7046" class="Bound">𝓤</a> <a id="7274" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7276" href="Relations.Continuous.html#7050" class="Bound">𝓦</a> <a id="7278" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7281" href="Relations.Continuous.html#7206" class="Function">dep-compatible-fun</a> <a id="7300" href="Relations.Continuous.html#7300" class="Bound">𝕗</a> <a id="7302" href="Relations.Continuous.html#7302" class="Bound">R</a>  <a id="7305" class="Symbol">=</a> <a id="7307" class="Symbol">∀</a> <a id="7309" href="Relations.Continuous.html#7309" class="Bound">𝕒</a> <a id="7311" class="Symbol">→</a> <a id="7313" class="Symbol">(</a><a id="7314" href="Relations.Continuous.html#7098" class="Function">lift-dep-rel</a> <a id="7327" href="Relations.Continuous.html#7302" class="Bound">R</a><a id="7328" class="Symbol">)</a> <a id="7330" href="Relations.Continuous.html#7309" class="Bound">𝕒</a> <a id="7332" class="Symbol">→</a> <a id="7334" href="Relations.Continuous.html#7302" class="Bound">R</a> <a id="7336" class="Symbol">λ</a> <a id="7338" href="Relations.Continuous.html#7338" class="Bound">i</a> <a id="7340" class="Symbol">→</a> <a id="7342" class="Symbol">(</a><a id="7343" href="Relations.Continuous.html#7300" class="Bound">𝕗</a> <a id="7345" href="Relations.Continuous.html#7338" class="Bound">i</a><a id="7346" class="Symbol">)(</a><a id="7348" href="Relations.Continuous.html#7309" class="Bound">𝕒</a> <a id="7350" href="Relations.Continuous.html#7338" class="Bound">i</a><a id="7351" class="Symbol">)</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → J → A i`.


--------------------------------------

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
