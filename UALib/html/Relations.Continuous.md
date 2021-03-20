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

Below we will define `ConRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ConRel` the type of **continuous relations**.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, ternary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type---said another way, they are *single-sorted* relations---but we will remove this limitation as well when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ConRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A j` to `A k` to … *ad infinitum*, where the collection represented by the ``indexing'' type \ab I might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We will refer to such relations as **dependent continuous relations** (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

#### <a id="continuous-relations">Continuous relations</a>

In this subsection we define the type `ConRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **continuous relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ConRel"></a><a id="3265" href="Relations.Continuous.html#3265" class="Function">ConRel</a> <a id="3272" class="Symbol">:</a> <a id="3274" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3276" href="Universes.html#403" class="Function Operator">̇</a> <a id="3278" class="Symbol">→</a> <a id="3280" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3282" href="Universes.html#403" class="Function Operator">̇</a> <a id="3284" class="Symbol">→</a> <a id="3286" class="Symbol">(</a><a id="3287" href="Relations.Continuous.html#3287" class="Bound">𝓦</a> <a id="3289" class="Symbol">:</a> <a id="3291" href="Universes.html#205" class="Postulate">Universe</a><a id="3299" class="Symbol">)</a> <a id="3301" class="Symbol">→</a> <a id="3303" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3305" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3307" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3309" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3311" href="Relations.Continuous.html#3287" class="Bound">𝓦</a> <a id="3313" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3315" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3317" href="Relations.Continuous.html#3265" class="Function">ConRel</a> <a id="3324" href="Relations.Continuous.html#3324" class="Bound">I</a> <a id="3326" href="Relations.Continuous.html#3326" class="Bound">A</a> <a id="3328" href="Relations.Continuous.html#3328" class="Bound">𝓦</a> <a id="3330" class="Symbol">=</a> <a id="3332" class="Symbol">(</a><a id="3333" href="Relations.Continuous.html#3324" class="Bound">I</a> <a id="3335" class="Symbol">→</a> <a id="3337" href="Relations.Continuous.html#3326" class="Bound">A</a><a id="3338" class="Symbol">)</a> <a id="3340" class="Symbol">→</a> <a id="3342" href="Relations.Continuous.html#3328" class="Bound">𝓦</a> <a id="3344" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3603" class="Keyword">module</a> <a id="3610" href="Relations.Continuous.html#3610" class="Module">_</a> <a id="3612" class="Symbol">{</a><a id="3613" href="Relations.Continuous.html#3613" class="Bound">𝓤</a> <a id="3615" href="Relations.Continuous.html#3615" class="Bound">𝓥</a> <a id="3617" href="Relations.Continuous.html#3617" class="Bound">𝓦</a> <a id="3619" class="Symbol">:</a> <a id="3621" href="Universes.html#205" class="Postulate">Universe</a><a id="3629" class="Symbol">}</a> <a id="3631" class="Symbol">{</a><a id="3632" href="Relations.Continuous.html#3632" class="Bound">I</a> <a id="3634" href="Relations.Continuous.html#3634" class="Bound">J</a> <a id="3636" class="Symbol">:</a> <a id="3638" href="Relations.Continuous.html#3615" class="Bound">𝓥</a> <a id="3640" href="Universes.html#403" class="Function Operator">̇</a><a id="3641" class="Symbol">}</a> <a id="3643" class="Symbol">{</a><a id="3644" href="Relations.Continuous.html#3644" class="Bound">A</a> <a id="3646" class="Symbol">:</a> <a id="3648" href="Relations.Continuous.html#3613" class="Bound">𝓤</a> <a id="3650" href="Universes.html#403" class="Function Operator">̇</a><a id="3651" class="Symbol">}</a> <a id="3653" class="Keyword">where</a>

 <a id="3661" href="Relations.Continuous.html#3661" class="Function">lift-con-rel</a> <a id="3674" class="Symbol">:</a> <a id="3676" href="Relations.Continuous.html#3265" class="Function">ConRel</a> <a id="3683" href="Relations.Continuous.html#3632" class="Bound">I</a> <a id="3685" href="Relations.Continuous.html#3644" class="Bound">A</a> <a id="3687" href="Relations.Continuous.html#3617" class="Bound">𝓦</a> <a id="3689" class="Symbol">→</a> <a id="3691" class="Symbol">(</a><a id="3692" href="Relations.Continuous.html#3632" class="Bound">I</a> <a id="3694" class="Symbol">→</a> <a id="3696" href="Relations.Continuous.html#3634" class="Bound">J</a> <a id="3698" class="Symbol">→</a> <a id="3700" href="Relations.Continuous.html#3644" class="Bound">A</a><a id="3701" class="Symbol">)</a> <a id="3703" class="Symbol">→</a> <a id="3705" href="Relations.Continuous.html#3615" class="Bound">𝓥</a> <a id="3707" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3709" href="Relations.Continuous.html#3617" class="Bound">𝓦</a> <a id="3711" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3714" href="Relations.Continuous.html#3661" class="Function">lift-con-rel</a> <a id="3727" href="Relations.Continuous.html#3727" class="Bound">R</a> <a id="3729" href="Relations.Continuous.html#3729" class="Bound">𝕒</a> <a id="3731" class="Symbol">=</a> <a id="3733" class="Symbol">∀</a> <a id="3735" class="Symbol">(</a><a id="3736" href="Relations.Continuous.html#3736" class="Bound">j</a> <a id="3738" class="Symbol">:</a> <a id="3740" href="Relations.Continuous.html#3634" class="Bound">J</a><a id="3741" class="Symbol">)</a> <a id="3743" class="Symbol">→</a> <a id="3745" href="Relations.Continuous.html#3727" class="Bound">R</a> <a id="3747" class="Symbol">λ</a> <a id="3749" href="Relations.Continuous.html#3749" class="Bound">i</a> <a id="3751" class="Symbol">→</a> <a id="3753" class="Symbol">(</a><a id="3754" href="Relations.Continuous.html#3729" class="Bound">𝕒</a> <a id="3756" href="Relations.Continuous.html#3749" class="Bound">i</a><a id="3757" class="Symbol">)</a> <a id="3759" href="Relations.Continuous.html#3736" class="Bound">j</a>

 <a id="3763" href="Relations.Continuous.html#3763" class="Function">con-compatible-fun</a> <a id="3782" class="Symbol">:</a> <a id="3784" class="Symbol">(</a><a id="3785" href="Relations.Continuous.html#3632" class="Bound">I</a> <a id="3787" class="Symbol">→</a> <a id="3789" class="Symbol">(</a><a id="3790" href="Relations.Continuous.html#3634" class="Bound">J</a> <a id="3792" class="Symbol">→</a> <a id="3794" href="Relations.Continuous.html#3644" class="Bound">A</a><a id="3795" class="Symbol">)</a> <a id="3797" class="Symbol">→</a> <a id="3799" href="Relations.Continuous.html#3644" class="Bound">A</a><a id="3800" class="Symbol">)</a> <a id="3802" class="Symbol">→</a> <a id="3804" href="Relations.Continuous.html#3265" class="Function">ConRel</a> <a id="3811" href="Relations.Continuous.html#3632" class="Bound">I</a> <a id="3813" href="Relations.Continuous.html#3644" class="Bound">A</a> <a id="3815" href="Relations.Continuous.html#3617" class="Bound">𝓦</a> <a id="3817" class="Symbol">→</a> <a id="3819" href="Relations.Continuous.html#3615" class="Bound">𝓥</a> <a id="3821" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3823" href="Relations.Continuous.html#3613" class="Bound">𝓤</a> <a id="3825" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3827" href="Relations.Continuous.html#3617" class="Bound">𝓦</a> <a id="3829" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3832" href="Relations.Continuous.html#3763" class="Function">con-compatible-fun</a> <a id="3851" href="Relations.Continuous.html#3851" class="Bound">𝕗</a> <a id="3853" href="Relations.Continuous.html#3853" class="Bound">R</a>  <a id="3856" class="Symbol">=</a> <a id="3858" class="Symbol">∀</a> <a id="3860" href="Relations.Continuous.html#3860" class="Bound">𝕒</a> <a id="3862" class="Symbol">→</a> <a id="3864" class="Symbol">(</a><a id="3865" href="Relations.Continuous.html#3661" class="Function">lift-con-rel</a> <a id="3878" href="Relations.Continuous.html#3853" class="Bound">R</a><a id="3879" class="Symbol">)</a> <a id="3881" href="Relations.Continuous.html#3860" class="Bound">𝕒</a> <a id="3883" class="Symbol">→</a> <a id="3885" href="Relations.Continuous.html#3853" class="Bound">R</a> <a id="3887" class="Symbol">λ</a> <a id="3889" href="Relations.Continuous.html#3889" class="Bound">i</a> <a id="3891" class="Symbol">→</a> <a id="3893" class="Symbol">(</a><a id="3894" href="Relations.Continuous.html#3851" class="Bound">𝕗</a> <a id="3896" href="Relations.Continuous.html#3889" class="Bound">i</a><a id="3897" class="Symbol">)</a> <a id="3899" class="Symbol">(</a><a id="3900" href="Relations.Continuous.html#3860" class="Bound">𝕒</a> <a id="3902" href="Relations.Continuous.html#3889" class="Bound">i</a><a id="3903" class="Symbol">)</a>

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

<a id="DepRel"></a><a id="6473" href="Relations.Continuous.html#6473" class="Function">DepRel</a> <a id="6480" class="Symbol">:</a> <a id="6482" class="Symbol">(</a><a id="6483" href="Relations.Continuous.html#6483" class="Bound">I</a> <a id="6485" class="Symbol">:</a> <a id="6487" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6489" href="Universes.html#403" class="Function Operator">̇</a><a id="6490" class="Symbol">)(</a><a id="6492" href="Relations.Continuous.html#6492" class="Bound">A</a> <a id="6494" class="Symbol">:</a> <a id="6496" href="Relations.Continuous.html#6483" class="Bound">I</a> <a id="6498" class="Symbol">→</a> <a id="6500" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6502" href="Universes.html#403" class="Function Operator">̇</a><a id="6503" class="Symbol">)(</a><a id="6505" href="Relations.Continuous.html#6505" class="Bound">𝓦</a> <a id="6507" class="Symbol">:</a> <a id="6509" href="Universes.html#205" class="Postulate">Universe</a><a id="6517" class="Symbol">)</a> <a id="6519" class="Symbol">→</a> <a id="6521" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6523" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6525" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6527" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6529" href="Relations.Continuous.html#6505" class="Bound">𝓦</a> <a id="6531" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="6533" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6535" href="Relations.Continuous.html#6473" class="Function">DepRel</a> <a id="6542" href="Relations.Continuous.html#6542" class="Bound">I</a> <a id="6544" href="Relations.Continuous.html#6544" class="Bound">A</a> <a id="6546" href="Relations.Continuous.html#6546" class="Bound">𝓦</a> <a id="6548" class="Symbol">=</a> <a id="6550" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6552" href="Relations.Continuous.html#6544" class="Bound">A</a> <a id="6554" class="Symbol">→</a> <a id="6556" href="Relations.Continuous.html#6546" class="Bound">𝓦</a> <a id="6558" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="7061" class="Keyword">module</a> <a id="7068" href="Relations.Continuous.html#7068" class="Module">_</a> <a id="7070" class="Symbol">{</a><a id="7071" href="Relations.Continuous.html#7071" class="Bound">𝓤</a> <a id="7073" href="Relations.Continuous.html#7073" class="Bound">𝓥</a> <a id="7075" href="Relations.Continuous.html#7075" class="Bound">𝓦</a> <a id="7077" class="Symbol">:</a> <a id="7079" href="Universes.html#205" class="Postulate">Universe</a><a id="7087" class="Symbol">}</a> <a id="7089" class="Symbol">{</a><a id="7090" href="Relations.Continuous.html#7090" class="Bound">I</a> <a id="7092" href="Relations.Continuous.html#7092" class="Bound">J</a> <a id="7094" class="Symbol">:</a> <a id="7096" href="Relations.Continuous.html#7073" class="Bound">𝓥</a> <a id="7098" href="Universes.html#403" class="Function Operator">̇</a><a id="7099" class="Symbol">}</a> <a id="7101" class="Symbol">{</a><a id="7102" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7104" class="Symbol">:</a> <a id="7106" href="Relations.Continuous.html#7090" class="Bound">I</a> <a id="7108" class="Symbol">→</a> <a id="7110" href="Relations.Continuous.html#7071" class="Bound">𝓤</a> <a id="7112" href="Universes.html#403" class="Function Operator">̇</a><a id="7113" class="Symbol">}</a> <a id="7115" class="Keyword">where</a>

 <a id="7123" href="Relations.Continuous.html#7123" class="Function">lift-dep-rel</a> <a id="7136" class="Symbol">:</a> <a id="7138" href="Relations.Continuous.html#6473" class="Function">DepRel</a> <a id="7145" href="Relations.Continuous.html#7090" class="Bound">I</a> <a id="7147" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7149" href="Relations.Continuous.html#7075" class="Bound">𝓦</a> <a id="7151" class="Symbol">→</a> <a id="7153" class="Symbol">(∀</a> <a id="7156" href="Relations.Continuous.html#7156" class="Bound">i</a> <a id="7158" class="Symbol">→</a> <a id="7160" href="Relations.Continuous.html#7092" class="Bound">J</a> <a id="7162" class="Symbol">→</a> <a id="7164" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7166" href="Relations.Continuous.html#7156" class="Bound">i</a><a id="7167" class="Symbol">)</a> <a id="7169" class="Symbol">→</a> <a id="7171" href="Relations.Continuous.html#7073" class="Bound">𝓥</a> <a id="7173" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7175" href="Relations.Continuous.html#7075" class="Bound">𝓦</a> <a id="7177" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7180" href="Relations.Continuous.html#7123" class="Function">lift-dep-rel</a> <a id="7193" href="Relations.Continuous.html#7193" class="Bound">R</a> <a id="7195" href="Relations.Continuous.html#7195" class="Bound">𝕒</a> <a id="7197" class="Symbol">=</a> <a id="7199" class="Symbol">∀</a> <a id="7201" class="Symbol">(</a><a id="7202" href="Relations.Continuous.html#7202" class="Bound">j</a> <a id="7204" class="Symbol">:</a> <a id="7206" href="Relations.Continuous.html#7092" class="Bound">J</a><a id="7207" class="Symbol">)</a> <a id="7209" class="Symbol">→</a> <a id="7211" href="Relations.Continuous.html#7193" class="Bound">R</a> <a id="7213" class="Symbol">(λ</a> <a id="7216" href="Relations.Continuous.html#7216" class="Bound">i</a> <a id="7218" class="Symbol">→</a> <a id="7220" class="Symbol">(</a><a id="7221" href="Relations.Continuous.html#7195" class="Bound">𝕒</a> <a id="7223" href="Relations.Continuous.html#7216" class="Bound">i</a><a id="7224" class="Symbol">)</a> <a id="7226" href="Relations.Continuous.html#7202" class="Bound">j</a><a id="7227" class="Symbol">)</a>

 <a id="7231" href="Relations.Continuous.html#7231" class="Function">dep-compatible-fun</a> <a id="7250" class="Symbol">:</a> <a id="7252" class="Symbol">(∀</a> <a id="7255" href="Relations.Continuous.html#7255" class="Bound">i</a> <a id="7257" class="Symbol">→</a> <a id="7259" class="Symbol">(</a><a id="7260" href="Relations.Continuous.html#7092" class="Bound">J</a> <a id="7262" class="Symbol">→</a> <a id="7264" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7266" href="Relations.Continuous.html#7255" class="Bound">i</a><a id="7267" class="Symbol">)</a> <a id="7269" class="Symbol">→</a> <a id="7271" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7273" href="Relations.Continuous.html#7255" class="Bound">i</a><a id="7274" class="Symbol">)</a> <a id="7276" class="Symbol">→</a> <a id="7278" href="Relations.Continuous.html#6473" class="Function">DepRel</a> <a id="7285" href="Relations.Continuous.html#7090" class="Bound">I</a> <a id="7287" href="Relations.Continuous.html#7102" class="Bound">A</a> <a id="7289" href="Relations.Continuous.html#7075" class="Bound">𝓦</a> <a id="7291" class="Symbol">→</a> <a id="7293" href="Relations.Continuous.html#7073" class="Bound">𝓥</a> <a id="7295" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7297" href="Relations.Continuous.html#7071" class="Bound">𝓤</a> <a id="7299" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7301" href="Relations.Continuous.html#7075" class="Bound">𝓦</a> <a id="7303" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7306" href="Relations.Continuous.html#7231" class="Function">dep-compatible-fun</a> <a id="7325" href="Relations.Continuous.html#7325" class="Bound">𝕗</a> <a id="7327" href="Relations.Continuous.html#7327" class="Bound">R</a>  <a id="7330" class="Symbol">=</a> <a id="7332" class="Symbol">∀</a> <a id="7334" href="Relations.Continuous.html#7334" class="Bound">𝕒</a> <a id="7336" class="Symbol">→</a> <a id="7338" class="Symbol">(</a><a id="7339" href="Relations.Continuous.html#7123" class="Function">lift-dep-rel</a> <a id="7352" href="Relations.Continuous.html#7327" class="Bound">R</a><a id="7353" class="Symbol">)</a> <a id="7355" href="Relations.Continuous.html#7334" class="Bound">𝕒</a> <a id="7357" class="Symbol">→</a> <a id="7359" href="Relations.Continuous.html#7327" class="Bound">R</a> <a id="7361" class="Symbol">λ</a> <a id="7363" href="Relations.Continuous.html#7363" class="Bound">i</a> <a id="7365" class="Symbol">→</a> <a id="7367" class="Symbol">(</a><a id="7368" href="Relations.Continuous.html#7325" class="Bound">𝕗</a> <a id="7370" href="Relations.Continuous.html#7363" class="Bound">i</a><a id="7371" class="Symbol">)(</a><a id="7373" href="Relations.Continuous.html#7334" class="Bound">𝕒</a> <a id="7375" href="Relations.Continuous.html#7363" class="Bound">i</a><a id="7376" class="Symbol">)</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → J → A i`.


--------------------------------------

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
