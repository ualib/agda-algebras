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

Below we will define `ContRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ContRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ContRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.



#### <a id="continuous-and-dependent-relations">Continuous and dependent relations</a>

Here we define the types `ContRel` and `DepRel`. The first of these represents predicates of arbitrary arity over a single type `A`; we call these *continuous relations*.<sup>[1](Relations.Continuous.html#fn1)</sup>
To define `DepRel`, the type of *dependent relations*, we exploit the full power of dependent types and provide a completely general relation type.

<pre class="Agda">

<a id="ContRel"></a><a id="3130" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="3138" class="Symbol">:</a> <a id="3140" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3142" href="Universes.html#403" class="Function Operator">̇</a> <a id="3144" class="Symbol">→</a> <a id="3146" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3148" href="Universes.html#403" class="Function Operator">̇</a> <a id="3150" class="Symbol">→</a> <a id="3152" class="Symbol">(</a><a id="3153" href="Relations.Continuous.html#3153" class="Bound">𝓦</a> <a id="3155" class="Symbol">:</a> <a id="3157" href="Universes.html#205" class="Postulate">Universe</a><a id="3165" class="Symbol">)</a> <a id="3167" class="Symbol">→</a> <a id="3169" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3171" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3173" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3175" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3177" href="Relations.Continuous.html#3153" class="Bound">𝓦</a> <a id="3179" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3181" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3183" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="3191" href="Relations.Continuous.html#3191" class="Bound">I</a> <a id="3193" href="Relations.Continuous.html#3193" class="Bound">A</a> <a id="3195" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3197" class="Symbol">=</a> <a id="3199" class="Symbol">(</a><a id="3200" href="Relations.Continuous.html#3191" class="Bound">I</a> <a id="3202" class="Symbol">→</a> <a id="3204" href="Relations.Continuous.html#3193" class="Bound">A</a><a id="3205" class="Symbol">)</a> <a id="3207" class="Symbol">→</a> <a id="3209" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3211" href="Universes.html#403" class="Function Operator">̇</a>

<a id="DepRel"></a><a id="3214" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="3221" class="Symbol">:</a> <a id="3223" class="Symbol">(</a><a id="3224" href="Relations.Continuous.html#3224" class="Bound">I</a> <a id="3226" class="Symbol">:</a> <a id="3228" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3230" href="Universes.html#403" class="Function Operator">̇</a><a id="3231" class="Symbol">)</a> <a id="3233" class="Symbol">→</a> <a id="3235" class="Symbol">(</a><a id="3236" href="Relations.Continuous.html#3224" class="Bound">I</a> <a id="3238" class="Symbol">→</a> <a id="3240" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3242" href="Universes.html#403" class="Function Operator">̇</a><a id="3243" class="Symbol">)</a> <a id="3245" class="Symbol">→</a> <a id="3247" class="Symbol">(</a><a id="3248" href="Relations.Continuous.html#3248" class="Bound">𝓦</a> <a id="3250" class="Symbol">:</a> <a id="3252" href="Universes.html#205" class="Postulate">Universe</a><a id="3260" class="Symbol">)</a> <a id="3262" class="Symbol">→</a> <a id="3264" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3266" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3268" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3270" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3272" href="Relations.Continuous.html#3248" class="Bound">𝓦</a> <a id="3274" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3276" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3278" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="3285" href="Relations.Continuous.html#3285" class="Bound">I</a> <a id="3287" href="Relations.Continuous.html#3287" class="Bound">𝒜</a> <a id="3289" href="Relations.Continuous.html#3289" class="Bound">𝓦</a> <a id="3291" class="Symbol">=</a> <a id="3293" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3295" href="Relations.Continuous.html#3287" class="Bound">𝒜</a> <a id="3297" class="Symbol">→</a> <a id="3299" href="Relations.Continuous.html#3289" class="Bound">𝓦</a> <a id="3301" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

Here, the tuples of a relation of type `DepRel I 𝒜 𝓦` will inhabit the dependent function type `𝒜 : I → 𝓤 ̇` (where the codomain may depend on the input coordinate `i : I` of the domain). Heuristically, we can think of an inhabitant of type `DepRel I 𝒜 𝓦` as a relation from `𝒜 i` to `𝒜 j` to `𝒜 k` to …. (This is only a rough heuristic since `I` could denote an uncountable collection.<sup>[2](Relations.Continuous.html#fn2)</sup>)





#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

It will be helpful to have some functions that make it easy to assert that a given operation is compatible with a given relation.  The following functions serve this purpose.

<pre class="Agda">

<a id="4036" class="Keyword">module</a> <a id="4043" href="Relations.Continuous.html#4043" class="Module">_</a> <a id="4045" class="Symbol">{</a><a id="4046" href="Relations.Continuous.html#4046" class="Bound">I</a> <a id="4048" href="Relations.Continuous.html#4048" class="Bound">J</a> <a id="4050" class="Symbol">:</a> <a id="4052" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4054" href="Universes.html#403" class="Function Operator">̇</a><a id="4055" class="Symbol">}</a> <a id="4057" class="Symbol">{</a><a id="4058" href="Relations.Continuous.html#4058" class="Bound">A</a> <a id="4060" class="Symbol">:</a> <a id="4062" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4064" href="Universes.html#403" class="Function Operator">̇</a><a id="4065" class="Symbol">}</a> <a id="4067" class="Keyword">where</a>

 <a id="4075" href="Relations.Continuous.html#4075" class="Function">eval-cont-rel</a> <a id="4089" class="Symbol">:</a> <a id="4091" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="4099" href="Relations.Continuous.html#4046" class="Bound">I</a> <a id="4101" href="Relations.Continuous.html#4058" class="Bound">A</a> <a id="4103" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4105" class="Symbol">→</a> <a id="4107" class="Symbol">(</a><a id="4108" href="Relations.Continuous.html#4046" class="Bound">I</a> <a id="4110" class="Symbol">→</a> <a id="4112" href="Relations.Continuous.html#4048" class="Bound">J</a> <a id="4114" class="Symbol">→</a> <a id="4116" href="Relations.Continuous.html#4058" class="Bound">A</a><a id="4117" class="Symbol">)</a> <a id="4119" class="Symbol">→</a> <a id="4121" href="Relations.Continuous.html#4052" class="Bound">𝓥</a> <a id="4123" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4125" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4127" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4130" href="Relations.Continuous.html#4075" class="Function">eval-cont-rel</a> <a id="4144" href="Relations.Continuous.html#4144" class="Bound">R</a> <a id="4146" href="Relations.Continuous.html#4146" class="Bound">𝒶</a> <a id="4148" class="Symbol">=</a> <a id="4150" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4152" href="Relations.Continuous.html#4152" class="Bound">j</a> <a id="4154" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4156" href="Relations.Continuous.html#4048" class="Bound">J</a> <a id="4158" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4160" href="Relations.Continuous.html#4144" class="Bound">R</a> <a id="4162" class="Symbol">λ</a> <a id="4164" href="Relations.Continuous.html#4164" class="Bound">i</a> <a id="4166" class="Symbol">→</a> <a id="4168" href="Relations.Continuous.html#4146" class="Bound">𝒶</a> <a id="4170" href="Relations.Continuous.html#4164" class="Bound">i</a> <a id="4172" href="Relations.Continuous.html#4152" class="Bound">j</a>

 <a id="4176" href="Relations.Continuous.html#4176" class="Function">cont-compatible-op</a> <a id="4195" class="Symbol">:</a> <a id="4197" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="4200" href="Relations.Continuous.html#4048" class="Bound">J</a> <a id="4202" href="Relations.Continuous.html#4058" class="Bound">A</a> <a id="4204" class="Symbol">→</a> <a id="4206" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="4214" href="Relations.Continuous.html#4046" class="Bound">I</a> <a id="4216" href="Relations.Continuous.html#4058" class="Bound">A</a> <a id="4218" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4220" class="Symbol">→</a> <a id="4222" href="Relations.Continuous.html#4052" class="Bound">𝓥</a> <a id="4224" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4226" href="Relations.Continuous.html#4062" class="Bound">𝓤</a> <a id="4228" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4230" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4232" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4235" href="Relations.Continuous.html#4176" class="Function">cont-compatible-op</a> <a id="4254" href="Relations.Continuous.html#4254" class="Bound">𝑓</a> <a id="4256" href="Relations.Continuous.html#4256" class="Bound">R</a>  <a id="4259" class="Symbol">=</a> <a id="4261" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4263" href="Relations.Continuous.html#4263" class="Bound">𝒶</a> <a id="4265" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4267" class="Symbol">(</a><a id="4268" href="Relations.Continuous.html#4046" class="Bound">I</a> <a id="4270" class="Symbol">→</a> <a id="4272" href="Relations.Continuous.html#4048" class="Bound">J</a> <a id="4274" class="Symbol">→</a> <a id="4276" href="Relations.Continuous.html#4058" class="Bound">A</a><a id="4277" class="Symbol">)</a> <a id="4279" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4281" class="Symbol">(</a><a id="4282" href="Relations.Continuous.html#4075" class="Function">eval-cont-rel</a> <a id="4296" href="Relations.Continuous.html#4256" class="Bound">R</a> <a id="4298" href="Relations.Continuous.html#4263" class="Bound">𝒶</a> <a id="4300" class="Symbol">→</a> <a id="4302" href="Relations.Continuous.html#4256" class="Bound">R</a> <a id="4304" class="Symbol">λ</a> <a id="4306" href="Relations.Continuous.html#4306" class="Bound">i</a> <a id="4308" class="Symbol">→</a> <a id="4310" class="Symbol">(</a><a id="4311" href="Relations.Continuous.html#4254" class="Bound">𝑓</a> <a id="4313" class="Symbol">(</a><a id="4314" href="Relations.Continuous.html#4263" class="Bound">𝒶</a> <a id="4316" href="Relations.Continuous.html#4306" class="Bound">i</a><a id="4317" class="Symbol">)))</a>

</pre>

The first of these is an *evaluation* function which "lifts" an `I`-ary relation to an `(I → J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of the `J`-tuples belong to the original relation. The second definition denotes compatibility of an operation with a continuous relation.

Readers who find the syntax of the last two definitions nauseating might be helped by an explication of the semantics of these deifnitions. First, internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Next, recall that a continuous relation `R` denotes a certain collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` "belongs to" or "satisfies" `R`).  For such `R`, the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which `eval-cont-rel R 𝒶` holds.

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns. For example, here are the i-th and k-th columns (for some `i k : I`).

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2
𝑎 i 3      𝒶 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-cont-rel R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row of the `I` columns shown above belongs to the original relation `R`. Finally, `cont-compatible-op` takes a `J`-ary operation `𝑓 : Op J A` and an `I`-tuple `𝒶 : I → J → A` of `J`-tuples, and determines whether the `I`-tuple `λ i → 𝑓 (𝑎 i)` belongs to `R`.


Above we saw lifts of continuous relations and what it means for such relations to be compatible with operations. We conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a dependent relation with an operation.

<pre class="Agda">

<a id="6295" class="Keyword">module</a> <a id="6302" href="Relations.Continuous.html#6302" class="Module">_</a> <a id="6304" class="Symbol">{</a><a id="6305" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6307" href="Relations.Continuous.html#6307" class="Bound">J</a> <a id="6309" class="Symbol">:</a> <a id="6311" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6313" href="Universes.html#403" class="Function Operator">̇</a><a id="6314" class="Symbol">}</a> <a id="6316" class="Symbol">{</a><a id="6317" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6319" class="Symbol">:</a> <a id="6321" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6323" class="Symbol">→</a> <a id="6325" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6327" href="Universes.html#403" class="Function Operator">̇</a><a id="6328" class="Symbol">}</a> <a id="6330" class="Keyword">where</a>

 <a id="6338" href="Relations.Continuous.html#6338" class="Function">eval-dep-rel</a> <a id="6351" class="Symbol">:</a> <a id="6353" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="6360" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6362" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6364" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6366" class="Symbol">→</a> <a id="6368" class="Symbol">(∀</a> <a id="6371" href="Relations.Continuous.html#6371" class="Bound">i</a> <a id="6373" class="Symbol">→</a> <a id="6375" class="Symbol">(</a><a id="6376" href="Relations.Continuous.html#6307" class="Bound">J</a> <a id="6378" class="Symbol">→</a> <a id="6380" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6382" href="Relations.Continuous.html#6371" class="Bound">i</a><a id="6383" class="Symbol">))</a> <a id="6386" class="Symbol">→</a> <a id="6388" href="Relations.Continuous.html#6311" class="Bound">𝓥</a> <a id="6390" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6392" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6394" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6397" href="Relations.Continuous.html#6338" class="Function">eval-dep-rel</a> <a id="6410" href="Relations.Continuous.html#6410" class="Bound">R</a> <a id="6412" href="Relations.Continuous.html#6412" class="Bound">𝒶</a> <a id="6414" class="Symbol">=</a> <a id="6416" class="Symbol">∀</a> <a id="6418" href="Relations.Continuous.html#6418" class="Bound">j</a> <a id="6420" class="Symbol">→</a> <a id="6422" href="Relations.Continuous.html#6410" class="Bound">R</a> <a id="6424" class="Symbol">(λ</a> <a id="6427" href="Relations.Continuous.html#6427" class="Bound">i</a> <a id="6429" class="Symbol">→</a> <a id="6431" class="Symbol">(</a><a id="6432" href="Relations.Continuous.html#6412" class="Bound">𝒶</a> <a id="6434" href="Relations.Continuous.html#6427" class="Bound">i</a><a id="6435" class="Symbol">)</a> <a id="6437" href="Relations.Continuous.html#6418" class="Bound">j</a><a id="6438" class="Symbol">)</a>

 <a id="6442" href="Relations.Continuous.html#6442" class="Function">dep-compatible-op</a> <a id="6460" class="Symbol">:</a> <a id="6462" class="Symbol">(∀</a> <a id="6465" href="Relations.Continuous.html#6465" class="Bound">i</a> <a id="6467" class="Symbol">→</a> <a id="6469" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="6472" href="Relations.Continuous.html#6307" class="Bound">J</a> <a id="6474" class="Symbol">(</a><a id="6475" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6477" href="Relations.Continuous.html#6465" class="Bound">i</a><a id="6478" class="Symbol">))</a> <a id="6481" class="Symbol">→</a> <a id="6483" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="6490" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6492" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6494" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6496" class="Symbol">→</a> <a id="6498" href="Relations.Continuous.html#6311" class="Bound">𝓥</a> <a id="6500" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6502" href="Relations.Continuous.html#6325" class="Bound">𝓤</a> <a id="6504" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6506" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6508" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6511" href="Relations.Continuous.html#6442" class="Function">dep-compatible-op</a> <a id="6529" href="Relations.Continuous.html#6529" class="Bound">𝑓</a> <a id="6531" href="Relations.Continuous.html#6531" class="Bound">R</a>  <a id="6534" class="Symbol">=</a> <a id="6536" class="Symbol">∀</a> <a id="6538" href="Relations.Continuous.html#6538" class="Bound">𝒶</a> <a id="6540" class="Symbol">→</a> <a id="6542" class="Symbol">(</a><a id="6543" href="Relations.Continuous.html#6338" class="Function">eval-dep-rel</a> <a id="6556" href="Relations.Continuous.html#6531" class="Bound">R</a><a id="6557" class="Symbol">)</a> <a id="6559" href="Relations.Continuous.html#6538" class="Bound">𝒶</a> <a id="6561" class="Symbol">→</a> <a id="6563" href="Relations.Continuous.html#6531" class="Bound">R</a> <a id="6565" class="Symbol">λ</a> <a id="6567" href="Relations.Continuous.html#6567" class="Bound">i</a> <a id="6569" class="Symbol">→</a> <a id="6571" class="Symbol">(</a><a id="6572" href="Relations.Continuous.html#6529" class="Bound">𝑓</a> <a id="6574" href="Relations.Continuous.html#6567" class="Bound">i</a><a id="6575" class="Symbol">)(</a><a id="6577" href="Relations.Continuous.html#6538" class="Bound">𝒶</a> <a id="6579" href="Relations.Continuous.html#6567" class="Bound">i</a><a id="6580" class="Symbol">)</a>

 <a id="6584" class="Comment">-- equivalent definition using Π notation</a>
 <a id="6627" href="Relations.Continuous.html#6627" class="Function">dep-compatible&#39;-op</a> <a id="6646" class="Symbol">:</a> <a id="6648" class="Symbol">(</a><a id="6649" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6651" href="Relations.Continuous.html#6651" class="Bound">i</a> <a id="6653" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6655" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6657" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6659" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="6662" href="Relations.Continuous.html#6307" class="Bound">J</a> <a id="6664" class="Symbol">(</a><a id="6665" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6667" href="Relations.Continuous.html#6651" class="Bound">i</a><a id="6668" class="Symbol">))</a> <a id="6671" class="Symbol">→</a> <a id="6673" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="6680" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6682" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6684" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6686" class="Symbol">→</a> <a id="6688" href="Relations.Continuous.html#6311" class="Bound">𝓥</a> <a id="6690" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6692" href="Relations.Continuous.html#6325" class="Bound">𝓤</a> <a id="6694" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6696" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6698" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6701" href="Relations.Continuous.html#6627" class="Function">dep-compatible&#39;-op</a> <a id="6720" href="Relations.Continuous.html#6720" class="Bound">𝑓</a> <a id="6722" href="Relations.Continuous.html#6722" class="Bound">R</a>  <a id="6725" class="Symbol">=</a>  <a id="6728" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6730" href="Relations.Continuous.html#6730" class="Bound">𝒶</a> <a id="6732" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6734" class="Symbol">(</a><a id="6735" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6737" href="Relations.Continuous.html#6737" class="Bound">i</a> <a id="6739" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6741" href="Relations.Continuous.html#6305" class="Bound">I</a> <a id="6743" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6745" class="Symbol">(</a><a id="6746" href="Relations.Continuous.html#6307" class="Bound">J</a> <a id="6748" class="Symbol">→</a> <a id="6750" href="Relations.Continuous.html#6317" class="Bound">𝒜</a> <a id="6752" href="Relations.Continuous.html#6737" class="Bound">i</a><a id="6753" class="Symbol">))</a> <a id="6756" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6758" class="Symbol">((</a><a id="6760" href="Relations.Continuous.html#6338" class="Function">eval-dep-rel</a> <a id="6773" href="Relations.Continuous.html#6722" class="Bound">R</a><a id="6774" class="Symbol">)</a> <a id="6776" href="Relations.Continuous.html#6730" class="Bound">𝒶</a> <a id="6778" class="Symbol">→</a> <a id="6780" href="Relations.Continuous.html#6722" class="Bound">R</a> <a id="6782" class="Symbol">λ</a> <a id="6784" href="Relations.Continuous.html#6784" class="Bound">i</a> <a id="6786" class="Symbol">→</a> <a id="6788" class="Symbol">(</a><a id="6789" href="Relations.Continuous.html#6720" class="Bound">𝑓</a> <a id="6791" href="Relations.Continuous.html#6784" class="Bound">i</a><a id="6792" class="Symbol">)(</a><a id="6794" href="Relations.Continuous.html#6730" class="Bound">𝒶</a> <a id="6796" href="Relations.Continuous.html#6784" class="Bound">i</a><a id="6797" class="Symbol">))</a>

</pre>

<!-- In the definition of `dep-compatible`, we let Agda infer the type of `𝒶`, which is `Π i ꞉ I , (J → 𝒜 i)` in this case. -->


--------------------------------------

<sup>*</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general than those presented elsewhere, but they are used only very rarely in other parts of the [Agda UALib][]. Therefore, the sections marked `*` may be safely skimmed or skipped when first encountering them.</span>

<sup>1</sup><span class="footnote" id="fn1"> For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes: `𝓞` is reserved for types representing *operation symbols*; `𝓥` is reserved for types representing *arities* of relations or operations (see also [Algebras.Signatures][]).</span>

<sup>2</sup><span class="footnote" id="fn2"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>

<br>
<br>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}



<!--

UNNECESSARY.  The ∈ and ⊆  relations defined for Pred are polymorphic and they work just fine
for the general relation types.



Just as we did for unary predicates, we can define inclusion relations for our new general relation types.

_∈C_ : {I : 𝓥 ̇}{A : 𝓤 ̇} → (I → A) → ContRel I A 𝓦 → 𝓦 ̇
x ∈C R = R x

_⊆C_ : {I : 𝓥 ̇}{A : 𝓤 ̇ } → ContRel I A 𝓦 → ContRel I A 𝓩 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓩 ̇
P ⊆C Q = ∀ {x} → x ∈C P → x ∈C Q

_∈D_ : {I : 𝓥 ̇}{𝒜 : I → 𝓤 ̇} → Π 𝒜 → DepRel I 𝒜 𝓦 → 𝓦 ̇
x ∈D R = R x

_⊆D_ : {I : 𝓥 ̇}{𝒜 : I → 𝓤 ̇ } → DepRel I 𝒜 𝓦 → DepRel I 𝒜 𝓩 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓩 ̇
P ⊆D Q = ∀ {x} → x ∈D P → x ∈D Q

infix 4 _⊆C_ _⊆D_

-->
