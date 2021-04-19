---
layout: default
title : Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="general-relations">General Relations*</a>

This is the [Relations.Continuous][] module of the [Agda Universal Algebra Library][].<sup>[*](Relations.Continuous.html#fn0)</sup>

<pre class="Agda">

<a id="333" class="Symbol">{-#</a> <a id="337" class="Keyword">OPTIONS</a> <a id="345" class="Pragma">--without-K</a> <a id="357" class="Pragma">--exact-split</a> <a id="371" class="Pragma">--safe</a> <a id="378" class="Symbol">#-}</a>

<a id="383" class="Keyword">module</a> <a id="390" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="411" class="Keyword">where</a>

<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="449" class="Keyword">public</a>

</pre>

#### <a id="motivation">Motivation</a>
In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ContRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ContRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ContRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.



#### <a id="continuous-and-dependent-relations">Continuous and dependent relations</a>

We now define the type `ContRel` which represents predicates of arbitrary arity over a single type `A`. We call this the type of *continuous relations*.<sup>[1](Relations.Continuous.html#fn1)</sup>)

<pre class="Agda">

<a id="ContRel"></a><a id="2959" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="2967" class="Symbol">:</a> <a id="2969" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2971" href="Universes.html#403" class="Function Operator">̇</a> <a id="2973" class="Symbol">→</a> <a id="2975" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2977" href="Universes.html#403" class="Function Operator">̇</a> <a id="2979" class="Symbol">→</a> <a id="2981" class="Symbol">(</a><a id="2982" href="Relations.Continuous.html#2982" class="Bound">𝓦</a> <a id="2984" class="Symbol">:</a> <a id="2986" href="Universes.html#205" class="Postulate">Universe</a><a id="2994" class="Symbol">)</a> <a id="2996" class="Symbol">→</a> <a id="2998" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3000" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3002" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3004" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3006" href="Relations.Continuous.html#2982" class="Bound">𝓦</a> <a id="3008" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3010" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3012" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="3020" href="Relations.Continuous.html#3020" class="Bound">I</a> <a id="3022" href="Relations.Continuous.html#3022" class="Bound">A</a> <a id="3024" href="Relations.Continuous.html#3024" class="Bound">𝓦</a> <a id="3026" class="Symbol">=</a> <a id="3028" class="Symbol">(</a><a id="3029" href="Relations.Continuous.html#3020" class="Bound">I</a> <a id="3031" class="Symbol">→</a> <a id="3033" href="Relations.Continuous.html#3022" class="Bound">A</a><a id="3034" class="Symbol">)</a> <a id="3036" class="Symbol">→</a> <a id="3038" href="Relations.Continuous.html#3024" class="Bound">𝓦</a> <a id="3040" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We now exploit the full power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type `𝒜 : I → 𝓤 ̇`, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `𝒜 i` to `𝒜 j` to `𝒜 k` to …. (This is only an heuristic since \ab I can represent an uncountable collection.\cref{uncountable}.<sup>[2](Relations.Continuous.html#fn2)</sup>)

<pre class="Agda">

<a id="DepRel"></a><a id="3581" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="3588" class="Symbol">:</a> <a id="3590" class="Symbol">(</a><a id="3591" href="Relations.Continuous.html#3591" class="Bound">I</a> <a id="3593" class="Symbol">:</a> <a id="3595" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3597" href="Universes.html#403" class="Function Operator">̇</a><a id="3598" class="Symbol">)</a> <a id="3600" class="Symbol">→</a> <a id="3602" class="Symbol">(</a><a id="3603" href="Relations.Continuous.html#3591" class="Bound">I</a> <a id="3605" class="Symbol">→</a> <a id="3607" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3609" href="Universes.html#403" class="Function Operator">̇</a><a id="3610" class="Symbol">)</a> <a id="3612" class="Symbol">→</a> <a id="3614" class="Symbol">(</a><a id="3615" href="Relations.Continuous.html#3615" class="Bound">𝓦</a> <a id="3617" class="Symbol">:</a> <a id="3619" href="Universes.html#205" class="Postulate">Universe</a><a id="3627" class="Symbol">)</a> <a id="3629" class="Symbol">→</a> <a id="3631" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3633" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3635" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3637" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3639" href="Relations.Continuous.html#3615" class="Bound">𝓦</a> <a id="3641" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3643" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3645" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="3652" href="Relations.Continuous.html#3652" class="Bound">I</a> <a id="3654" href="Relations.Continuous.html#3654" class="Bound">𝒜</a> <a id="3656" href="Relations.Continuous.html#3656" class="Bound">𝓦</a> <a id="3658" class="Symbol">=</a> <a id="3660" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3662" href="Relations.Continuous.html#3654" class="Bound">𝒜</a> <a id="3664" class="Symbol">→</a> <a id="3666" href="Relations.Continuous.html#3656" class="Bound">𝓦</a> <a id="3668" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.



#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define some functions that make it easy to assert that a given operation is compatible with a given relation.  The first is an *evaluation* function which "lifts" an `I`-ary relation to an `(I → J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of the `J`-tuples belong to the original relation.

<pre class="Agda">

<a id="4209" class="Keyword">module</a> <a id="4216" href="Relations.Continuous.html#4216" class="Module">_</a> <a id="4218" class="Symbol">{</a><a id="4219" href="Relations.Continuous.html#4219" class="Bound">I</a> <a id="4221" href="Relations.Continuous.html#4221" class="Bound">J</a> <a id="4223" class="Symbol">:</a> <a id="4225" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4227" href="Universes.html#403" class="Function Operator">̇</a><a id="4228" class="Symbol">}</a> <a id="4230" class="Symbol">{</a><a id="4231" href="Relations.Continuous.html#4231" class="Bound">A</a> <a id="4233" class="Symbol">:</a> <a id="4235" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4237" href="Universes.html#403" class="Function Operator">̇</a><a id="4238" class="Symbol">}</a> <a id="4240" class="Keyword">where</a>

 <a id="4248" href="Relations.Continuous.html#4248" class="Function">eval-cont-rel</a> <a id="4262" class="Symbol">:</a> <a id="4264" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="4272" href="Relations.Continuous.html#4219" class="Bound">I</a> <a id="4274" href="Relations.Continuous.html#4231" class="Bound">A</a> <a id="4276" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4278" class="Symbol">→</a> <a id="4280" class="Symbol">(</a><a id="4281" href="Relations.Continuous.html#4219" class="Bound">I</a> <a id="4283" class="Symbol">→</a> <a id="4285" href="Relations.Continuous.html#4221" class="Bound">J</a> <a id="4287" class="Symbol">→</a> <a id="4289" href="Relations.Continuous.html#4231" class="Bound">A</a><a id="4290" class="Symbol">)</a> <a id="4292" class="Symbol">→</a> <a id="4294" href="Relations.Continuous.html#4225" class="Bound">𝓥</a> <a id="4296" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4298" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4300" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4303" href="Relations.Continuous.html#4248" class="Function">eval-cont-rel</a> <a id="4317" href="Relations.Continuous.html#4317" class="Bound">R</a> <a id="4319" href="Relations.Continuous.html#4319" class="Bound">𝒶</a> <a id="4321" class="Symbol">=</a> <a id="4323" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4325" href="Relations.Continuous.html#4325" class="Bound">j</a> <a id="4327" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4329" href="Relations.Continuous.html#4221" class="Bound">J</a> <a id="4331" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4333" href="Relations.Continuous.html#4317" class="Bound">R</a> <a id="4335" class="Symbol">λ</a> <a id="4337" href="Relations.Continuous.html#4337" class="Bound">i</a> <a id="4339" class="Symbol">→</a> <a id="4341" href="Relations.Continuous.html#4319" class="Bound">𝒶</a> <a id="4343" href="Relations.Continuous.html#4337" class="Bound">i</a> <a id="4345" href="Relations.Continuous.html#4325" class="Bound">j</a>

 <a id="4349" href="Relations.Continuous.html#4349" class="Function">cont-compatible-op</a> <a id="4368" class="Symbol">:</a> <a id="4370" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="4373" href="Relations.Continuous.html#4221" class="Bound">J</a> <a id="4375" href="Relations.Continuous.html#4231" class="Bound">A</a> <a id="4377" class="Symbol">→</a> <a id="4379" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="4387" href="Relations.Continuous.html#4219" class="Bound">I</a> <a id="4389" href="Relations.Continuous.html#4231" class="Bound">A</a> <a id="4391" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4393" class="Symbol">→</a> <a id="4395" href="Relations.Continuous.html#4225" class="Bound">𝓥</a> <a id="4397" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4399" href="Relations.Continuous.html#4235" class="Bound">𝓤</a> <a id="4401" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4403" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4405" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4408" href="Relations.Continuous.html#4349" class="Function">cont-compatible-op</a> <a id="4427" href="Relations.Continuous.html#4427" class="Bound">𝑓</a> <a id="4429" href="Relations.Continuous.html#4429" class="Bound">R</a>  <a id="4432" class="Symbol">=</a> <a id="4434" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4436" href="Relations.Continuous.html#4436" class="Bound">𝒶</a> <a id="4438" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4440" class="Symbol">(</a><a id="4441" href="Relations.Continuous.html#4219" class="Bound">I</a> <a id="4443" class="Symbol">→</a> <a id="4445" href="Relations.Continuous.html#4221" class="Bound">J</a> <a id="4447" class="Symbol">→</a> <a id="4449" href="Relations.Continuous.html#4231" class="Bound">A</a><a id="4450" class="Symbol">)</a> <a id="4452" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4454" class="Symbol">(</a><a id="4455" href="Relations.Continuous.html#4248" class="Function">eval-cont-rel</a> <a id="4469" href="Relations.Continuous.html#4429" class="Bound">R</a> <a id="4471" href="Relations.Continuous.html#4436" class="Bound">𝒶</a> <a id="4473" class="Symbol">→</a> <a id="4475" href="Relations.Continuous.html#4429" class="Bound">R</a> <a id="4477" class="Symbol">λ</a> <a id="4479" href="Relations.Continuous.html#4479" class="Bound">i</a> <a id="4481" class="Symbol">→</a> <a id="4483" class="Symbol">(</a><a id="4484" href="Relations.Continuous.html#4427" class="Bound">𝑓</a> <a id="4486" class="Symbol">(</a><a id="4487" href="Relations.Continuous.html#4436" class="Bound">𝒶</a> <a id="4489" href="Relations.Continuous.html#4479" class="Bound">i</a><a id="4490" class="Symbol">)))</a>

</pre>

To readers who find the syntax of the last two definitions nauseating, we recommend focusing on the semantics. First, internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Next, recall that a continuous relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."  For each continuous relation `R`, the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which `eval-cont-rel R 𝒶` holds. For simplicity, pretend that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns. For example, here are the i-th and k-th columns (for some `i k : I`).

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2
𝑎 i 3      𝒶 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-cont-rel R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which represents the assertion that each row of the `I` columns shown above belongs to the original relation `R`. Finally, `cont-compatible-op` takes a `J`-ary operation `𝑓 : Op J A` and an `I`-tuple `𝒶 : I → J → A` of `J`-tuples, and determines whether the `I`-tuple `λ i → 𝑓 (𝑎 i)` belongs to `R`.


Above we saw lifts of continuous relations and what it means for such relations to be compatible with operations. We conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a dependent relation with an operation.

<pre class="Agda">

<a id="6172" class="Keyword">module</a> <a id="6179" href="Relations.Continuous.html#6179" class="Module">_</a> <a id="6181" class="Symbol">{</a><a id="6182" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6184" href="Relations.Continuous.html#6184" class="Bound">J</a> <a id="6186" class="Symbol">:</a> <a id="6188" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6190" href="Universes.html#403" class="Function Operator">̇</a><a id="6191" class="Symbol">}</a> <a id="6193" class="Symbol">{</a><a id="6194" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6196" class="Symbol">:</a> <a id="6198" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6200" class="Symbol">→</a> <a id="6202" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6204" href="Universes.html#403" class="Function Operator">̇</a><a id="6205" class="Symbol">}</a> <a id="6207" class="Keyword">where</a>

 <a id="6215" href="Relations.Continuous.html#6215" class="Function">eval-dep-rel</a> <a id="6228" class="Symbol">:</a> <a id="6230" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="6237" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6239" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6241" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6243" class="Symbol">→</a> <a id="6245" class="Symbol">(∀</a> <a id="6248" href="Relations.Continuous.html#6248" class="Bound">i</a> <a id="6250" class="Symbol">→</a> <a id="6252" class="Symbol">(</a><a id="6253" href="Relations.Continuous.html#6184" class="Bound">J</a> <a id="6255" class="Symbol">→</a> <a id="6257" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6259" href="Relations.Continuous.html#6248" class="Bound">i</a><a id="6260" class="Symbol">))</a> <a id="6263" class="Symbol">→</a> <a id="6265" href="Relations.Continuous.html#6188" class="Bound">𝓥</a> <a id="6267" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6269" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6271" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6274" href="Relations.Continuous.html#6215" class="Function">eval-dep-rel</a> <a id="6287" href="Relations.Continuous.html#6287" class="Bound">R</a> <a id="6289" href="Relations.Continuous.html#6289" class="Bound">𝒶</a> <a id="6291" class="Symbol">=</a> <a id="6293" class="Symbol">∀</a> <a id="6295" href="Relations.Continuous.html#6295" class="Bound">j</a> <a id="6297" class="Symbol">→</a> <a id="6299" href="Relations.Continuous.html#6287" class="Bound">R</a> <a id="6301" class="Symbol">(λ</a> <a id="6304" href="Relations.Continuous.html#6304" class="Bound">i</a> <a id="6306" class="Symbol">→</a> <a id="6308" class="Symbol">(</a><a id="6309" href="Relations.Continuous.html#6289" class="Bound">𝒶</a> <a id="6311" href="Relations.Continuous.html#6304" class="Bound">i</a><a id="6312" class="Symbol">)</a> <a id="6314" href="Relations.Continuous.html#6295" class="Bound">j</a><a id="6315" class="Symbol">)</a>

 <a id="6319" href="Relations.Continuous.html#6319" class="Function">dep-compatible-op</a> <a id="6337" class="Symbol">:</a> <a id="6339" class="Symbol">(∀</a> <a id="6342" href="Relations.Continuous.html#6342" class="Bound">i</a> <a id="6344" class="Symbol">→</a> <a id="6346" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="6349" href="Relations.Continuous.html#6184" class="Bound">J</a> <a id="6351" class="Symbol">(</a><a id="6352" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6354" href="Relations.Continuous.html#6342" class="Bound">i</a><a id="6355" class="Symbol">))</a> <a id="6358" class="Symbol">→</a> <a id="6360" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="6367" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6369" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6371" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6373" class="Symbol">→</a> <a id="6375" href="Relations.Continuous.html#6188" class="Bound">𝓥</a> <a id="6377" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6379" href="Relations.Continuous.html#6202" class="Bound">𝓤</a> <a id="6381" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6383" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6385" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6388" href="Relations.Continuous.html#6319" class="Function">dep-compatible-op</a> <a id="6406" href="Relations.Continuous.html#6406" class="Bound">𝑓</a> <a id="6408" href="Relations.Continuous.html#6408" class="Bound">R</a>  <a id="6411" class="Symbol">=</a> <a id="6413" class="Symbol">∀</a> <a id="6415" href="Relations.Continuous.html#6415" class="Bound">𝒶</a> <a id="6417" class="Symbol">→</a> <a id="6419" class="Symbol">(</a><a id="6420" href="Relations.Continuous.html#6215" class="Function">eval-dep-rel</a> <a id="6433" href="Relations.Continuous.html#6408" class="Bound">R</a><a id="6434" class="Symbol">)</a> <a id="6436" href="Relations.Continuous.html#6415" class="Bound">𝒶</a> <a id="6438" class="Symbol">→</a> <a id="6440" href="Relations.Continuous.html#6408" class="Bound">R</a> <a id="6442" class="Symbol">λ</a> <a id="6444" href="Relations.Continuous.html#6444" class="Bound">i</a> <a id="6446" class="Symbol">→</a> <a id="6448" class="Symbol">(</a><a id="6449" href="Relations.Continuous.html#6406" class="Bound">𝑓</a> <a id="6451" href="Relations.Continuous.html#6444" class="Bound">i</a><a id="6452" class="Symbol">)(</a><a id="6454" href="Relations.Continuous.html#6415" class="Bound">𝒶</a> <a id="6456" href="Relations.Continuous.html#6444" class="Bound">i</a><a id="6457" class="Symbol">)</a>

 <a id="6461" class="Comment">-- equivalent definition using Π notation</a>
 <a id="6504" href="Relations.Continuous.html#6504" class="Function">dep-compatible&#39;-op</a> <a id="6523" class="Symbol">:</a> <a id="6525" class="Symbol">(</a><a id="6526" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6528" href="Relations.Continuous.html#6528" class="Bound">i</a> <a id="6530" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6532" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6534" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6536" href="Relations.Discrete.html#7763" class="Function">Op</a> <a id="6539" href="Relations.Continuous.html#6184" class="Bound">J</a> <a id="6541" class="Symbol">(</a><a id="6542" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6544" href="Relations.Continuous.html#6528" class="Bound">i</a><a id="6545" class="Symbol">))</a> <a id="6548" class="Symbol">→</a> <a id="6550" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="6557" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6559" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6561" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6563" class="Symbol">→</a> <a id="6565" href="Relations.Continuous.html#6188" class="Bound">𝓥</a> <a id="6567" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6569" href="Relations.Continuous.html#6202" class="Bound">𝓤</a> <a id="6571" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6573" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6575" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6578" href="Relations.Continuous.html#6504" class="Function">dep-compatible&#39;-op</a> <a id="6597" href="Relations.Continuous.html#6597" class="Bound">𝑓</a> <a id="6599" href="Relations.Continuous.html#6599" class="Bound">R</a>  <a id="6602" class="Symbol">=</a>  <a id="6605" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6607" href="Relations.Continuous.html#6607" class="Bound">𝒶</a> <a id="6609" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6611" class="Symbol">(</a><a id="6612" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6614" href="Relations.Continuous.html#6614" class="Bound">i</a> <a id="6616" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6618" href="Relations.Continuous.html#6182" class="Bound">I</a> <a id="6620" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6622" class="Symbol">(</a><a id="6623" href="Relations.Continuous.html#6184" class="Bound">J</a> <a id="6625" class="Symbol">→</a> <a id="6627" href="Relations.Continuous.html#6194" class="Bound">𝒜</a> <a id="6629" href="Relations.Continuous.html#6614" class="Bound">i</a><a id="6630" class="Symbol">))</a> <a id="6633" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6635" class="Symbol">((</a><a id="6637" href="Relations.Continuous.html#6215" class="Function">eval-dep-rel</a> <a id="6650" href="Relations.Continuous.html#6599" class="Bound">R</a><a id="6651" class="Symbol">)</a> <a id="6653" href="Relations.Continuous.html#6607" class="Bound">𝒶</a> <a id="6655" class="Symbol">→</a> <a id="6657" href="Relations.Continuous.html#6599" class="Bound">R</a> <a id="6659" class="Symbol">λ</a> <a id="6661" href="Relations.Continuous.html#6661" class="Bound">i</a> <a id="6663" class="Symbol">→</a> <a id="6665" class="Symbol">(</a><a id="6666" href="Relations.Continuous.html#6597" class="Bound">𝑓</a> <a id="6668" href="Relations.Continuous.html#6661" class="Bound">i</a><a id="6669" class="Symbol">)(</a><a id="6671" href="Relations.Continuous.html#6607" class="Bound">𝒶</a> <a id="6673" href="Relations.Continuous.html#6661" class="Bound">i</a><a id="6674" class="Symbol">))</a>

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
