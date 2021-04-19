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

We now define the type `ContRel` which represents predicates of arbitrary arity over a single type `A`. We call this the type of *continuous relations*.<sup>[1](Relations.Continuous.html#fn1)</sup>)

<pre class="Agda">

<a id="ContRel"></a><a id="2965" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="2973" class="Symbol">:</a> <a id="2975" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2977" href="Universes.html#403" class="Function Operator">̇</a> <a id="2979" class="Symbol">→</a> <a id="2981" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2983" href="Universes.html#403" class="Function Operator">̇</a> <a id="2985" class="Symbol">→</a> <a id="2987" class="Symbol">(</a><a id="2988" href="Relations.Continuous.html#2988" class="Bound">𝓦</a> <a id="2990" class="Symbol">:</a> <a id="2992" href="Universes.html#205" class="Postulate">Universe</a><a id="3000" class="Symbol">)</a> <a id="3002" class="Symbol">→</a> <a id="3004" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3006" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3008" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3010" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3012" href="Relations.Continuous.html#2988" class="Bound">𝓦</a> <a id="3014" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3016" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3018" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="3026" href="Relations.Continuous.html#3026" class="Bound">I</a> <a id="3028" href="Relations.Continuous.html#3028" class="Bound">A</a> <a id="3030" href="Relations.Continuous.html#3030" class="Bound">𝓦</a> <a id="3032" class="Symbol">=</a> <a id="3034" class="Symbol">(</a><a id="3035" href="Relations.Continuous.html#3026" class="Bound">I</a> <a id="3037" class="Symbol">→</a> <a id="3039" href="Relations.Continuous.html#3028" class="Bound">A</a><a id="3040" class="Symbol">)</a> <a id="3042" class="Symbol">→</a> <a id="3044" href="Relations.Continuous.html#3030" class="Bound">𝓦</a> <a id="3046" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We now exploit the full power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type `𝒜 : I → 𝓤 ̇`, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `𝒜 i` to `𝒜 j` to `𝒜 k` to …. (This is only an heuristic since \ab I can represent an uncountable collection.\cref{uncountable}.<sup>[2](Relations.Continuous.html#fn2)</sup>)

<pre class="Agda">

<a id="DepRel"></a><a id="3587" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="3594" class="Symbol">:</a> <a id="3596" class="Symbol">(</a><a id="3597" href="Relations.Continuous.html#3597" class="Bound">I</a> <a id="3599" class="Symbol">:</a> <a id="3601" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3603" href="Universes.html#403" class="Function Operator">̇</a><a id="3604" class="Symbol">)</a> <a id="3606" class="Symbol">→</a> <a id="3608" class="Symbol">(</a><a id="3609" href="Relations.Continuous.html#3597" class="Bound">I</a> <a id="3611" class="Symbol">→</a> <a id="3613" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3615" href="Universes.html#403" class="Function Operator">̇</a><a id="3616" class="Symbol">)</a> <a id="3618" class="Symbol">→</a> <a id="3620" class="Symbol">(</a><a id="3621" href="Relations.Continuous.html#3621" class="Bound">𝓦</a> <a id="3623" class="Symbol">:</a> <a id="3625" href="Universes.html#205" class="Postulate">Universe</a><a id="3633" class="Symbol">)</a> <a id="3635" class="Symbol">→</a> <a id="3637" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3639" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3641" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3643" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3645" href="Relations.Continuous.html#3621" class="Bound">𝓦</a> <a id="3647" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3649" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3651" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="3658" href="Relations.Continuous.html#3658" class="Bound">I</a> <a id="3660" href="Relations.Continuous.html#3660" class="Bound">𝒜</a> <a id="3662" href="Relations.Continuous.html#3662" class="Bound">𝓦</a> <a id="3664" class="Symbol">=</a> <a id="3666" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3668" href="Relations.Continuous.html#3660" class="Bound">𝒜</a> <a id="3670" class="Symbol">→</a> <a id="3672" href="Relations.Continuous.html#3662" class="Bound">𝓦</a> <a id="3674" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.



#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define some functions that make it easy to assert that a given operation is compatible with a given relation.  The first is an *evaluation* function which "lifts" an `I`-ary relation to an `(I → J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of the `J`-tuples belong to the original relation.

<pre class="Agda">

<a id="4215" class="Keyword">module</a> <a id="4222" href="Relations.Continuous.html#4222" class="Module">_</a> <a id="4224" class="Symbol">{</a><a id="4225" href="Relations.Continuous.html#4225" class="Bound">I</a> <a id="4227" href="Relations.Continuous.html#4227" class="Bound">J</a> <a id="4229" class="Symbol">:</a> <a id="4231" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4233" href="Universes.html#403" class="Function Operator">̇</a><a id="4234" class="Symbol">}</a> <a id="4236" class="Symbol">{</a><a id="4237" href="Relations.Continuous.html#4237" class="Bound">A</a> <a id="4239" class="Symbol">:</a> <a id="4241" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4243" href="Universes.html#403" class="Function Operator">̇</a><a id="4244" class="Symbol">}</a> <a id="4246" class="Keyword">where</a>

 <a id="4254" href="Relations.Continuous.html#4254" class="Function">eval-cont-rel</a> <a id="4268" class="Symbol">:</a> <a id="4270" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="4278" href="Relations.Continuous.html#4225" class="Bound">I</a> <a id="4280" href="Relations.Continuous.html#4237" class="Bound">A</a> <a id="4282" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4284" class="Symbol">→</a> <a id="4286" class="Symbol">(</a><a id="4287" href="Relations.Continuous.html#4225" class="Bound">I</a> <a id="4289" class="Symbol">→</a> <a id="4291" href="Relations.Continuous.html#4227" class="Bound">J</a> <a id="4293" class="Symbol">→</a> <a id="4295" href="Relations.Continuous.html#4237" class="Bound">A</a><a id="4296" class="Symbol">)</a> <a id="4298" class="Symbol">→</a> <a id="4300" href="Relations.Continuous.html#4231" class="Bound">𝓥</a> <a id="4302" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4304" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4306" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4309" href="Relations.Continuous.html#4254" class="Function">eval-cont-rel</a> <a id="4323" href="Relations.Continuous.html#4323" class="Bound">R</a> <a id="4325" href="Relations.Continuous.html#4325" class="Bound">𝒶</a> <a id="4327" class="Symbol">=</a> <a id="4329" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4331" href="Relations.Continuous.html#4331" class="Bound">j</a> <a id="4333" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4335" href="Relations.Continuous.html#4227" class="Bound">J</a> <a id="4337" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4339" href="Relations.Continuous.html#4323" class="Bound">R</a> <a id="4341" class="Symbol">λ</a> <a id="4343" href="Relations.Continuous.html#4343" class="Bound">i</a> <a id="4345" class="Symbol">→</a> <a id="4347" href="Relations.Continuous.html#4325" class="Bound">𝒶</a> <a id="4349" href="Relations.Continuous.html#4343" class="Bound">i</a> <a id="4351" href="Relations.Continuous.html#4331" class="Bound">j</a>

 <a id="4355" href="Relations.Continuous.html#4355" class="Function">cont-compatible-op</a> <a id="4374" class="Symbol">:</a> <a id="4376" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="4379" href="Relations.Continuous.html#4227" class="Bound">J</a> <a id="4381" href="Relations.Continuous.html#4237" class="Bound">A</a> <a id="4383" class="Symbol">→</a> <a id="4385" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="4393" href="Relations.Continuous.html#4225" class="Bound">I</a> <a id="4395" href="Relations.Continuous.html#4237" class="Bound">A</a> <a id="4397" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4399" class="Symbol">→</a> <a id="4401" href="Relations.Continuous.html#4231" class="Bound">𝓥</a> <a id="4403" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4405" href="Relations.Continuous.html#4241" class="Bound">𝓤</a> <a id="4407" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4409" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4411" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4414" href="Relations.Continuous.html#4355" class="Function">cont-compatible-op</a> <a id="4433" href="Relations.Continuous.html#4433" class="Bound">𝑓</a> <a id="4435" href="Relations.Continuous.html#4435" class="Bound">R</a>  <a id="4438" class="Symbol">=</a> <a id="4440" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4442" href="Relations.Continuous.html#4442" class="Bound">𝒶</a> <a id="4444" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4446" class="Symbol">(</a><a id="4447" href="Relations.Continuous.html#4225" class="Bound">I</a> <a id="4449" class="Symbol">→</a> <a id="4451" href="Relations.Continuous.html#4227" class="Bound">J</a> <a id="4453" class="Symbol">→</a> <a id="4455" href="Relations.Continuous.html#4237" class="Bound">A</a><a id="4456" class="Symbol">)</a> <a id="4458" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4460" class="Symbol">(</a><a id="4461" href="Relations.Continuous.html#4254" class="Function">eval-cont-rel</a> <a id="4475" href="Relations.Continuous.html#4435" class="Bound">R</a> <a id="4477" href="Relations.Continuous.html#4442" class="Bound">𝒶</a> <a id="4479" class="Symbol">→</a> <a id="4481" href="Relations.Continuous.html#4435" class="Bound">R</a> <a id="4483" class="Symbol">λ</a> <a id="4485" href="Relations.Continuous.html#4485" class="Bound">i</a> <a id="4487" class="Symbol">→</a> <a id="4489" class="Symbol">(</a><a id="4490" href="Relations.Continuous.html#4433" class="Bound">𝑓</a> <a id="4492" class="Symbol">(</a><a id="4493" href="Relations.Continuous.html#4442" class="Bound">𝒶</a> <a id="4495" href="Relations.Continuous.html#4485" class="Bound">i</a><a id="4496" class="Symbol">)))</a>

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

<a id="6178" class="Keyword">module</a> <a id="6185" href="Relations.Continuous.html#6185" class="Module">_</a> <a id="6187" class="Symbol">{</a><a id="6188" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6190" href="Relations.Continuous.html#6190" class="Bound">J</a> <a id="6192" class="Symbol">:</a> <a id="6194" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6196" href="Universes.html#403" class="Function Operator">̇</a><a id="6197" class="Symbol">}</a> <a id="6199" class="Symbol">{</a><a id="6200" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6202" class="Symbol">:</a> <a id="6204" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6206" class="Symbol">→</a> <a id="6208" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6210" href="Universes.html#403" class="Function Operator">̇</a><a id="6211" class="Symbol">}</a> <a id="6213" class="Keyword">where</a>

 <a id="6221" href="Relations.Continuous.html#6221" class="Function">eval-dep-rel</a> <a id="6234" class="Symbol">:</a> <a id="6236" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="6243" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6245" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6247" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6249" class="Symbol">→</a> <a id="6251" class="Symbol">(∀</a> <a id="6254" href="Relations.Continuous.html#6254" class="Bound">i</a> <a id="6256" class="Symbol">→</a> <a id="6258" class="Symbol">(</a><a id="6259" href="Relations.Continuous.html#6190" class="Bound">J</a> <a id="6261" class="Symbol">→</a> <a id="6263" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6265" href="Relations.Continuous.html#6254" class="Bound">i</a><a id="6266" class="Symbol">))</a> <a id="6269" class="Symbol">→</a> <a id="6271" href="Relations.Continuous.html#6194" class="Bound">𝓥</a> <a id="6273" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6275" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6277" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6280" href="Relations.Continuous.html#6221" class="Function">eval-dep-rel</a> <a id="6293" href="Relations.Continuous.html#6293" class="Bound">R</a> <a id="6295" href="Relations.Continuous.html#6295" class="Bound">𝒶</a> <a id="6297" class="Symbol">=</a> <a id="6299" class="Symbol">∀</a> <a id="6301" href="Relations.Continuous.html#6301" class="Bound">j</a> <a id="6303" class="Symbol">→</a> <a id="6305" href="Relations.Continuous.html#6293" class="Bound">R</a> <a id="6307" class="Symbol">(λ</a> <a id="6310" href="Relations.Continuous.html#6310" class="Bound">i</a> <a id="6312" class="Symbol">→</a> <a id="6314" class="Symbol">(</a><a id="6315" href="Relations.Continuous.html#6295" class="Bound">𝒶</a> <a id="6317" href="Relations.Continuous.html#6310" class="Bound">i</a><a id="6318" class="Symbol">)</a> <a id="6320" href="Relations.Continuous.html#6301" class="Bound">j</a><a id="6321" class="Symbol">)</a>

 <a id="6325" href="Relations.Continuous.html#6325" class="Function">dep-compatible-op</a> <a id="6343" class="Symbol">:</a> <a id="6345" class="Symbol">(∀</a> <a id="6348" href="Relations.Continuous.html#6348" class="Bound">i</a> <a id="6350" class="Symbol">→</a> <a id="6352" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="6355" href="Relations.Continuous.html#6190" class="Bound">J</a> <a id="6357" class="Symbol">(</a><a id="6358" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6360" href="Relations.Continuous.html#6348" class="Bound">i</a><a id="6361" class="Symbol">))</a> <a id="6364" class="Symbol">→</a> <a id="6366" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="6373" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6375" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6377" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6379" class="Symbol">→</a> <a id="6381" href="Relations.Continuous.html#6194" class="Bound">𝓥</a> <a id="6383" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6385" href="Relations.Continuous.html#6208" class="Bound">𝓤</a> <a id="6387" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6389" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6391" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6394" href="Relations.Continuous.html#6325" class="Function">dep-compatible-op</a> <a id="6412" href="Relations.Continuous.html#6412" class="Bound">𝑓</a> <a id="6414" href="Relations.Continuous.html#6414" class="Bound">R</a>  <a id="6417" class="Symbol">=</a> <a id="6419" class="Symbol">∀</a> <a id="6421" href="Relations.Continuous.html#6421" class="Bound">𝒶</a> <a id="6423" class="Symbol">→</a> <a id="6425" class="Symbol">(</a><a id="6426" href="Relations.Continuous.html#6221" class="Function">eval-dep-rel</a> <a id="6439" href="Relations.Continuous.html#6414" class="Bound">R</a><a id="6440" class="Symbol">)</a> <a id="6442" href="Relations.Continuous.html#6421" class="Bound">𝒶</a> <a id="6444" class="Symbol">→</a> <a id="6446" href="Relations.Continuous.html#6414" class="Bound">R</a> <a id="6448" class="Symbol">λ</a> <a id="6450" href="Relations.Continuous.html#6450" class="Bound">i</a> <a id="6452" class="Symbol">→</a> <a id="6454" class="Symbol">(</a><a id="6455" href="Relations.Continuous.html#6412" class="Bound">𝑓</a> <a id="6457" href="Relations.Continuous.html#6450" class="Bound">i</a><a id="6458" class="Symbol">)(</a><a id="6460" href="Relations.Continuous.html#6421" class="Bound">𝒶</a> <a id="6462" href="Relations.Continuous.html#6450" class="Bound">i</a><a id="6463" class="Symbol">)</a>

 <a id="6467" class="Comment">-- equivalent definition using Π notation</a>
 <a id="6510" href="Relations.Continuous.html#6510" class="Function">dep-compatible&#39;-op</a> <a id="6529" class="Symbol">:</a> <a id="6531" class="Symbol">(</a><a id="6532" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6534" href="Relations.Continuous.html#6534" class="Bound">i</a> <a id="6536" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6538" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6540" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6542" href="Relations.Discrete.html#7323" class="Function">Op</a> <a id="6545" href="Relations.Continuous.html#6190" class="Bound">J</a> <a id="6547" class="Symbol">(</a><a id="6548" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6550" href="Relations.Continuous.html#6534" class="Bound">i</a><a id="6551" class="Symbol">))</a> <a id="6554" class="Symbol">→</a> <a id="6556" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="6563" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6565" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6567" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6569" class="Symbol">→</a> <a id="6571" href="Relations.Continuous.html#6194" class="Bound">𝓥</a> <a id="6573" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6575" href="Relations.Continuous.html#6208" class="Bound">𝓤</a> <a id="6577" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6579" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6581" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6584" href="Relations.Continuous.html#6510" class="Function">dep-compatible&#39;-op</a> <a id="6603" href="Relations.Continuous.html#6603" class="Bound">𝑓</a> <a id="6605" href="Relations.Continuous.html#6605" class="Bound">R</a>  <a id="6608" class="Symbol">=</a>  <a id="6611" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6613" href="Relations.Continuous.html#6613" class="Bound">𝒶</a> <a id="6615" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6617" class="Symbol">(</a><a id="6618" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="6620" href="Relations.Continuous.html#6620" class="Bound">i</a> <a id="6622" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="6624" href="Relations.Continuous.html#6188" class="Bound">I</a> <a id="6626" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6628" class="Symbol">(</a><a id="6629" href="Relations.Continuous.html#6190" class="Bound">J</a> <a id="6631" class="Symbol">→</a> <a id="6633" href="Relations.Continuous.html#6200" class="Bound">𝒜</a> <a id="6635" href="Relations.Continuous.html#6620" class="Bound">i</a><a id="6636" class="Symbol">))</a> <a id="6639" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="6641" class="Symbol">((</a><a id="6643" href="Relations.Continuous.html#6221" class="Function">eval-dep-rel</a> <a id="6656" href="Relations.Continuous.html#6605" class="Bound">R</a><a id="6657" class="Symbol">)</a> <a id="6659" href="Relations.Continuous.html#6613" class="Bound">𝒶</a> <a id="6661" class="Symbol">→</a> <a id="6663" href="Relations.Continuous.html#6605" class="Bound">R</a> <a id="6665" class="Symbol">λ</a> <a id="6667" href="Relations.Continuous.html#6667" class="Bound">i</a> <a id="6669" class="Symbol">→</a> <a id="6671" class="Symbol">(</a><a id="6672" href="Relations.Continuous.html#6603" class="Bound">𝑓</a> <a id="6674" href="Relations.Continuous.html#6667" class="Bound">i</a><a id="6675" class="Symbol">)(</a><a id="6677" href="Relations.Continuous.html#6613" class="Bound">𝒶</a> <a id="6679" href="Relations.Continuous.html#6667" class="Bound">i</a><a id="6680" class="Symbol">))</a>

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
