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

Below we will define `ContRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ContRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, ternary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type---said another way, they are *single-sorted* relations---but we will remove this limitation as well when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ContRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

#### <a id="continuous-relations">Continuous relations</a>

We now define the type `ContRel` which represents predicates of arbitrary arity over a single type `A`. We call this the type of *continuous relations*.

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ContRel"></a><a id="3260" href="Relations.Continuous.html#3260" class="Function">ContRel</a> <a id="3268" class="Symbol">:</a> <a id="3270" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3272" href="Universes.html#403" class="Function Operator">̇</a> <a id="3274" class="Symbol">→</a> <a id="3276" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3278" href="Universes.html#403" class="Function Operator">̇</a> <a id="3280" class="Symbol">→</a> <a id="3282" class="Symbol">(</a><a id="3283" href="Relations.Continuous.html#3283" class="Bound">𝓦</a> <a id="3285" class="Symbol">:</a> <a id="3287" href="Universes.html#205" class="Postulate">Universe</a><a id="3295" class="Symbol">)</a> <a id="3297" class="Symbol">→</a> <a id="3299" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3301" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3303" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3305" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3307" href="Relations.Continuous.html#3283" class="Bound">𝓦</a> <a id="3309" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3311" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3313" href="Relations.Continuous.html#3260" class="Function">ContRel</a> <a id="3321" href="Relations.Continuous.html#3321" class="Bound">I</a> <a id="3323" href="Relations.Continuous.html#3323" class="Bound">A</a> <a id="3325" href="Relations.Continuous.html#3325" class="Bound">𝓦</a> <a id="3327" class="Symbol">=</a> <a id="3329" class="Symbol">(</a><a id="3330" href="Relations.Continuous.html#3321" class="Bound">I</a> <a id="3332" class="Symbol">→</a> <a id="3334" href="Relations.Continuous.html#3323" class="Bound">A</a><a id="3335" class="Symbol">)</a> <a id="3337" class="Symbol">→</a> <a id="3339" href="Relations.Continuous.html#3325" class="Bound">𝓦</a> <a id="3341" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.  The first is an *evaluation* function which  an `I`-ary relation to an `I → J`-ary relation. The lifted relation will tuples of members of the original relation.

<pre class="Agda">

<a id="3763" class="Keyword">module</a> <a id="3770" href="Relations.Continuous.html#3770" class="Module">_</a> <a id="3772" class="Symbol">{</a><a id="3773" href="Relations.Continuous.html#3773" class="Bound">I</a> <a id="3775" href="Relations.Continuous.html#3775" class="Bound">J</a> <a id="3777" class="Symbol">:</a> <a id="3779" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3781" href="Universes.html#403" class="Function Operator">̇</a><a id="3782" class="Symbol">}</a> <a id="3784" class="Symbol">{</a><a id="3785" href="Relations.Continuous.html#3785" class="Bound">A</a> <a id="3787" class="Symbol">:</a> <a id="3789" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3791" href="Universes.html#403" class="Function Operator">̇</a><a id="3792" class="Symbol">}</a> <a id="3794" class="Keyword">where</a>

 <a id="3802" href="Relations.Continuous.html#3802" class="Function">eval-cont-rel</a> <a id="3816" class="Symbol">:</a> <a id="3818" href="Relations.Continuous.html#3260" class="Function">ContRel</a> <a id="3826" href="Relations.Continuous.html#3773" class="Bound">I</a> <a id="3828" href="Relations.Continuous.html#3785" class="Bound">A</a> <a id="3830" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3832" class="Symbol">→</a> <a id="3834" class="Symbol">(</a><a id="3835" href="Relations.Continuous.html#3773" class="Bound">I</a> <a id="3837" class="Symbol">→</a> <a id="3839" href="Relations.Continuous.html#3775" class="Bound">J</a> <a id="3841" class="Symbol">→</a> <a id="3843" href="Relations.Continuous.html#3785" class="Bound">A</a><a id="3844" class="Symbol">)</a> <a id="3846" class="Symbol">→</a> <a id="3848" href="Relations.Continuous.html#3779" class="Bound">𝓥</a> <a id="3850" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3852" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3854" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3857" href="Relations.Continuous.html#3802" class="Function">eval-cont-rel</a> <a id="3871" href="Relations.Continuous.html#3871" class="Bound">R</a> <a id="3873" href="Relations.Continuous.html#3873" class="Bound">𝒂</a> <a id="3875" class="Symbol">=</a> <a id="3877" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3879" href="Relations.Continuous.html#3879" class="Bound">j</a> <a id="3881" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="3883" href="Relations.Continuous.html#3775" class="Bound">J</a> <a id="3885" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="3887" href="Relations.Continuous.html#3871" class="Bound">R</a> <a id="3889" class="Symbol">λ</a> <a id="3891" href="Relations.Continuous.html#3891" class="Bound">i</a> <a id="3893" class="Symbol">→</a> <a id="3895" href="Relations.Continuous.html#3873" class="Bound">𝒂</a> <a id="3897" href="Relations.Continuous.html#3891" class="Bound">i</a> <a id="3899" href="Relations.Continuous.html#3879" class="Bound">j</a>

 <a id="3903" href="Relations.Continuous.html#3903" class="Function">cont-compatible-fun</a> <a id="3923" class="Symbol">:</a> <a id="3925" class="Symbol">((</a><a id="3927" href="Relations.Continuous.html#3775" class="Bound">J</a> <a id="3929" class="Symbol">→</a> <a id="3931" href="Relations.Continuous.html#3785" class="Bound">A</a><a id="3932" class="Symbol">)</a> <a id="3934" class="Symbol">→</a> <a id="3936" href="Relations.Continuous.html#3785" class="Bound">A</a><a id="3937" class="Symbol">)</a> <a id="3939" class="Symbol">→</a> <a id="3941" href="Relations.Continuous.html#3260" class="Function">ContRel</a> <a id="3949" href="Relations.Continuous.html#3773" class="Bound">I</a> <a id="3951" href="Relations.Continuous.html#3785" class="Bound">A</a> <a id="3953" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3955" class="Symbol">→</a> <a id="3957" href="Relations.Continuous.html#3779" class="Bound">𝓥</a> <a id="3959" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3961" href="Relations.Continuous.html#3789" class="Bound">𝓤</a> <a id="3963" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3965" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3967" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3970" href="Relations.Continuous.html#3903" class="Function">cont-compatible-fun</a> <a id="3990" href="Relations.Continuous.html#3990" class="Bound">𝑓</a> <a id="3992" href="Relations.Continuous.html#3992" class="Bound">R</a>  <a id="3995" class="Symbol">=</a> <a id="3997" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3999" href="Relations.Continuous.html#3999" class="Bound">𝒂</a> <a id="4001" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4003" class="Symbol">(</a><a id="4004" href="Relations.Continuous.html#3773" class="Bound">I</a> <a id="4006" class="Symbol">→</a> <a id="4008" href="Relations.Continuous.html#3775" class="Bound">J</a> <a id="4010" class="Symbol">→</a> <a id="4012" href="Relations.Continuous.html#3785" class="Bound">A</a><a id="4013" class="Symbol">)</a> <a id="4015" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4017" class="Symbol">(</a><a id="4018" href="Relations.Continuous.html#3802" class="Function">eval-cont-rel</a> <a id="4032" href="Relations.Continuous.html#3992" class="Bound">R</a> <a id="4034" href="Relations.Continuous.html#3999" class="Bound">𝒂</a> <a id="4036" class="Symbol">→</a> <a id="4038" href="Relations.Continuous.html#3992" class="Bound">R</a> <a id="4040" class="Symbol">λ</a> <a id="4042" href="Relations.Continuous.html#4042" class="Bound">i</a> <a id="4044" class="Symbol">→</a> <a id="4046" class="Symbol">(</a><a id="4047" href="Relations.Continuous.html#3990" class="Bound">𝑓</a> <a id="4049" class="Symbol">(</a><a id="4050" href="Relations.Continuous.html#3999" class="Bound">𝒂</a> <a id="4052" href="Relations.Continuous.html#4042" class="Bound">i</a><a id="4053" class="Symbol">)))</a>

 <a id="4059" class="Comment">-- eval-cont-rel : ContRel I A 𝓦 → (I → J → A) → 𝓥 ⊔ 𝓦 ̇</a>
 <a id="4117" class="Comment">-- eval-cont-rel R 𝕒 = ∀ (j : J) → R λ i → (𝕒 i) j</a>

 <a id="4170" class="Comment">-- cont-compatible-fun : (I → (J → A) → A) → ContRel I A 𝓦 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇</a>
 <a id="4244" class="Comment">-- cont-compatible-fun 𝕗 R  = ∀ 𝕒 → (eval-cont-rel R) 𝕒 → R λ i → (𝕗 i) (𝕒 i)</a>

</pre>

<!-- In the definition of `cont-compatible-fun`, we let Agda infer the type of `𝒂`, which is `I → (J → A)`. -->

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics. In fact, we should probably pause here to discuss these semantics, lest the even more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝒂 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, then recall that a continuous relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Now consider the function `eval-cont-rel`.  For each continuous relation `R`, the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝒂 : I → J → A` such that `eval-cont-rel R 𝒂` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝒂 i 1      𝒂 k 1
𝒂 i 2      𝒂 k 2
𝑎 i 3      𝒂 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒂 i J      𝒂 k J
```

Now `eval-cont-rel R 𝒂` is defined by `∀ j → R (λ i → 𝒂 i j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `cont-compatible-fun`.  Here, `𝑓 : (J → A) → A` denotes a `J`-ary operation on `A`.  That is, `𝑓` takes a `J`-tuple `𝒂 i : J → A` and evaluates to some inhabitant `𝑓 (𝑎 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝒂 : I → (J → A)` is precisely the type on which the relation `eval-cont-rel R` is defined.


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type `𝒜 : I → 𝓤 ̇`, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `𝒜 i` to `𝒜 j` to `𝒜 k` to ….

<pre class="Agda">

<a id="DepRel"></a><a id="6759" href="Relations.Continuous.html#6759" class="Function">DepRel</a> <a id="6766" class="Symbol">:</a> <a id="6768" class="Symbol">(</a><a id="6769" href="Relations.Continuous.html#6769" class="Bound">I</a> <a id="6771" class="Symbol">:</a> <a id="6773" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6775" href="Universes.html#403" class="Function Operator">̇</a><a id="6776" class="Symbol">)</a> <a id="6778" class="Symbol">→</a> <a id="6780" class="Symbol">(</a><a id="6781" href="Relations.Continuous.html#6769" class="Bound">I</a> <a id="6783" class="Symbol">→</a> <a id="6785" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6787" href="Universes.html#403" class="Function Operator">̇</a><a id="6788" class="Symbol">)</a> <a id="6790" class="Symbol">→</a> <a id="6792" class="Symbol">(</a><a id="6793" href="Relations.Continuous.html#6793" class="Bound">𝓦</a> <a id="6795" class="Symbol">:</a> <a id="6797" href="Universes.html#205" class="Postulate">Universe</a><a id="6805" class="Symbol">)</a> <a id="6807" class="Symbol">→</a> <a id="6809" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6811" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6813" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6815" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6817" href="Relations.Continuous.html#6793" class="Bound">𝓦</a> <a id="6819" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="6821" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6823" href="Relations.Continuous.html#6759" class="Function">DepRel</a> <a id="6830" href="Relations.Continuous.html#6830" class="Bound">I</a> <a id="6832" href="Relations.Continuous.html#6832" class="Bound">𝒜</a> <a id="6834" href="Relations.Continuous.html#6834" class="Bound">𝓦</a> <a id="6836" class="Symbol">=</a> <a id="6838" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6840" href="Relations.Continuous.html#6832" class="Bound">𝒜</a> <a id="6842" class="Symbol">→</a> <a id="6844" href="Relations.Continuous.html#6834" class="Bound">𝓦</a> <a id="6846" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="7347" class="Keyword">module</a> <a id="7354" href="Relations.Continuous.html#7354" class="Module">_</a> <a id="7356" class="Symbol">{</a><a id="7357" href="Relations.Continuous.html#7357" class="Bound">I</a> <a id="7359" href="Relations.Continuous.html#7359" class="Bound">J</a> <a id="7361" class="Symbol">:</a> <a id="7363" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7365" href="Universes.html#403" class="Function Operator">̇</a><a id="7366" class="Symbol">}</a> <a id="7368" class="Symbol">{</a><a id="7369" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7371" class="Symbol">:</a> <a id="7373" href="Relations.Continuous.html#7357" class="Bound">I</a> <a id="7375" class="Symbol">→</a> <a id="7377" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7379" href="Universes.html#403" class="Function Operator">̇</a><a id="7380" class="Symbol">}</a> <a id="7382" class="Keyword">where</a>

 <a id="7390" href="Relations.Continuous.html#7390" class="Function">lift-dep-rel</a> <a id="7403" class="Symbol">:</a> <a id="7405" href="Relations.Continuous.html#6759" class="Function">DepRel</a> <a id="7412" href="Relations.Continuous.html#7357" class="Bound">I</a> <a id="7414" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7416" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7418" class="Symbol">→</a> <a id="7420" class="Symbol">(∀</a> <a id="7423" href="Relations.Continuous.html#7423" class="Bound">i</a> <a id="7425" class="Symbol">→</a> <a id="7427" href="Relations.Continuous.html#7359" class="Bound">J</a> <a id="7429" class="Symbol">→</a> <a id="7431" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7433" href="Relations.Continuous.html#7423" class="Bound">i</a><a id="7434" class="Symbol">)</a> <a id="7436" class="Symbol">→</a> <a id="7438" href="Relations.Continuous.html#7363" class="Bound">𝓥</a> <a id="7440" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7442" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7444" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7447" href="Relations.Continuous.html#7390" class="Function">lift-dep-rel</a> <a id="7460" href="Relations.Continuous.html#7460" class="Bound">R</a> <a id="7462" href="Relations.Continuous.html#7462" class="Bound">𝕒</a> <a id="7464" class="Symbol">=</a> <a id="7466" class="Symbol">∀</a> <a id="7468" class="Symbol">(</a><a id="7469" href="Relations.Continuous.html#7469" class="Bound">j</a> <a id="7471" class="Symbol">:</a> <a id="7473" href="Relations.Continuous.html#7359" class="Bound">J</a><a id="7474" class="Symbol">)</a> <a id="7476" class="Symbol">→</a> <a id="7478" href="Relations.Continuous.html#7460" class="Bound">R</a> <a id="7480" class="Symbol">(λ</a> <a id="7483" href="Relations.Continuous.html#7483" class="Bound">i</a> <a id="7485" class="Symbol">→</a> <a id="7487" class="Symbol">(</a><a id="7488" href="Relations.Continuous.html#7462" class="Bound">𝕒</a> <a id="7490" href="Relations.Continuous.html#7483" class="Bound">i</a><a id="7491" class="Symbol">)</a> <a id="7493" href="Relations.Continuous.html#7469" class="Bound">j</a><a id="7494" class="Symbol">)</a>

 <a id="7498" href="Relations.Continuous.html#7498" class="Function">dep-compatible-fun</a> <a id="7517" class="Symbol">:</a> <a id="7519" class="Symbol">(∀</a> <a id="7522" href="Relations.Continuous.html#7522" class="Bound">i</a> <a id="7524" class="Symbol">→</a> <a id="7526" class="Symbol">(</a><a id="7527" href="Relations.Continuous.html#7359" class="Bound">J</a> <a id="7529" class="Symbol">→</a> <a id="7531" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7533" href="Relations.Continuous.html#7522" class="Bound">i</a><a id="7534" class="Symbol">)</a> <a id="7536" class="Symbol">→</a> <a id="7538" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7540" href="Relations.Continuous.html#7522" class="Bound">i</a><a id="7541" class="Symbol">)</a> <a id="7543" class="Symbol">→</a> <a id="7545" href="Relations.Continuous.html#6759" class="Function">DepRel</a> <a id="7552" href="Relations.Continuous.html#7357" class="Bound">I</a> <a id="7554" href="Relations.Continuous.html#7369" class="Bound">𝒜</a> <a id="7556" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7558" class="Symbol">→</a> <a id="7560" href="Relations.Continuous.html#7363" class="Bound">𝓥</a> <a id="7562" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7564" href="Relations.Continuous.html#7377" class="Bound">𝓤</a> <a id="7566" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7568" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7570" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7573" href="Relations.Continuous.html#7498" class="Function">dep-compatible-fun</a> <a id="7592" href="Relations.Continuous.html#7592" class="Bound">𝕗</a> <a id="7594" href="Relations.Continuous.html#7594" class="Bound">R</a>  <a id="7597" class="Symbol">=</a> <a id="7599" class="Symbol">∀</a> <a id="7601" href="Relations.Continuous.html#7601" class="Bound">𝕒</a> <a id="7603" class="Symbol">→</a> <a id="7605" class="Symbol">(</a><a id="7606" href="Relations.Continuous.html#7390" class="Function">lift-dep-rel</a> <a id="7619" href="Relations.Continuous.html#7594" class="Bound">R</a><a id="7620" class="Symbol">)</a> <a id="7622" href="Relations.Continuous.html#7601" class="Bound">𝕒</a> <a id="7624" class="Symbol">→</a> <a id="7626" href="Relations.Continuous.html#7594" class="Bound">R</a> <a id="7628" class="Symbol">λ</a> <a id="7630" href="Relations.Continuous.html#7630" class="Bound">i</a> <a id="7632" class="Symbol">→</a> <a id="7634" class="Symbol">(</a><a id="7635" href="Relations.Continuous.html#7592" class="Bound">𝕗</a> <a id="7637" href="Relations.Continuous.html#7630" class="Bound">i</a><a id="7638" class="Symbol">)(</a><a id="7640" href="Relations.Continuous.html#7601" class="Bound">𝕒</a> <a id="7642" href="Relations.Continuous.html#7630" class="Bound">i</a><a id="7643" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → 𝒜 i` of `𝕒`.)


--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
