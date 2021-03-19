---
layout: default
title : UALib.Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="unary-relations">Discrete Relations</a>

This section presents the [UALib.Relations.Discrete][] module of the [Agda Universal Algebra Library][], which covers *unary* and *binary relations*.  We refer to these as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* we introduce in the next module ([Relations.Continuous][]). We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).

<pre class="Agda">

<a id="720" class="Symbol">{-#</a> <a id="724" class="Keyword">OPTIONS</a> <a id="732" class="Pragma">--without-K</a> <a id="744" class="Pragma">--exact-split</a> <a id="758" class="Pragma">--safe</a> <a id="765" class="Symbol">#-}</a>

<a id="770" class="Keyword">module</a> <a id="777" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="796" class="Keyword">where</a>

<a id="803" class="Keyword">open</a> <a id="808" class="Keyword">import</a> <a id="815" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="829" class="Keyword">public</a>

</pre>

#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : 𝓤 ̇`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>
(which is similar to the one found in the `Relation/Unary.agda` file of the [Agda Standard Library][]).

<pre class="Agda">

<a id="1628" class="Keyword">module</a> <a id="1635" href="Relations.Discrete.html#1635" class="Module">_</a> <a id="1637" class="Symbol">{</a><a id="1638" href="Relations.Discrete.html#1638" class="Bound">𝓤</a> <a id="1640" class="Symbol">:</a> <a id="1642" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1650" class="Symbol">}</a> <a id="1652" class="Keyword">where</a>

 <a id="1660" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="1665" class="Symbol">:</a> <a id="1667" href="Relations.Discrete.html#1638" class="Bound">𝓤</a> <a id="1669" href="Universes.html#403" class="Function Operator">̇</a> <a id="1671" class="Symbol">→</a> <a id="1673" class="Symbol">(</a><a id="1674" href="Relations.Discrete.html#1674" class="Bound">𝓦</a> <a id="1676" class="Symbol">:</a> <a id="1678" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1686" class="Symbol">)</a> <a id="1688" class="Symbol">→</a> <a id="1690" href="Relations.Discrete.html#1638" class="Bound">𝓤</a> <a id="1692" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1694" href="Relations.Discrete.html#1674" class="Bound">𝓦</a> <a id="1696" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1698" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="1701" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="1706" href="Relations.Discrete.html#1706" class="Bound">A</a> <a id="1708" href="Relations.Discrete.html#1708" class="Bound">𝓦</a> <a id="1710" class="Symbol">=</a> <a id="1712" href="Relations.Discrete.html#1706" class="Bound">A</a> <a id="1714" class="Symbol">→</a> <a id="1716" href="Relations.Discrete.html#1708" class="Bound">𝓦</a> <a id="1718" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `𝓤 ̇`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

Like the [Agda Standard Library][], the [UALib][] includes types that represent the *element inclusion* and *subset inclusion* relations from set theory. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The definition of `∈` is standard. Nonetheless, here it is.<sup>[1]</sup>

<pre class="Agda">

<a id="2500" class="Keyword">module</a> <a id="2507" href="Relations.Discrete.html#2507" class="Module">_</a> <a id="2509" class="Symbol">{</a><a id="2510" href="Relations.Discrete.html#2510" class="Bound">𝓧</a> <a id="2512" href="Relations.Discrete.html#2512" class="Bound">𝓨</a> <a id="2514" class="Symbol">:</a> <a id="2516" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2524" class="Symbol">}</a> <a id="2526" class="Symbol">{</a><a id="2527" href="Relations.Discrete.html#2527" class="Bound">A</a> <a id="2529" class="Symbol">:</a> <a id="2531" href="Relations.Discrete.html#2510" class="Bound">𝓧</a> <a id="2533" href="Universes.html#403" class="Function Operator">̇</a> <a id="2535" class="Symbol">}</a> <a id="2537" class="Keyword">where</a>

 <a id="2545" href="Relations.Discrete.html#2545" class="Function Operator">_∈_</a> <a id="2549" class="Symbol">:</a> <a id="2551" href="Relations.Discrete.html#2527" class="Bound">A</a> <a id="2553" class="Symbol">→</a> <a id="2555" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="2560" href="Relations.Discrete.html#2527" class="Bound">A</a> <a id="2562" href="Relations.Discrete.html#2512" class="Bound">𝓨</a> <a id="2564" class="Symbol">→</a> <a id="2566" href="Relations.Discrete.html#2512" class="Bound">𝓨</a> <a id="2568" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2571" href="Relations.Discrete.html#2571" class="Bound">x</a> <a id="2573" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="2575" href="Relations.Discrete.html#2575" class="Bound">P</a> <a id="2577" class="Symbol">=</a> <a id="2579" href="Relations.Discrete.html#2575" class="Bound">P</a> <a id="2581" href="Relations.Discrete.html#2571" class="Bound">x</a>

</pre>

The "subset" relation is denoted, as usual, with the `⊆` symbol (cf. `Relation/Unary.agda` in the [Agda Standard Library][]).

<pre class="Agda">

<a id="2737" class="Keyword">module</a> <a id="2744" href="Relations.Discrete.html#2744" class="Module">_</a> <a id="2746" class="Symbol">{</a><a id="2747" href="Relations.Discrete.html#2747" class="Bound">𝓧</a> <a id="2749" href="Relations.Discrete.html#2749" class="Bound">𝓨</a> <a id="2751" href="Relations.Discrete.html#2751" class="Bound">𝓩</a> <a id="2753" class="Symbol">:</a> <a id="2755" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2763" class="Symbol">}{</a><a id="2765" href="Relations.Discrete.html#2765" class="Bound">A</a> <a id="2767" class="Symbol">:</a> <a id="2769" href="Relations.Discrete.html#2747" class="Bound">𝓧</a> <a id="2771" href="Universes.html#403" class="Function Operator">̇</a> <a id="2773" class="Symbol">}</a> <a id="2775" class="Keyword">where</a>

 <a id="2783" href="Relations.Discrete.html#2783" class="Function Operator">_⊆_</a> <a id="2787" class="Symbol">:</a> <a id="2789" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="2794" href="Relations.Discrete.html#2765" class="Bound">A</a> <a id="2796" href="Relations.Discrete.html#2749" class="Bound">𝓨</a> <a id="2798" class="Symbol">→</a> <a id="2800" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="2805" href="Relations.Discrete.html#2765" class="Bound">A</a> <a id="2807" href="Relations.Discrete.html#2751" class="Bound">𝓩</a> <a id="2809" class="Symbol">→</a> <a id="2811" href="Relations.Discrete.html#2747" class="Bound">𝓧</a> <a id="2813" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2815" href="Relations.Discrete.html#2749" class="Bound">𝓨</a> <a id="2817" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2819" href="Relations.Discrete.html#2751" class="Bound">𝓩</a> <a id="2821" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2824" href="Relations.Discrete.html#2824" class="Bound">P</a> <a id="2826" href="Relations.Discrete.html#2783" class="Function Operator">⊆</a> <a id="2828" href="Relations.Discrete.html#2828" class="Bound">Q</a> <a id="2830" class="Symbol">=</a> <a id="2832" class="Symbol">∀</a> <a id="2834" class="Symbol">{</a><a id="2835" href="Relations.Discrete.html#2835" class="Bound">x</a><a id="2836" class="Symbol">}</a> <a id="2838" class="Symbol">→</a> <a id="2840" href="Relations.Discrete.html#2835" class="Bound">x</a> <a id="2842" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="2844" href="Relations.Discrete.html#2824" class="Bound">P</a> <a id="2846" class="Symbol">→</a> <a id="2848" href="Relations.Discrete.html#2835" class="Bound">x</a> <a id="2850" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="2852" href="Relations.Discrete.html#2828" class="Bound">Q</a>

 <a id="2856" class="Keyword">infix</a> <a id="2862" class="Number">4</a> <a id="2864" href="Relations.Discrete.html#2783" class="Function Operator">_⊆_</a>


</pre>

#### <a id="the-extensionality-axiom">The axiom of extensionality</a>

In type theory everything is represented as a type and, as we have just seen, this includes subsets.  Equality of types is a nontrivial matter, and thus so is equality of subsets when represented as unary predicates.  Fortunately, it is straightforward to write down the type that represents what we typically means in informal mathematics for two subsets to be equal. In the [UALib][] we denote this type by `≐` and define it as follows.<sup>[2](Relations.Discrete.html#fn2)</sup>

<pre class="Agda">

<a id="3450" class="Keyword">module</a> <a id="3457" href="Relations.Discrete.html#3457" class="Module">_</a> <a id="3459" class="Symbol">{</a><a id="3460" href="Relations.Discrete.html#3460" class="Bound">𝓧</a> <a id="3462" href="Relations.Discrete.html#3462" class="Bound">𝓨</a> <a id="3464" href="Relations.Discrete.html#3464" class="Bound">𝓩</a> <a id="3466" class="Symbol">:</a> <a id="3468" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3476" class="Symbol">}{</a><a id="3478" href="Relations.Discrete.html#3478" class="Bound">A</a> <a id="3480" class="Symbol">:</a> <a id="3482" href="Relations.Discrete.html#3460" class="Bound">𝓧</a> <a id="3484" href="Universes.html#403" class="Function Operator">̇</a> <a id="3486" class="Symbol">}</a> <a id="3488" class="Keyword">where</a>

 <a id="3496" href="Relations.Discrete.html#3496" class="Function Operator">_≐_</a> <a id="3500" class="Symbol">:</a> <a id="3502" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="3507" href="Relations.Discrete.html#3478" class="Bound">A</a> <a id="3509" href="Relations.Discrete.html#3462" class="Bound">𝓨</a> <a id="3511" class="Symbol">→</a> <a id="3513" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="3518" href="Relations.Discrete.html#3478" class="Bound">A</a> <a id="3520" href="Relations.Discrete.html#3464" class="Bound">𝓩</a> <a id="3522" class="Symbol">→</a> <a id="3524" href="Relations.Discrete.html#3460" class="Bound">𝓧</a> <a id="3526" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3528" href="Relations.Discrete.html#3462" class="Bound">𝓨</a> <a id="3530" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3532" href="Relations.Discrete.html#3464" class="Bound">𝓩</a> <a id="3534" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3537" href="Relations.Discrete.html#3537" class="Bound">P</a> <a id="3539" href="Relations.Discrete.html#3496" class="Function Operator">≐</a> <a id="3541" href="Relations.Discrete.html#3541" class="Bound">Q</a> <a id="3543" class="Symbol">=</a> <a id="3545" class="Symbol">(</a><a id="3546" href="Relations.Discrete.html#3537" class="Bound">P</a> <a id="3548" href="Relations.Discrete.html#2783" class="Function Operator">⊆</a> <a id="3550" href="Relations.Discrete.html#3541" class="Bound">Q</a><a id="3551" class="Symbol">)</a> <a id="3553" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="3555" class="Symbol">(</a><a id="3556" href="Relations.Discrete.html#3541" class="Bound">Q</a> <a id="3558" href="Relations.Discrete.html#2783" class="Function Operator">⊆</a> <a id="3560" href="Relations.Discrete.html#3537" class="Bound">P</a><a id="3561" class="Symbol">)</a>

 <a id="3565" class="Keyword">infix</a> <a id="3571" class="Number">4</a> <a id="3573" href="Relations.Discrete.html#3496" class="Function Operator">_≐_</a>

</pre>

Thus, a proof of `P ≐ Q` is a pair `(p , q)` where where `p : P ⊆ Q` and `q : Q ⊆ P` are proofs of the first and second inclusions, respectively. If `P` and `Q` are definitionally equal (i.e., `P ≡ Q`), then both `P ⊆ Q` and `Q ⊆ P` hold, so `P ≐ Q` also holds, as we now confirm.

<pre class="Agda">

<a id="3886" class="Keyword">module</a> <a id="3893" href="Relations.Discrete.html#3893" class="Module">_</a> <a id="3895" class="Symbol">{</a><a id="3896" href="Relations.Discrete.html#3896" class="Bound">𝓧</a> <a id="3898" href="Relations.Discrete.html#3898" class="Bound">𝓨</a> <a id="3900" class="Symbol">:</a> <a id="3902" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3910" class="Symbol">}{</a><a id="3912" href="Relations.Discrete.html#3912" class="Bound">A</a> <a id="3914" class="Symbol">:</a> <a id="3916" href="Relations.Discrete.html#3896" class="Bound">𝓧</a> <a id="3918" href="Universes.html#403" class="Function Operator">̇</a><a id="3919" class="Symbol">}</a> <a id="3921" class="Keyword">where</a>

 <a id="3929" href="Relations.Discrete.html#3929" class="Function">Pred-≡</a> <a id="3936" class="Symbol">:</a> <a id="3938" class="Symbol">{</a><a id="3939" href="Relations.Discrete.html#3939" class="Bound">P</a> <a id="3941" href="Relations.Discrete.html#3941" class="Bound">Q</a> <a id="3943" class="Symbol">:</a> <a id="3945" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="3950" href="Relations.Discrete.html#3912" class="Bound">A</a> <a id="3952" href="Relations.Discrete.html#3898" class="Bound">𝓨</a><a id="3953" class="Symbol">}</a> <a id="3955" class="Symbol">→</a> <a id="3957" href="Relations.Discrete.html#3939" class="Bound">P</a> <a id="3959" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="3961" href="Relations.Discrete.html#3941" class="Bound">Q</a> <a id="3963" class="Symbol">→</a> <a id="3965" href="Relations.Discrete.html#3939" class="Bound">P</a> <a id="3967" href="Relations.Discrete.html#3496" class="Function Operator">≐</a> <a id="3969" href="Relations.Discrete.html#3941" class="Bound">Q</a>
 <a id="3972" href="Relations.Discrete.html#3929" class="Function">Pred-≡</a> <a id="3979" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="3984" class="Symbol">=</a> <a id="3986" class="Symbol">(λ</a> <a id="3989" href="Relations.Discrete.html#3989" class="Bound">z</a> <a id="3991" class="Symbol">→</a> <a id="3993" href="Relations.Discrete.html#3989" class="Bound">z</a><a id="3994" class="Symbol">)</a> <a id="3996" href="Prelude.Preliminaries.html#11712" class="InductiveConstructor Operator">,</a> <a id="3998" class="Symbol">(λ</a> <a id="4001" href="Relations.Discrete.html#4001" class="Bound">z</a> <a id="4003" class="Symbol">→</a> <a id="4005" href="Relations.Discrete.html#4001" class="Bound">z</a><a id="4006" class="Symbol">)</a>

</pre>

The converse is not provable in [MLTT][]. However, we can define its type and postulate that it holds axiomatically, if we wish.  This is called the *axiom of extensionality* and a type that represents this axiom is the following.

<pre class="Agda">

<a id="4267" class="Keyword">module</a> <a id="4274" href="Relations.Discrete.html#4274" class="Module">_</a> <a id="4276" class="Symbol">{</a><a id="4277" href="Relations.Discrete.html#4277" class="Bound">𝓧</a> <a id="4279" class="Symbol">:</a> <a id="4281" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4289" class="Symbol">}</a> <a id="4291" class="Keyword">where</a>

 <a id="4299" href="Relations.Discrete.html#4299" class="Function">ext-axiom</a> <a id="4309" class="Symbol">:</a> <a id="4311" href="Relations.Discrete.html#4277" class="Bound">𝓧</a> <a id="4313" href="Universes.html#403" class="Function Operator">̇</a> <a id="4315" class="Symbol">→</a> <a id="4317" class="Symbol">(</a><a id="4318" href="Relations.Discrete.html#4318" class="Bound">𝓨</a> <a id="4320" class="Symbol">:</a> <a id="4322" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4330" class="Symbol">)</a> <a id="4332" class="Symbol">→</a> <a id="4334" href="Relations.Discrete.html#4277" class="Bound">𝓧</a> <a id="4336" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4338" href="Relations.Discrete.html#4318" class="Bound">𝓨</a> <a id="4340" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="4342" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4345" href="Relations.Discrete.html#4299" class="Function">ext-axiom</a> <a id="4355" href="Relations.Discrete.html#4355" class="Bound">A</a> <a id="4357" href="Relations.Discrete.html#4357" class="Bound">𝓨</a> <a id="4359" class="Symbol">=</a> <a id="4361" class="Symbol">∀</a> <a id="4363" class="Symbol">(</a><a id="4364" href="Relations.Discrete.html#4364" class="Bound">P</a> <a id="4366" href="Relations.Discrete.html#4366" class="Bound">Q</a> <a id="4368" class="Symbol">:</a> <a id="4370" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="4375" href="Relations.Discrete.html#4355" class="Bound">A</a> <a id="4377" href="Relations.Discrete.html#4357" class="Bound">𝓨</a><a id="4378" class="Symbol">)</a> <a id="4380" class="Symbol">→</a> <a id="4382" href="Relations.Discrete.html#4364" class="Bound">P</a> <a id="4384" href="Relations.Discrete.html#3496" class="Function Operator">≐</a> <a id="4386" href="Relations.Discrete.html#4366" class="Bound">Q</a> <a id="4388" class="Symbol">→</a> <a id="4390" href="Relations.Discrete.html#4364" class="Bound">P</a> <a id="4392" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4394" href="Relations.Discrete.html#4366" class="Bound">Q</a>

</pre>

Note that the type `ext-axiom` does not itself postulate the axiom of extensionality.  It merely defines the axiom.  If we want to postulate it, we must assume we have a witness, or inhabitant of the type. We could do this in Agda in a number of ways, but probably the easiest is to simply add the witness as a parameter to a module, like so.<sup>[3](Relations.Discrete#fn3)</sup>

<pre class="Agda">

<a id="4805" class="Keyword">module</a> <a id="ext-axiom-postulated"></a><a id="4812" href="Relations.Discrete.html#4812" class="Module">ext-axiom-postulated</a> <a id="4833" class="Symbol">{</a><a id="4834" href="Relations.Discrete.html#4834" class="Bound">𝓧</a> <a id="4836" href="Relations.Discrete.html#4836" class="Bound">𝓨</a> <a id="4838" class="Symbol">:</a> <a id="4840" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4848" class="Symbol">}{</a><a id="4850" href="Relations.Discrete.html#4850" class="Bound">A</a> <a id="4852" class="Symbol">:</a> <a id="4854" href="Relations.Discrete.html#4834" class="Bound">𝓧</a> <a id="4856" href="Universes.html#403" class="Function Operator">̇</a><a id="4857" class="Symbol">}</a> <a id="4859" class="Symbol">{</a><a id="4860" href="Relations.Discrete.html#4860" class="Bound">ea</a> <a id="4863" class="Symbol">:</a> <a id="4865" href="Relations.Discrete.html#4299" class="Function">ext-axiom</a> <a id="4875" href="Relations.Discrete.html#4850" class="Bound">A</a> <a id="4877" href="Relations.Discrete.html#4836" class="Bound">𝓨</a><a id="4878" class="Symbol">}</a> <a id="4880" class="Keyword">where</a>

</pre>

We treat other notions of extensionality in the [Relations.Truncation][] module.



#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later. The first provides convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

<pre class="Agda">

<a id="5275" class="Keyword">module</a> <a id="5282" href="Relations.Discrete.html#5282" class="Module">_</a> <a id="5284" class="Symbol">{</a><a id="5285" href="Relations.Discrete.html#5285" class="Bound">𝓧</a> <a id="5287" href="Relations.Discrete.html#5287" class="Bound">𝓨</a> <a id="5289" href="Relations.Discrete.html#5289" class="Bound">𝓩</a> <a id="5291" class="Symbol">:</a> <a id="5293" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5301" class="Symbol">}{</a><a id="5303" href="Relations.Discrete.html#5303" class="Bound">A</a> <a id="5305" class="Symbol">:</a> <a id="5307" href="Relations.Discrete.html#5285" class="Bound">𝓧</a> <a id="5309" href="Universes.html#403" class="Function Operator">̇</a> <a id="5311" class="Symbol">}</a> <a id="5313" class="Symbol">{</a><a id="5314" href="Relations.Discrete.html#5314" class="Bound">B</a> <a id="5316" class="Symbol">:</a> <a id="5318" href="Relations.Discrete.html#5287" class="Bound">𝓨</a> <a id="5320" href="Universes.html#403" class="Function Operator">̇</a> <a id="5322" class="Symbol">}</a> <a id="5324" class="Keyword">where</a>

 <a id="5332" href="Relations.Discrete.html#5332" class="Function Operator">Im_⊆_</a> <a id="5338" class="Symbol">:</a> <a id="5340" class="Symbol">(</a><a id="5341" href="Relations.Discrete.html#5303" class="Bound">A</a> <a id="5343" class="Symbol">→</a> <a id="5345" href="Relations.Discrete.html#5314" class="Bound">B</a><a id="5346" class="Symbol">)</a> <a id="5348" class="Symbol">→</a> <a id="5350" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="5355" href="Relations.Discrete.html#5314" class="Bound">B</a> <a id="5357" href="Relations.Discrete.html#5289" class="Bound">𝓩</a> <a id="5359" class="Symbol">→</a> <a id="5361" href="Relations.Discrete.html#5285" class="Bound">𝓧</a> <a id="5363" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5365" href="Relations.Discrete.html#5289" class="Bound">𝓩</a> <a id="5367" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5370" href="Relations.Discrete.html#5332" class="Function Operator">Im</a> <a id="5373" href="Relations.Discrete.html#5373" class="Bound">f</a> <a id="5375" href="Relations.Discrete.html#5332" class="Function Operator">⊆</a> <a id="5377" href="Relations.Discrete.html#5377" class="Bound">S</a> <a id="5379" class="Symbol">=</a> <a id="5381" class="Symbol">∀</a> <a id="5383" href="Relations.Discrete.html#5383" class="Bound">x</a> <a id="5385" class="Symbol">→</a> <a id="5387" href="Relations.Discrete.html#5373" class="Bound">f</a> <a id="5389" href="Relations.Discrete.html#5383" class="Bound">x</a> <a id="5391" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="5393" href="Relations.Discrete.html#5377" class="Bound">S</a>

</pre>

The following inductive type represents *disjoint union*.<sup>[4](Relations.Discrete#fn4)</sup>

<pre class="Agda">

<a id="5519" class="Keyword">data</a> <a id="_⊎_"></a><a id="5524" href="Relations.Discrete.html#5524" class="Datatype Operator">_⊎_</a> <a id="5528" class="Symbol">{</a><a id="5529" href="Relations.Discrete.html#5529" class="Bound">𝓧</a> <a id="5531" href="Relations.Discrete.html#5531" class="Bound">𝓨</a> <a id="5533" class="Symbol">:</a> <a id="5535" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5543" class="Symbol">}(</a><a id="5545" href="Relations.Discrete.html#5545" class="Bound">A</a> <a id="5547" class="Symbol">:</a> <a id="5549" href="Relations.Discrete.html#5529" class="Bound">𝓧</a> <a id="5551" href="Universes.html#403" class="Function Operator">̇</a><a id="5552" class="Symbol">)</a> <a id="5554" class="Symbol">(</a><a id="5555" href="Relations.Discrete.html#5555" class="Bound">B</a> <a id="5557" class="Symbol">:</a> <a id="5559" href="Relations.Discrete.html#5531" class="Bound">𝓨</a> <a id="5561" href="Universes.html#403" class="Function Operator">̇</a><a id="5562" class="Symbol">)</a> <a id="5564" class="Symbol">:</a> <a id="5566" href="Relations.Discrete.html#5529" class="Bound">𝓧</a> <a id="5568" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5570" href="Relations.Discrete.html#5531" class="Bound">𝓨</a> <a id="5572" href="Universes.html#403" class="Function Operator">̇</a> <a id="5574" class="Keyword">where</a>
 <a id="_⊎_.inj₁"></a><a id="5581" href="Relations.Discrete.html#5581" class="InductiveConstructor">inj₁</a> <a id="5586" class="Symbol">:</a> <a id="5588" class="Symbol">(</a><a id="5589" href="Relations.Discrete.html#5589" class="Bound">x</a> <a id="5591" class="Symbol">:</a> <a id="5593" href="Relations.Discrete.html#5545" class="Bound">A</a><a id="5594" class="Symbol">)</a> <a id="5596" class="Symbol">→</a> <a id="5598" href="Relations.Discrete.html#5545" class="Bound">A</a> <a id="5600" href="Relations.Discrete.html#5524" class="Datatype Operator">⊎</a> <a id="5602" href="Relations.Discrete.html#5555" class="Bound">B</a>
 <a id="_⊎_.inj₂"></a><a id="5605" href="Relations.Discrete.html#5605" class="InductiveConstructor">inj₂</a> <a id="5610" class="Symbol">:</a> <a id="5612" class="Symbol">(</a><a id="5613" href="Relations.Discrete.html#5613" class="Bound">y</a> <a id="5615" class="Symbol">:</a> <a id="5617" href="Relations.Discrete.html#5555" class="Bound">B</a><a id="5618" class="Symbol">)</a> <a id="5620" class="Symbol">→</a> <a id="5622" href="Relations.Discrete.html#5545" class="Bound">A</a> <a id="5624" href="Relations.Discrete.html#5524" class="Datatype Operator">⊎</a> <a id="5626" href="Relations.Discrete.html#5555" class="Bound">B</a>

</pre>

And this can be used to represent *union*, as follows.

<pre class="Agda">

<a id="_∪_"></a><a id="5711" href="Relations.Discrete.html#5711" class="Function Operator">_∪_</a> <a id="5715" class="Symbol">:</a> <a id="5717" class="Symbol">{</a><a id="5718" href="Relations.Discrete.html#5718" class="Bound">𝓧</a> <a id="5720" href="Relations.Discrete.html#5720" class="Bound">𝓨</a> <a id="5722" href="Relations.Discrete.html#5722" class="Bound">𝓩</a> <a id="5724" class="Symbol">:</a> <a id="5726" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5734" class="Symbol">}{</a><a id="5736" href="Relations.Discrete.html#5736" class="Bound">A</a> <a id="5738" class="Symbol">:</a> <a id="5740" href="Relations.Discrete.html#5718" class="Bound">𝓧</a> <a id="5742" href="Universes.html#403" class="Function Operator">̇</a><a id="5743" class="Symbol">}</a> <a id="5745" class="Symbol">→</a> <a id="5747" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="5752" href="Relations.Discrete.html#5736" class="Bound">A</a> <a id="5754" href="Relations.Discrete.html#5720" class="Bound">𝓨</a> <a id="5756" class="Symbol">→</a> <a id="5758" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="5763" href="Relations.Discrete.html#5736" class="Bound">A</a> <a id="5765" href="Relations.Discrete.html#5722" class="Bound">𝓩</a> <a id="5767" class="Symbol">→</a> <a id="5769" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="5774" href="Relations.Discrete.html#5736" class="Bound">A</a> <a id="5776" class="Symbol">_</a>
<a id="5778" href="Relations.Discrete.html#5778" class="Bound">P</a> <a id="5780" href="Relations.Discrete.html#5711" class="Function Operator">∪</a> <a id="5782" href="Relations.Discrete.html#5782" class="Bound">Q</a> <a id="5784" class="Symbol">=</a> <a id="5786" class="Symbol">λ</a> <a id="5788" href="Relations.Discrete.html#5788" class="Bound">x</a> <a id="5790" class="Symbol">→</a> <a id="5792" href="Relations.Discrete.html#5788" class="Bound">x</a> <a id="5794" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="5796" href="Relations.Discrete.html#5778" class="Bound">P</a> <a id="5798" href="Relations.Discrete.html#5524" class="Datatype Operator">⊎</a> <a id="5800" href="Relations.Discrete.html#5788" class="Bound">x</a> <a id="5802" href="Relations.Discrete.html#2545" class="Function Operator">∈</a> <a id="5804" href="Relations.Discrete.html#5782" class="Bound">Q</a>

<a id="5807" class="Keyword">infixr</a> <a id="5814" class="Number">1</a> <a id="5816" href="Relations.Discrete.html#5524" class="Datatype Operator">_⊎_</a> <a id="5820" href="Relations.Discrete.html#5711" class="Function Operator">_∪_</a>

</pre>

The *empty set* is naturally represented by the *empty type*, `𝟘`, and the latter is defined in the `MGS-MLTT` module of the [Type Topology][] library.

<pre class="Agda">

<a id="6004" class="Keyword">open</a> <a id="6009" class="Keyword">import</a> <a id="6016" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="6025" class="Keyword">using</a> <a id="6031" class="Symbol">(</a><a id="6032" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="6033" class="Symbol">)</a>

<a id="∅"></a><a id="6036" href="Relations.Discrete.html#6036" class="Function">∅</a> <a id="6038" class="Symbol">:</a> <a id="6040" class="Symbol">{</a><a id="6041" href="Relations.Discrete.html#6041" class="Bound">𝓧</a> <a id="6043" class="Symbol">:</a> <a id="6045" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6053" class="Symbol">}{</a><a id="6055" href="Relations.Discrete.html#6055" class="Bound">A</a> <a id="6057" class="Symbol">:</a> <a id="6059" href="Relations.Discrete.html#6041" class="Bound">𝓧</a> <a id="6061" href="Universes.html#403" class="Function Operator">̇</a><a id="6062" class="Symbol">}</a> <a id="6064" class="Symbol">→</a> <a id="6066" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="6071" href="Relations.Discrete.html#6055" class="Bound">A</a> <a id="6073" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="6076" href="Relations.Discrete.html#6036" class="Function">∅</a> <a id="6078" class="Symbol">=</a> <a id="6080" class="Symbol">λ</a> <a id="6082" href="Relations.Discrete.html#6082" class="Bound">_</a> <a id="6084" class="Symbol">→</a> <a id="6086" href="MGS-MLTT.html#712" class="Function">𝟘</a>

</pre>

Before closing our little predicates toolbox, let's insert a type that provides a natural way to represent *singletons*.

<pre class="Agda">

<a id="｛_｝"></a><a id="6237" href="Relations.Discrete.html#6237" class="Function Operator">｛_｝</a> <a id="6241" class="Symbol">:</a> <a id="6243" class="Symbol">{</a><a id="6244" href="Relations.Discrete.html#6244" class="Bound">𝓧</a> <a id="6246" class="Symbol">:</a> <a id="6248" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6256" class="Symbol">}{</a><a id="6258" href="Relations.Discrete.html#6258" class="Bound">A</a> <a id="6260" class="Symbol">:</a> <a id="6262" href="Relations.Discrete.html#6244" class="Bound">𝓧</a> <a id="6264" href="Universes.html#403" class="Function Operator">̇</a><a id="6265" class="Symbol">}</a> <a id="6267" class="Symbol">→</a> <a id="6269" href="Relations.Discrete.html#6258" class="Bound">A</a> <a id="6271" class="Symbol">→</a> <a id="6273" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="6278" href="Relations.Discrete.html#6258" class="Bound">A</a> <a id="6280" class="Symbol">_</a>
<a id="6282" href="Relations.Discrete.html#6237" class="Function Operator">｛</a> <a id="6284" href="Relations.Discrete.html#6284" class="Bound">x</a> <a id="6286" href="Relations.Discrete.html#6237" class="Function Operator">｝</a> <a id="6288" class="Symbol">=</a> <a id="6290" href="Relations.Discrete.html#6284" class="Bound">x</a> <a id="6292" href="Prelude.Equality.html#1398" class="Datatype Operator">≡_</a>

</pre>


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → 𝓡 ̇` (for some universe 𝓡). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → 𝓡 ̇`, while a binary relation should have type `A → (A → 𝓡 ̇)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

<pre class="Agda">

<a id="7015" class="Keyword">module</a> <a id="7022" href="Relations.Discrete.html#7022" class="Module">_</a> <a id="7024" class="Symbol">{</a><a id="7025" href="Relations.Discrete.html#7025" class="Bound">𝓤</a> <a id="7027" href="Relations.Discrete.html#7027" class="Bound">𝓡</a> <a id="7029" class="Symbol">:</a> <a id="7031" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7039" class="Symbol">}</a> <a id="7041" class="Keyword">where</a>

 <a id="7049" href="Relations.Discrete.html#7049" class="Function">REL</a> <a id="7053" class="Symbol">:</a> <a id="7055" href="Relations.Discrete.html#7025" class="Bound">𝓤</a> <a id="7057" href="Universes.html#403" class="Function Operator">̇</a> <a id="7059" class="Symbol">→</a> <a id="7061" href="Relations.Discrete.html#7027" class="Bound">𝓡</a> <a id="7063" href="Universes.html#403" class="Function Operator">̇</a> <a id="7065" class="Symbol">→</a> <a id="7067" class="Symbol">(</a><a id="7068" href="Relations.Discrete.html#7068" class="Bound">𝓝</a> <a id="7070" class="Symbol">:</a> <a id="7072" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7080" class="Symbol">)</a> <a id="7082" class="Symbol">→</a> <a id="7084" class="Symbol">(</a><a id="7085" href="Relations.Discrete.html#7025" class="Bound">𝓤</a> <a id="7087" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7089" href="Relations.Discrete.html#7027" class="Bound">𝓡</a> <a id="7091" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7093" href="Relations.Discrete.html#7068" class="Bound">𝓝</a> <a id="7095" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a><a id="7096" class="Symbol">)</a> <a id="7098" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7101" href="Relations.Discrete.html#7049" class="Function">REL</a> <a id="7105" href="Relations.Discrete.html#7105" class="Bound">A</a> <a id="7107" href="Relations.Discrete.html#7107" class="Bound">B</a> <a id="7109" href="Relations.Discrete.html#7109" class="Bound">𝓝</a> <a id="7111" class="Symbol">=</a> <a id="7113" href="Relations.Discrete.html#7105" class="Bound">A</a> <a id="7115" class="Symbol">→</a> <a id="7117" href="Relations.Discrete.html#7107" class="Bound">B</a> <a id="7119" class="Symbol">→</a> <a id="7121" href="Relations.Discrete.html#7109" class="Bound">𝓝</a> <a id="7123" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

In the special case, where `𝓤 ≡ 𝓡` and `A ≡ B`, we have

<pre class="Agda">

<a id="7209" class="Keyword">module</a> <a id="7216" href="Relations.Discrete.html#7216" class="Module">_</a> <a id="7218" class="Symbol">{</a><a id="7219" href="Relations.Discrete.html#7219" class="Bound">𝓤</a> <a id="7221" class="Symbol">:</a> <a id="7223" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7231" class="Symbol">}</a> <a id="7233" class="Keyword">where</a>

 <a id="7241" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="7245" class="Symbol">:</a> <a id="7247" href="Relations.Discrete.html#7219" class="Bound">𝓤</a> <a id="7249" href="Universes.html#403" class="Function Operator">̇</a> <a id="7251" class="Symbol">→</a> <a id="7253" class="Symbol">(</a><a id="7254" href="Relations.Discrete.html#7254" class="Bound">𝓝</a> <a id="7256" class="Symbol">:</a> <a id="7258" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7266" class="Symbol">)</a> <a id="7268" class="Symbol">→</a> <a id="7270" href="Relations.Discrete.html#7219" class="Bound">𝓤</a> <a id="7272" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7274" href="Relations.Discrete.html#7254" class="Bound">𝓝</a> <a id="7276" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="7278" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7281" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="7285" href="Relations.Discrete.html#7285" class="Bound">A</a> <a id="7287" href="Relations.Discrete.html#7287" class="Bound">𝓝</a> <a id="7289" class="Symbol">=</a> <a id="7291" href="Relations.Discrete.html#7049" class="Function">REL</a> <a id="7295" href="Relations.Discrete.html#7285" class="Bound">A</a> <a id="7297" href="Relations.Discrete.html#7285" class="Bound">A</a> <a id="7299" href="Relations.Discrete.html#7287" class="Bound">𝓝</a>

</pre>


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


<pre class="Agda">

<a id="7742" class="Keyword">module</a> <a id="7749" href="Relations.Discrete.html#7749" class="Module">_</a> <a id="7751" class="Symbol">{</a><a id="7752" href="Relations.Discrete.html#7752" class="Bound">𝓤</a> <a id="7754" href="Relations.Discrete.html#7754" class="Bound">𝓡</a> <a id="7756" class="Symbol">:</a> <a id="7758" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="7766" class="Symbol">}{</a><a id="7768" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7770" class="Symbol">:</a> <a id="7772" href="Relations.Discrete.html#7752" class="Bound">𝓤</a> <a id="7774" href="Universes.html#403" class="Function Operator">̇</a><a id="7775" class="Symbol">}{</a><a id="7777" href="Relations.Discrete.html#7777" class="Bound">B</a> <a id="7779" class="Symbol">:</a> <a id="7781" href="Relations.Discrete.html#7754" class="Bound">𝓡</a> <a id="7783" href="Universes.html#403" class="Function Operator">̇</a><a id="7784" class="Symbol">}</a> <a id="7786" class="Keyword">where</a>

 <a id="7794" href="Relations.Discrete.html#7794" class="Function">ker</a> <a id="7798" class="Symbol">:</a> <a id="7800" class="Symbol">(</a><a id="7801" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7803" class="Symbol">→</a> <a id="7805" href="Relations.Discrete.html#7777" class="Bound">B</a><a id="7806" class="Symbol">)</a> <a id="7808" class="Symbol">→</a> <a id="7810" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="7814" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7816" href="Relations.Discrete.html#7754" class="Bound">𝓡</a>
 <a id="7819" href="Relations.Discrete.html#7794" class="Function">ker</a> <a id="7823" href="Relations.Discrete.html#7823" class="Bound">g</a> <a id="7825" href="Relations.Discrete.html#7825" class="Bound">x</a> <a id="7827" href="Relations.Discrete.html#7827" class="Bound">y</a> <a id="7829" class="Symbol">=</a> <a id="7831" href="Relations.Discrete.html#7823" class="Bound">g</a> <a id="7833" href="Relations.Discrete.html#7825" class="Bound">x</a> <a id="7835" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="7837" href="Relations.Discrete.html#7823" class="Bound">g</a> <a id="7839" href="Relations.Discrete.html#7827" class="Bound">y</a>

 <a id="7843" href="Relations.Discrete.html#7843" class="Function">kernel</a> <a id="7850" class="Symbol">:</a> <a id="7852" class="Symbol">(</a><a id="7853" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7855" class="Symbol">→</a> <a id="7857" href="Relations.Discrete.html#7777" class="Bound">B</a><a id="7858" class="Symbol">)</a> <a id="7860" class="Symbol">→</a> <a id="7862" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="7867" class="Symbol">(</a><a id="7868" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7870" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="7872" href="Relations.Discrete.html#7768" class="Bound">A</a><a id="7873" class="Symbol">)</a> <a id="7875" href="Relations.Discrete.html#7754" class="Bound">𝓡</a>
 <a id="7878" href="Relations.Discrete.html#7843" class="Function">kernel</a> <a id="7885" href="Relations.Discrete.html#7885" class="Bound">g</a> <a id="7887" class="Symbol">(</a><a id="7888" href="Relations.Discrete.html#7888" class="Bound">x</a> <a id="7890" href="Prelude.Preliminaries.html#11712" class="InductiveConstructor Operator">,</a> <a id="7892" href="Relations.Discrete.html#7892" class="Bound">y</a><a id="7893" class="Symbol">)</a> <a id="7895" class="Symbol">=</a> <a id="7897" href="Relations.Discrete.html#7885" class="Bound">g</a> <a id="7899" href="Relations.Discrete.html#7888" class="Bound">x</a> <a id="7901" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="7903" href="Relations.Discrete.html#7885" class="Bound">g</a> <a id="7905" href="Relations.Discrete.html#7892" class="Bound">y</a>

 <a id="7909" href="Relations.Discrete.html#7909" class="Function">ker-sigma</a> <a id="7919" class="Symbol">:</a> <a id="7921" class="Symbol">(</a><a id="7922" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7924" class="Symbol">→</a> <a id="7926" href="Relations.Discrete.html#7777" class="Bound">B</a><a id="7927" class="Symbol">)</a> <a id="7929" class="Symbol">→</a> <a id="7931" href="Relations.Discrete.html#7752" class="Bound">𝓤</a> <a id="7933" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7935" href="Relations.Discrete.html#7754" class="Bound">𝓡</a> <a id="7937" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7940" href="Relations.Discrete.html#7909" class="Function">ker-sigma</a> <a id="7950" href="Relations.Discrete.html#7950" class="Bound">g</a> <a id="7952" class="Symbol">=</a> <a id="7954" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="7956" href="Relations.Discrete.html#7956" class="Bound">x</a> <a id="7958" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="7960" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7962" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="7964" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="7966" href="Relations.Discrete.html#7966" class="Bound">y</a> <a id="7968" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="7970" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="7972" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="7974" href="Relations.Discrete.html#7950" class="Bound">g</a> <a id="7976" href="Relations.Discrete.html#7956" class="Bound">x</a> <a id="7978" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="7980" href="Relations.Discrete.html#7950" class="Bound">g</a> <a id="7982" href="Relations.Discrete.html#7966" class="Bound">y</a>

 <a id="7986" href="Relations.Discrete.html#7986" class="Function">ker-sigma&#39;</a> <a id="7997" class="Symbol">:</a> <a id="7999" class="Symbol">(</a><a id="8000" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="8002" class="Symbol">→</a> <a id="8004" href="Relations.Discrete.html#7777" class="Bound">B</a><a id="8005" class="Symbol">)</a> <a id="8007" class="Symbol">→</a> <a id="8009" href="Relations.Discrete.html#7752" class="Bound">𝓤</a> <a id="8011" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8013" href="Relations.Discrete.html#7754" class="Bound">𝓡</a> <a id="8015" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8018" href="Relations.Discrete.html#7986" class="Function">ker-sigma&#39;</a> <a id="8029" href="Relations.Discrete.html#8029" class="Bound">g</a> <a id="8031" class="Symbol">=</a> <a id="8033" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8035" href="Relations.Discrete.html#8035" class="Bound">(x</a> <a id="8038" href="Relations.Discrete.html#8035" class="Bound">,</a> <a id="8040" href="Relations.Discrete.html#8035" class="Bound">y)</a> <a id="8043" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8045" class="Symbol">(</a><a id="8046" href="Relations.Discrete.html#7768" class="Bound">A</a> <a id="8048" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="8050" href="Relations.Discrete.html#7768" class="Bound">A</a><a id="8051" class="Symbol">)</a> <a id="8053" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8055" href="Relations.Discrete.html#8029" class="Bound">g</a> <a id="8057" href="Relations.Discrete.html#8036" class="Bound">x</a> <a id="8059" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8061" href="Relations.Discrete.html#8029" class="Bound">g</a> <a id="8063" href="Relations.Discrete.html#8040" class="Bound">y</a>

</pre>


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.

<pre class="Agda">

<a id="8252" class="Keyword">module</a> <a id="8259" href="Relations.Discrete.html#8259" class="Module">_</a> <a id="8261" class="Symbol">{</a><a id="8262" href="Relations.Discrete.html#8262" class="Bound">𝓤</a> <a id="8264" class="Symbol">:</a> <a id="8266" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="8274" class="Symbol">}{</a><a id="8276" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8278" class="Symbol">:</a> <a id="8280" href="Relations.Discrete.html#8262" class="Bound">𝓤</a> <a id="8282" href="Universes.html#403" class="Function Operator">̇</a> <a id="8284" class="Symbol">}</a> <a id="8286" class="Keyword">where</a>

 <a id="8294" href="Relations.Discrete.html#8294" class="Function">𝟎</a> <a id="8296" class="Symbol">:</a> <a id="8298" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="8302" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8304" href="Relations.Discrete.html#8262" class="Bound">𝓤</a>
 <a id="8307" href="Relations.Discrete.html#8294" class="Function">𝟎</a> <a id="8309" href="Relations.Discrete.html#8309" class="Bound">a</a> <a id="8311" href="Relations.Discrete.html#8311" class="Bound">b</a> <a id="8313" class="Symbol">=</a> <a id="8315" href="Relations.Discrete.html#8309" class="Bound">a</a> <a id="8317" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8319" href="Relations.Discrete.html#8311" class="Bound">b</a>

 <a id="8323" href="Relations.Discrete.html#8323" class="Function">𝟎-pred</a> <a id="8330" class="Symbol">:</a> <a id="8332" href="Relations.Discrete.html#1660" class="Function">Pred</a> <a id="8337" class="Symbol">(</a><a id="8338" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8340" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="8342" href="Relations.Discrete.html#8276" class="Bound">A</a><a id="8343" class="Symbol">)</a> <a id="8345" href="Relations.Discrete.html#8262" class="Bound">𝓤</a>
 <a id="8348" href="Relations.Discrete.html#8323" class="Function">𝟎-pred</a> <a id="8355" class="Symbol">(</a><a id="8356" href="Relations.Discrete.html#8356" class="Bound">a</a> <a id="8358" href="Prelude.Preliminaries.html#11712" class="InductiveConstructor Operator">,</a> <a id="8360" href="Relations.Discrete.html#8360" class="Bound">a&#39;</a><a id="8362" class="Symbol">)</a> <a id="8364" class="Symbol">=</a> <a id="8366" href="Relations.Discrete.html#8356" class="Bound">a</a> <a id="8368" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8370" href="Relations.Discrete.html#8360" class="Bound">a&#39;</a>

 <a id="8375" href="Relations.Discrete.html#8375" class="Function">𝟎-sigma</a> <a id="8383" class="Symbol">:</a> <a id="8385" href="Relations.Discrete.html#8262" class="Bound">𝓤</a> <a id="8387" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8390" href="Relations.Discrete.html#8375" class="Function">𝟎-sigma</a> <a id="8398" class="Symbol">=</a> <a id="8400" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8402" href="Relations.Discrete.html#8402" class="Bound">a</a> <a id="8404" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8406" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8408" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8410" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8412" href="Relations.Discrete.html#8412" class="Bound">b</a> <a id="8414" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8416" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8418" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8420" href="Relations.Discrete.html#8402" class="Bound">a</a> <a id="8422" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8424" href="Relations.Discrete.html#8412" class="Bound">b</a>

 <a id="8428" href="Relations.Discrete.html#8428" class="Function">𝟎-sigma&#39;</a> <a id="8437" class="Symbol">:</a> <a id="8439" href="Relations.Discrete.html#8262" class="Bound">𝓤</a> <a id="8441" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8444" href="Relations.Discrete.html#8428" class="Function">𝟎-sigma&#39;</a> <a id="8453" class="Symbol">=</a> <a id="8455" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8457" href="Relations.Discrete.html#8457" class="Bound">(x</a> <a id="8460" href="Relations.Discrete.html#8457" class="Bound">,</a> <a id="8462" href="Relations.Discrete.html#8457" class="Bound">y)</a> <a id="8465" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8467" class="Symbol">(</a><a id="8468" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8470" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="8472" href="Relations.Discrete.html#8276" class="Bound">A</a><a id="8473" class="Symbol">)</a> <a id="8475" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8477" href="Relations.Discrete.html#8458" class="Bound">x</a> <a id="8479" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="8481" href="Relations.Discrete.html#8462" class="Bound">y</a>

</pre>

The *total relation* over `A`, which in set theory is the full Cartesian product `A × A`, could be represented using the one-element type from the `MGS-MLTT` module of [Type Topology][], as follows.

<pre class="Agda">

 <a id="8711" class="Keyword">open</a> <a id="8716" class="Keyword">import</a> <a id="8723" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="8732" class="Keyword">using</a> <a id="8738" class="Symbol">(</a><a id="8739" href="MGS-MLTT.html#408" class="Function">𝟙</a><a id="8740" class="Symbol">)</a>

 <a id="8744" href="Relations.Discrete.html#8744" class="Function">𝟏</a> <a id="8746" class="Symbol">:</a> <a id="8748" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="8752" href="Relations.Discrete.html#8276" class="Bound">A</a> <a id="8754" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
 <a id="8758" href="Relations.Discrete.html#8744" class="Function">𝟏</a> <a id="8760" href="Relations.Discrete.html#8760" class="Bound">a</a> <a id="8762" href="Relations.Discrete.html#8762" class="Bound">b</a> <a id="8764" class="Symbol">=</a> <a id="8766" href="MGS-MLTT.html#408" class="Function">𝟙</a>
</pre>



#### <a id="implication">Implication</a>

We denote and define implication for binary predicates (relations) as follows. (These are borrowed from the [Agda Standard Library][]; we have merely translated them into [Type Topology][]/[UALib][] notation.)

<pre class="Agda">

<a id="9049" class="Keyword">module</a> <a id="9056" href="Relations.Discrete.html#9056" class="Module">_</a> <a id="9058" class="Symbol">{</a><a id="9059" href="Relations.Discrete.html#9059" class="Bound">𝓧</a> <a id="9061" href="Relations.Discrete.html#9061" class="Bound">𝓨</a> <a id="9063" href="Relations.Discrete.html#9063" class="Bound">𝓩</a> <a id="9065" class="Symbol">:</a> <a id="9067" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9075" class="Symbol">}{</a><a id="9077" href="Relations.Discrete.html#9077" class="Bound">A</a> <a id="9079" class="Symbol">:</a> <a id="9081" href="Relations.Discrete.html#9059" class="Bound">𝓧</a> <a id="9083" href="Universes.html#403" class="Function Operator">̇</a><a id="9084" class="Symbol">}{</a><a id="9086" href="Relations.Discrete.html#9086" class="Bound">B</a> <a id="9088" class="Symbol">:</a> <a id="9090" href="Relations.Discrete.html#9061" class="Bound">𝓨</a> <a id="9092" href="Universes.html#403" class="Function Operator">̇</a><a id="9093" class="Symbol">}{</a><a id="9095" href="Relations.Discrete.html#9095" class="Bound">C</a> <a id="9097" class="Symbol">:</a> <a id="9099" href="Relations.Discrete.html#9063" class="Bound">𝓩</a> <a id="9101" href="Universes.html#403" class="Function Operator">̇</a><a id="9102" class="Symbol">}</a> <a id="9104" class="Keyword">where</a>

 <a id="9112" href="Relations.Discrete.html#9112" class="Function Operator">_on_</a> <a id="9117" class="Symbol">:</a> <a id="9119" class="Symbol">(</a><a id="9120" href="Relations.Discrete.html#9086" class="Bound">B</a> <a id="9122" class="Symbol">→</a> <a id="9124" href="Relations.Discrete.html#9086" class="Bound">B</a> <a id="9126" class="Symbol">→</a> <a id="9128" href="Relations.Discrete.html#9095" class="Bound">C</a><a id="9129" class="Symbol">)</a> <a id="9131" class="Symbol">→</a> <a id="9133" class="Symbol">(</a><a id="9134" href="Relations.Discrete.html#9077" class="Bound">A</a> <a id="9136" class="Symbol">→</a> <a id="9138" href="Relations.Discrete.html#9086" class="Bound">B</a><a id="9139" class="Symbol">)</a> <a id="9141" class="Symbol">→</a> <a id="9143" class="Symbol">(</a><a id="9144" href="Relations.Discrete.html#9077" class="Bound">A</a> <a id="9146" class="Symbol">→</a> <a id="9148" href="Relations.Discrete.html#9077" class="Bound">A</a> <a id="9150" class="Symbol">→</a> <a id="9152" href="Relations.Discrete.html#9095" class="Bound">C</a><a id="9153" class="Symbol">)</a>
 <a id="9156" href="Relations.Discrete.html#9156" class="Bound">R</a> <a id="9158" href="Relations.Discrete.html#9112" class="Function Operator">on</a> <a id="9161" href="Relations.Discrete.html#9161" class="Bound">g</a> <a id="9163" class="Symbol">=</a> <a id="9165" class="Symbol">λ</a> <a id="9167" href="Relations.Discrete.html#9167" class="Bound">x</a> <a id="9169" href="Relations.Discrete.html#9169" class="Bound">y</a> <a id="9171" class="Symbol">→</a> <a id="9173" href="Relations.Discrete.html#9156" class="Bound">R</a> <a id="9175" class="Symbol">(</a><a id="9176" href="Relations.Discrete.html#9161" class="Bound">g</a> <a id="9178" href="Relations.Discrete.html#9167" class="Bound">x</a><a id="9179" class="Symbol">)</a> <a id="9181" class="Symbol">(</a><a id="9182" href="Relations.Discrete.html#9161" class="Bound">g</a> <a id="9184" href="Relations.Discrete.html#9169" class="Bound">y</a><a id="9185" class="Symbol">)</a>


<a id="9189" class="Keyword">module</a> <a id="9196" href="Relations.Discrete.html#9196" class="Module">_</a> <a id="9198" class="Symbol">{</a><a id="9199" href="Relations.Discrete.html#9199" class="Bound">𝓦</a> <a id="9201" href="Relations.Discrete.html#9201" class="Bound">𝓧</a> <a id="9203" href="Relations.Discrete.html#9203" class="Bound">𝓨</a> <a id="9205" href="Relations.Discrete.html#9205" class="Bound">𝓩</a> <a id="9207" class="Symbol">:</a> <a id="9209" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9217" class="Symbol">}{</a><a id="9219" href="Relations.Discrete.html#9219" class="Bound">A</a> <a id="9221" class="Symbol">:</a> <a id="9223" href="Relations.Discrete.html#9199" class="Bound">𝓦</a> <a id="9225" href="Universes.html#403" class="Function Operator">̇</a> <a id="9227" class="Symbol">}</a> <a id="9229" class="Symbol">{</a><a id="9230" href="Relations.Discrete.html#9230" class="Bound">B</a> <a id="9232" class="Symbol">:</a> <a id="9234" href="Relations.Discrete.html#9201" class="Bound">𝓧</a> <a id="9236" href="Universes.html#403" class="Function Operator">̇</a> <a id="9238" class="Symbol">}</a> <a id="9240" class="Keyword">where</a>

 <a id="9248" href="Relations.Discrete.html#9248" class="Function Operator">_⇒_</a> <a id="9252" class="Symbol">:</a> <a id="9254" href="Relations.Discrete.html#7049" class="Function">REL</a> <a id="9258" href="Relations.Discrete.html#9219" class="Bound">A</a> <a id="9260" href="Relations.Discrete.html#9230" class="Bound">B</a> <a id="9262" href="Relations.Discrete.html#9203" class="Bound">𝓨</a> <a id="9264" class="Symbol">→</a> <a id="9266" href="Relations.Discrete.html#7049" class="Function">REL</a> <a id="9270" href="Relations.Discrete.html#9219" class="Bound">A</a> <a id="9272" href="Relations.Discrete.html#9230" class="Bound">B</a> <a id="9274" href="Relations.Discrete.html#9205" class="Bound">𝓩</a> <a id="9276" class="Symbol">→</a> <a id="9278" href="Relations.Discrete.html#9199" class="Bound">𝓦</a> <a id="9280" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9282" href="Relations.Discrete.html#9201" class="Bound">𝓧</a> <a id="9284" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9286" href="Relations.Discrete.html#9203" class="Bound">𝓨</a> <a id="9288" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9290" href="Relations.Discrete.html#9205" class="Bound">𝓩</a> <a id="9292" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9295" href="Relations.Discrete.html#9295" class="Bound">P</a> <a id="9297" href="Relations.Discrete.html#9248" class="Function Operator">⇒</a> <a id="9299" href="Relations.Discrete.html#9299" class="Bound">Q</a> <a id="9301" class="Symbol">=</a> <a id="9303" class="Symbol">∀</a> <a id="9305" class="Symbol">{</a><a id="9306" href="Relations.Discrete.html#9306" class="Bound">i</a> <a id="9308" href="Relations.Discrete.html#9308" class="Bound">j</a><a id="9309" class="Symbol">}</a> <a id="9311" class="Symbol">→</a> <a id="9313" href="Relations.Discrete.html#9295" class="Bound">P</a> <a id="9315" href="Relations.Discrete.html#9306" class="Bound">i</a> <a id="9317" href="Relations.Discrete.html#9308" class="Bound">j</a> <a id="9319" class="Symbol">→</a> <a id="9321" href="Relations.Discrete.html#9299" class="Bound">Q</a> <a id="9323" href="Relations.Discrete.html#9306" class="Bound">i</a> <a id="9325" href="Relations.Discrete.html#9308" class="Bound">j</a>

 <a id="9329" class="Keyword">infixr</a> <a id="9336" class="Number">4</a> <a id="9338" href="Relations.Discrete.html#9248" class="Function Operator">_⇒_</a>

</pre>

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.

<pre class="Agda">

<a id="9452" class="Keyword">module</a> <a id="9459" href="Relations.Discrete.html#9459" class="Module">_</a> <a id="9461" class="Symbol">{</a><a id="9462" href="Relations.Discrete.html#9462" class="Bound">𝓦</a> <a id="9464" href="Relations.Discrete.html#9464" class="Bound">𝓧</a> <a id="9466" href="Relations.Discrete.html#9466" class="Bound">𝓨</a> <a id="9468" href="Relations.Discrete.html#9468" class="Bound">𝓩</a> <a id="9470" class="Symbol">:</a> <a id="9472" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9480" class="Symbol">}{</a><a id="9482" href="Relations.Discrete.html#9482" class="Bound">A</a> <a id="9484" class="Symbol">:</a> <a id="9486" href="Relations.Discrete.html#9462" class="Bound">𝓦</a> <a id="9488" href="Universes.html#403" class="Function Operator">̇</a> <a id="9490" class="Symbol">}</a> <a id="9492" class="Symbol">{</a><a id="9493" href="Relations.Discrete.html#9493" class="Bound">B</a> <a id="9495" class="Symbol">:</a> <a id="9497" href="Relations.Discrete.html#9464" class="Bound">𝓧</a> <a id="9499" href="Universes.html#403" class="Function Operator">̇</a> <a id="9501" class="Symbol">}</a> <a id="9503" class="Keyword">where</a>

 <a id="9511" href="Relations.Discrete.html#9511" class="Function Operator">_=[_]⇒_</a> <a id="9519" class="Symbol">:</a> <a id="9521" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="9525" href="Relations.Discrete.html#9482" class="Bound">A</a> <a id="9527" href="Relations.Discrete.html#9466" class="Bound">𝓨</a> <a id="9529" class="Symbol">→</a> <a id="9531" class="Symbol">(</a><a id="9532" href="Relations.Discrete.html#9482" class="Bound">A</a> <a id="9534" class="Symbol">→</a> <a id="9536" href="Relations.Discrete.html#9493" class="Bound">B</a><a id="9537" class="Symbol">)</a> <a id="9539" class="Symbol">→</a> <a id="9541" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="9545" href="Relations.Discrete.html#9493" class="Bound">B</a> <a id="9547" href="Relations.Discrete.html#9468" class="Bound">𝓩</a> <a id="9549" class="Symbol">→</a> <a id="9551" href="Relations.Discrete.html#9462" class="Bound">𝓦</a> <a id="9553" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9555" href="Relations.Discrete.html#9466" class="Bound">𝓨</a> <a id="9557" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9559" href="Relations.Discrete.html#9468" class="Bound">𝓩</a> <a id="9561" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9564" href="Relations.Discrete.html#9564" class="Bound">P</a> <a id="9566" href="Relations.Discrete.html#9511" class="Function Operator">=[</a> <a id="9569" href="Relations.Discrete.html#9569" class="Bound">g</a> <a id="9571" href="Relations.Discrete.html#9511" class="Function Operator">]⇒</a> <a id="9574" href="Relations.Discrete.html#9574" class="Bound">Q</a> <a id="9576" class="Symbol">=</a> <a id="9578" href="Relations.Discrete.html#9564" class="Bound">P</a> <a id="9580" href="Relations.Discrete.html#9248" class="Function Operator">⇒</a> <a id="9582" class="Symbol">(</a><a id="9583" href="Relations.Discrete.html#9574" class="Bound">Q</a> <a id="9585" href="Relations.Discrete.html#9112" class="Function Operator">on</a> <a id="9588" href="Relations.Discrete.html#9569" class="Bound">g</a><a id="9589" class="Symbol">)</a>

 <a id="9593" class="Keyword">infixr</a> <a id="9600" class="Number">4</a> <a id="9602" href="Relations.Discrete.html#9511" class="Function Operator">_=[_]⇒_</a>

</pre>


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

Before discussing general and dependent relations, we pause to define some types that are useful for asserting and proving facts about *compatibility* of functions with binary relations. The first definition simply lifts a binary relation on `A` to a binary relation on tuples of type `I → A`. N.B. This is not to be confused with the sort of (universe) lifting that we defined in the [Prelude.Lifts][] module.

<pre class="Agda">

<a id="10136" class="Keyword">module</a> <a id="10143" href="Relations.Discrete.html#10143" class="Module">_</a> <a id="10145" class="Symbol">{</a><a id="10146" href="Relations.Discrete.html#10146" class="Bound">𝓤</a> <a id="10148" href="Relations.Discrete.html#10148" class="Bound">𝓥</a> <a id="10150" href="Relations.Discrete.html#10150" class="Bound">𝓦</a> <a id="10152" class="Symbol">:</a> <a id="10154" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="10162" class="Symbol">}{</a><a id="10164" href="Relations.Discrete.html#10164" class="Bound">I</a> <a id="10166" class="Symbol">:</a> <a id="10168" href="Relations.Discrete.html#10148" class="Bound">𝓥</a> <a id="10170" href="Universes.html#403" class="Function Operator">̇</a><a id="10171" class="Symbol">}{</a><a id="10173" href="Relations.Discrete.html#10173" class="Bound">A</a> <a id="10175" class="Symbol">:</a> <a id="10177" href="Relations.Discrete.html#10146" class="Bound">𝓤</a> <a id="10179" href="Universes.html#403" class="Function Operator">̇</a><a id="10180" class="Symbol">}</a> <a id="10182" class="Keyword">where</a>

 <a id="10190" href="Relations.Discrete.html#10190" class="Function">lift-rel</a> <a id="10199" class="Symbol">:</a> <a id="10201" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="10205" href="Relations.Discrete.html#10173" class="Bound">A</a> <a id="10207" href="Relations.Discrete.html#10150" class="Bound">𝓦</a> <a id="10209" class="Symbol">→</a> <a id="10211" class="Symbol">(</a><a id="10212" href="Relations.Discrete.html#10164" class="Bound">I</a> <a id="10214" class="Symbol">→</a> <a id="10216" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10217" class="Symbol">)</a> <a id="10219" class="Symbol">→</a> <a id="10221" class="Symbol">(</a><a id="10222" href="Relations.Discrete.html#10164" class="Bound">I</a> <a id="10224" class="Symbol">→</a> <a id="10226" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10227" class="Symbol">)</a> <a id="10229" class="Symbol">→</a> <a id="10231" href="Relations.Discrete.html#10148" class="Bound">𝓥</a> <a id="10233" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10235" href="Relations.Discrete.html#10150" class="Bound">𝓦</a> <a id="10237" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10240" href="Relations.Discrete.html#10190" class="Function">lift-rel</a> <a id="10249" href="Relations.Discrete.html#10249" class="Bound">R</a> <a id="10251" href="Relations.Discrete.html#10251" class="Bound">u</a> <a id="10253" href="Relations.Discrete.html#10253" class="Bound">v</a> <a id="10255" class="Symbol">=</a> <a id="10257" class="Symbol">∀</a> <a id="10259" href="Relations.Discrete.html#10259" class="Bound">i</a> <a id="10261" class="Symbol">→</a> <a id="10263" href="Relations.Discrete.html#10249" class="Bound">R</a> <a id="10265" class="Symbol">(</a><a id="10266" href="Relations.Discrete.html#10251" class="Bound">u</a> <a id="10268" href="Relations.Discrete.html#10259" class="Bound">i</a><a id="10269" class="Symbol">)</a> <a id="10271" class="Symbol">(</a><a id="10272" href="Relations.Discrete.html#10253" class="Bound">v</a> <a id="10274" href="Relations.Discrete.html#10259" class="Bound">i</a><a id="10275" class="Symbol">)</a>

 <a id="10279" href="Relations.Discrete.html#10279" class="Function">compatible-fun</a> <a id="10294" class="Symbol">:</a> <a id="10296" class="Symbol">(</a><a id="10297" href="Relations.Discrete.html#10297" class="Bound">f</a> <a id="10299" class="Symbol">:</a> <a id="10301" class="Symbol">(</a><a id="10302" href="Relations.Discrete.html#10164" class="Bound">I</a> <a id="10304" class="Symbol">→</a> <a id="10306" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10307" class="Symbol">)</a> <a id="10309" class="Symbol">→</a> <a id="10311" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10312" class="Symbol">)(</a><a id="10314" href="Relations.Discrete.html#10314" class="Bound">R</a> <a id="10316" class="Symbol">:</a> <a id="10318" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="10322" href="Relations.Discrete.html#10173" class="Bound">A</a> <a id="10324" href="Relations.Discrete.html#10150" class="Bound">𝓦</a><a id="10325" class="Symbol">)</a> <a id="10327" class="Symbol">→</a> <a id="10329" href="Relations.Discrete.html#10148" class="Bound">𝓥</a> <a id="10331" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10333" href="Relations.Discrete.html#10146" class="Bound">𝓤</a> <a id="10335" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10337" href="Relations.Discrete.html#10150" class="Bound">𝓦</a> <a id="10339" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10342" href="Relations.Discrete.html#10279" class="Function">compatible-fun</a> <a id="10357" href="Relations.Discrete.html#10357" class="Bound">f</a> <a id="10359" href="Relations.Discrete.html#10359" class="Bound">R</a>  <a id="10362" class="Symbol">=</a> <a id="10364" class="Symbol">(</a><a id="10365" href="Relations.Discrete.html#10190" class="Function">lift-rel</a> <a id="10374" href="Relations.Discrete.html#10359" class="Bound">R</a><a id="10375" class="Symbol">)</a> <a id="10377" href="Relations.Discrete.html#9511" class="Function Operator">=[</a> <a id="10380" href="Relations.Discrete.html#10357" class="Bound">f</a> <a id="10382" href="Relations.Discrete.html#9511" class="Function Operator">]⇒</a> <a id="10385" href="Relations.Discrete.html#10359" class="Bound">R</a>

</pre>

We used the slick implication notation in the definition of `compatible-fun`, but we could have defined it more explicitly, like so.

<pre class="Agda">

 <a id="10549" href="Relations.Discrete.html#10549" class="Function">compatible-fun&#39;</a> <a id="10565" class="Symbol">:</a> <a id="10567" class="Symbol">(</a><a id="10568" href="Relations.Discrete.html#10568" class="Bound">f</a> <a id="10570" class="Symbol">:</a> <a id="10572" class="Symbol">(</a><a id="10573" href="Relations.Discrete.html#10164" class="Bound">I</a> <a id="10575" class="Symbol">→</a> <a id="10577" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10578" class="Symbol">)</a> <a id="10580" class="Symbol">→</a> <a id="10582" href="Relations.Discrete.html#10173" class="Bound">A</a><a id="10583" class="Symbol">)(</a><a id="10585" href="Relations.Discrete.html#10585" class="Bound">R</a> <a id="10587" class="Symbol">:</a> <a id="10589" href="Relations.Discrete.html#7241" class="Function">Rel</a> <a id="10593" href="Relations.Discrete.html#10173" class="Bound">A</a> <a id="10595" href="Relations.Discrete.html#10150" class="Bound">𝓦</a><a id="10596" class="Symbol">)</a> <a id="10598" class="Symbol">→</a> <a id="10600" href="Relations.Discrete.html#10148" class="Bound">𝓥</a> <a id="10602" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10604" href="Relations.Discrete.html#10146" class="Bound">𝓤</a> <a id="10606" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10608" href="Relations.Discrete.html#10150" class="Bound">𝓦</a> <a id="10610" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10613" href="Relations.Discrete.html#10549" class="Function">compatible-fun&#39;</a> <a id="10629" href="Relations.Discrete.html#10629" class="Bound">f</a> <a id="10631" href="Relations.Discrete.html#10631" class="Bound">R</a>  <a id="10634" class="Symbol">=</a> <a id="10636" class="Symbol">∀</a> <a id="10638" href="Relations.Discrete.html#10638" class="Bound">u</a> <a id="10640" href="Relations.Discrete.html#10640" class="Bound">v</a> <a id="10642" class="Symbol">→</a> <a id="10644" class="Symbol">(</a><a id="10645" href="Relations.Discrete.html#10190" class="Function">lift-rel</a> <a id="10654" href="Relations.Discrete.html#10631" class="Bound">R</a><a id="10655" class="Symbol">)</a> <a id="10657" href="Relations.Discrete.html#10638" class="Bound">u</a> <a id="10659" href="Relations.Discrete.html#10640" class="Bound">v</a> <a id="10661" class="Symbol">→</a> <a id="10663" href="Relations.Discrete.html#10631" class="Bound">R</a> <a id="10665" class="Symbol">(</a><a id="10666" href="Relations.Discrete.html#10629" class="Bound">f</a> <a id="10668" href="Relations.Discrete.html#10638" class="Bound">u</a><a id="10669" class="Symbol">)</a> <a id="10671" class="Symbol">(</a><a id="10672" href="Relations.Discrete.html#10629" class="Bound">f</a> <a id="10674" href="Relations.Discrete.html#10640" class="Bound">v</a><a id="10675" class="Symbol">)</a>

</pre>

However, this is a rare case in which the more elegant syntax may result in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2">In [agda2-mode][] type `\doteq` or `\.=` to produce `≐`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn4">**Unicode Hint**. In [agda2-mode][] type `\u+` or `\uplus` to produce the symbol `⊎`.</span>



<p></p>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}


<!-- not used

 open import MGS-MLTT using (¬) public

 _∉_ : A → Pred A 𝓨 → 𝓨 ̇
 x ∉ P = ¬ (x ∈ P)

 infix 4 _∈_ _∉_

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where
 _⊇_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ⊇ Q = Q ⊆ P
 infix 4 _⊇_

 Pred-≡→⊇ : {P Q : Pred A 𝓨} → P ≡ Q → (P ⊇ Q)
 Pred-≡→⊇ refl = (λ z → z)


-- img : {𝓧 : Universe}{X Y : 𝓧 ̇ }(f : X → Y)(P : Pred Y 𝓧) → Im f ⊆ P → X → Σ P
-- img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁


-- module _ {𝓧 𝓨 : Universe}{A : 𝓧 ̇} where

--  Pred-refl : {P Q : Pred A 𝓨} → P ≡ Q → (a : A) → a ∈ P → a ∈ Q
--  Pred-refl refl _ = λ z → z

--  Pred-≡→⊆ : {P Q : Pred A 𝓨} → P ≡ Q → (P ⊆ Q)
--  Pred-≡→⊆ refl = (λ z → z)


We close the predicates toolbox with the following pair of useful transport lemmas.


module _ {𝓧 𝓨 : Universe}{A : 𝓧 ̇ } where

 cong-app-pred : {B₁ B₂ : Pred A 𝓨}(x : A) → x ∈ B₁ → B₁ ≡ B₂ → x ∈ B₂
 cong-app-pred x B₁x refl = B₁x

 cong-pred : {B : Pred A 𝓨}(x y : A) → x ∈ B → x ≡ y → y ∈ B
 cong-pred x .x Bx refl = Bx



-->



