---
layout: default
title : Overture.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This is the [Overture.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="293" class="Symbol">{-#</a> <a id="297" class="Keyword">OPTIONS</a> <a id="305" class="Pragma">--without-K</a> <a id="317" class="Pragma">--exact-split</a> <a id="331" class="Pragma">--safe</a> <a id="338" class="Symbol">#-}</a>

<a id="343" class="Keyword">module</a> <a id="350" href="Overture.Lifts.html" class="Module">Overture.Lifts</a> <a id="365" class="Keyword">where</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="Overture.Inverses.html" class="Module">Overture.Inverses</a> <a id="402" class="Keyword">public</a>

</pre>

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
𝓤 ̇ : 𝓤 ⁺ ̇,   𝓤 ⁺ ̇ : 𝓤 ⁺ ⁺ ̇,  etc.
```

This means that the universe `𝓤 ̇` has type `𝓤 ⁺ ̇`, and  `𝓤 ⁺ ̇` has type  `𝓤 ⁺ ⁺ ̇`, and so on.  It is important to note, however, this does *not* imply that  `𝓤 ̇ : 𝓤 ⁺ ⁺ ̇`. In other words, Agda's universe hierarchy is *noncumulative*. This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand, a noncumulative hierarchy can sometimes make for a nonfun proof assistant. Specifically, in certain situations, the noncumulativity makes it unduly difficult to convince Agda that a program or proof is correct.

Presently, we will describe general lifting and lowering functions that help us overcome this technical issue. Later (in the [Lifts of Algebras](Algebras.Algebras.html#lifts-of-algebras) section) we provide some domain-specific analogs of these tools. We will prove some nice properties that make these effective mechanisms for resolving universe level problems when working with algebra types.

#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
𝓤 != 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

There are some general "lifting and lowering" tools that make these situations easier to deal with. These must be applied with some care to avoid making the type theory inconsistent. In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the `Level` module of the [Agda Standard Library][], is defined as follows.

<pre class="Agda">

<a id="2989" class="Keyword">record</a> <a id="Lift"></a><a id="2996" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="3001" class="Symbol">{</a><a id="3002" href="Overture.Lifts.html#3002" class="Bound">𝓦</a> <a id="3004" href="Overture.Lifts.html#3004" class="Bound">𝓤</a> <a id="3006" class="Symbol">:</a> <a id="3008" href="Universes.html#205" class="Postulate">Universe</a><a id="3016" class="Symbol">}</a> <a id="3018" class="Symbol">(</a><a id="3019" href="Overture.Lifts.html#3019" class="Bound">A</a> <a id="3021" class="Symbol">:</a> <a id="3023" href="Overture.Lifts.html#3004" class="Bound">𝓤</a> <a id="3025" href="Universes.html#403" class="Function Operator">̇</a><a id="3026" class="Symbol">)</a> <a id="3028" class="Symbol">:</a> <a id="3030" href="Overture.Lifts.html#3004" class="Bound">𝓤</a> <a id="3032" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3034" href="Overture.Lifts.html#3002" class="Bound">𝓦</a> <a id="3036" href="Universes.html#403" class="Function Operator">̇</a>  <a id="3039" class="Keyword">where</a>
 <a id="3046" class="Keyword">constructor</a> <a id="lift"></a><a id="3058" href="Overture.Lifts.html#3058" class="InductiveConstructor">lift</a>
 <a id="3064" class="Keyword">field</a> <a id="Lift.lower"></a><a id="3070" href="Overture.Lifts.html#3070" class="Field">lower</a> <a id="3076" class="Symbol">:</a> <a id="3078" href="Overture.Lifts.html#3019" class="Bound">A</a>
<a id="3080" class="Keyword">open</a> <a id="3085" href="Overture.Lifts.html#2996" class="Module">Lift</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3518" href="Overture.Lifts.html#3518" class="Function">lift∼lower</a> <a id="3529" class="Symbol">:</a> <a id="3531" class="Symbol">{</a><a id="3532" href="Overture.Lifts.html#3532" class="Bound">𝓦</a> <a id="3534" href="Overture.Lifts.html#3534" class="Bound">𝓤</a> <a id="3536" class="Symbol">:</a> <a id="3538" href="Universes.html#205" class="Postulate">Universe</a><a id="3546" class="Symbol">}{</a><a id="3548" href="Overture.Lifts.html#3548" class="Bound">A</a> <a id="3550" class="Symbol">:</a> <a id="3552" href="Overture.Lifts.html#3534" class="Bound">𝓤</a> <a id="3554" href="Universes.html#403" class="Function Operator">̇</a><a id="3555" class="Symbol">}</a> <a id="3557" class="Symbol">→</a> <a id="3559" href="Overture.Lifts.html#3058" class="InductiveConstructor">lift</a> <a id="3564" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3566" href="Overture.Lifts.html#3070" class="Field">lower</a> <a id="3572" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3574" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3577" class="Symbol">(</a><a id="3578" href="Overture.Lifts.html#2996" class="Record">Lift</a><a id="3582" class="Symbol">{</a><a id="3583" href="Overture.Lifts.html#3532" class="Bound">𝓦</a><a id="3584" class="Symbol">}</a> <a id="3586" href="Overture.Lifts.html#3548" class="Bound">A</a><a id="3587" class="Symbol">)</a>
<a id="3589" href="Overture.Lifts.html#3518" class="Function">lift∼lower</a> <a id="3600" class="Symbol">=</a> <a id="3602" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

<a id="lower∼lift"></a><a id="3608" href="Overture.Lifts.html#3608" class="Function">lower∼lift</a> <a id="3619" class="Symbol">:</a> <a id="3621" class="Symbol">{</a><a id="3622" href="Overture.Lifts.html#3622" class="Bound">𝓦</a> <a id="3624" href="Overture.Lifts.html#3624" class="Bound">𝓤</a> <a id="3626" class="Symbol">:</a> <a id="3628" href="Universes.html#205" class="Postulate">Universe</a><a id="3636" class="Symbol">}{</a><a id="3638" href="Overture.Lifts.html#3638" class="Bound">A</a> <a id="3640" class="Symbol">:</a> <a id="3642" href="Overture.Lifts.html#3624" class="Bound">𝓤</a> <a id="3644" href="Universes.html#403" class="Function Operator">̇</a><a id="3645" class="Symbol">}</a> <a id="3647" class="Symbol">→</a> <a id="3649" href="Overture.Lifts.html#3070" class="Field">lower</a><a id="3654" class="Symbol">{</a><a id="3655" href="Overture.Lifts.html#3622" class="Bound">𝓦</a><a id="3656" class="Symbol">}{</a><a id="3658" href="Overture.Lifts.html#3624" class="Bound">𝓤</a><a id="3659" class="Symbol">}</a> <a id="3661" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="3663" href="Overture.Lifts.html#3058" class="InductiveConstructor">lift</a> <a id="3668" href="MGS-MLTT.html#4207" class="Datatype Operator">≡</a> <a id="3670" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="3673" href="Overture.Lifts.html#3638" class="Bound">A</a>
<a id="3675" href="Overture.Lifts.html#3608" class="Function">lower∼lift</a> <a id="3686" class="Symbol">=</a> <a id="3688" href="MGS-MLTT.html#4221" class="InductiveConstructor">refl</a>

</pre>

The proofs are trivial. Nonetheless, we'll find a few holes that these observations can fill.

---------------

<sup>1</sup><span class="footnote" id="fn1">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


<p></p>

[← Overture.Inverses](Overture.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
