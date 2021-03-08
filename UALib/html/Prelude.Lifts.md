---
layout: default
title : Prelude.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This section presents the [UALib.Prelude.Lifts][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="311" class="Symbol">{-#</a> <a id="315" class="Keyword">OPTIONS</a> <a id="323" class="Pragma">--without-K</a> <a id="335" class="Pragma">--exact-split</a> <a id="349" class="Pragma">--safe</a> <a id="356" class="Symbol">#-}</a>

<a id="361" class="Keyword">module</a> <a id="368" href="Prelude.Lifts.html" class="Module">Prelude.Lifts</a> <a id="382" class="Keyword">where</a>

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="Prelude.Inverses.html" class="Module">Prelude.Inverses</a> <a id="418" class="Keyword">public</a>

</pre>

#### The noncumulative hierarchy

The hierarchy of universe levels in Agda looks like this:

𝓤₀ : 𝓤₁, &nbsp; 𝓤₁ : 𝓤₂, &nbsp; 𝓤₂ : 𝓤₃, …

This means that the type level of 𝓤₀ is 𝓤₁, and for each `n` The type level of 𝓤ₙ is 𝓤ₙ₊₁.

It is important to note, however, this does *not* imply that 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃, and so on.  In other words, Agda's universe hierarchy is **noncummulative**.  This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand (in this author's experience) a noncummulative hierarchy can sometimes make for a nonfun proof assistant.

Luckily, there are ways to overcome this technical issue. We describe general lifting and lowering functions below, and then later, in the section on [Lifts of algebras](https://ualib.gitlab.io/Algebras.Algebras.html#lifts-of-algebras), we'll see the domain-specific analogs of these tools which turn out to have some nice properties that make them very effective for resolving universe level problems when working with algebra datatypes.

#### Lifting and lowering

Let us be more concrete about what is at issue here by giving an example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺) <br>
when checking that the expression SP𝒦 has type <br>
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346 <br>
</samp>

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we have developed some domain specific tools for the lifting and lowering of universe levels inhabited by some of the key algebraic types of the [UALib][].  These tools must be applied with some care to avoid making the type theory inconsistent. In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the `Level` module of the [Agda Standard Library][], is defined as follows.

<pre class="Agda">

<a id="2667" class="Keyword">record</a> <a id="Lift"></a><a id="2674" href="Prelude.Lifts.html#2674" class="Record">Lift</a> <a id="2679" class="Symbol">{</a><a id="2680" href="Prelude.Lifts.html#2680" class="Bound">𝓦</a> <a id="2682" href="Prelude.Lifts.html#2682" class="Bound">𝓤</a> <a id="2684" class="Symbol">:</a> <a id="2686" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2694" class="Symbol">}</a> <a id="2696" class="Symbol">(</a><a id="2697" href="Prelude.Lifts.html#2697" class="Bound">X</a> <a id="2699" class="Symbol">:</a> <a id="2701" href="Prelude.Lifts.html#2682" class="Bound">𝓤</a> <a id="2703" href="Universes.html#403" class="Function Operator">̇</a><a id="2704" class="Symbol">)</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="Prelude.Lifts.html#2682" class="Bound">𝓤</a> <a id="2710" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2712" href="Prelude.Lifts.html#2680" class="Bound">𝓦</a> <a id="2714" href="Universes.html#403" class="Function Operator">̇</a>  <a id="2717" class="Keyword">where</a>
 <a id="2724" class="Keyword">constructor</a> <a id="lift"></a><a id="2736" href="Prelude.Lifts.html#2736" class="InductiveConstructor">lift</a>
 <a id="2742" class="Keyword">field</a> <a id="Lift.lower"></a><a id="2748" href="Prelude.Lifts.html#2748" class="Field">lower</a> <a id="2754" class="Symbol">:</a> <a id="2756" href="Prelude.Lifts.html#2697" class="Bound">X</a>
<a id="2758" class="Keyword">open</a> <a id="2763" href="Prelude.Lifts.html#2674" class="Module">Lift</a>

</pre>


<pre class="Agda">

<a id="2796" class="Comment">-- Next, we give various ways to lift function types.</a>
<a id="2850" class="Comment">-- module _ {𝓦 𝓧 𝓨 : Universe} where</a>

<a id="2888" class="Comment">--  lift-dom : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓦}{𝓧} X → Y)</a>
<a id="2953" class="Comment">--  lift-dom f = λ x → (f (lower x))</a>

<a id="2991" class="Comment">--  lift-cod : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (X → Lift{𝓦}{𝓨} Y)</a>
<a id="3056" class="Comment">--  lift-cod f = λ x → lift (f x)</a>


<a id="3092" class="Comment">-- module _ {𝓦 𝓩 𝓧 𝓨 : Universe} where</a>

<a id="3132" class="Comment">--  lift-fun : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓦}{𝓧} X → Lift{𝓩}{𝓨} Y)</a>
<a id="3208" class="Comment">--  lift-fun f = λ x → lift (f (lower x))</a>

<a id="3251" class="Comment">-- For example, `lift-dom` takes a function `f` defined on the domain `X : 𝓧 ̇` and returns a function defined on the domain `Lift{𝓦}{𝓧} X : 𝓧 ⊔ 𝓦 ̇`, whose type lives in the universe `𝓧 ⊔ 𝓦`.</a>

</pre>

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Later, there will be some situations that require this fact, as well as its brother, so we formalize these related and their trivial proofs.

<pre class="Agda">

<a id="lift∼lower"></a><a id="3958" href="Prelude.Lifts.html#3958" class="Function">lift∼lower</a> <a id="3969" class="Symbol">:</a> <a id="3971" class="Symbol">{</a><a id="3972" href="Prelude.Lifts.html#3972" class="Bound">𝓦</a> <a id="3974" href="Prelude.Lifts.html#3974" class="Bound">𝓧</a> <a id="3976" class="Symbol">:</a> <a id="3978" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3986" class="Symbol">}{</a><a id="3988" href="Prelude.Lifts.html#3988" class="Bound">X</a> <a id="3990" class="Symbol">:</a> <a id="3992" href="Prelude.Lifts.html#3974" class="Bound">𝓧</a> <a id="3994" href="Universes.html#403" class="Function Operator">̇</a><a id="3995" class="Symbol">}</a> <a id="3997" class="Symbol">→</a> <a id="3999" href="Prelude.Lifts.html#2736" class="InductiveConstructor">lift</a> <a id="4004" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="4006" href="Prelude.Lifts.html#2748" class="Field">lower</a> <a id="4012" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="4014" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="4017" class="Symbol">(</a><a id="4018" href="Prelude.Lifts.html#2674" class="Record">Lift</a><a id="4022" class="Symbol">{</a><a id="4023" href="Prelude.Lifts.html#3972" class="Bound">𝓦</a><a id="4024" class="Symbol">}{</a><a id="4026" href="Prelude.Lifts.html#3974" class="Bound">𝓧</a><a id="4027" class="Symbol">}</a> <a id="4029" href="Prelude.Lifts.html#3988" class="Bound">X</a><a id="4030" class="Symbol">)</a>
<a id="4032" href="Prelude.Lifts.html#3958" class="Function">lift∼lower</a> <a id="4043" class="Symbol">=</a> <a id="4045" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

<a id="lower∼lift"></a><a id="4051" href="Prelude.Lifts.html#4051" class="Function">lower∼lift</a> <a id="4062" class="Symbol">:</a> <a id="4064" class="Symbol">{</a><a id="4065" href="Prelude.Lifts.html#4065" class="Bound">𝓦</a> <a id="4067" href="Prelude.Lifts.html#4067" class="Bound">𝓧</a> <a id="4069" class="Symbol">:</a> <a id="4071" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4079" class="Symbol">}{</a><a id="4081" href="Prelude.Lifts.html#4081" class="Bound">X</a> <a id="4083" class="Symbol">:</a> <a id="4085" href="Prelude.Lifts.html#4067" class="Bound">𝓧</a> <a id="4087" href="Universes.html#403" class="Function Operator">̇</a><a id="4088" class="Symbol">}</a> <a id="4090" class="Symbol">→</a> <a id="4092" href="Prelude.Lifts.html#2748" class="Field">lower</a><a id="4097" class="Symbol">{</a><a id="4098" href="Prelude.Lifts.html#4065" class="Bound">𝓦</a><a id="4099" class="Symbol">}{</a><a id="4101" href="Prelude.Lifts.html#4067" class="Bound">𝓧</a><a id="4102" class="Symbol">}</a> <a id="4104" href="MGS-MLTT.html#3813" class="Function Operator">∘</a> <a id="4106" href="Prelude.Lifts.html#2736" class="InductiveConstructor">lift</a> <a id="4111" href="Prelude.Equality.html#1231" class="Datatype Operator">≡</a> <a id="4113" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a> <a id="4116" href="Prelude.Lifts.html#4081" class="Bound">X</a>
<a id="4118" href="Prelude.Lifts.html#4051" class="Function">lower∼lift</a> <a id="4129" class="Symbol">=</a> <a id="4131" href="Prelude.Equality.html#1245" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>


---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
