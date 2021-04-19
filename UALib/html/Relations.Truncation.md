---
layout: default
title : Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation, Sets, Propositions</a>

This section presents the [Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss *truncation* and *h-sets* (which we just call *sets*).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

<pre class="Agda">

<a id="1097" class="Symbol">{-#</a> <a id="1101" class="Keyword">OPTIONS</a> <a id="1109" class="Pragma">--without-K</a> <a id="1121" class="Pragma">--exact-split</a> <a id="1135" class="Pragma">--safe</a> <a id="1142" class="Symbol">#-}</a>

<a id="1147" class="Keyword">module</a> <a id="1154" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="1175" class="Keyword">where</a>

<a id="1182" class="Keyword">open</a> <a id="1187" class="Keyword">import</a> <a id="1194" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1214" class="Keyword">public</a>

<a id="1222" class="Keyword">open</a> <a id="1227" class="Keyword">import</a> <a id="1234" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1243" class="Keyword">using</a> <a id="1249" class="Symbol">(</a><a id="1250" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="1253" class="Symbol">)</a> <a id="1255" class="Keyword">public</a>

</pre>

#### <a id="truncation">Truncation</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `A` and an identity relation `_≡₀_` on `A` so that, given two inhabitants of `A`, say, `a b : A`, we can form the type `a ≡₀ b`. Suppose `p` and `q` inhabit the type `a ≡₀ b`; that is, `p` and `q` are proofs of `a ≡₀ b`, in which case we write `p q : a ≡₀ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡₀`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡₀ b` are the same.
If such a proof exists for all `p q : a ≡₀ b`, then the proof of `a ≡₀ b` is unique; as a property of
the types `A` and `≡₀`, this is sometimes called <a id="uniqueness-of-identity-proofs">*uniqueness of identity proofs*</a> (uip).

Now, perhaps we have two proofs, say, `r s : p ≡₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

<pre class="Agda">

<a id="3474" class="Keyword">module</a> <a id="hide-is-set"></a><a id="3481" href="Relations.Truncation.html#3481" class="Module">hide-is-set</a> <a id="3493" class="Symbol">{</a><a id="3494" href="Relations.Truncation.html#3494" class="Bound">𝓤</a> <a id="3496" class="Symbol">:</a> <a id="3498" href="Universes.html#205" class="Postulate">Universe</a><a id="3506" class="Symbol">}</a> <a id="3508" class="Keyword">where</a>

 <a id="hide-is-set.is-set"></a><a id="3516" href="Relations.Truncation.html#3516" class="Function">is-set</a> <a id="3523" class="Symbol">:</a> <a id="3525" href="Relations.Truncation.html#3494" class="Bound">𝓤</a> <a id="3527" href="Universes.html#403" class="Function Operator">̇</a> <a id="3529" class="Symbol">→</a> <a id="3531" href="Relations.Truncation.html#3494" class="Bound">𝓤</a> <a id="3533" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3536" href="Relations.Truncation.html#3516" class="Function">is-set</a> <a id="3543" href="Relations.Truncation.html#3543" class="Bound">A</a> <a id="3545" class="Symbol">=</a> <a id="3547" class="Symbol">(</a><a id="3548" href="Relations.Truncation.html#3548" class="Bound">x</a> <a id="3550" href="Relations.Truncation.html#3550" class="Bound">y</a> <a id="3552" class="Symbol">:</a> <a id="3554" href="Relations.Truncation.html#3543" class="Bound">A</a><a id="3555" class="Symbol">)</a> <a id="3557" class="Symbol">→</a> <a id="3559" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="3575" class="Symbol">(</a><a id="3576" href="Relations.Truncation.html#3548" class="Bound">x</a> <a id="3578" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3580" href="Relations.Truncation.html#3550" class="Bound">y</a><a id="3581" class="Symbol">)</a>

<a id="3584" class="Keyword">open</a> <a id="3589" class="Keyword">import</a> <a id="3596" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="3611" class="Keyword">using</a> <a id="3617" class="Symbol">(</a><a id="3618" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="3624" class="Symbol">)</a> <a id="3626" class="Keyword">public</a>

</pre>

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

<pre class="Agda">

<a id="4048" class="Keyword">module</a> <a id="hide-to-Σ-≡"></a><a id="4055" href="Relations.Truncation.html#4055" class="Module">hide-to-Σ-≡</a> <a id="4067" class="Symbol">{</a><a id="4068" href="Relations.Truncation.html#4068" class="Bound">𝓤</a> <a id="4070" href="Relations.Truncation.html#4070" class="Bound">𝓦</a> <a id="4072" class="Symbol">:</a> <a id="4074" href="Universes.html#205" class="Postulate">Universe</a><a id="4082" class="Symbol">}</a> <a id="4084" class="Keyword">where</a>

 <a id="hide-to-Σ-≡.to-Σ-≡"></a><a id="4092" href="Relations.Truncation.html#4092" class="Function">to-Σ-≡</a> <a id="4099" class="Symbol">:</a> <a id="4101" class="Symbol">{</a><a id="4102" href="Relations.Truncation.html#4102" class="Bound">A</a> <a id="4104" class="Symbol">:</a> <a id="4106" href="Relations.Truncation.html#4068" class="Bound">𝓤</a> <a id="4108" href="Universes.html#403" class="Function Operator">̇</a> <a id="4110" class="Symbol">}</a> <a id="4112" class="Symbol">{</a><a id="4113" href="Relations.Truncation.html#4113" class="Bound">B</a> <a id="4115" class="Symbol">:</a> <a id="4117" href="Relations.Truncation.html#4102" class="Bound">A</a> <a id="4119" class="Symbol">→</a> <a id="4121" href="Relations.Truncation.html#4070" class="Bound">𝓦</a> <a id="4123" href="Universes.html#403" class="Function Operator">̇</a> <a id="4125" class="Symbol">}</a> <a id="4127" class="Symbol">{</a><a id="4128" href="Relations.Truncation.html#4128" class="Bound">σ</a> <a id="4130" href="Relations.Truncation.html#4130" class="Bound">τ</a> <a id="4132" class="Symbol">:</a> <a id="4134" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="4136" href="Relations.Truncation.html#4113" class="Bound">B</a><a id="4137" class="Symbol">}</a>
  <a id="4141" class="Symbol">→</a>       <a id="4149" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4151" href="Relations.Truncation.html#4151" class="Bound">p</a> <a id="4153" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4155" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4157" href="Relations.Truncation.html#4128" class="Bound">σ</a> <a id="4159" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4161" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4163" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4165" href="Relations.Truncation.html#4130" class="Bound">τ</a> <a id="4167" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4169" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4171" class="Symbol">(</a><a id="4172" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4182" href="Relations.Truncation.html#4113" class="Bound">B</a> <a id="4184" href="Relations.Truncation.html#4151" class="Bound">p</a> <a id="4186" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4188" href="Relations.Truncation.html#4128" class="Bound">σ</a> <a id="4190" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a><a id="4191" class="Symbol">)</a> <a id="4193" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4195" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4197" href="Relations.Truncation.html#4130" class="Bound">τ</a> <a id="4199" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a>
  <a id="4203" class="Symbol">→</a>       <a id="4211" href="Relations.Truncation.html#4128" class="Bound">σ</a> <a id="4213" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4215" href="Relations.Truncation.html#4130" class="Bound">τ</a>

 <a id="4219" href="Relations.Truncation.html#4092" class="Function">to-Σ-≡</a> <a id="4226" class="Symbol">(</a><a id="4227" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4232" class="Symbol">{</a><a id="4233" class="Argument">x</a> <a id="4235" class="Symbol">=</a> <a id="4237" href="Relations.Truncation.html#4237" class="Bound">x</a><a id="4238" class="Symbol">}</a> <a id="4240" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4242" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4247" class="Symbol">{</a><a id="4248" class="Argument">x</a> <a id="4250" class="Symbol">=</a> <a id="4252" href="Relations.Truncation.html#4252" class="Bound">a</a><a id="4253" class="Symbol">})</a> <a id="4256" class="Symbol">=</a> <a id="4258" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4263" class="Symbol">{</a><a id="4264" class="Argument">x</a> <a id="4266" class="Symbol">=</a> <a id="4268" class="Symbol">(</a><a id="4269" href="Relations.Truncation.html#4237" class="Bound">x</a> <a id="4271" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4273" href="Relations.Truncation.html#4252" class="Bound">a</a><a id="4274" class="Symbol">)}</a>

<a id="4278" class="Keyword">open</a> <a id="4283" class="Keyword">import</a> <a id="4290" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="4305" class="Keyword">using</a> <a id="4311" class="Symbol">(</a><a id="4312" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="4318" class="Symbol">)</a> <a id="4320" class="Keyword">public</a>

</pre>

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.

<pre class="Agda">

<a id="5235" class="Keyword">module</a> <a id="5242" href="Relations.Truncation.html#5242" class="Module">_</a> <a id="5244" class="Symbol">{</a><a id="5245" href="Relations.Truncation.html#5245" class="Bound">𝓤</a> <a id="5247" href="Relations.Truncation.html#5247" class="Bound">𝓦</a> <a id="5249" class="Symbol">:</a> <a id="5251" href="Universes.html#205" class="Postulate">Universe</a><a id="5259" class="Symbol">}{</a><a id="5261" href="Relations.Truncation.html#5261" class="Bound">A</a> <a id="5263" class="Symbol">:</a> <a id="5265" href="Relations.Truncation.html#5245" class="Bound">𝓤</a> <a id="5267" href="Universes.html#403" class="Function Operator">̇</a><a id="5268" class="Symbol">}{</a><a id="5270" href="Relations.Truncation.html#5270" class="Bound">B</a> <a id="5272" class="Symbol">:</a> <a id="5274" href="Relations.Truncation.html#5247" class="Bound">𝓦</a> <a id="5276" href="Universes.html#403" class="Function Operator">̇</a><a id="5277" class="Symbol">}</a> <a id="5279" class="Keyword">where</a>

 <a id="5287" href="Relations.Truncation.html#5287" class="Function">monic-is-embedding|Set</a> <a id="5310" class="Symbol">:</a> <a id="5312" class="Symbol">(</a><a id="5313" href="Relations.Truncation.html#5313" class="Bound">f</a> <a id="5315" class="Symbol">:</a> <a id="5317" href="Relations.Truncation.html#5261" class="Bound">A</a> <a id="5319" class="Symbol">→</a> <a id="5321" href="Relations.Truncation.html#5270" class="Bound">B</a><a id="5322" class="Symbol">)</a> <a id="5324" class="Symbol">→</a> <a id="5326" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="5333" href="Relations.Truncation.html#5270" class="Bound">B</a> <a id="5335" class="Symbol">→</a> <a id="5337" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="5343" href="Relations.Truncation.html#5313" class="Bound">f</a> <a id="5345" class="Symbol">→</a> <a id="5347" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="5360" href="Relations.Truncation.html#5313" class="Bound">f</a>

 <a id="5364" href="Relations.Truncation.html#5287" class="Function">monic-is-embedding|Set</a> <a id="5387" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5389" href="Relations.Truncation.html#5389" class="Bound">Bset</a> <a id="5394" href="Relations.Truncation.html#5394" class="Bound">fmon</a> <a id="5399" href="Relations.Truncation.html#5399" class="Bound">b</a> <a id="5401" class="Symbol">(</a><a id="5402" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5404" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5406" href="Relations.Truncation.html#5406" class="Bound">fu≡b</a><a id="5410" class="Symbol">)</a> <a id="5412" class="Symbol">(</a><a id="5413" href="Relations.Truncation.html#5413" class="Bound">v</a> <a id="5415" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5417" href="Relations.Truncation.html#5417" class="Bound">fv≡b</a><a id="5421" class="Symbol">)</a> <a id="5423" class="Symbol">=</a> <a id="5425" href="Relations.Truncation.html#5657" class="Function">γ</a>
  <a id="5429" class="Keyword">where</a>
  <a id="5437" href="Relations.Truncation.html#5437" class="Function">fuv</a> <a id="5441" class="Symbol">:</a> <a id="5443" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5445" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5447" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5449" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5451" href="Relations.Truncation.html#5413" class="Bound">v</a>
  <a id="5455" href="Relations.Truncation.html#5437" class="Function">fuv</a> <a id="5459" class="Symbol">=</a> <a id="5461" href="Overture.Equality.html#2957" class="Function">≡-trans</a> <a id="5469" href="Relations.Truncation.html#5406" class="Bound">fu≡b</a> <a id="5474" class="Symbol">(</a><a id="5475" href="Relations.Truncation.html#5417" class="Bound">fv≡b</a> <a id="5480" href="MGS-MLTT.html#6125" class="Function Operator">⁻¹</a><a id="5482" class="Symbol">)</a>

  <a id="5487" href="Relations.Truncation.html#5487" class="Function">uv</a> <a id="5490" class="Symbol">:</a> <a id="5492" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5494" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5496" href="Relations.Truncation.html#5413" class="Bound">v</a>
  <a id="5500" href="Relations.Truncation.html#5487" class="Function">uv</a> <a id="5503" class="Symbol">=</a> <a id="5505" href="Relations.Truncation.html#5394" class="Bound">fmon</a> <a id="5510" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5512" href="Relations.Truncation.html#5413" class="Bound">v</a> <a id="5514" href="Relations.Truncation.html#5437" class="Function">fuv</a>

  <a id="5521" href="Relations.Truncation.html#5521" class="Function">arg1</a> <a id="5526" class="Symbol">:</a> <a id="5528" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5530" href="Relations.Truncation.html#5530" class="Bound">p</a> <a id="5532" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5534" class="Symbol">(</a><a id="5535" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5537" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5539" href="Relations.Truncation.html#5413" class="Bound">v</a><a id="5540" class="Symbol">)</a> <a id="5542" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5544" class="Symbol">(</a><a id="5545" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5555" class="Symbol">(λ</a> <a id="5558" href="Relations.Truncation.html#5558" class="Bound">a</a> <a id="5560" class="Symbol">→</a> <a id="5562" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5564" href="Relations.Truncation.html#5558" class="Bound">a</a> <a id="5566" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5568" href="Relations.Truncation.html#5399" class="Bound">b</a><a id="5569" class="Symbol">)</a> <a id="5571" href="Relations.Truncation.html#5530" class="Bound">p</a> <a id="5573" href="Relations.Truncation.html#5406" class="Bound">fu≡b</a><a id="5577" class="Symbol">)</a> <a id="5579" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5581" href="Relations.Truncation.html#5417" class="Bound">fv≡b</a>
  <a id="5588" href="Relations.Truncation.html#5521" class="Function">arg1</a> <a id="5593" class="Symbol">=</a> <a id="5595" href="Relations.Truncation.html#5487" class="Function">uv</a> <a id="5598" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5600" href="Relations.Truncation.html#5389" class="Bound">Bset</a> <a id="5605" class="Symbol">(</a><a id="5606" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5608" href="Relations.Truncation.html#5413" class="Bound">v</a><a id="5609" class="Symbol">)</a> <a id="5611" href="Relations.Truncation.html#5399" class="Bound">b</a> <a id="5613" class="Symbol">(</a><a id="5614" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5624" class="Symbol">(λ</a> <a id="5627" href="Relations.Truncation.html#5627" class="Bound">a</a> <a id="5629" class="Symbol">→</a> <a id="5631" href="Relations.Truncation.html#5387" class="Bound">f</a> <a id="5633" href="Relations.Truncation.html#5627" class="Bound">a</a> <a id="5635" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5637" href="Relations.Truncation.html#5399" class="Bound">b</a><a id="5638" class="Symbol">)</a> <a id="5640" href="Relations.Truncation.html#5487" class="Function">uv</a> <a id="5643" href="Relations.Truncation.html#5406" class="Bound">fu≡b</a><a id="5647" class="Symbol">)</a> <a id="5649" href="Relations.Truncation.html#5417" class="Bound">fv≡b</a>

  <a id="5657" href="Relations.Truncation.html#5657" class="Function">γ</a> <a id="5659" class="Symbol">:</a> <a id="5661" href="Relations.Truncation.html#5402" class="Bound">u</a> <a id="5663" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5665" href="Relations.Truncation.html#5406" class="Bound">fu≡b</a> <a id="5670" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5672" href="Relations.Truncation.html#5413" class="Bound">v</a> <a id="5674" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5676" href="Relations.Truncation.html#5417" class="Bound">fv≡b</a>
  <a id="5683" href="Relations.Truncation.html#5657" class="Function">γ</a> <a id="5685" class="Symbol">=</a> <a id="5687" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a> <a id="5694" href="Relations.Truncation.html#5521" class="Function">arg1</a>

</pre>

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a *set* (in the sense defined above), then we add to the name of the theorem the suffix `|Set`, which calls to mind the standard mathematical notation for the restriction of a function.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

<pre class="Agda">

 <a id="6247" href="Relations.Truncation.html#6247" class="Function">embedding-iff-monic|Set</a> <a id="6271" class="Symbol">:</a> <a id="6273" class="Symbol">(</a><a id="6274" href="Relations.Truncation.html#6274" class="Bound">f</a> <a id="6276" class="Symbol">:</a> <a id="6278" href="Relations.Truncation.html#5261" class="Bound">A</a> <a id="6280" class="Symbol">→</a> <a id="6282" href="Relations.Truncation.html#5270" class="Bound">B</a><a id="6283" class="Symbol">)</a> <a id="6285" class="Symbol">→</a> <a id="6287" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="6294" href="Relations.Truncation.html#5270" class="Bound">B</a> <a id="6296" class="Symbol">→</a> <a id="6298" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="6311" href="Relations.Truncation.html#6274" class="Bound">f</a> <a id="6313" href="MGS-MLTT.html#7080" class="Function Operator">⇔</a> <a id="6315" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="6321" href="Relations.Truncation.html#6274" class="Bound">f</a>
 <a id="6324" href="Relations.Truncation.html#6247" class="Function">embedding-iff-monic|Set</a> <a id="6348" href="Relations.Truncation.html#6348" class="Bound">f</a> <a id="6350" href="Relations.Truncation.html#6350" class="Bound">Bset</a> <a id="6355" class="Symbol">=</a> <a id="6357" class="Symbol">(</a><a id="6358" href="Overture.Inverses.html#5685" class="Function">embedding-is-monic</a> <a id="6377" href="Relations.Truncation.html#6348" class="Bound">f</a><a id="6378" class="Symbol">)</a><a id="6379" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="6381" class="Symbol">(</a><a id="6382" href="Relations.Truncation.html#5287" class="Function">monic-is-embedding|Set</a> <a id="6405" href="Relations.Truncation.html#6348" class="Bound">f</a> <a id="6407" href="Relations.Truncation.html#6350" class="Bound">Bset</a><a id="6411" class="Symbol">)</a>

</pre>


#### <a id="equivalence-class-truncation">Equivalence class truncation</a>

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

In the next module ([Relations.Extensionality][]) we will define a *quotient extensionality* principle that will require a form of unique identity proofs---specifically, we will assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

<pre class="Agda">

<a id="blk-uip"></a><a id="7086" href="Relations.Truncation.html#7086" class="Function">blk-uip</a> <a id="7094" class="Symbol">:</a> <a id="7096" class="Symbol">{</a><a id="7097" href="Relations.Truncation.html#7097" class="Bound">𝓦</a> <a id="7099" href="Relations.Truncation.html#7099" class="Bound">𝓤</a> <a id="7101" class="Symbol">:</a> <a id="7103" href="Universes.html#205" class="Postulate">Universe</a><a id="7111" class="Symbol">}(</a><a id="7113" href="Relations.Truncation.html#7113" class="Bound">A</a> <a id="7115" class="Symbol">:</a> <a id="7117" href="Relations.Truncation.html#7099" class="Bound">𝓤</a> <a id="7119" href="Universes.html#403" class="Function Operator">̇</a><a id="7120" class="Symbol">)(</a><a id="7122" href="Relations.Truncation.html#7122" class="Bound">R</a> <a id="7124" class="Symbol">:</a> <a id="7126" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="7130" href="Relations.Truncation.html#7113" class="Bound">A</a> <a id="7132" href="Relations.Truncation.html#7097" class="Bound">𝓦</a> <a id="7134" class="Symbol">)</a> <a id="7136" class="Symbol">→</a> <a id="7138" href="Relations.Truncation.html#7099" class="Bound">𝓤</a> <a id="7140" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7142" href="Relations.Truncation.html#7097" class="Bound">𝓦</a> <a id="7144" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="7146" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7148" href="Relations.Truncation.html#7086" class="Function">blk-uip</a> <a id="7156" class="Symbol">{</a><a id="7157" href="Relations.Truncation.html#7157" class="Bound">𝓦</a><a id="7158" class="Symbol">}</a> <a id="7160" href="Relations.Truncation.html#7160" class="Bound">A</a> <a id="7162" href="Relations.Truncation.html#7162" class="Bound">R</a> <a id="7164" class="Symbol">=</a> <a id="7166" class="Symbol">∀</a> <a id="7168" class="Symbol">(</a><a id="7169" href="Relations.Truncation.html#7169" class="Bound">C</a> <a id="7171" class="Symbol">:</a> <a id="7173" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="7178" href="Relations.Truncation.html#7160" class="Bound">A</a> <a id="7180" href="Relations.Truncation.html#7157" class="Bound">𝓦</a><a id="7181" class="Symbol">)</a> <a id="7183" class="Symbol">→</a> <a id="7185" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="7201" class="Symbol">(</a><a id="7202" href="Relations.Quotients.html#4062" class="Function">IsBlock</a> <a id="7210" href="Relations.Truncation.html#7169" class="Bound">C</a> <a id="7212" class="Symbol">{</a><a id="7213" href="Relations.Truncation.html#7162" class="Bound">R</a><a id="7214" class="Symbol">})</a>

</pre>


----------------------------

#### <a id="general-propositions">General propositions*</a>

This section defines more general truncated predicates which we call *continuous propositions* and *dependent propositions*. Recall, above (in the [Relations.Continuous][] module) we defined types called `ContRel` and `DepRel` to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and *truncated dependent relation type*, the inhabitants of which we will call *continuous propositions* and *dependent propositions*, respectively.

<pre class="Agda">

<a id="7869" class="Keyword">module</a> <a id="7876" href="Relations.Truncation.html#7876" class="Module">_</a> <a id="7878" class="Symbol">{</a><a id="7879" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="7881" class="Symbol">:</a> <a id="7883" href="Universes.html#205" class="Postulate">Universe</a><a id="7891" class="Symbol">}{</a><a id="7893" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="7895" class="Symbol">:</a> <a id="7897" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7899" href="Universes.html#403" class="Function Operator">̇</a><a id="7900" class="Symbol">}</a> <a id="7902" class="Keyword">where</a>

 <a id="7910" class="Keyword">open</a> <a id="7915" class="Keyword">import</a> <a id="7922" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="7943" class="Keyword">using</a> <a id="7949" class="Symbol">(</a><a id="7950" href="Relations.Continuous.html#2959" class="Function">ContRel</a><a id="7957" class="Symbol">;</a> <a id="7959" href="Relations.Continuous.html#3581" class="Function">DepRel</a><a id="7965" class="Symbol">)</a>

 <a id="7969" href="Relations.Truncation.html#7969" class="Function">IsContProp</a> <a id="7980" class="Symbol">:</a> <a id="7982" class="Symbol">{</a><a id="7983" href="Relations.Truncation.html#7983" class="Bound">A</a> <a id="7985" class="Symbol">:</a> <a id="7987" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="7989" href="Universes.html#403" class="Function Operator">̇</a><a id="7990" class="Symbol">}{</a><a id="7992" href="Relations.Truncation.html#7992" class="Bound">𝓦</a> <a id="7994" class="Symbol">:</a> <a id="7996" href="Universes.html#205" class="Postulate">Universe</a><a id="8004" class="Symbol">}</a> <a id="8006" class="Symbol">→</a> <a id="8008" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="8016" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8018" href="Relations.Truncation.html#7983" class="Bound">A</a> <a id="8020" href="Relations.Truncation.html#7992" class="Bound">𝓦</a>  <a id="8023" class="Symbol">→</a> <a id="8025" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8027" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8029" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8031" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8033" href="Relations.Truncation.html#7992" class="Bound">𝓦</a> <a id="8035" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8038" href="Relations.Truncation.html#7969" class="Function">IsContProp</a> <a id="8049" class="Symbol">{</a><a id="8050" class="Argument">A</a> <a id="8052" class="Symbol">=</a> <a id="8054" href="Relations.Truncation.html#8054" class="Bound">A</a><a id="8055" class="Symbol">}</a> <a id="8057" href="Relations.Truncation.html#8057" class="Bound">P</a> <a id="8059" class="Symbol">=</a> <a id="8061" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8063" href="Relations.Truncation.html#8063" class="Bound">𝑎</a> <a id="8065" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8067" class="Symbol">(</a><a id="8068" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8070" class="Symbol">→</a> <a id="8072" href="Relations.Truncation.html#8054" class="Bound">A</a><a id="8073" class="Symbol">)</a> <a id="8075" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8077" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8093" class="Symbol">(</a><a id="8094" href="Relations.Truncation.html#8057" class="Bound">P</a> <a id="8096" href="Relations.Truncation.html#8063" class="Bound">𝑎</a><a id="8097" class="Symbol">)</a>

 <a id="8101" href="Relations.Truncation.html#8101" class="Function">ContProp</a> <a id="8110" class="Symbol">:</a> <a id="8112" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8114" href="Universes.html#403" class="Function Operator">̇</a> <a id="8116" class="Symbol">→</a> <a id="8118" class="Symbol">(</a><a id="8119" href="Relations.Truncation.html#8119" class="Bound">𝓦</a> <a id="8121" class="Symbol">:</a> <a id="8123" href="Universes.html#205" class="Postulate">Universe</a><a id="8131" class="Symbol">)</a> <a id="8133" class="Symbol">→</a> <a id="8135" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8137" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8139" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8141" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8143" href="Relations.Truncation.html#8119" class="Bound">𝓦</a> <a id="8145" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8147" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8150" href="Relations.Truncation.html#8101" class="Function">ContProp</a> <a id="8159" href="Relations.Truncation.html#8159" class="Bound">A</a> <a id="8161" href="Relations.Truncation.html#8161" class="Bound">𝓦</a> <a id="8163" class="Symbol">=</a> <a id="8165" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8167" href="Relations.Truncation.html#8167" class="Bound">P</a> <a id="8169" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8171" class="Symbol">(</a><a id="8172" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="8180" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8182" href="Relations.Truncation.html#8159" class="Bound">A</a> <a id="8184" href="Relations.Truncation.html#8161" class="Bound">𝓦</a><a id="8185" class="Symbol">)</a> <a id="8187" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8189" href="Relations.Truncation.html#7969" class="Function">IsContProp</a> <a id="8200" href="Relations.Truncation.html#8167" class="Bound">P</a>

 <a id="8204" href="Relations.Truncation.html#8204" class="Function">cont-prop-ext</a> <a id="8218" class="Symbol">:</a> <a id="8220" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8222" href="Universes.html#403" class="Function Operator">̇</a> <a id="8224" class="Symbol">→</a> <a id="8226" class="Symbol">(</a><a id="8227" href="Relations.Truncation.html#8227" class="Bound">𝓦</a> <a id="8229" class="Symbol">:</a> <a id="8231" href="Universes.html#205" class="Postulate">Universe</a><a id="8239" class="Symbol">)</a> <a id="8241" class="Symbol">→</a> <a id="8243" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8245" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8247" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8249" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8251" href="Relations.Truncation.html#8227" class="Bound">𝓦</a> <a id="8253" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8255" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8258" href="Relations.Truncation.html#8204" class="Function">cont-prop-ext</a> <a id="8272" href="Relations.Truncation.html#8272" class="Bound">A</a> <a id="8274" href="Relations.Truncation.html#8274" class="Bound">𝓦</a> <a id="8276" class="Symbol">=</a> <a id="8278" class="Symbol">{</a><a id="8279" href="Relations.Truncation.html#8279" class="Bound">P</a> <a id="8281" href="Relations.Truncation.html#8281" class="Bound">Q</a> <a id="8283" class="Symbol">:</a> <a id="8285" href="Relations.Truncation.html#8101" class="Function">ContProp</a> <a id="8294" href="Relations.Truncation.html#8272" class="Bound">A</a> <a id="8296" href="Relations.Truncation.html#8274" class="Bound">𝓦</a> <a id="8298" class="Symbol">}</a> <a id="8300" class="Symbol">→</a> <a id="8302" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8304" href="Relations.Truncation.html#8279" class="Bound">P</a> <a id="8306" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8308" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8310" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8312" href="Relations.Truncation.html#8281" class="Bound">Q</a> <a id="8314" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8316" class="Symbol">→</a> <a id="8318" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8320" href="Relations.Truncation.html#8281" class="Bound">Q</a> <a id="8322" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8324" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8326" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8328" href="Relations.Truncation.html#8279" class="Bound">P</a> <a id="8330" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8332" class="Symbol">→</a> <a id="8334" href="Relations.Truncation.html#8279" class="Bound">P</a> <a id="8336" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8338" href="Relations.Truncation.html#8281" class="Bound">Q</a>

 <a id="8342" href="Relations.Truncation.html#8342" class="Function">IsDepProp</a> <a id="8352" class="Symbol">:</a> <a id="8354" class="Symbol">{</a><a id="8355" href="Relations.Truncation.html#8355" class="Bound">I</a> <a id="8357" class="Symbol">:</a> <a id="8359" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8361" href="Universes.html#403" class="Function Operator">̇</a><a id="8362" class="Symbol">}{</a><a id="8364" href="Relations.Truncation.html#8364" class="Bound">𝒜</a> <a id="8366" class="Symbol">:</a> <a id="8368" href="Relations.Truncation.html#8355" class="Bound">I</a> <a id="8370" class="Symbol">→</a> <a id="8372" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8374" href="Universes.html#403" class="Function Operator">̇</a><a id="8375" class="Symbol">}{</a><a id="8377" href="Relations.Truncation.html#8377" class="Bound">𝓦</a> <a id="8379" class="Symbol">:</a> <a id="8381" href="Universes.html#205" class="Postulate">Universe</a><a id="8389" class="Symbol">}</a> <a id="8391" class="Symbol">→</a> <a id="8393" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="8400" href="Relations.Truncation.html#8355" class="Bound">I</a> <a id="8402" href="Relations.Truncation.html#8364" class="Bound">𝒜</a> <a id="8404" href="Relations.Truncation.html#8377" class="Bound">𝓦</a>  <a id="8407" class="Symbol">→</a> <a id="8409" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8411" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8413" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8415" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8417" href="Relations.Truncation.html#8377" class="Bound">𝓦</a> <a id="8419" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8422" href="Relations.Truncation.html#8342" class="Function">IsDepProp</a> <a id="8432" class="Symbol">{</a><a id="8433" class="Argument">I</a> <a id="8435" class="Symbol">=</a> <a id="8437" href="Relations.Truncation.html#8437" class="Bound">I</a><a id="8438" class="Symbol">}</a> <a id="8440" class="Symbol">{</a><a id="8441" href="Relations.Truncation.html#8441" class="Bound">𝒜</a><a id="8442" class="Symbol">}</a> <a id="8444" href="Relations.Truncation.html#8444" class="Bound">P</a> <a id="8446" class="Symbol">=</a> <a id="8448" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8450" href="Relations.Truncation.html#8450" class="Bound">𝑎</a> <a id="8452" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8454" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8456" href="Relations.Truncation.html#8441" class="Bound">𝒜</a> <a id="8458" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8460" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8476" class="Symbol">(</a><a id="8477" href="Relations.Truncation.html#8444" class="Bound">P</a> <a id="8479" href="Relations.Truncation.html#8450" class="Bound">𝑎</a><a id="8480" class="Symbol">)</a>

 <a id="8484" href="Relations.Truncation.html#8484" class="Function">DepProp</a> <a id="8492" class="Symbol">:</a> <a id="8494" class="Symbol">(</a><a id="8495" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8497" class="Symbol">→</a> <a id="8499" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8501" href="Universes.html#403" class="Function Operator">̇</a><a id="8502" class="Symbol">)</a> <a id="8504" class="Symbol">→</a> <a id="8506" class="Symbol">(</a><a id="8507" href="Relations.Truncation.html#8507" class="Bound">𝓦</a> <a id="8509" class="Symbol">:</a> <a id="8511" href="Universes.html#205" class="Postulate">Universe</a><a id="8519" class="Symbol">)</a> <a id="8521" class="Symbol">→</a> <a id="8523" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8525" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8527" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8529" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8531" href="Relations.Truncation.html#8507" class="Bound">𝓦</a> <a id="8533" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8535" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8538" href="Relations.Truncation.html#8484" class="Function">DepProp</a> <a id="8546" href="Relations.Truncation.html#8546" class="Bound">𝒜</a> <a id="8548" href="Relations.Truncation.html#8548" class="Bound">𝓦</a> <a id="8550" class="Symbol">=</a> <a id="8552" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8554" href="Relations.Truncation.html#8554" class="Bound">P</a> <a id="8556" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8558" class="Symbol">(</a><a id="8559" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="8566" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8568" href="Relations.Truncation.html#8546" class="Bound">𝒜</a> <a id="8570" href="Relations.Truncation.html#8548" class="Bound">𝓦</a><a id="8571" class="Symbol">)</a> <a id="8573" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8575" href="Relations.Truncation.html#8342" class="Function">IsDepProp</a> <a id="8585" href="Relations.Truncation.html#8554" class="Bound">P</a>

 <a id="8589" href="Relations.Truncation.html#8589" class="Function">dep-prop-ext</a> <a id="8602" class="Symbol">:</a> <a id="8604" class="Symbol">(</a><a id="8605" href="Relations.Truncation.html#7893" class="Bound">I</a> <a id="8607" class="Symbol">→</a> <a id="8609" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8611" href="Universes.html#403" class="Function Operator">̇</a><a id="8612" class="Symbol">)</a> <a id="8614" class="Symbol">→</a> <a id="8616" class="Symbol">(</a><a id="8617" href="Relations.Truncation.html#8617" class="Bound">𝓦</a> <a id="8619" class="Symbol">:</a> <a id="8621" href="Universes.html#205" class="Postulate">Universe</a><a id="8629" class="Symbol">)</a> <a id="8631" class="Symbol">→</a> <a id="8633" href="Relations.Truncation.html#7879" class="Bound">𝓤</a> <a id="8635" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8637" href="Relations.Truncation.html#7897" class="Bound">𝓥</a> <a id="8639" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8641" href="Relations.Truncation.html#8617" class="Bound">𝓦</a> <a id="8643" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8645" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8648" href="Relations.Truncation.html#8589" class="Function">dep-prop-ext</a> <a id="8661" href="Relations.Truncation.html#8661" class="Bound">𝒜</a> <a id="8663" href="Relations.Truncation.html#8663" class="Bound">𝓦</a> <a id="8665" class="Symbol">=</a> <a id="8667" class="Symbol">{</a><a id="8668" href="Relations.Truncation.html#8668" class="Bound">P</a> <a id="8670" href="Relations.Truncation.html#8670" class="Bound">Q</a> <a id="8672" class="Symbol">:</a> <a id="8674" href="Relations.Truncation.html#8484" class="Function">DepProp</a> <a id="8682" href="Relations.Truncation.html#8661" class="Bound">𝒜</a> <a id="8684" href="Relations.Truncation.html#8663" class="Bound">𝓦</a><a id="8685" class="Symbol">}</a> <a id="8687" class="Symbol">→</a> <a id="8689" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8691" href="Relations.Truncation.html#8668" class="Bound">P</a> <a id="8693" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8695" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8697" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8699" href="Relations.Truncation.html#8670" class="Bound">Q</a> <a id="8701" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8703" class="Symbol">→</a> <a id="8705" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8707" href="Relations.Truncation.html#8670" class="Bound">Q</a> <a id="8709" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8711" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8713" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8715" href="Relations.Truncation.html#8668" class="Bound">P</a> <a id="8717" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8719" class="Symbol">→</a> <a id="8721" href="Relations.Truncation.html#8668" class="Bound">P</a> <a id="8723" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8725" href="Relations.Truncation.html#8670" class="Bound">Q</a>

</pre>


-----------------------------------

<sup>*</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general than some of the types defined in other sections. As yet these general types are not used elsewhere in the [UALib][], so sections marked * may be safely skimmed or skipped.</span>


<sup>1</sup><span class="footnote" id="fn1"> As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

<sup>2</sup><span class="footnote" id="fn2"> See [https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality](www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality).</span>

<sup>3</sup><span class="footnote" id="fn3"> This is another example of proof-irrelevance. Indeed, if `R` is a binary proposition and we have two proofs of `R x y`, then the proofs are indistinguishable.
</span>

<br>
<br>

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Relations.Extensionality →](Relations.Extensionality.html)</span>


{% include UALib.Links.md %}















<!-- NO LONGER USED STUFF

Recall, we defined the relation `_≐_` for predicates as follows: `P ≐ Q = (P ⊆ Q) × (Q ⊆ P)`.  Therefore, if we postulate `prop-ext 𝓤 𝓦` and `P ≐ Q`, then `P ≡ Q` obviously follows. Nonetheless, let us record this observation.
<sup>3</sup><span class="footnote" id="fn3"> [Agda][] now has a type called [Prop](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html), but we have never tried to use it. It likely provides at least some of the functionality we develop here, however, our preference is to assume only a minimal MLTT foundation and build up the types we need ourselves. For details about [Prop](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html), consult the official documentation at [agda.readthedocs.io/en/v2.6.1.3/language/prop.html](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html)</span>


module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇} where

 prop-ext' : prop-ext 𝓤 𝓦 → {P Q : Pred₁ A 𝓦} → ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q
 prop-ext' pe hyp = pe (fst hyp) (snd hyp)

Thus, for truncated predicates `P` and `Q`, if `prop-ext` holds, then `(P ⊆ Q) × (Q ⊆ P) → P ≡ Q`, which is a useful extensionality principle.

prop-ext₁ : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦) ⁺ ̇
prop-ext₁ 𝓤 𝓦 = ∀ {A : 𝓤 ̇}{P Q : Pred₁ A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

The foregoing easily generalizes to binary relations and, in particular, equivalence relations.  Indeed, if `R` is a binary relation on `A` and for each pair `x y : A` there is at most one proof of `R x y`, then we call `R` a *binary proposition*. We use [Type Topology][]'s `is-subsingleton-valued` type to impose this truncation assumption on a binary relation.<sup>[3](Relations.Truncation.html#fn3)</sup>

Pred₂ : {𝓤 : Universe} → 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
Pred₂ A 𝓦 = Σ R ꞉ (Rel A 𝓦) , is-subsingleton-valued R

Recall, `is-subsingleton-valued` is simply defined as

`is-subsingleton-valued R = ∀ x y → is-subsingleton (R x y)`

which is the assertion that for all `x` `y` there is at most one proof of `R x y`.  We call this the *uniqueness-of-membership-proofs* (UMP) property.  The functions `IsContProp` and `IsDepProp`, defined below, generalize this concept from binary to arbitrary (continuous and dependent) relations.

Sometimes we will want to assume that a type `A` is a *set*. As we just learned, this means there is at most one proof that two inhabitants of `A` are the same.  Analogously, for predicates on `A`, we may wish to assume that there is at most one proof that an inhabitant of `A` satisfies the given predicate.  If a unary predicate satisfies this condition, then we call it a (unary) *proposition*.  We could represent this concept in type theory by the following Sigma type: `Σ P ꞉ (Pred A 𝓦) , ∀ x → is-subsingleton (P x)`. However, as we will not have occasion to use this type, we omit the formal definition.



We define a *truncated equivalence* to be an equivalence relation that has unique membership proofs; the following types represent such relations.

module _ {𝓤 𝓦 : Universe} where

 record IsEqv {A : 𝓤 ̇}(R : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field equiv : IsEquivalence R
        ump : is-subsingleton-valued R  -- "uniqueness of membership proofs" (ump)

 Eqv : 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺ ̇
 Eqv A = Σ R ꞉ Rel A 𝓦 , IsEqv R


To see the point of this, suppose `cont-prop-ext A 𝓦` holds. Then we can prove that logically equivalent continuous propositions of type `ContProp A 𝓦` are equivalent. In other words, under the stated hypotheses, we obtain a useful extensionality lemma for continuous propositions.

 cont-prop-ext' : {A : 𝓤 ̇}{𝓦 : Universe} → cont-prop-ext A 𝓦 → {P Q : ContProp A 𝓦}
  →               ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

 cont-prop-ext' pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥

Applying the extensionality principle for dependent continuous relations is no harder than applying the special cases of this principle defined earlier.


 module _ (𝒜 : I → 𝓤 ̇)(𝓦 : Universe) where

  dep-prop-ext' : dep-prop-ext 𝒜 𝓦 → {P Q : DepProp 𝒜 𝓦} → ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q
  dep-prop-ext' pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥



-->



