---
layout: default
title : Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation</a>

This section presents the [Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss *truncation* and *h-sets* (which we just call *sets*).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

<pre class="Agda">

<a id="1077" class="Symbol">{-#</a> <a id="1081" class="Keyword">OPTIONS</a> <a id="1089" class="Pragma">--without-K</a> <a id="1101" class="Pragma">--exact-split</a> <a id="1115" class="Pragma">--safe</a> <a id="1122" class="Symbol">#-}</a>

<a id="1127" class="Keyword">module</a> <a id="1134" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="1155" class="Keyword">where</a>

<a id="1162" class="Keyword">open</a> <a id="1167" class="Keyword">import</a> <a id="1174" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1194" class="Keyword">public</a>

<a id="1202" class="Keyword">open</a> <a id="1207" class="Keyword">import</a> <a id="1214" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1223" class="Keyword">using</a> <a id="1229" class="Symbol">(</a><a id="1230" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="1233" class="Symbol">)</a> <a id="1235" class="Keyword">public</a>

</pre>

#### <a id="uniqueness-of-identity-proofs">Uniqueness of identity proofs</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `A` and an identity relation `_≡₀_` on `A` so that, given two inhabitants of `A`, say, `a b : A`, we can form the type `a ≡₀ b`. Suppose `p` and `q` inhabit the type `a ≡₀ b`; that is, `p` and `q` are proofs of `a ≡₀ b`, in which case we write `p q : a ≡₀ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡₀`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡₀ b` are the same.
If such a proof exists for all `p q : a ≡₀ b`, then the proof of `a ≡₀ b` is unique; as a property of
the types `A` and `≡₀`, this is sometimes called <a id="uniqueness-of-identity-proofs">*uniqueness of identity proofs*</a> (uip).

Now, perhaps we have two proofs, say, `r s : p ≡₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

<pre class="Agda">

<a id="3492" class="Keyword">module</a> <a id="hide-is-set"></a><a id="3499" href="Relations.Truncation.html#3499" class="Module">hide-is-set</a> <a id="3511" class="Symbol">{</a><a id="3512" href="Relations.Truncation.html#3512" class="Bound">𝓤</a> <a id="3514" class="Symbol">:</a> <a id="3516" href="Universes.html#205" class="Postulate">Universe</a><a id="3524" class="Symbol">}</a> <a id="3526" class="Keyword">where</a>

 <a id="hide-is-set.is-set"></a><a id="3534" href="Relations.Truncation.html#3534" class="Function">is-set</a> <a id="3541" class="Symbol">:</a> <a id="3543" href="Relations.Truncation.html#3512" class="Bound">𝓤</a> <a id="3545" href="Universes.html#403" class="Function Operator">̇</a> <a id="3547" class="Symbol">→</a> <a id="3549" href="Relations.Truncation.html#3512" class="Bound">𝓤</a> <a id="3551" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3554" href="Relations.Truncation.html#3534" class="Function">is-set</a> <a id="3561" href="Relations.Truncation.html#3561" class="Bound">A</a> <a id="3563" class="Symbol">=</a> <a id="3565" class="Symbol">(</a><a id="3566" href="Relations.Truncation.html#3566" class="Bound">x</a> <a id="3568" href="Relations.Truncation.html#3568" class="Bound">y</a> <a id="3570" class="Symbol">:</a> <a id="3572" href="Relations.Truncation.html#3561" class="Bound">A</a><a id="3573" class="Symbol">)</a> <a id="3575" class="Symbol">→</a> <a id="3577" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="3593" class="Symbol">(</a><a id="3594" href="Relations.Truncation.html#3566" class="Bound">x</a> <a id="3596" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="3598" href="Relations.Truncation.html#3568" class="Bound">y</a><a id="3599" class="Symbol">)</a>

<a id="3602" class="Keyword">open</a> <a id="3607" class="Keyword">import</a> <a id="3614" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="3629" class="Keyword">using</a> <a id="3635" class="Symbol">(</a><a id="3636" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="3642" class="Symbol">)</a> <a id="3644" class="Keyword">public</a>

</pre>

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

<pre class="Agda">

<a id="4066" class="Keyword">module</a> <a id="hide-to-Σ-≡"></a><a id="4073" href="Relations.Truncation.html#4073" class="Module">hide-to-Σ-≡</a> <a id="4085" class="Symbol">{</a><a id="4086" href="Relations.Truncation.html#4086" class="Bound">𝓤</a> <a id="4088" href="Relations.Truncation.html#4088" class="Bound">𝓦</a> <a id="4090" class="Symbol">:</a> <a id="4092" href="Universes.html#205" class="Postulate">Universe</a><a id="4100" class="Symbol">}</a> <a id="4102" class="Keyword">where</a>

 <a id="hide-to-Σ-≡.to-Σ-≡"></a><a id="4110" href="Relations.Truncation.html#4110" class="Function">to-Σ-≡</a> <a id="4117" class="Symbol">:</a> <a id="4119" class="Symbol">{</a><a id="4120" href="Relations.Truncation.html#4120" class="Bound">A</a> <a id="4122" class="Symbol">:</a> <a id="4124" href="Relations.Truncation.html#4086" class="Bound">𝓤</a> <a id="4126" href="Universes.html#403" class="Function Operator">̇</a> <a id="4128" class="Symbol">}</a> <a id="4130" class="Symbol">{</a><a id="4131" href="Relations.Truncation.html#4131" class="Bound">B</a> <a id="4133" class="Symbol">:</a> <a id="4135" href="Relations.Truncation.html#4120" class="Bound">A</a> <a id="4137" class="Symbol">→</a> <a id="4139" href="Relations.Truncation.html#4088" class="Bound">𝓦</a> <a id="4141" href="Universes.html#403" class="Function Operator">̇</a> <a id="4143" class="Symbol">}</a> <a id="4145" class="Symbol">{</a><a id="4146" href="Relations.Truncation.html#4146" class="Bound">σ</a> <a id="4148" href="Relations.Truncation.html#4148" class="Bound">τ</a> <a id="4150" class="Symbol">:</a> <a id="4152" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="4154" href="Relations.Truncation.html#4131" class="Bound">B</a><a id="4155" class="Symbol">}</a>
  <a id="4159" class="Symbol">→</a>       <a id="4167" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4169" href="Relations.Truncation.html#4169" class="Bound">p</a> <a id="4171" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4173" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4175" href="Relations.Truncation.html#4146" class="Bound">σ</a> <a id="4177" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4179" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4181" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4183" href="Relations.Truncation.html#4148" class="Bound">τ</a> <a id="4185" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4187" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4189" class="Symbol">(</a><a id="4190" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4200" href="Relations.Truncation.html#4131" class="Bound">B</a> <a id="4202" href="Relations.Truncation.html#4169" class="Bound">p</a> <a id="4204" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4206" href="Relations.Truncation.html#4146" class="Bound">σ</a> <a id="4208" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a><a id="4209" class="Symbol">)</a> <a id="4211" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4213" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4215" href="Relations.Truncation.html#4148" class="Bound">τ</a> <a id="4217" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a>
  <a id="4221" class="Symbol">→</a>       <a id="4229" href="Relations.Truncation.html#4146" class="Bound">σ</a> <a id="4231" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="4233" href="Relations.Truncation.html#4148" class="Bound">τ</a>

 <a id="4237" href="Relations.Truncation.html#4110" class="Function">to-Σ-≡</a> <a id="4244" class="Symbol">(</a><a id="4245" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4250" class="Symbol">{</a><a id="4251" class="Argument">x</a> <a id="4253" class="Symbol">=</a> <a id="4255" href="Relations.Truncation.html#4255" class="Bound">x</a><a id="4256" class="Symbol">}</a> <a id="4258" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4260" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4265" class="Symbol">{</a><a id="4266" class="Argument">x</a> <a id="4268" class="Symbol">=</a> <a id="4270" href="Relations.Truncation.html#4270" class="Bound">a</a><a id="4271" class="Symbol">})</a> <a id="4274" class="Symbol">=</a> <a id="4276" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4281" class="Symbol">{</a><a id="4282" class="Argument">x</a> <a id="4284" class="Symbol">=</a> <a id="4286" class="Symbol">(</a><a id="4287" href="Relations.Truncation.html#4255" class="Bound">x</a> <a id="4289" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4291" href="Relations.Truncation.html#4270" class="Bound">a</a><a id="4292" class="Symbol">)}</a>

<a id="4296" class="Keyword">open</a> <a id="4301" class="Keyword">import</a> <a id="4308" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="4323" class="Keyword">using</a> <a id="4329" class="Symbol">(</a><a id="4330" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="4336" class="Symbol">)</a> <a id="4338" class="Keyword">public</a>

</pre>

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.

<pre class="Agda">

<a id="5253" class="Keyword">module</a> <a id="5260" href="Relations.Truncation.html#5260" class="Module">_</a> <a id="5262" class="Symbol">{</a><a id="5263" href="Relations.Truncation.html#5263" class="Bound">𝓤</a> <a id="5265" href="Relations.Truncation.html#5265" class="Bound">𝓦</a> <a id="5267" class="Symbol">:</a> <a id="5269" href="Universes.html#205" class="Postulate">Universe</a><a id="5277" class="Symbol">}{</a><a id="5279" href="Relations.Truncation.html#5279" class="Bound">A</a> <a id="5281" class="Symbol">:</a> <a id="5283" href="Relations.Truncation.html#5263" class="Bound">𝓤</a> <a id="5285" href="Universes.html#403" class="Function Operator">̇</a><a id="5286" class="Symbol">}{</a><a id="5288" href="Relations.Truncation.html#5288" class="Bound">B</a> <a id="5290" class="Symbol">:</a> <a id="5292" href="Relations.Truncation.html#5265" class="Bound">𝓦</a> <a id="5294" href="Universes.html#403" class="Function Operator">̇</a><a id="5295" class="Symbol">}</a> <a id="5297" class="Keyword">where</a>

 <a id="5305" href="Relations.Truncation.html#5305" class="Function">monic-is-embedding|Set</a> <a id="5328" class="Symbol">:</a> <a id="5330" class="Symbol">(</a><a id="5331" href="Relations.Truncation.html#5331" class="Bound">f</a> <a id="5333" class="Symbol">:</a> <a id="5335" href="Relations.Truncation.html#5279" class="Bound">A</a> <a id="5337" class="Symbol">→</a> <a id="5339" href="Relations.Truncation.html#5288" class="Bound">B</a><a id="5340" class="Symbol">)</a> <a id="5342" class="Symbol">→</a> <a id="5344" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="5351" href="Relations.Truncation.html#5288" class="Bound">B</a> <a id="5353" class="Symbol">→</a> <a id="5355" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="5361" href="Relations.Truncation.html#5331" class="Bound">f</a> <a id="5363" class="Symbol">→</a> <a id="5365" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="5378" href="Relations.Truncation.html#5331" class="Bound">f</a>

 <a id="5382" href="Relations.Truncation.html#5305" class="Function">monic-is-embedding|Set</a> <a id="5405" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5407" href="Relations.Truncation.html#5407" class="Bound">Bset</a> <a id="5412" href="Relations.Truncation.html#5412" class="Bound">fmon</a> <a id="5417" href="Relations.Truncation.html#5417" class="Bound">b</a> <a id="5419" class="Symbol">(</a><a id="5420" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5422" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5424" href="Relations.Truncation.html#5424" class="Bound">fu≡b</a><a id="5428" class="Symbol">)</a> <a id="5430" class="Symbol">(</a><a id="5431" href="Relations.Truncation.html#5431" class="Bound">v</a> <a id="5433" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5435" href="Relations.Truncation.html#5435" class="Bound">fv≡b</a><a id="5439" class="Symbol">)</a> <a id="5441" class="Symbol">=</a> <a id="5443" href="Relations.Truncation.html#5675" class="Function">γ</a>
  <a id="5447" class="Keyword">where</a>
  <a id="5455" href="Relations.Truncation.html#5455" class="Function">fuv</a> <a id="5459" class="Symbol">:</a> <a id="5461" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5463" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5465" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5467" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5469" href="Relations.Truncation.html#5431" class="Bound">v</a>
  <a id="5473" href="Relations.Truncation.html#5455" class="Function">fuv</a> <a id="5477" class="Symbol">=</a> <a id="5479" href="Overture.Equality.html#2957" class="Function">≡-trans</a> <a id="5487" href="Relations.Truncation.html#5424" class="Bound">fu≡b</a> <a id="5492" class="Symbol">(</a><a id="5493" href="Relations.Truncation.html#5435" class="Bound">fv≡b</a> <a id="5498" href="MGS-MLTT.html#6125" class="Function Operator">⁻¹</a><a id="5500" class="Symbol">)</a>

  <a id="5505" href="Relations.Truncation.html#5505" class="Function">uv</a> <a id="5508" class="Symbol">:</a> <a id="5510" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5512" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5514" href="Relations.Truncation.html#5431" class="Bound">v</a>
  <a id="5518" href="Relations.Truncation.html#5505" class="Function">uv</a> <a id="5521" class="Symbol">=</a> <a id="5523" href="Relations.Truncation.html#5412" class="Bound">fmon</a> <a id="5528" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5530" href="Relations.Truncation.html#5431" class="Bound">v</a> <a id="5532" href="Relations.Truncation.html#5455" class="Function">fuv</a>

  <a id="5539" href="Relations.Truncation.html#5539" class="Function">arg1</a> <a id="5544" class="Symbol">:</a> <a id="5546" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5548" href="Relations.Truncation.html#5548" class="Bound">p</a> <a id="5550" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5552" class="Symbol">(</a><a id="5553" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5555" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5557" href="Relations.Truncation.html#5431" class="Bound">v</a><a id="5558" class="Symbol">)</a> <a id="5560" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5562" class="Symbol">(</a><a id="5563" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5573" class="Symbol">(λ</a> <a id="5576" href="Relations.Truncation.html#5576" class="Bound">a</a> <a id="5578" class="Symbol">→</a> <a id="5580" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5582" href="Relations.Truncation.html#5576" class="Bound">a</a> <a id="5584" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5586" href="Relations.Truncation.html#5417" class="Bound">b</a><a id="5587" class="Symbol">)</a> <a id="5589" href="Relations.Truncation.html#5548" class="Bound">p</a> <a id="5591" href="Relations.Truncation.html#5424" class="Bound">fu≡b</a><a id="5595" class="Symbol">)</a> <a id="5597" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5599" href="Relations.Truncation.html#5435" class="Bound">fv≡b</a>
  <a id="5606" href="Relations.Truncation.html#5539" class="Function">arg1</a> <a id="5611" class="Symbol">=</a> <a id="5613" href="Relations.Truncation.html#5505" class="Function">uv</a> <a id="5616" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5618" href="Relations.Truncation.html#5407" class="Bound">Bset</a> <a id="5623" class="Symbol">(</a><a id="5624" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5626" href="Relations.Truncation.html#5431" class="Bound">v</a><a id="5627" class="Symbol">)</a> <a id="5629" href="Relations.Truncation.html#5417" class="Bound">b</a> <a id="5631" class="Symbol">(</a><a id="5632" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5642" class="Symbol">(λ</a> <a id="5645" href="Relations.Truncation.html#5645" class="Bound">a</a> <a id="5647" class="Symbol">→</a> <a id="5649" href="Relations.Truncation.html#5405" class="Bound">f</a> <a id="5651" href="Relations.Truncation.html#5645" class="Bound">a</a> <a id="5653" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5655" href="Relations.Truncation.html#5417" class="Bound">b</a><a id="5656" class="Symbol">)</a> <a id="5658" href="Relations.Truncation.html#5505" class="Function">uv</a> <a id="5661" href="Relations.Truncation.html#5424" class="Bound">fu≡b</a><a id="5665" class="Symbol">)</a> <a id="5667" href="Relations.Truncation.html#5435" class="Bound">fv≡b</a>

  <a id="5675" href="Relations.Truncation.html#5675" class="Function">γ</a> <a id="5677" class="Symbol">:</a> <a id="5679" href="Relations.Truncation.html#5420" class="Bound">u</a> <a id="5681" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5683" href="Relations.Truncation.html#5424" class="Bound">fu≡b</a> <a id="5688" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="5690" href="Relations.Truncation.html#5431" class="Bound">v</a> <a id="5692" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5694" href="Relations.Truncation.html#5435" class="Bound">fv≡b</a>
  <a id="5701" href="Relations.Truncation.html#5675" class="Function">γ</a> <a id="5703" class="Symbol">=</a> <a id="5705" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a> <a id="5712" href="Relations.Truncation.html#5539" class="Function">arg1</a>

</pre>

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a *set* (in the sense defined above), then we add to the name of the theorem the suffix `|Set`, which calls to mind the standard mathematical notation for the restriction of a function.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

<pre class="Agda">

 <a id="6265" href="Relations.Truncation.html#6265" class="Function">embedding-iff-monic|Set</a> <a id="6289" class="Symbol">:</a> <a id="6291" class="Symbol">(</a><a id="6292" href="Relations.Truncation.html#6292" class="Bound">f</a> <a id="6294" class="Symbol">:</a> <a id="6296" href="Relations.Truncation.html#5279" class="Bound">A</a> <a id="6298" class="Symbol">→</a> <a id="6300" href="Relations.Truncation.html#5288" class="Bound">B</a><a id="6301" class="Symbol">)</a> <a id="6303" class="Symbol">→</a> <a id="6305" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="6312" href="Relations.Truncation.html#5288" class="Bound">B</a> <a id="6314" class="Symbol">→</a> <a id="6316" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="6329" href="Relations.Truncation.html#6292" class="Bound">f</a> <a id="6331" href="MGS-MLTT.html#7080" class="Function Operator">⇔</a> <a id="6333" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="6339" href="Relations.Truncation.html#6292" class="Bound">f</a>
 <a id="6342" href="Relations.Truncation.html#6265" class="Function">embedding-iff-monic|Set</a> <a id="6366" href="Relations.Truncation.html#6366" class="Bound">f</a> <a id="6368" href="Relations.Truncation.html#6368" class="Bound">Bset</a> <a id="6373" class="Symbol">=</a> <a id="6375" class="Symbol">(</a><a id="6376" href="Overture.Inverses.html#5685" class="Function">embedding-is-monic</a> <a id="6395" href="Relations.Truncation.html#6366" class="Bound">f</a><a id="6396" class="Symbol">)</a><a id="6397" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="6399" class="Symbol">(</a><a id="6400" href="Relations.Truncation.html#5305" class="Function">monic-is-embedding|Set</a> <a id="6423" href="Relations.Truncation.html#6366" class="Bound">f</a> <a id="6425" href="Relations.Truncation.html#6368" class="Bound">Bset</a><a id="6429" class="Symbol">)</a>

</pre>


#### <a id="equivalence-class-truncation">Equivalence class truncation</a>

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

In the next module ([Relations.Extensionality][]) we will define a *quotient extensionality* principle that will require a form of unique identity proofs---specifically, we will assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

<pre class="Agda">

<a id="blk-uip"></a><a id="7104" href="Relations.Truncation.html#7104" class="Function">blk-uip</a> <a id="7112" class="Symbol">:</a> <a id="7114" class="Symbol">{</a><a id="7115" href="Relations.Truncation.html#7115" class="Bound">𝓦</a> <a id="7117" href="Relations.Truncation.html#7117" class="Bound">𝓤</a> <a id="7119" class="Symbol">:</a> <a id="7121" href="Universes.html#205" class="Postulate">Universe</a><a id="7129" class="Symbol">}(</a><a id="7131" href="Relations.Truncation.html#7131" class="Bound">A</a> <a id="7133" class="Symbol">:</a> <a id="7135" href="Relations.Truncation.html#7117" class="Bound">𝓤</a> <a id="7137" href="Universes.html#403" class="Function Operator">̇</a><a id="7138" class="Symbol">)(</a><a id="7140" href="Relations.Truncation.html#7140" class="Bound">R</a> <a id="7142" class="Symbol">:</a> <a id="7144" href="Relations.Discrete.html#4775" class="Function">Rel</a> <a id="7148" href="Relations.Truncation.html#7131" class="Bound">A</a> <a id="7150" href="Relations.Truncation.html#7115" class="Bound">𝓦</a> <a id="7152" class="Symbol">)</a> <a id="7154" class="Symbol">→</a> <a id="7156" href="Relations.Truncation.html#7117" class="Bound">𝓤</a> <a id="7158" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7160" href="Relations.Truncation.html#7115" class="Bound">𝓦</a> <a id="7162" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="7164" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7166" href="Relations.Truncation.html#7104" class="Function">blk-uip</a> <a id="7174" class="Symbol">{</a><a id="7175" href="Relations.Truncation.html#7175" class="Bound">𝓦</a><a id="7176" class="Symbol">}</a> <a id="7178" href="Relations.Truncation.html#7178" class="Bound">A</a> <a id="7180" href="Relations.Truncation.html#7180" class="Bound">R</a> <a id="7182" class="Symbol">=</a> <a id="7184" class="Symbol">∀</a> <a id="7186" class="Symbol">(</a><a id="7187" href="Relations.Truncation.html#7187" class="Bound">C</a> <a id="7189" class="Symbol">:</a> <a id="7191" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="7196" href="Relations.Truncation.html#7178" class="Bound">A</a> <a id="7198" href="Relations.Truncation.html#7175" class="Bound">𝓦</a><a id="7199" class="Symbol">)</a> <a id="7201" class="Symbol">→</a> <a id="7203" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="7219" class="Symbol">(</a><a id="7220" href="Relations.Quotients.html#4062" class="Function">IsBlock</a> <a id="7228" href="Relations.Truncation.html#7187" class="Bound">C</a> <a id="7230" class="Symbol">{</a><a id="7231" href="Relations.Truncation.html#7180" class="Bound">R</a><a id="7232" class="Symbol">})</a>

</pre>


----------------------------

#### <a id="general-propositions">General propositions*</a>

This section defines more general truncated predicates which we call *continuous propositions* and *dependent propositions*. Recall, above (in the [Relations.Continuous][] module) we defined types called `ContRel` and `DepRel` to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and *truncated dependent relation type*, the inhabitants of which we will call *continuous propositions* and *dependent propositions*, respectively.

<pre class="Agda">

<a id="7887" class="Keyword">module</a> <a id="7894" href="Relations.Truncation.html#7894" class="Module">_</a> <a id="7896" class="Symbol">{</a><a id="7897" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="7899" class="Symbol">:</a> <a id="7901" href="Universes.html#205" class="Postulate">Universe</a><a id="7909" class="Symbol">}{</a><a id="7911" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="7913" class="Symbol">:</a> <a id="7915" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7917" href="Universes.html#403" class="Function Operator">̇</a><a id="7918" class="Symbol">}</a> <a id="7920" class="Keyword">where</a>

 <a id="7928" class="Keyword">open</a> <a id="7933" class="Keyword">import</a> <a id="7940" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="7961" class="Keyword">using</a> <a id="7967" class="Symbol">(</a><a id="7968" href="Relations.Continuous.html#2959" class="Function">ContRel</a><a id="7975" class="Symbol">;</a> <a id="7977" href="Relations.Continuous.html#3581" class="Function">DepRel</a><a id="7983" class="Symbol">)</a>

 <a id="7987" href="Relations.Truncation.html#7987" class="Function">IsContProp</a> <a id="7998" class="Symbol">:</a> <a id="8000" class="Symbol">{</a><a id="8001" href="Relations.Truncation.html#8001" class="Bound">A</a> <a id="8003" class="Symbol">:</a> <a id="8005" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8007" href="Universes.html#403" class="Function Operator">̇</a><a id="8008" class="Symbol">}{</a><a id="8010" href="Relations.Truncation.html#8010" class="Bound">𝓦</a> <a id="8012" class="Symbol">:</a> <a id="8014" href="Universes.html#205" class="Postulate">Universe</a><a id="8022" class="Symbol">}</a> <a id="8024" class="Symbol">→</a> <a id="8026" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="8034" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8036" href="Relations.Truncation.html#8001" class="Bound">A</a> <a id="8038" href="Relations.Truncation.html#8010" class="Bound">𝓦</a>  <a id="8041" class="Symbol">→</a> <a id="8043" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8045" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8047" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8049" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8051" href="Relations.Truncation.html#8010" class="Bound">𝓦</a> <a id="8053" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8056" href="Relations.Truncation.html#7987" class="Function">IsContProp</a> <a id="8067" class="Symbol">{</a><a id="8068" class="Argument">A</a> <a id="8070" class="Symbol">=</a> <a id="8072" href="Relations.Truncation.html#8072" class="Bound">A</a><a id="8073" class="Symbol">}</a> <a id="8075" href="Relations.Truncation.html#8075" class="Bound">P</a> <a id="8077" class="Symbol">=</a> <a id="8079" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8081" href="Relations.Truncation.html#8081" class="Bound">𝑎</a> <a id="8083" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8085" class="Symbol">(</a><a id="8086" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8088" class="Symbol">→</a> <a id="8090" href="Relations.Truncation.html#8072" class="Bound">A</a><a id="8091" class="Symbol">)</a> <a id="8093" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8095" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8111" class="Symbol">(</a><a id="8112" href="Relations.Truncation.html#8075" class="Bound">P</a> <a id="8114" href="Relations.Truncation.html#8081" class="Bound">𝑎</a><a id="8115" class="Symbol">)</a>

 <a id="8119" href="Relations.Truncation.html#8119" class="Function">ContProp</a> <a id="8128" class="Symbol">:</a> <a id="8130" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8132" href="Universes.html#403" class="Function Operator">̇</a> <a id="8134" class="Symbol">→</a> <a id="8136" class="Symbol">(</a><a id="8137" href="Relations.Truncation.html#8137" class="Bound">𝓦</a> <a id="8139" class="Symbol">:</a> <a id="8141" href="Universes.html#205" class="Postulate">Universe</a><a id="8149" class="Symbol">)</a> <a id="8151" class="Symbol">→</a> <a id="8153" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8155" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8157" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8159" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8161" href="Relations.Truncation.html#8137" class="Bound">𝓦</a> <a id="8163" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8165" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8168" href="Relations.Truncation.html#8119" class="Function">ContProp</a> <a id="8177" href="Relations.Truncation.html#8177" class="Bound">A</a> <a id="8179" href="Relations.Truncation.html#8179" class="Bound">𝓦</a> <a id="8181" class="Symbol">=</a> <a id="8183" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8185" href="Relations.Truncation.html#8185" class="Bound">P</a> <a id="8187" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8189" class="Symbol">(</a><a id="8190" href="Relations.Continuous.html#2959" class="Function">ContRel</a> <a id="8198" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8200" href="Relations.Truncation.html#8177" class="Bound">A</a> <a id="8202" href="Relations.Truncation.html#8179" class="Bound">𝓦</a><a id="8203" class="Symbol">)</a> <a id="8205" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8207" href="Relations.Truncation.html#7987" class="Function">IsContProp</a> <a id="8218" href="Relations.Truncation.html#8185" class="Bound">P</a>

 <a id="8222" href="Relations.Truncation.html#8222" class="Function">cont-prop-ext</a> <a id="8236" class="Symbol">:</a> <a id="8238" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8240" href="Universes.html#403" class="Function Operator">̇</a> <a id="8242" class="Symbol">→</a> <a id="8244" class="Symbol">(</a><a id="8245" href="Relations.Truncation.html#8245" class="Bound">𝓦</a> <a id="8247" class="Symbol">:</a> <a id="8249" href="Universes.html#205" class="Postulate">Universe</a><a id="8257" class="Symbol">)</a> <a id="8259" class="Symbol">→</a> <a id="8261" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8263" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8265" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8267" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8269" href="Relations.Truncation.html#8245" class="Bound">𝓦</a> <a id="8271" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8273" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8276" href="Relations.Truncation.html#8222" class="Function">cont-prop-ext</a> <a id="8290" href="Relations.Truncation.html#8290" class="Bound">A</a> <a id="8292" href="Relations.Truncation.html#8292" class="Bound">𝓦</a> <a id="8294" class="Symbol">=</a> <a id="8296" class="Symbol">{</a><a id="8297" href="Relations.Truncation.html#8297" class="Bound">P</a> <a id="8299" href="Relations.Truncation.html#8299" class="Bound">Q</a> <a id="8301" class="Symbol">:</a> <a id="8303" href="Relations.Truncation.html#8119" class="Function">ContProp</a> <a id="8312" href="Relations.Truncation.html#8290" class="Bound">A</a> <a id="8314" href="Relations.Truncation.html#8292" class="Bound">𝓦</a> <a id="8316" class="Symbol">}</a> <a id="8318" class="Symbol">→</a> <a id="8320" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8322" href="Relations.Truncation.html#8297" class="Bound">P</a> <a id="8324" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8326" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8328" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8330" href="Relations.Truncation.html#8299" class="Bound">Q</a> <a id="8332" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8334" class="Symbol">→</a> <a id="8336" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8338" href="Relations.Truncation.html#8299" class="Bound">Q</a> <a id="8340" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8342" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8344" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8346" href="Relations.Truncation.html#8297" class="Bound">P</a> <a id="8348" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8350" class="Symbol">→</a> <a id="8352" href="Relations.Truncation.html#8297" class="Bound">P</a> <a id="8354" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8356" href="Relations.Truncation.html#8299" class="Bound">Q</a>

 <a id="8360" href="Relations.Truncation.html#8360" class="Function">IsDepProp</a> <a id="8370" class="Symbol">:</a> <a id="8372" class="Symbol">{</a><a id="8373" href="Relations.Truncation.html#8373" class="Bound">I</a> <a id="8375" class="Symbol">:</a> <a id="8377" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8379" href="Universes.html#403" class="Function Operator">̇</a><a id="8380" class="Symbol">}{</a><a id="8382" href="Relations.Truncation.html#8382" class="Bound">𝒜</a> <a id="8384" class="Symbol">:</a> <a id="8386" href="Relations.Truncation.html#8373" class="Bound">I</a> <a id="8388" class="Symbol">→</a> <a id="8390" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8392" href="Universes.html#403" class="Function Operator">̇</a><a id="8393" class="Symbol">}{</a><a id="8395" href="Relations.Truncation.html#8395" class="Bound">𝓦</a> <a id="8397" class="Symbol">:</a> <a id="8399" href="Universes.html#205" class="Postulate">Universe</a><a id="8407" class="Symbol">}</a> <a id="8409" class="Symbol">→</a> <a id="8411" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="8418" href="Relations.Truncation.html#8373" class="Bound">I</a> <a id="8420" href="Relations.Truncation.html#8382" class="Bound">𝒜</a> <a id="8422" href="Relations.Truncation.html#8395" class="Bound">𝓦</a>  <a id="8425" class="Symbol">→</a> <a id="8427" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8429" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8431" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8433" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8435" href="Relations.Truncation.html#8395" class="Bound">𝓦</a> <a id="8437" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8440" href="Relations.Truncation.html#8360" class="Function">IsDepProp</a> <a id="8450" class="Symbol">{</a><a id="8451" class="Argument">I</a> <a id="8453" class="Symbol">=</a> <a id="8455" href="Relations.Truncation.html#8455" class="Bound">I</a><a id="8456" class="Symbol">}</a> <a id="8458" class="Symbol">{</a><a id="8459" href="Relations.Truncation.html#8459" class="Bound">𝒜</a><a id="8460" class="Symbol">}</a> <a id="8462" href="Relations.Truncation.html#8462" class="Bound">P</a> <a id="8464" class="Symbol">=</a> <a id="8466" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8468" href="Relations.Truncation.html#8468" class="Bound">𝑎</a> <a id="8470" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8472" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8474" href="Relations.Truncation.html#8459" class="Bound">𝒜</a> <a id="8476" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8478" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8494" class="Symbol">(</a><a id="8495" href="Relations.Truncation.html#8462" class="Bound">P</a> <a id="8497" href="Relations.Truncation.html#8468" class="Bound">𝑎</a><a id="8498" class="Symbol">)</a>

 <a id="8502" href="Relations.Truncation.html#8502" class="Function">DepProp</a> <a id="8510" class="Symbol">:</a> <a id="8512" class="Symbol">(</a><a id="8513" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8515" class="Symbol">→</a> <a id="8517" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8519" href="Universes.html#403" class="Function Operator">̇</a><a id="8520" class="Symbol">)</a> <a id="8522" class="Symbol">→</a> <a id="8524" class="Symbol">(</a><a id="8525" href="Relations.Truncation.html#8525" class="Bound">𝓦</a> <a id="8527" class="Symbol">:</a> <a id="8529" href="Universes.html#205" class="Postulate">Universe</a><a id="8537" class="Symbol">)</a> <a id="8539" class="Symbol">→</a> <a id="8541" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8543" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8545" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8547" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8549" href="Relations.Truncation.html#8525" class="Bound">𝓦</a> <a id="8551" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8553" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8556" href="Relations.Truncation.html#8502" class="Function">DepProp</a> <a id="8564" href="Relations.Truncation.html#8564" class="Bound">𝒜</a> <a id="8566" href="Relations.Truncation.html#8566" class="Bound">𝓦</a> <a id="8568" class="Symbol">=</a> <a id="8570" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8572" href="Relations.Truncation.html#8572" class="Bound">P</a> <a id="8574" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8576" class="Symbol">(</a><a id="8577" href="Relations.Continuous.html#3581" class="Function">DepRel</a> <a id="8584" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8586" href="Relations.Truncation.html#8564" class="Bound">𝒜</a> <a id="8588" href="Relations.Truncation.html#8566" class="Bound">𝓦</a><a id="8589" class="Symbol">)</a> <a id="8591" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8593" href="Relations.Truncation.html#8360" class="Function">IsDepProp</a> <a id="8603" href="Relations.Truncation.html#8572" class="Bound">P</a>

 <a id="8607" href="Relations.Truncation.html#8607" class="Function">dep-prop-ext</a> <a id="8620" class="Symbol">:</a> <a id="8622" class="Symbol">(</a><a id="8623" href="Relations.Truncation.html#7911" class="Bound">I</a> <a id="8625" class="Symbol">→</a> <a id="8627" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8629" href="Universes.html#403" class="Function Operator">̇</a><a id="8630" class="Symbol">)</a> <a id="8632" class="Symbol">→</a> <a id="8634" class="Symbol">(</a><a id="8635" href="Relations.Truncation.html#8635" class="Bound">𝓦</a> <a id="8637" class="Symbol">:</a> <a id="8639" href="Universes.html#205" class="Postulate">Universe</a><a id="8647" class="Symbol">)</a> <a id="8649" class="Symbol">→</a> <a id="8651" href="Relations.Truncation.html#7897" class="Bound">𝓤</a> <a id="8653" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8655" href="Relations.Truncation.html#7915" class="Bound">𝓥</a> <a id="8657" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8659" href="Relations.Truncation.html#8635" class="Bound">𝓦</a> <a id="8661" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8663" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8666" href="Relations.Truncation.html#8607" class="Function">dep-prop-ext</a> <a id="8679" href="Relations.Truncation.html#8679" class="Bound">𝒜</a> <a id="8681" href="Relations.Truncation.html#8681" class="Bound">𝓦</a> <a id="8683" class="Symbol">=</a> <a id="8685" class="Symbol">{</a><a id="8686" href="Relations.Truncation.html#8686" class="Bound">P</a> <a id="8688" href="Relations.Truncation.html#8688" class="Bound">Q</a> <a id="8690" class="Symbol">:</a> <a id="8692" href="Relations.Truncation.html#8502" class="Function">DepProp</a> <a id="8700" href="Relations.Truncation.html#8679" class="Bound">𝒜</a> <a id="8702" href="Relations.Truncation.html#8681" class="Bound">𝓦</a><a id="8703" class="Symbol">}</a> <a id="8705" class="Symbol">→</a> <a id="8707" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8709" href="Relations.Truncation.html#8686" class="Bound">P</a> <a id="8711" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8713" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8715" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8717" href="Relations.Truncation.html#8688" class="Bound">Q</a> <a id="8719" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8721" class="Symbol">→</a> <a id="8723" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8725" href="Relations.Truncation.html#8688" class="Bound">Q</a> <a id="8727" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8729" href="Relations.Discrete.html#2587" class="Function Operator">⊆</a> <a id="8731" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8733" href="Relations.Truncation.html#8686" class="Bound">P</a> <a id="8735" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8737" class="Symbol">→</a> <a id="8739" href="Relations.Truncation.html#8686" class="Bound">P</a> <a id="8741" href="Overture.Equality.html#2419" class="Datatype Operator">≡</a> <a id="8743" href="Relations.Truncation.html#8688" class="Bound">Q</a>

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



