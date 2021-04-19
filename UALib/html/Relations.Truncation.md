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

#### <a id="sets">Sets</a>

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

<pre class="Agda">

<a id="3520" class="Keyword">module</a> <a id="hide-is-set"></a><a id="3527" href="Relations.Truncation.html#3527" class="Module">hide-is-set</a> <a id="3539" class="Symbol">{</a><a id="3540" href="Relations.Truncation.html#3540" class="Bound">𝓤</a> <a id="3542" class="Symbol">:</a> <a id="3544" href="Universes.html#205" class="Postulate">Universe</a><a id="3552" class="Symbol">}</a> <a id="3554" class="Keyword">where</a>

 <a id="hide-is-set.is-set"></a><a id="3562" href="Relations.Truncation.html#3562" class="Function">is-set</a> <a id="3569" class="Symbol">:</a> <a id="3571" href="Relations.Truncation.html#3540" class="Bound">𝓤</a> <a id="3573" href="Universes.html#403" class="Function Operator">̇</a> <a id="3575" class="Symbol">→</a> <a id="3577" href="Relations.Truncation.html#3540" class="Bound">𝓤</a> <a id="3579" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3582" href="Relations.Truncation.html#3562" class="Function">is-set</a> <a id="3589" href="Relations.Truncation.html#3589" class="Bound">A</a> <a id="3591" class="Symbol">=</a> <a id="3593" class="Symbol">(</a><a id="3594" href="Relations.Truncation.html#3594" class="Bound">x</a> <a id="3596" href="Relations.Truncation.html#3596" class="Bound">y</a> <a id="3598" class="Symbol">:</a> <a id="3600" href="Relations.Truncation.html#3589" class="Bound">A</a><a id="3601" class="Symbol">)</a> <a id="3603" class="Symbol">→</a> <a id="3605" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="3621" class="Symbol">(</a><a id="3622" href="Relations.Truncation.html#3594" class="Bound">x</a> <a id="3624" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="3626" href="Relations.Truncation.html#3596" class="Bound">y</a><a id="3627" class="Symbol">)</a>

<a id="3630" class="Keyword">open</a> <a id="3635" class="Keyword">import</a> <a id="3642" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="3657" class="Keyword">using</a> <a id="3663" class="Symbol">(</a><a id="3664" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="3670" class="Symbol">)</a> <a id="3672" class="Keyword">public</a>

</pre>

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

<pre class="Agda">

<a id="4094" class="Keyword">module</a> <a id="hide-to-Σ-≡"></a><a id="4101" href="Relations.Truncation.html#4101" class="Module">hide-to-Σ-≡</a> <a id="4113" class="Symbol">{</a><a id="4114" href="Relations.Truncation.html#4114" class="Bound">𝓤</a> <a id="4116" href="Relations.Truncation.html#4116" class="Bound">𝓦</a> <a id="4118" class="Symbol">:</a> <a id="4120" href="Universes.html#205" class="Postulate">Universe</a><a id="4128" class="Symbol">}</a> <a id="4130" class="Keyword">where</a>

 <a id="hide-to-Σ-≡.to-Σ-≡"></a><a id="4138" href="Relations.Truncation.html#4138" class="Function">to-Σ-≡</a> <a id="4145" class="Symbol">:</a> <a id="4147" class="Symbol">{</a><a id="4148" href="Relations.Truncation.html#4148" class="Bound">A</a> <a id="4150" class="Symbol">:</a> <a id="4152" href="Relations.Truncation.html#4114" class="Bound">𝓤</a> <a id="4154" href="Universes.html#403" class="Function Operator">̇</a> <a id="4156" class="Symbol">}</a> <a id="4158" class="Symbol">{</a><a id="4159" href="Relations.Truncation.html#4159" class="Bound">B</a> <a id="4161" class="Symbol">:</a> <a id="4163" href="Relations.Truncation.html#4148" class="Bound">A</a> <a id="4165" class="Symbol">→</a> <a id="4167" href="Relations.Truncation.html#4116" class="Bound">𝓦</a> <a id="4169" href="Universes.html#403" class="Function Operator">̇</a> <a id="4171" class="Symbol">}</a> <a id="4173" class="Symbol">{</a><a id="4174" href="Relations.Truncation.html#4174" class="Bound">σ</a> <a id="4176" href="Relations.Truncation.html#4176" class="Bound">τ</a> <a id="4178" class="Symbol">:</a> <a id="4180" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="4182" href="Relations.Truncation.html#4159" class="Bound">B</a><a id="4183" class="Symbol">}</a>
  <a id="4187" class="Symbol">→</a>       <a id="4195" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4197" href="Relations.Truncation.html#4197" class="Bound">p</a> <a id="4199" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4201" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4203" href="Relations.Truncation.html#4174" class="Bound">σ</a> <a id="4205" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4207" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4209" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4211" href="Relations.Truncation.html#4176" class="Bound">τ</a> <a id="4213" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4215" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4217" class="Symbol">(</a><a id="4218" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4228" href="Relations.Truncation.html#4159" class="Bound">B</a> <a id="4230" href="Relations.Truncation.html#4197" class="Bound">p</a> <a id="4232" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4234" href="Relations.Truncation.html#4174" class="Bound">σ</a> <a id="4236" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a><a id="4237" class="Symbol">)</a> <a id="4239" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4241" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4243" href="Relations.Truncation.html#4176" class="Bound">τ</a> <a id="4245" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a>
  <a id="4249" class="Symbol">→</a>       <a id="4257" href="Relations.Truncation.html#4174" class="Bound">σ</a> <a id="4259" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4261" href="Relations.Truncation.html#4176" class="Bound">τ</a>

 <a id="4265" href="Relations.Truncation.html#4138" class="Function">to-Σ-≡</a> <a id="4272" class="Symbol">(</a><a id="4273" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4278" class="Symbol">{</a><a id="4279" class="Argument">x</a> <a id="4281" class="Symbol">=</a> <a id="4283" href="Relations.Truncation.html#4283" class="Bound">x</a><a id="4284" class="Symbol">}</a> <a id="4286" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4288" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4293" class="Symbol">{</a><a id="4294" class="Argument">x</a> <a id="4296" class="Symbol">=</a> <a id="4298" href="Relations.Truncation.html#4298" class="Bound">a</a><a id="4299" class="Symbol">})</a> <a id="4302" class="Symbol">=</a> <a id="4304" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4309" class="Symbol">{</a><a id="4310" class="Argument">x</a> <a id="4312" class="Symbol">=</a> <a id="4314" class="Symbol">(</a><a id="4315" href="Relations.Truncation.html#4283" class="Bound">x</a> <a id="4317" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4319" href="Relations.Truncation.html#4298" class="Bound">a</a><a id="4320" class="Symbol">)}</a>

<a id="4324" class="Keyword">open</a> <a id="4329" class="Keyword">import</a> <a id="4336" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="4351" class="Keyword">using</a> <a id="4357" class="Symbol">(</a><a id="4358" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="4364" class="Symbol">)</a> <a id="4366" class="Keyword">public</a>

</pre>

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.

<pre class="Agda">

<a id="5281" class="Keyword">module</a> <a id="5288" href="Relations.Truncation.html#5288" class="Module">_</a> <a id="5290" class="Symbol">{</a><a id="5291" href="Relations.Truncation.html#5291" class="Bound">𝓤</a> <a id="5293" href="Relations.Truncation.html#5293" class="Bound">𝓦</a> <a id="5295" class="Symbol">:</a> <a id="5297" href="Universes.html#205" class="Postulate">Universe</a><a id="5305" class="Symbol">}{</a><a id="5307" href="Relations.Truncation.html#5307" class="Bound">A</a> <a id="5309" class="Symbol">:</a> <a id="5311" href="Relations.Truncation.html#5291" class="Bound">𝓤</a> <a id="5313" href="Universes.html#403" class="Function Operator">̇</a><a id="5314" class="Symbol">}{</a><a id="5316" href="Relations.Truncation.html#5316" class="Bound">B</a> <a id="5318" class="Symbol">:</a> <a id="5320" href="Relations.Truncation.html#5293" class="Bound">𝓦</a> <a id="5322" href="Universes.html#403" class="Function Operator">̇</a><a id="5323" class="Symbol">}</a> <a id="5325" class="Keyword">where</a>

 <a id="5333" href="Relations.Truncation.html#5333" class="Function">monic-is-embedding|Set</a> <a id="5356" class="Symbol">:</a> <a id="5358" class="Symbol">(</a><a id="5359" href="Relations.Truncation.html#5359" class="Bound">f</a> <a id="5361" class="Symbol">:</a> <a id="5363" href="Relations.Truncation.html#5307" class="Bound">A</a> <a id="5365" class="Symbol">→</a> <a id="5367" href="Relations.Truncation.html#5316" class="Bound">B</a><a id="5368" class="Symbol">)</a> <a id="5370" class="Symbol">→</a> <a id="5372" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="5379" href="Relations.Truncation.html#5316" class="Bound">B</a> <a id="5381" class="Symbol">→</a> <a id="5383" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="5389" href="Relations.Truncation.html#5359" class="Bound">f</a> <a id="5391" class="Symbol">→</a> <a id="5393" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="5406" href="Relations.Truncation.html#5359" class="Bound">f</a>

 <a id="5410" href="Relations.Truncation.html#5333" class="Function">monic-is-embedding|Set</a> <a id="5433" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5435" href="Relations.Truncation.html#5435" class="Bound">Bset</a> <a id="5440" href="Relations.Truncation.html#5440" class="Bound">fmon</a> <a id="5445" href="Relations.Truncation.html#5445" class="Bound">b</a> <a id="5447" class="Symbol">(</a><a id="5448" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5450" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5452" href="Relations.Truncation.html#5452" class="Bound">fu≡b</a><a id="5456" class="Symbol">)</a> <a id="5458" class="Symbol">(</a><a id="5459" href="Relations.Truncation.html#5459" class="Bound">v</a> <a id="5461" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5463" href="Relations.Truncation.html#5463" class="Bound">fv≡b</a><a id="5467" class="Symbol">)</a> <a id="5469" class="Symbol">=</a> <a id="5471" href="Relations.Truncation.html#5703" class="Function">γ</a>
  <a id="5475" class="Keyword">where</a>
  <a id="5483" href="Relations.Truncation.html#5483" class="Function">fuv</a> <a id="5487" class="Symbol">:</a> <a id="5489" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5491" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5493" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5495" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5497" href="Relations.Truncation.html#5459" class="Bound">v</a>
  <a id="5501" href="Relations.Truncation.html#5483" class="Function">fuv</a> <a id="5505" class="Symbol">=</a> <a id="5507" href="Overture.Equality.html#3061" class="Function">≡-trans</a> <a id="5515" href="Relations.Truncation.html#5452" class="Bound">fu≡b</a> <a id="5520" class="Symbol">(</a><a id="5521" href="Relations.Truncation.html#5463" class="Bound">fv≡b</a> <a id="5526" href="MGS-MLTT.html#6125" class="Function Operator">⁻¹</a><a id="5528" class="Symbol">)</a>

  <a id="5533" href="Relations.Truncation.html#5533" class="Function">uv</a> <a id="5536" class="Symbol">:</a> <a id="5538" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5540" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5542" href="Relations.Truncation.html#5459" class="Bound">v</a>
  <a id="5546" href="Relations.Truncation.html#5533" class="Function">uv</a> <a id="5549" class="Symbol">=</a> <a id="5551" href="Relations.Truncation.html#5440" class="Bound">fmon</a> <a id="5556" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5558" href="Relations.Truncation.html#5459" class="Bound">v</a> <a id="5560" href="Relations.Truncation.html#5483" class="Function">fuv</a>

  <a id="5567" href="Relations.Truncation.html#5567" class="Function">arg1</a> <a id="5572" class="Symbol">:</a> <a id="5574" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5576" href="Relations.Truncation.html#5576" class="Bound">p</a> <a id="5578" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5580" class="Symbol">(</a><a id="5581" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5583" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5585" href="Relations.Truncation.html#5459" class="Bound">v</a><a id="5586" class="Symbol">)</a> <a id="5588" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5590" class="Symbol">(</a><a id="5591" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5601" class="Symbol">(λ</a> <a id="5604" href="Relations.Truncation.html#5604" class="Bound">a</a> <a id="5606" class="Symbol">→</a> <a id="5608" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5610" href="Relations.Truncation.html#5604" class="Bound">a</a> <a id="5612" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5614" href="Relations.Truncation.html#5445" class="Bound">b</a><a id="5615" class="Symbol">)</a> <a id="5617" href="Relations.Truncation.html#5576" class="Bound">p</a> <a id="5619" href="Relations.Truncation.html#5452" class="Bound">fu≡b</a><a id="5623" class="Symbol">)</a> <a id="5625" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5627" href="Relations.Truncation.html#5463" class="Bound">fv≡b</a>
  <a id="5634" href="Relations.Truncation.html#5567" class="Function">arg1</a> <a id="5639" class="Symbol">=</a> <a id="5641" href="Relations.Truncation.html#5533" class="Function">uv</a> <a id="5644" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5646" href="Relations.Truncation.html#5435" class="Bound">Bset</a> <a id="5651" class="Symbol">(</a><a id="5652" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5654" href="Relations.Truncation.html#5459" class="Bound">v</a><a id="5655" class="Symbol">)</a> <a id="5657" href="Relations.Truncation.html#5445" class="Bound">b</a> <a id="5659" class="Symbol">(</a><a id="5660" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5670" class="Symbol">(λ</a> <a id="5673" href="Relations.Truncation.html#5673" class="Bound">a</a> <a id="5675" class="Symbol">→</a> <a id="5677" href="Relations.Truncation.html#5433" class="Bound">f</a> <a id="5679" href="Relations.Truncation.html#5673" class="Bound">a</a> <a id="5681" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5683" href="Relations.Truncation.html#5445" class="Bound">b</a><a id="5684" class="Symbol">)</a> <a id="5686" href="Relations.Truncation.html#5533" class="Function">uv</a> <a id="5689" href="Relations.Truncation.html#5452" class="Bound">fu≡b</a><a id="5693" class="Symbol">)</a> <a id="5695" href="Relations.Truncation.html#5463" class="Bound">fv≡b</a>

  <a id="5703" href="Relations.Truncation.html#5703" class="Function">γ</a> <a id="5705" class="Symbol">:</a> <a id="5707" href="Relations.Truncation.html#5448" class="Bound">u</a> <a id="5709" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5711" href="Relations.Truncation.html#5452" class="Bound">fu≡b</a> <a id="5716" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5718" href="Relations.Truncation.html#5459" class="Bound">v</a> <a id="5720" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5722" href="Relations.Truncation.html#5463" class="Bound">fv≡b</a>
  <a id="5729" href="Relations.Truncation.html#5703" class="Function">γ</a> <a id="5731" class="Symbol">=</a> <a id="5733" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a> <a id="5740" href="Relations.Truncation.html#5567" class="Function">arg1</a>

</pre>

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a *set* (in the sense defined above), then we add to the name of the theorem the suffix `|Set`, which calls to mind the standard mathematical notation for the restriction of a function.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

<pre class="Agda">

 <a id="6293" href="Relations.Truncation.html#6293" class="Function">embedding-iff-monic|Set</a> <a id="6317" class="Symbol">:</a> <a id="6319" class="Symbol">(</a><a id="6320" href="Relations.Truncation.html#6320" class="Bound">f</a> <a id="6322" class="Symbol">:</a> <a id="6324" href="Relations.Truncation.html#5307" class="Bound">A</a> <a id="6326" class="Symbol">→</a> <a id="6328" href="Relations.Truncation.html#5316" class="Bound">B</a><a id="6329" class="Symbol">)</a> <a id="6331" class="Symbol">→</a> <a id="6333" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="6340" href="Relations.Truncation.html#5316" class="Bound">B</a> <a id="6342" class="Symbol">→</a> <a id="6344" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="6357" href="Relations.Truncation.html#6320" class="Bound">f</a> <a id="6359" href="MGS-MLTT.html#7080" class="Function Operator">⇔</a> <a id="6361" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="6367" href="Relations.Truncation.html#6320" class="Bound">f</a>
 <a id="6370" href="Relations.Truncation.html#6293" class="Function">embedding-iff-monic|Set</a> <a id="6394" href="Relations.Truncation.html#6394" class="Bound">f</a> <a id="6396" href="Relations.Truncation.html#6396" class="Bound">Bset</a> <a id="6401" class="Symbol">=</a> <a id="6403" class="Symbol">(</a><a id="6404" href="Overture.Inverses.html#5685" class="Function">embedding-is-monic</a> <a id="6423" href="Relations.Truncation.html#6394" class="Bound">f</a><a id="6424" class="Symbol">)</a><a id="6425" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="6427" class="Symbol">(</a><a id="6428" href="Relations.Truncation.html#5333" class="Function">monic-is-embedding|Set</a> <a id="6451" href="Relations.Truncation.html#6394" class="Bound">f</a> <a id="6453" href="Relations.Truncation.html#6396" class="Bound">Bset</a><a id="6457" class="Symbol">)</a>

</pre>


#### <a id="equivalence-class-truncation">Equivalence class truncation</a>

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

In the next module ([Relations.Extensionality][]) we will define a *quotient extensionality* principle that will require a form of unique identity proofs---specifically, we will assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

<pre class="Agda">

<a id="blk-uip"></a><a id="7132" href="Relations.Truncation.html#7132" class="Function">blk-uip</a> <a id="7140" class="Symbol">:</a> <a id="7142" class="Symbol">{</a><a id="7143" href="Relations.Truncation.html#7143" class="Bound">𝓦</a> <a id="7145" href="Relations.Truncation.html#7145" class="Bound">𝓤</a> <a id="7147" class="Symbol">:</a> <a id="7149" href="Universes.html#205" class="Postulate">Universe</a><a id="7157" class="Symbol">}(</a><a id="7159" href="Relations.Truncation.html#7159" class="Bound">A</a> <a id="7161" class="Symbol">:</a> <a id="7163" href="Relations.Truncation.html#7145" class="Bound">𝓤</a> <a id="7165" href="Universes.html#403" class="Function Operator">̇</a><a id="7166" class="Symbol">)(</a><a id="7168" href="Relations.Truncation.html#7168" class="Bound">R</a> <a id="7170" class="Symbol">:</a> <a id="7172" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="7176" href="Relations.Truncation.html#7159" class="Bound">A</a> <a id="7178" href="Relations.Truncation.html#7143" class="Bound">𝓦</a> <a id="7180" class="Symbol">)</a> <a id="7182" class="Symbol">→</a> <a id="7184" href="Relations.Truncation.html#7145" class="Bound">𝓤</a> <a id="7186" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7188" href="Relations.Truncation.html#7143" class="Bound">𝓦</a> <a id="7190" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="7192" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7194" href="Relations.Truncation.html#7132" class="Function">blk-uip</a> <a id="7202" class="Symbol">{</a><a id="7203" href="Relations.Truncation.html#7203" class="Bound">𝓦</a><a id="7204" class="Symbol">}</a> <a id="7206" href="Relations.Truncation.html#7206" class="Bound">A</a> <a id="7208" href="Relations.Truncation.html#7208" class="Bound">R</a> <a id="7210" class="Symbol">=</a> <a id="7212" class="Symbol">∀</a> <a id="7214" class="Symbol">(</a><a id="7215" href="Relations.Truncation.html#7215" class="Bound">C</a> <a id="7217" class="Symbol">:</a> <a id="7219" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="7224" href="Relations.Truncation.html#7206" class="Bound">A</a> <a id="7226" href="Relations.Truncation.html#7203" class="Bound">𝓦</a><a id="7227" class="Symbol">)</a> <a id="7229" class="Symbol">→</a> <a id="7231" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="7247" class="Symbol">(</a><a id="7248" href="Relations.Quotients.html#4062" class="Function">IsBlock</a> <a id="7256" href="Relations.Truncation.html#7215" class="Bound">C</a> <a id="7258" class="Symbol">{</a><a id="7259" href="Relations.Truncation.html#7208" class="Bound">R</a><a id="7260" class="Symbol">})</a>

</pre>

It might seem unreasonable to postulate that there is at most one inhabitant of `IsBlock C`, since equivalence classes typically have multiple members, any one of which could serve as a class representative.  However, postulating `blk-uip A R` is tantamount to collapsing each `R`-block to a single point, and this is indeed the correct semantic interpretation of the elements of the quotient `A / R`.

----------------------------

#### <a id="general-propositions">General propositions*</a>

This section defines more general truncated predicates which we call *continuous propositions* and *dependent propositions*. Recall, above (in the [Relations.Continuous][] module) we defined types called `ContRel` and `DepRel` to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and *truncated dependent relation type*, the inhabitants of which we will call *continuous propositions* and *dependent propositions*, respectively.

<pre class="Agda">

<a id="8317" class="Keyword">module</a> <a id="8324" href="Relations.Truncation.html#8324" class="Module">_</a> <a id="8326" class="Symbol">{</a><a id="8327" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8329" class="Symbol">:</a> <a id="8331" href="Universes.html#205" class="Postulate">Universe</a><a id="8339" class="Symbol">}{</a><a id="8341" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="8343" class="Symbol">:</a> <a id="8345" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8347" href="Universes.html#403" class="Function Operator">̇</a><a id="8348" class="Symbol">}</a> <a id="8350" class="Keyword">where</a>

 <a id="8358" class="Keyword">open</a> <a id="8363" class="Keyword">import</a> <a id="8370" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="8391" class="Keyword">using</a> <a id="8397" class="Symbol">(</a><a id="8398" href="Relations.Continuous.html#2965" class="Function">ContRel</a><a id="8405" class="Symbol">;</a> <a id="8407" href="Relations.Continuous.html#3587" class="Function">DepRel</a><a id="8413" class="Symbol">)</a>

 <a id="8417" href="Relations.Truncation.html#8417" class="Function">IsContProp</a> <a id="8428" class="Symbol">:</a> <a id="8430" class="Symbol">{</a><a id="8431" href="Relations.Truncation.html#8431" class="Bound">A</a> <a id="8433" class="Symbol">:</a> <a id="8435" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8437" href="Universes.html#403" class="Function Operator">̇</a><a id="8438" class="Symbol">}{</a><a id="8440" href="Relations.Truncation.html#8440" class="Bound">𝓦</a> <a id="8442" class="Symbol">:</a> <a id="8444" href="Universes.html#205" class="Postulate">Universe</a><a id="8452" class="Symbol">}</a> <a id="8454" class="Symbol">→</a> <a id="8456" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="8464" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="8466" href="Relations.Truncation.html#8431" class="Bound">A</a> <a id="8468" href="Relations.Truncation.html#8440" class="Bound">𝓦</a>  <a id="8471" class="Symbol">→</a> <a id="8473" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8475" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8477" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8479" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8481" href="Relations.Truncation.html#8440" class="Bound">𝓦</a> <a id="8483" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8486" href="Relations.Truncation.html#8417" class="Function">IsContProp</a> <a id="8497" class="Symbol">{</a><a id="8498" class="Argument">A</a> <a id="8500" class="Symbol">=</a> <a id="8502" href="Relations.Truncation.html#8502" class="Bound">A</a><a id="8503" class="Symbol">}</a> <a id="8505" href="Relations.Truncation.html#8505" class="Bound">P</a> <a id="8507" class="Symbol">=</a> <a id="8509" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8511" href="Relations.Truncation.html#8511" class="Bound">𝑎</a> <a id="8513" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8515" class="Symbol">(</a><a id="8516" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="8518" class="Symbol">→</a> <a id="8520" href="Relations.Truncation.html#8502" class="Bound">A</a><a id="8521" class="Symbol">)</a> <a id="8523" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8525" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8541" class="Symbol">(</a><a id="8542" href="Relations.Truncation.html#8505" class="Bound">P</a> <a id="8544" href="Relations.Truncation.html#8511" class="Bound">𝑎</a><a id="8545" class="Symbol">)</a>

 <a id="8549" href="Relations.Truncation.html#8549" class="Function">ContProp</a> <a id="8558" class="Symbol">:</a> <a id="8560" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8562" href="Universes.html#403" class="Function Operator">̇</a> <a id="8564" class="Symbol">→</a> <a id="8566" class="Symbol">(</a><a id="8567" href="Relations.Truncation.html#8567" class="Bound">𝓦</a> <a id="8569" class="Symbol">:</a> <a id="8571" href="Universes.html#205" class="Postulate">Universe</a><a id="8579" class="Symbol">)</a> <a id="8581" class="Symbol">→</a> <a id="8583" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8585" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8587" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8589" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8591" href="Relations.Truncation.html#8567" class="Bound">𝓦</a> <a id="8593" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8595" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8598" href="Relations.Truncation.html#8549" class="Function">ContProp</a> <a id="8607" href="Relations.Truncation.html#8607" class="Bound">A</a> <a id="8609" href="Relations.Truncation.html#8609" class="Bound">𝓦</a> <a id="8611" class="Symbol">=</a> <a id="8613" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8615" href="Relations.Truncation.html#8615" class="Bound">P</a> <a id="8617" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8619" class="Symbol">(</a><a id="8620" href="Relations.Continuous.html#2965" class="Function">ContRel</a> <a id="8628" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="8630" href="Relations.Truncation.html#8607" class="Bound">A</a> <a id="8632" href="Relations.Truncation.html#8609" class="Bound">𝓦</a><a id="8633" class="Symbol">)</a> <a id="8635" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8637" href="Relations.Truncation.html#8417" class="Function">IsContProp</a> <a id="8648" href="Relations.Truncation.html#8615" class="Bound">P</a>

 <a id="8652" href="Relations.Truncation.html#8652" class="Function">cont-prop-ext</a> <a id="8666" class="Symbol">:</a> <a id="8668" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8670" href="Universes.html#403" class="Function Operator">̇</a> <a id="8672" class="Symbol">→</a> <a id="8674" class="Symbol">(</a><a id="8675" href="Relations.Truncation.html#8675" class="Bound">𝓦</a> <a id="8677" class="Symbol">:</a> <a id="8679" href="Universes.html#205" class="Postulate">Universe</a><a id="8687" class="Symbol">)</a> <a id="8689" class="Symbol">→</a> <a id="8691" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8693" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8695" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8697" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8699" href="Relations.Truncation.html#8675" class="Bound">𝓦</a> <a id="8701" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8703" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8706" href="Relations.Truncation.html#8652" class="Function">cont-prop-ext</a> <a id="8720" href="Relations.Truncation.html#8720" class="Bound">A</a> <a id="8722" href="Relations.Truncation.html#8722" class="Bound">𝓦</a> <a id="8724" class="Symbol">=</a> <a id="8726" class="Symbol">{</a><a id="8727" href="Relations.Truncation.html#8727" class="Bound">P</a> <a id="8729" href="Relations.Truncation.html#8729" class="Bound">Q</a> <a id="8731" class="Symbol">:</a> <a id="8733" href="Relations.Truncation.html#8549" class="Function">ContProp</a> <a id="8742" href="Relations.Truncation.html#8720" class="Bound">A</a> <a id="8744" href="Relations.Truncation.html#8722" class="Bound">𝓦</a> <a id="8746" class="Symbol">}</a> <a id="8748" class="Symbol">→</a> <a id="8750" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8752" href="Relations.Truncation.html#8727" class="Bound">P</a> <a id="8754" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8756" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="8758" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8760" href="Relations.Truncation.html#8729" class="Bound">Q</a> <a id="8762" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8764" class="Symbol">→</a> <a id="8766" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8768" href="Relations.Truncation.html#8729" class="Bound">Q</a> <a id="8770" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8772" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="8774" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8776" href="Relations.Truncation.html#8727" class="Bound">P</a> <a id="8778" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="8780" class="Symbol">→</a> <a id="8782" href="Relations.Truncation.html#8727" class="Bound">P</a> <a id="8784" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="8786" href="Relations.Truncation.html#8729" class="Bound">Q</a>

 <a id="8790" href="Relations.Truncation.html#8790" class="Function">IsDepProp</a> <a id="8800" class="Symbol">:</a> <a id="8802" class="Symbol">{</a><a id="8803" href="Relations.Truncation.html#8803" class="Bound">I</a> <a id="8805" class="Symbol">:</a> <a id="8807" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8809" href="Universes.html#403" class="Function Operator">̇</a><a id="8810" class="Symbol">}{</a><a id="8812" href="Relations.Truncation.html#8812" class="Bound">𝒜</a> <a id="8814" class="Symbol">:</a> <a id="8816" href="Relations.Truncation.html#8803" class="Bound">I</a> <a id="8818" class="Symbol">→</a> <a id="8820" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8822" href="Universes.html#403" class="Function Operator">̇</a><a id="8823" class="Symbol">}{</a><a id="8825" href="Relations.Truncation.html#8825" class="Bound">𝓦</a> <a id="8827" class="Symbol">:</a> <a id="8829" href="Universes.html#205" class="Postulate">Universe</a><a id="8837" class="Symbol">}</a> <a id="8839" class="Symbol">→</a> <a id="8841" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="8848" href="Relations.Truncation.html#8803" class="Bound">I</a> <a id="8850" href="Relations.Truncation.html#8812" class="Bound">𝒜</a> <a id="8852" href="Relations.Truncation.html#8825" class="Bound">𝓦</a>  <a id="8855" class="Symbol">→</a> <a id="8857" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8859" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8861" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8863" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8865" href="Relations.Truncation.html#8825" class="Bound">𝓦</a> <a id="8867" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8870" href="Relations.Truncation.html#8790" class="Function">IsDepProp</a> <a id="8880" class="Symbol">{</a><a id="8881" class="Argument">I</a> <a id="8883" class="Symbol">=</a> <a id="8885" href="Relations.Truncation.html#8885" class="Bound">I</a><a id="8886" class="Symbol">}</a> <a id="8888" class="Symbol">{</a><a id="8889" href="Relations.Truncation.html#8889" class="Bound">𝒜</a><a id="8890" class="Symbol">}</a> <a id="8892" href="Relations.Truncation.html#8892" class="Bound">P</a> <a id="8894" class="Symbol">=</a> <a id="8896" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8898" href="Relations.Truncation.html#8898" class="Bound">𝑎</a> <a id="8900" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8902" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="8904" href="Relations.Truncation.html#8889" class="Bound">𝒜</a> <a id="8906" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8908" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8924" class="Symbol">(</a><a id="8925" href="Relations.Truncation.html#8892" class="Bound">P</a> <a id="8927" href="Relations.Truncation.html#8898" class="Bound">𝑎</a><a id="8928" class="Symbol">)</a>

 <a id="8932" href="Relations.Truncation.html#8932" class="Function">DepProp</a> <a id="8940" class="Symbol">:</a> <a id="8942" class="Symbol">(</a><a id="8943" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="8945" class="Symbol">→</a> <a id="8947" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8949" href="Universes.html#403" class="Function Operator">̇</a><a id="8950" class="Symbol">)</a> <a id="8952" class="Symbol">→</a> <a id="8954" class="Symbol">(</a><a id="8955" href="Relations.Truncation.html#8955" class="Bound">𝓦</a> <a id="8957" class="Symbol">:</a> <a id="8959" href="Universes.html#205" class="Postulate">Universe</a><a id="8967" class="Symbol">)</a> <a id="8969" class="Symbol">→</a> <a id="8971" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="8973" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8975" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="8977" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8979" href="Relations.Truncation.html#8955" class="Bound">𝓦</a> <a id="8981" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8983" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8986" href="Relations.Truncation.html#8932" class="Function">DepProp</a> <a id="8994" href="Relations.Truncation.html#8994" class="Bound">𝒜</a> <a id="8996" href="Relations.Truncation.html#8996" class="Bound">𝓦</a> <a id="8998" class="Symbol">=</a> <a id="9000" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9002" href="Relations.Truncation.html#9002" class="Bound">P</a> <a id="9004" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9006" class="Symbol">(</a><a id="9007" href="Relations.Continuous.html#3587" class="Function">DepRel</a> <a id="9014" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="9016" href="Relations.Truncation.html#8994" class="Bound">𝒜</a> <a id="9018" href="Relations.Truncation.html#8996" class="Bound">𝓦</a><a id="9019" class="Symbol">)</a> <a id="9021" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9023" href="Relations.Truncation.html#8790" class="Function">IsDepProp</a> <a id="9033" href="Relations.Truncation.html#9002" class="Bound">P</a>

 <a id="9037" href="Relations.Truncation.html#9037" class="Function">dep-prop-ext</a> <a id="9050" class="Symbol">:</a> <a id="9052" class="Symbol">(</a><a id="9053" href="Relations.Truncation.html#8341" class="Bound">I</a> <a id="9055" class="Symbol">→</a> <a id="9057" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="9059" href="Universes.html#403" class="Function Operator">̇</a><a id="9060" class="Symbol">)</a> <a id="9062" class="Symbol">→</a> <a id="9064" class="Symbol">(</a><a id="9065" href="Relations.Truncation.html#9065" class="Bound">𝓦</a> <a id="9067" class="Symbol">:</a> <a id="9069" href="Universes.html#205" class="Postulate">Universe</a><a id="9077" class="Symbol">)</a> <a id="9079" class="Symbol">→</a> <a id="9081" href="Relations.Truncation.html#8327" class="Bound">𝓤</a> <a id="9083" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9085" href="Relations.Truncation.html#8345" class="Bound">𝓥</a> <a id="9087" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9089" href="Relations.Truncation.html#9065" class="Bound">𝓦</a> <a id="9091" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9093" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9096" href="Relations.Truncation.html#9037" class="Function">dep-prop-ext</a> <a id="9109" href="Relations.Truncation.html#9109" class="Bound">𝒜</a> <a id="9111" href="Relations.Truncation.html#9111" class="Bound">𝓦</a> <a id="9113" class="Symbol">=</a> <a id="9115" class="Symbol">{</a><a id="9116" href="Relations.Truncation.html#9116" class="Bound">P</a> <a id="9118" href="Relations.Truncation.html#9118" class="Bound">Q</a> <a id="9120" class="Symbol">:</a> <a id="9122" href="Relations.Truncation.html#8932" class="Function">DepProp</a> <a id="9130" href="Relations.Truncation.html#9109" class="Bound">𝒜</a> <a id="9132" href="Relations.Truncation.html#9111" class="Bound">𝓦</a><a id="9133" class="Symbol">}</a> <a id="9135" class="Symbol">→</a> <a id="9137" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9139" href="Relations.Truncation.html#9116" class="Bound">P</a> <a id="9141" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9143" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9145" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9147" href="Relations.Truncation.html#9118" class="Bound">Q</a> <a id="9149" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9151" class="Symbol">→</a> <a id="9153" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9155" href="Relations.Truncation.html#9118" class="Bound">Q</a> <a id="9157" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9159" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9161" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9163" href="Relations.Truncation.html#9116" class="Bound">P</a> <a id="9165" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9167" class="Symbol">→</a> <a id="9169" href="Relations.Truncation.html#9116" class="Bound">P</a> <a id="9171" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="9173" href="Relations.Truncation.html#9118" class="Bound">Q</a>

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



