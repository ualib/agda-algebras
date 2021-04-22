---
layout: default
title : Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation</a>

This section presents the [Relations.Truncation][] module of the [Agda Universal Algebra Library][].

We start with a brief discussion of standard notions of *truncation*, *h-sets* (which we just call *sets*), and the *uniqueness of identity types* principle.
We then prove that a monic function into a *set* is an embedding. The section concludes with a *uniqueness of identity proofs* principle for blocks of equivalence relations.

Readers who want to learn more about "proof-relevant mathematics" and other concepts mentioned in this module may wish to consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

<pre class="Agda">

<a id="1219" class="Symbol">{-#</a> <a id="1223" class="Keyword">OPTIONS</a> <a id="1231" class="Pragma">--without-K</a> <a id="1243" class="Pragma">--exact-split</a> <a id="1257" class="Pragma">--safe</a> <a id="1264" class="Symbol">#-}</a>

<a id="1269" class="Keyword">module</a> <a id="1276" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="1297" class="Keyword">where</a>

<a id="1304" class="Keyword">open</a> <a id="1309" class="Keyword">import</a> <a id="1316" href="Relations.Quotients.html" class="Module">Relations.Quotients</a> <a id="1336" class="Keyword">public</a>

<a id="1344" class="Keyword">open</a> <a id="1349" class="Keyword">import</a> <a id="1356" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="1365" class="Keyword">using</a> <a id="1371" class="Symbol">(</a><a id="1372" href="MGS-MLTT.html#7080" class="Function Operator">_⇔_</a><a id="1375" class="Symbol">)</a> <a id="1377" class="Keyword">public</a>

</pre>

#### <a id="uniqueness-of-identity-proofs">Uniqueness of identity proofs</a>

This brief introduction is intended for novices; those already familiar with the concept of *truncation* and *uniqueness of identity proofs* may want to skip to the next subsection.

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `A` and an identity relation `_≡₀_` on `A` so that, given two inhabitants of `A`, say, `a b : A`, we can form the type `a ≡₀ b`. Suppose `p` and `q` inhabit the type `a ≡₀ b`; that is, `p` and `q` are proofs of `a ≡₀ b`, in which case we write `p q : a ≡₀ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡₀`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡₀ b` are the same.
If such a proof exists for all `p q : a ≡₀ b`, then the proof of `a ≡₀ b` is unique; as a property of
the types `A` and `≡₀`, this is sometimes called <a id="uniqueness-of-identity-proofs">*uniqueness of identity proofs*</a> (uip).

Now, perhaps we have two proofs, say, `r s : p ≡₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

#### <a id="sets">Sets</a>

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library, using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]), as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

<pre class="Agda">

<a id="3805" class="Keyword">module</a> <a id="hide-is-set"></a><a id="3812" href="Relations.Truncation.html#3812" class="Module">hide-is-set</a> <a id="3824" class="Symbol">{</a><a id="3825" href="Relations.Truncation.html#3825" class="Bound">𝓤</a> <a id="3827" class="Symbol">:</a> <a id="3829" href="Universes.html#205" class="Postulate">Universe</a><a id="3837" class="Symbol">}</a> <a id="3839" class="Keyword">where</a>

 <a id="hide-is-set.is-set"></a><a id="3847" href="Relations.Truncation.html#3847" class="Function">is-set</a> <a id="3854" class="Symbol">:</a> <a id="3856" href="Relations.Truncation.html#3825" class="Bound">𝓤</a> <a id="3858" href="Universes.html#403" class="Function Operator">̇</a> <a id="3860" class="Symbol">→</a> <a id="3862" href="Relations.Truncation.html#3825" class="Bound">𝓤</a> <a id="3864" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3867" href="Relations.Truncation.html#3847" class="Function">is-set</a> <a id="3874" href="Relations.Truncation.html#3874" class="Bound">A</a> <a id="3876" class="Symbol">=</a> <a id="3878" class="Symbol">(</a><a id="3879" href="Relations.Truncation.html#3879" class="Bound">x</a> <a id="3881" href="Relations.Truncation.html#3881" class="Bound">y</a> <a id="3883" class="Symbol">:</a> <a id="3885" href="Relations.Truncation.html#3874" class="Bound">A</a><a id="3886" class="Symbol">)</a> <a id="3888" class="Symbol">→</a> <a id="3890" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="3906" class="Symbol">(</a><a id="3907" href="Relations.Truncation.html#3879" class="Bound">x</a> <a id="3909" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="3911" href="Relations.Truncation.html#3881" class="Bound">y</a><a id="3912" class="Symbol">)</a>

<a id="3915" class="Keyword">open</a> <a id="3920" class="Keyword">import</a> <a id="3927" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="3942" class="Keyword">using</a> <a id="3948" class="Symbol">(</a><a id="3949" href="MGS-Basic-UF.html#1929" class="Function">is-set</a><a id="3955" class="Symbol">)</a> <a id="3957" class="Keyword">public</a>

</pre>

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

<pre class="Agda">

<a id="4379" class="Keyword">module</a> <a id="hide-to-Σ-≡"></a><a id="4386" href="Relations.Truncation.html#4386" class="Module">hide-to-Σ-≡</a> <a id="4398" class="Symbol">{</a><a id="4399" href="Relations.Truncation.html#4399" class="Bound">𝓤</a> <a id="4401" href="Relations.Truncation.html#4401" class="Bound">𝓦</a> <a id="4403" class="Symbol">:</a> <a id="4405" href="Universes.html#205" class="Postulate">Universe</a><a id="4413" class="Symbol">}{</a><a id="4415" href="Relations.Truncation.html#4415" class="Bound">A</a> <a id="4417" class="Symbol">:</a> <a id="4419" href="Relations.Truncation.html#4399" class="Bound">𝓤</a> <a id="4421" href="Universes.html#403" class="Function Operator">̇</a><a id="4422" class="Symbol">}{</a><a id="4424" href="Relations.Truncation.html#4424" class="Bound">B</a> <a id="4426" class="Symbol">:</a> <a id="4428" href="Relations.Truncation.html#4415" class="Bound">A</a> <a id="4430" class="Symbol">→</a> <a id="4432" href="Relations.Truncation.html#4401" class="Bound">𝓦</a> <a id="4434" href="Universes.html#403" class="Function Operator">̇</a><a id="4435" class="Symbol">}</a> <a id="4437" class="Keyword">where</a>

 <a id="hide-to-Σ-≡.to-Σ-≡"></a><a id="4445" href="Relations.Truncation.html#4445" class="Function">to-Σ-≡</a> <a id="4452" class="Symbol">:</a> <a id="4454" class="Symbol">{</a><a id="4455" href="Relations.Truncation.html#4455" class="Bound">σ</a> <a id="4457" href="Relations.Truncation.html#4457" class="Bound">τ</a> <a id="4459" class="Symbol">:</a> <a id="4461" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="4463" href="Relations.Truncation.html#4424" class="Bound">B</a><a id="4464" class="Symbol">}</a> <a id="4466" class="Symbol">→</a> <a id="4468" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4470" href="Relations.Truncation.html#4470" class="Bound">p</a> <a id="4472" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4474" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4476" href="Relations.Truncation.html#4455" class="Bound">σ</a> <a id="4478" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4480" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4482" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4484" href="Relations.Truncation.html#4457" class="Bound">τ</a> <a id="4486" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4488" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4490" class="Symbol">(</a><a id="4491" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4501" href="Relations.Truncation.html#4424" class="Bound">B</a> <a id="4503" href="Relations.Truncation.html#4470" class="Bound">p</a> <a id="4505" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4507" href="Relations.Truncation.html#4455" class="Bound">σ</a> <a id="4509" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a><a id="4510" class="Symbol">)</a> <a id="4512" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4514" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4516" href="Relations.Truncation.html#4457" class="Bound">τ</a> <a id="4518" href="Overture.Preliminaries.html#13884" class="Function Operator">∥</a> <a id="4520" class="Symbol">→</a> <a id="4522" href="Relations.Truncation.html#4455" class="Bound">σ</a> <a id="4524" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="4526" href="Relations.Truncation.html#4457" class="Bound">τ</a>
 <a id="4529" href="Relations.Truncation.html#4445" class="Function">to-Σ-≡</a> <a id="4536" class="Symbol">(</a><a id="4537" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4542" class="Symbol">{</a><a id="4543" class="Argument">x</a> <a id="4545" class="Symbol">=</a> <a id="4547" href="Relations.Truncation.html#4547" class="Bound">x</a><a id="4548" class="Symbol">}</a> <a id="4550" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4552" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4557" class="Symbol">{</a><a id="4558" class="Argument">x</a> <a id="4560" class="Symbol">=</a> <a id="4562" href="Relations.Truncation.html#4562" class="Bound">a</a><a id="4563" class="Symbol">})</a> <a id="4566" class="Symbol">=</a> <a id="4568" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4573" class="Symbol">{</a><a id="4574" class="Argument">x</a> <a id="4576" class="Symbol">=</a> <a id="4578" class="Symbol">(</a><a id="4579" href="Relations.Truncation.html#4547" class="Bound">x</a> <a id="4581" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="4583" href="Relations.Truncation.html#4562" class="Bound">a</a><a id="4584" class="Symbol">)}</a>

<a id="4588" class="Keyword">open</a> <a id="4593" class="Keyword">import</a> <a id="4600" href="MGS-Embeddings.html" class="Module">MGS-Embeddings</a> <a id="4615" class="Keyword">using</a> <a id="4621" class="Symbol">(</a><a id="4622" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a><a id="4628" class="Symbol">)</a> <a id="4630" class="Keyword">public</a>

</pre>

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.

<pre class="Agda">

<a id="5545" class="Keyword">module</a> <a id="5552" href="Relations.Truncation.html#5552" class="Module">_</a> <a id="5554" class="Symbol">{</a><a id="5555" href="Relations.Truncation.html#5555" class="Bound">𝓤</a> <a id="5557" href="Relations.Truncation.html#5557" class="Bound">𝓦</a> <a id="5559" class="Symbol">:</a> <a id="5561" href="Universes.html#205" class="Postulate">Universe</a><a id="5569" class="Symbol">}{</a><a id="5571" href="Relations.Truncation.html#5571" class="Bound">A</a> <a id="5573" class="Symbol">:</a> <a id="5575" href="Relations.Truncation.html#5555" class="Bound">𝓤</a> <a id="5577" href="Universes.html#403" class="Function Operator">̇</a><a id="5578" class="Symbol">}{</a><a id="5580" href="Relations.Truncation.html#5580" class="Bound">B</a> <a id="5582" class="Symbol">:</a> <a id="5584" href="Relations.Truncation.html#5557" class="Bound">𝓦</a> <a id="5586" href="Universes.html#403" class="Function Operator">̇</a><a id="5587" class="Symbol">}</a> <a id="5589" class="Keyword">where</a>

 <a id="5597" href="Relations.Truncation.html#5597" class="Function">monic-is-embedding|Set</a> <a id="5620" class="Symbol">:</a> <a id="5622" class="Symbol">(</a><a id="5623" href="Relations.Truncation.html#5623" class="Bound">f</a> <a id="5625" class="Symbol">:</a> <a id="5627" href="Relations.Truncation.html#5571" class="Bound">A</a> <a id="5629" class="Symbol">→</a> <a id="5631" href="Relations.Truncation.html#5580" class="Bound">B</a><a id="5632" class="Symbol">)</a> <a id="5634" class="Symbol">→</a> <a id="5636" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="5643" href="Relations.Truncation.html#5580" class="Bound">B</a> <a id="5645" class="Symbol">→</a> <a id="5647" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="5653" href="Relations.Truncation.html#5623" class="Bound">f</a> <a id="5655" class="Symbol">→</a> <a id="5657" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="5670" href="Relations.Truncation.html#5623" class="Bound">f</a>

 <a id="5674" href="Relations.Truncation.html#5597" class="Function">monic-is-embedding|Set</a> <a id="5697" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5699" href="Relations.Truncation.html#5699" class="Bound">Bset</a> <a id="5704" href="Relations.Truncation.html#5704" class="Bound">fmon</a> <a id="5709" href="Relations.Truncation.html#5709" class="Bound">b</a> <a id="5711" class="Symbol">(</a><a id="5712" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5714" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5716" href="Relations.Truncation.html#5716" class="Bound">fu≡b</a><a id="5720" class="Symbol">)</a> <a id="5722" class="Symbol">(</a><a id="5723" href="Relations.Truncation.html#5723" class="Bound">v</a> <a id="5725" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5727" href="Relations.Truncation.html#5727" class="Bound">fv≡b</a><a id="5731" class="Symbol">)</a> <a id="5733" class="Symbol">=</a> <a id="5735" href="Relations.Truncation.html#5967" class="Function">γ</a>
  <a id="5739" class="Keyword">where</a>
  <a id="5747" href="Relations.Truncation.html#5747" class="Function">fuv</a> <a id="5751" class="Symbol">:</a> <a id="5753" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5755" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5757" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5759" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5761" href="Relations.Truncation.html#5723" class="Bound">v</a>
  <a id="5765" href="Relations.Truncation.html#5747" class="Function">fuv</a> <a id="5769" class="Symbol">=</a> <a id="5771" href="Overture.Equality.html#3061" class="Function">≡-trans</a> <a id="5779" href="Relations.Truncation.html#5716" class="Bound">fu≡b</a> <a id="5784" class="Symbol">(</a><a id="5785" href="Relations.Truncation.html#5727" class="Bound">fv≡b</a> <a id="5790" href="MGS-MLTT.html#6125" class="Function Operator">⁻¹</a><a id="5792" class="Symbol">)</a>

  <a id="5797" href="Relations.Truncation.html#5797" class="Function">uv</a> <a id="5800" class="Symbol">:</a> <a id="5802" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5804" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5806" href="Relations.Truncation.html#5723" class="Bound">v</a>
  <a id="5810" href="Relations.Truncation.html#5797" class="Function">uv</a> <a id="5813" class="Symbol">=</a> <a id="5815" href="Relations.Truncation.html#5704" class="Bound">fmon</a> <a id="5820" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5822" href="Relations.Truncation.html#5723" class="Bound">v</a> <a id="5824" href="Relations.Truncation.html#5747" class="Function">fuv</a>

  <a id="5831" href="Relations.Truncation.html#5831" class="Function">arg1</a> <a id="5836" class="Symbol">:</a> <a id="5838" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5840" href="Relations.Truncation.html#5840" class="Bound">p</a> <a id="5842" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5844" class="Symbol">(</a><a id="5845" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5847" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5849" href="Relations.Truncation.html#5723" class="Bound">v</a><a id="5850" class="Symbol">)</a> <a id="5852" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5854" class="Symbol">(</a><a id="5855" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5865" class="Symbol">(λ</a> <a id="5868" href="Relations.Truncation.html#5868" class="Bound">a</a> <a id="5870" class="Symbol">→</a> <a id="5872" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5874" href="Relations.Truncation.html#5868" class="Bound">a</a> <a id="5876" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5878" href="Relations.Truncation.html#5709" class="Bound">b</a><a id="5879" class="Symbol">)</a> <a id="5881" href="Relations.Truncation.html#5840" class="Bound">p</a> <a id="5883" href="Relations.Truncation.html#5716" class="Bound">fu≡b</a><a id="5887" class="Symbol">)</a> <a id="5889" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5891" href="Relations.Truncation.html#5727" class="Bound">fv≡b</a>
  <a id="5898" href="Relations.Truncation.html#5831" class="Function">arg1</a> <a id="5903" class="Symbol">=</a> <a id="5905" href="Relations.Truncation.html#5797" class="Function">uv</a> <a id="5908" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5910" href="Relations.Truncation.html#5699" class="Bound">Bset</a> <a id="5915" class="Symbol">(</a><a id="5916" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5918" href="Relations.Truncation.html#5723" class="Bound">v</a><a id="5919" class="Symbol">)</a> <a id="5921" href="Relations.Truncation.html#5709" class="Bound">b</a> <a id="5923" class="Symbol">(</a><a id="5924" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="5934" class="Symbol">(λ</a> <a id="5937" href="Relations.Truncation.html#5937" class="Bound">a</a> <a id="5939" class="Symbol">→</a> <a id="5941" href="Relations.Truncation.html#5697" class="Bound">f</a> <a id="5943" href="Relations.Truncation.html#5937" class="Bound">a</a> <a id="5945" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5947" href="Relations.Truncation.html#5709" class="Bound">b</a><a id="5948" class="Symbol">)</a> <a id="5950" href="Relations.Truncation.html#5797" class="Function">uv</a> <a id="5953" href="Relations.Truncation.html#5716" class="Bound">fu≡b</a><a id="5957" class="Symbol">)</a> <a id="5959" href="Relations.Truncation.html#5727" class="Bound">fv≡b</a>

  <a id="5967" href="Relations.Truncation.html#5967" class="Function">γ</a> <a id="5969" class="Symbol">:</a> <a id="5971" href="Relations.Truncation.html#5712" class="Bound">u</a> <a id="5973" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5975" href="Relations.Truncation.html#5716" class="Bound">fu≡b</a> <a id="5980" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="5982" href="Relations.Truncation.html#5723" class="Bound">v</a> <a id="5984" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="5986" href="Relations.Truncation.html#5727" class="Bound">fv≡b</a>
  <a id="5993" href="Relations.Truncation.html#5967" class="Function">γ</a> <a id="5995" class="Symbol">=</a> <a id="5997" href="MGS-Basic-UF.html#7284" class="Function">to-Σ-≡</a> <a id="6004" href="Relations.Truncation.html#5831" class="Function">arg1</a>

</pre>

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a *set* (in the sense defined above), then we add to the name of the theorem the suffix `|Set`, which calls to mind the standard mathematical notation for the restriction of a function.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

<pre class="Agda">

 <a id="6557" href="Relations.Truncation.html#6557" class="Function">embedding-iff-monic|Set</a> <a id="6581" class="Symbol">:</a> <a id="6583" class="Symbol">(</a><a id="6584" href="Relations.Truncation.html#6584" class="Bound">f</a> <a id="6586" class="Symbol">:</a> <a id="6588" href="Relations.Truncation.html#5571" class="Bound">A</a> <a id="6590" class="Symbol">→</a> <a id="6592" href="Relations.Truncation.html#5580" class="Bound">B</a><a id="6593" class="Symbol">)</a> <a id="6595" class="Symbol">→</a> <a id="6597" href="MGS-Basic-UF.html#1929" class="Function">is-set</a> <a id="6604" href="Relations.Truncation.html#5580" class="Bound">B</a> <a id="6606" class="Symbol">→</a> <a id="6608" href="MGS-Embeddings.html#384" class="Function">is-embedding</a> <a id="6621" href="Relations.Truncation.html#6584" class="Bound">f</a> <a id="6623" href="MGS-MLTT.html#7080" class="Function Operator">⇔</a> <a id="6625" href="Overture.Inverses.html#3777" class="Function">Monic</a> <a id="6631" href="Relations.Truncation.html#6584" class="Bound">f</a>
 <a id="6634" href="Relations.Truncation.html#6557" class="Function">embedding-iff-monic|Set</a> <a id="6658" href="Relations.Truncation.html#6658" class="Bound">f</a> <a id="6660" href="Relations.Truncation.html#6660" class="Bound">Bset</a> <a id="6665" class="Symbol">=</a> <a id="6667" class="Symbol">(</a><a id="6668" href="Overture.Inverses.html#5685" class="Function">embedding-is-monic</a> <a id="6687" href="Relations.Truncation.html#6658" class="Bound">f</a><a id="6688" class="Symbol">)</a><a id="6689" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="6691" class="Symbol">(</a><a id="6692" href="Relations.Truncation.html#5597" class="Function">monic-is-embedding|Set</a> <a id="6715" href="Relations.Truncation.html#6658" class="Bound">f</a> <a id="6717" href="Relations.Truncation.html#6660" class="Bound">Bset</a><a id="6721" class="Symbol">)</a>

</pre>


#### <a id="equivalence-class-truncation">Equivalence class truncation</a>

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

In the next module ([Relations.Extensionality][]) we will define a *quotient extensionality* principle that will require a form of unique identity proofs---specifically, we will assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

<pre class="Agda">

<a id="blk-uip"></a><a id="7396" href="Relations.Truncation.html#7396" class="Function">blk-uip</a> <a id="7404" class="Symbol">:</a> <a id="7406" class="Symbol">{</a><a id="7407" href="Relations.Truncation.html#7407" class="Bound">𝓦</a> <a id="7409" href="Relations.Truncation.html#7409" class="Bound">𝓤</a> <a id="7411" class="Symbol">:</a> <a id="7413" href="Universes.html#205" class="Postulate">Universe</a><a id="7421" class="Symbol">}(</a><a id="7423" href="Relations.Truncation.html#7423" class="Bound">A</a> <a id="7425" class="Symbol">:</a> <a id="7427" href="Relations.Truncation.html#7409" class="Bound">𝓤</a> <a id="7429" href="Universes.html#403" class="Function Operator">̇</a><a id="7430" class="Symbol">)(</a><a id="7432" href="Relations.Truncation.html#7432" class="Bound">R</a> <a id="7434" class="Symbol">:</a> <a id="7436" href="Relations.Discrete.html#4335" class="Function">Rel</a> <a id="7440" href="Relations.Truncation.html#7423" class="Bound">A</a> <a id="7442" href="Relations.Truncation.html#7407" class="Bound">𝓦</a> <a id="7444" class="Symbol">)</a> <a id="7446" class="Symbol">→</a> <a id="7448" href="Relations.Truncation.html#7409" class="Bound">𝓤</a> <a id="7450" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7452" href="Relations.Truncation.html#7407" class="Bound">𝓦</a> <a id="7454" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="7456" href="Universes.html#403" class="Function Operator">̇</a>
<a id="7458" href="Relations.Truncation.html#7396" class="Function">blk-uip</a> <a id="7466" class="Symbol">{</a><a id="7467" href="Relations.Truncation.html#7467" class="Bound">𝓦</a><a id="7468" class="Symbol">}</a> <a id="7470" href="Relations.Truncation.html#7470" class="Bound">A</a> <a id="7472" href="Relations.Truncation.html#7472" class="Bound">R</a> <a id="7474" class="Symbol">=</a> <a id="7476" class="Symbol">∀</a> <a id="7478" class="Symbol">(</a><a id="7479" href="Relations.Truncation.html#7479" class="Bound">C</a> <a id="7481" class="Symbol">:</a> <a id="7483" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="7488" href="Relations.Truncation.html#7470" class="Bound">A</a> <a id="7490" href="Relations.Truncation.html#7467" class="Bound">𝓦</a><a id="7491" class="Symbol">)</a> <a id="7493" class="Symbol">→</a> <a id="7495" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="7511" class="Symbol">(</a><a id="7512" href="Relations.Quotients.html#3881" class="Function">IsBlock</a> <a id="7520" href="Relations.Truncation.html#7479" class="Bound">C</a> <a id="7522" class="Symbol">{</a><a id="7523" href="Relations.Truncation.html#7472" class="Bound">R</a><a id="7524" class="Symbol">})</a>

</pre>

It might seem unreasonable to postulate that there is at most one inhabitant of `IsBlock C`, since equivalence classes typically have multiple members, any one of which could serve as a class representative.  However, postulating `blk-uip A R` is tantamount to collapsing each `R`-block to a single point, and this is indeed the correct semantic interpretation of the elements of the quotient `A / R`.

----------------------------

#### <a id="general-propositions">General propositions*</a>

This section defines more general truncated predicates which we call *continuous propositions* and *dependent propositions*. Recall, above (in the [Relations.Continuous][] module) we defined types called `ContRel` and `DepRel` to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and *truncated dependent relation type*, the inhabitants of which we will call *continuous propositions* and *dependent propositions*, respectively.

<pre class="Agda">

<a id="8581" class="Keyword">module</a> <a id="8588" href="Relations.Truncation.html#8588" class="Module">_</a> <a id="8590" class="Symbol">{</a><a id="8591" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8593" class="Symbol">:</a> <a id="8595" href="Universes.html#205" class="Postulate">Universe</a><a id="8603" class="Symbol">}{</a><a id="8605" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="8607" class="Symbol">:</a> <a id="8609" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="8611" href="Universes.html#403" class="Function Operator">̇</a><a id="8612" class="Symbol">}</a> <a id="8614" class="Keyword">where</a>

 <a id="8622" class="Keyword">open</a> <a id="8627" class="Keyword">import</a> <a id="8634" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="8655" class="Keyword">using</a> <a id="8661" class="Symbol">(</a><a id="8662" href="Relations.Continuous.html#3130" class="Function">ContRel</a><a id="8669" class="Symbol">;</a> <a id="8671" href="Relations.Continuous.html#3214" class="Function">DepRel</a><a id="8677" class="Symbol">)</a>

 <a id="8681" href="Relations.Truncation.html#8681" class="Function">IsContProp</a> <a id="8692" class="Symbol">:</a> <a id="8694" class="Symbol">{</a><a id="8695" href="Relations.Truncation.html#8695" class="Bound">A</a> <a id="8697" class="Symbol">:</a> <a id="8699" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8701" href="Universes.html#403" class="Function Operator">̇</a><a id="8702" class="Symbol">}{</a><a id="8704" href="Relations.Truncation.html#8704" class="Bound">𝓦</a> <a id="8706" class="Symbol">:</a> <a id="8708" href="Universes.html#205" class="Postulate">Universe</a><a id="8716" class="Symbol">}</a> <a id="8718" class="Symbol">→</a> <a id="8720" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="8728" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="8730" href="Relations.Truncation.html#8695" class="Bound">A</a> <a id="8732" href="Relations.Truncation.html#8704" class="Bound">𝓦</a>  <a id="8735" class="Symbol">→</a> <a id="8737" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="8739" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8741" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8743" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8745" href="Relations.Truncation.html#8704" class="Bound">𝓦</a> <a id="8747" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8750" href="Relations.Truncation.html#8681" class="Function">IsContProp</a> <a id="8761" class="Symbol">{</a><a id="8762" class="Argument">A</a> <a id="8764" class="Symbol">=</a> <a id="8766" href="Relations.Truncation.html#8766" class="Bound">A</a><a id="8767" class="Symbol">}</a> <a id="8769" href="Relations.Truncation.html#8769" class="Bound">P</a> <a id="8771" class="Symbol">=</a> <a id="8773" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8775" href="Relations.Truncation.html#8775" class="Bound">𝑎</a> <a id="8777" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8779" class="Symbol">(</a><a id="8780" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="8782" class="Symbol">→</a> <a id="8784" href="Relations.Truncation.html#8766" class="Bound">A</a><a id="8785" class="Symbol">)</a> <a id="8787" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8789" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="8805" class="Symbol">(</a><a id="8806" href="Relations.Truncation.html#8769" class="Bound">P</a> <a id="8808" href="Relations.Truncation.html#8775" class="Bound">𝑎</a><a id="8809" class="Symbol">)</a>

 <a id="8813" href="Relations.Truncation.html#8813" class="Function">ContProp</a> <a id="8822" class="Symbol">:</a> <a id="8824" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8826" href="Universes.html#403" class="Function Operator">̇</a> <a id="8828" class="Symbol">→</a> <a id="8830" class="Symbol">(</a><a id="8831" href="Relations.Truncation.html#8831" class="Bound">𝓦</a> <a id="8833" class="Symbol">:</a> <a id="8835" href="Universes.html#205" class="Postulate">Universe</a><a id="8843" class="Symbol">)</a> <a id="8845" class="Symbol">→</a> <a id="8847" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8849" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8851" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="8853" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8855" href="Relations.Truncation.html#8831" class="Bound">𝓦</a> <a id="8857" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8859" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8862" href="Relations.Truncation.html#8813" class="Function">ContProp</a> <a id="8871" href="Relations.Truncation.html#8871" class="Bound">A</a> <a id="8873" href="Relations.Truncation.html#8873" class="Bound">𝓦</a> <a id="8875" class="Symbol">=</a> <a id="8877" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="8879" href="Relations.Truncation.html#8879" class="Bound">P</a> <a id="8881" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="8883" class="Symbol">(</a><a id="8884" href="Relations.Continuous.html#3130" class="Function">ContRel</a> <a id="8892" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="8894" href="Relations.Truncation.html#8871" class="Bound">A</a> <a id="8896" href="Relations.Truncation.html#8873" class="Bound">𝓦</a><a id="8897" class="Symbol">)</a> <a id="8899" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="8901" href="Relations.Truncation.html#8681" class="Function">IsContProp</a> <a id="8912" href="Relations.Truncation.html#8879" class="Bound">P</a>

 <a id="8916" href="Relations.Truncation.html#8916" class="Function">cont-prop-ext</a> <a id="8930" class="Symbol">:</a> <a id="8932" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8934" href="Universes.html#403" class="Function Operator">̇</a> <a id="8936" class="Symbol">→</a> <a id="8938" class="Symbol">(</a><a id="8939" href="Relations.Truncation.html#8939" class="Bound">𝓦</a> <a id="8941" class="Symbol">:</a> <a id="8943" href="Universes.html#205" class="Postulate">Universe</a><a id="8951" class="Symbol">)</a> <a id="8953" class="Symbol">→</a> <a id="8955" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="8957" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8959" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="8961" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8963" href="Relations.Truncation.html#8939" class="Bound">𝓦</a> <a id="8965" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="8967" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8970" href="Relations.Truncation.html#8916" class="Function">cont-prop-ext</a> <a id="8984" href="Relations.Truncation.html#8984" class="Bound">A</a> <a id="8986" href="Relations.Truncation.html#8986" class="Bound">𝓦</a> <a id="8988" class="Symbol">=</a> <a id="8990" class="Symbol">{</a><a id="8991" href="Relations.Truncation.html#8991" class="Bound">P</a> <a id="8993" href="Relations.Truncation.html#8993" class="Bound">Q</a> <a id="8995" class="Symbol">:</a> <a id="8997" href="Relations.Truncation.html#8813" class="Function">ContProp</a> <a id="9006" href="Relations.Truncation.html#8984" class="Bound">A</a> <a id="9008" href="Relations.Truncation.html#8986" class="Bound">𝓦</a> <a id="9010" class="Symbol">}</a> <a id="9012" class="Symbol">→</a> <a id="9014" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9016" href="Relations.Truncation.html#8991" class="Bound">P</a> <a id="9018" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9020" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9022" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9024" href="Relations.Truncation.html#8993" class="Bound">Q</a> <a id="9026" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9028" class="Symbol">→</a> <a id="9030" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9032" href="Relations.Truncation.html#8993" class="Bound">Q</a> <a id="9034" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9036" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9038" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9040" href="Relations.Truncation.html#8991" class="Bound">P</a> <a id="9042" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9044" class="Symbol">→</a> <a id="9046" href="Relations.Truncation.html#8991" class="Bound">P</a> <a id="9048" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="9050" href="Relations.Truncation.html#8993" class="Bound">Q</a>

 <a id="9054" href="Relations.Truncation.html#9054" class="Function">IsDepProp</a> <a id="9064" class="Symbol">:</a> <a id="9066" class="Symbol">{</a><a id="9067" href="Relations.Truncation.html#9067" class="Bound">I</a> <a id="9069" class="Symbol">:</a> <a id="9071" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="9073" href="Universes.html#403" class="Function Operator">̇</a><a id="9074" class="Symbol">}{</a><a id="9076" href="Relations.Truncation.html#9076" class="Bound">𝒜</a> <a id="9078" class="Symbol">:</a> <a id="9080" href="Relations.Truncation.html#9067" class="Bound">I</a> <a id="9082" class="Symbol">→</a> <a id="9084" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9086" href="Universes.html#403" class="Function Operator">̇</a><a id="9087" class="Symbol">}{</a><a id="9089" href="Relations.Truncation.html#9089" class="Bound">𝓦</a> <a id="9091" class="Symbol">:</a> <a id="9093" href="Universes.html#205" class="Postulate">Universe</a><a id="9101" class="Symbol">}</a> <a id="9103" class="Symbol">→</a> <a id="9105" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="9112" href="Relations.Truncation.html#9067" class="Bound">I</a> <a id="9114" href="Relations.Truncation.html#9076" class="Bound">𝒜</a> <a id="9116" href="Relations.Truncation.html#9089" class="Bound">𝓦</a>  <a id="9119" class="Symbol">→</a> <a id="9121" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="9123" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9125" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9127" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9129" href="Relations.Truncation.html#9089" class="Bound">𝓦</a> <a id="9131" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9134" href="Relations.Truncation.html#9054" class="Function">IsDepProp</a> <a id="9144" class="Symbol">{</a><a id="9145" class="Argument">I</a> <a id="9147" class="Symbol">=</a> <a id="9149" href="Relations.Truncation.html#9149" class="Bound">I</a><a id="9150" class="Symbol">}</a> <a id="9152" class="Symbol">{</a><a id="9153" href="Relations.Truncation.html#9153" class="Bound">𝒜</a><a id="9154" class="Symbol">}</a> <a id="9156" href="Relations.Truncation.html#9156" class="Bound">P</a> <a id="9158" class="Symbol">=</a> <a id="9160" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="9162" href="Relations.Truncation.html#9162" class="Bound">𝑎</a> <a id="9164" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="9166" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="9168" href="Relations.Truncation.html#9153" class="Bound">𝒜</a> <a id="9170" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="9172" href="MGS-Basic-UF.html#743" class="Function">is-subsingleton</a> <a id="9188" class="Symbol">(</a><a id="9189" href="Relations.Truncation.html#9156" class="Bound">P</a> <a id="9191" href="Relations.Truncation.html#9162" class="Bound">𝑎</a><a id="9192" class="Symbol">)</a>

 <a id="9196" href="Relations.Truncation.html#9196" class="Function">DepProp</a> <a id="9204" class="Symbol">:</a> <a id="9206" class="Symbol">(</a><a id="9207" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="9209" class="Symbol">→</a> <a id="9211" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9213" href="Universes.html#403" class="Function Operator">̇</a><a id="9214" class="Symbol">)</a> <a id="9216" class="Symbol">→</a> <a id="9218" class="Symbol">(</a><a id="9219" href="Relations.Truncation.html#9219" class="Bound">𝓦</a> <a id="9221" class="Symbol">:</a> <a id="9223" href="Universes.html#205" class="Postulate">Universe</a><a id="9231" class="Symbol">)</a> <a id="9233" class="Symbol">→</a> <a id="9235" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9237" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9239" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="9241" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9243" href="Relations.Truncation.html#9219" class="Bound">𝓦</a> <a id="9245" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9247" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9250" href="Relations.Truncation.html#9196" class="Function">DepProp</a> <a id="9258" href="Relations.Truncation.html#9258" class="Bound">𝒜</a> <a id="9260" href="Relations.Truncation.html#9260" class="Bound">𝓦</a> <a id="9262" class="Symbol">=</a> <a id="9264" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="9266" href="Relations.Truncation.html#9266" class="Bound">P</a> <a id="9268" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="9270" class="Symbol">(</a><a id="9271" href="Relations.Continuous.html#3214" class="Function">DepRel</a> <a id="9278" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="9280" href="Relations.Truncation.html#9258" class="Bound">𝒜</a> <a id="9282" href="Relations.Truncation.html#9260" class="Bound">𝓦</a><a id="9283" class="Symbol">)</a> <a id="9285" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="9287" href="Relations.Truncation.html#9054" class="Function">IsDepProp</a> <a id="9297" href="Relations.Truncation.html#9266" class="Bound">P</a>

 <a id="9301" href="Relations.Truncation.html#9301" class="Function">dep-prop-ext</a> <a id="9314" class="Symbol">:</a> <a id="9316" class="Symbol">(</a><a id="9317" href="Relations.Truncation.html#8605" class="Bound">I</a> <a id="9319" class="Symbol">→</a> <a id="9321" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9323" href="Universes.html#403" class="Function Operator">̇</a><a id="9324" class="Symbol">)</a> <a id="9326" class="Symbol">→</a> <a id="9328" class="Symbol">(</a><a id="9329" href="Relations.Truncation.html#9329" class="Bound">𝓦</a> <a id="9331" class="Symbol">:</a> <a id="9333" href="Universes.html#205" class="Postulate">Universe</a><a id="9341" class="Symbol">)</a> <a id="9343" class="Symbol">→</a> <a id="9345" href="Relations.Truncation.html#8591" class="Bound">𝓤</a> <a id="9347" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9349" href="Relations.Truncation.html#8609" class="Bound">𝓥</a> <a id="9351" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9353" href="Relations.Truncation.html#9329" class="Bound">𝓦</a> <a id="9355" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="9357" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9360" href="Relations.Truncation.html#9301" class="Function">dep-prop-ext</a> <a id="9373" href="Relations.Truncation.html#9373" class="Bound">𝒜</a> <a id="9375" href="Relations.Truncation.html#9375" class="Bound">𝓦</a> <a id="9377" class="Symbol">=</a> <a id="9379" class="Symbol">{</a><a id="9380" href="Relations.Truncation.html#9380" class="Bound">P</a> <a id="9382" href="Relations.Truncation.html#9382" class="Bound">Q</a> <a id="9384" class="Symbol">:</a> <a id="9386" href="Relations.Truncation.html#9196" class="Function">DepProp</a> <a id="9394" href="Relations.Truncation.html#9373" class="Bound">𝒜</a> <a id="9396" href="Relations.Truncation.html#9375" class="Bound">𝓦</a><a id="9397" class="Symbol">}</a> <a id="9399" class="Symbol">→</a> <a id="9401" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9403" href="Relations.Truncation.html#9380" class="Bound">P</a> <a id="9405" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9407" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9409" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9411" href="Relations.Truncation.html#9382" class="Bound">Q</a> <a id="9413" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9415" class="Symbol">→</a> <a id="9417" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9419" href="Relations.Truncation.html#9382" class="Bound">Q</a> <a id="9421" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9423" href="Relations.Discrete.html#2147" class="Function Operator">⊆</a> <a id="9425" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9427" href="Relations.Truncation.html#9380" class="Bound">P</a> <a id="9429" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="9431" class="Symbol">→</a> <a id="9433" href="Relations.Truncation.html#9380" class="Bound">P</a> <a id="9435" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="9437" href="Relations.Truncation.html#9382" class="Bound">Q</a>

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



